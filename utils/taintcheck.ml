(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(** Support for adding dynamic taint analysis to an IR program. Taint
    analysis is performed at the bit level. 
*)

open Vine
open Vine_util

module EString = ExtString.String;;

module StringMap = Map.Make(String);;

(** Creates shadows for all variables in the program.
    @return Program with added decls, and (opaque) mapping 
    from variable name to shadow-variable-name. The latter
    must be passed to other functions in this module.
*)
let create_shadows prog =
  let prefix = "shadow_" in

  let rec type_to_shadow_type t =
    t
    (*
    match t with
    | REG_1 | REG_8 | REG_16 | REG_32 | REG_64 ->
        REG_1
    | Array(idx, vt) ->
        Array(idx, type_to_shadow_type vt)
      | _ -> raise (Unimplemented "type_to_shadow") *)
  in

  let vis =
object
  inherit nop_vine_visitor
  val mutable shadowmap = StringMap.empty
  method get_shadowmap = shadowmap
  method visit_stmt s =
    match s with
    | Block(dl, sl) ->
        let shadowmap', dl' = 
          List.fold_left 
            (fun (shadowmap, decls) (decl:decl) ->
               let v,t = decl in
               (* if this fails, I'll need to do something smarter
                  to avoid naming collisions *)
               assert(not (EString.starts_with v prefix));

               let shadow_t = type_to_shadow_type t in
               let shadow_v = prefix ^ v in
               StringMap.add v (shadow_v, shadow_t) shadowmap,
               (shadow_v, shadow_t)::decl::decls)
            (shadowmap, [])
            dl
        in
        shadowmap <- shadowmap';
        ChangeDoChildrenPost(Block(dl',sl), id)
    | _ -> SkipChildren
end
  in
  let stmt_block = match prog with (dl, sl) -> Block(dl, sl) in
  let stmt_block' = stmt_accept vis stmt_block in
  let prog' = match stmt_block' with Block(dl, sl) -> (dl, sl) in
  prog', vis#get_shadowmap

(** @return an lval corresponding to the shadow variable of the
    given lval
*)
let lval_to_shadow lv shadowmap = 
  match lv with
  | Temp(v,t) -> 
      let shadow_v, shadow_t = StringMap.find v shadowmap in
      Temp(shadow_v, shadow_t)
  | Mem(v,t,idx) ->
      let shadow_v, shadow_t = StringMap.find v shadowmap in
      Mem(shadow_v, shadow_t, idx)

(** @return an expression for the taintedness of an expression *)
let tainted_exp exp shadowmap =
  let vis =
object(v)
  inherit nop_vine_visitor
  method visit_rlvalue lv =
    ChangeTo(lval_to_shadow lv shadowmap)

  method visit_exp exp =
    match exp with
    | Let(x, y, exp') ->
        ChangeDoChildrenPost(exp',
                             fun e -> 
                               Let(lval_to_shadow x shadowmap,
                                   exp_accept v y,
                                   Let(x,
                                       y, 
                                       e)))

    | BinOp(op, x, y) -> (
        match op with
          (* bitwise operations *)
        | BITAND | BITOR | XOR ->
            ChangeDoChildrenPost(BinOp(BITOR, x, y), id)
          (* shifts. not tainting lhs by rhs *)
        | LSHIFT | RSHIFT | ARSHIFT ->
            (* XXX: should special-case ARSHIFT, since shifted
               since new high bits depend on old high bit *)
            ChangeDoChildrenPost(BinOp(op, x, y), id)
           (* "munging ops", where result depends on all\most bits
              of operands. *)
        | PLUS | MINUS | TIMES | DIVIDE | SDIVIDE | MOD ->
            let x' = exp_accept v x in
            let y' = exp_accept v y in
            let x_t = Vine_typecheck.infer_type None x' in
            let y_t = Vine_typecheck.infer_type None y' in
            let res_t = Vine_typecheck.infer_type None exp in
            ChangeTo(
              Cast(CAST_SIGNED, res_t, 
                     BinOp(BITOR,
                           BinOp(NEQ, x', Constant(x_t, Int(0L))),
                           BinOp(NEQ, y', Constant(y_t, Int(0L))))))
            
	| EQ | NEQ | LT | LE | SLT | SLE ->
            let x' = exp_accept v x in
            let y' = exp_accept v y in
            let t = Vine_typecheck.infer_type None x' in
            ChangeTo(BinOp(BITOR,
                         BinOp(NEQ, x', Constant(t, Int(0L))),
                         BinOp(NEQ, y', Constant(t, Int(0L)))))
      )
    | UnOp(op, x) ->
        ChangeTo(exp_accept v x)
    | Constant(t, _) ->
        ChangeTo(Constant(t, Int(0L)))
    | Name _ ->
        raise (Unimplemented "tainted_exp: Name")
    | Unknown _ ->
        raise (Unimplemented "tainted_exp: Unknown")
    | Cast(ct, t, e) ->
        (* leave cast in- it mostly does the right thing.
           possible exception is signed  casts *)
        DoChildren
    | Lval(lv) -> 
        DoChildren
end
  in
  exp_accept vis exp 

(** Adds taint-tracking to a program. Assumes that variables
    starting with INPUT correspond to a taint-source, and ignores
    them. *)
let add_tracking prog shadowmap =
  let vis =
object
  inherit nop_vine_visitor
  method visit_stmt stmt =
    match stmt with
    | Move(Temp(v, _), rhs) when (EString.starts_with v "INPUT") ->
        (* don't add tracking for initialization stmts. XXX hackish *)
        SkipChildren
    | Move(lhs, rhs) ->
        let mov = Move(lhs, rhs)  in
        ChangeDoChildrenPost(mov,
                             (fun shadow_mov ->
                                Block([], [shadow_mov; mov])))
    | Block _ -> DoChildren
    | _ -> SkipChildren

  method visit_exp exp =
    ChangeTo(tainted_exp exp shadowmap)
      
  method visit_alvalue lv =
    ChangeTo(lval_to_shadow lv shadowmap)
end
  in
  let stmt_block = match prog with (dl, sl) -> Block(dl, sl) in
  let stmt_block' = stmt_accept vis stmt_block in
  match stmt_block' with Block(dl, sl) -> (dl, sl)

(** Adds taint-seeding to a program. Initializes the shadow
    of every variable whose name starts with INPUT to be tainted. *)
let add_seeds prog shadowmap =
  let rec _add_seeds shadowmap stmt =
    match stmt with
    | Block(dl, sl) ->
        let movs = 
          List.fold_left
            (fun movs (v, t) ->
               if EString.starts_with v "INPUT" then             
                 Move(lval_to_shadow (Temp(v,t)) shadowmap,
                      Constant(t, Int(-1L)))::movs
               else
                 movs)
            []
            dl 
        in
        (* XXX: what if there is a label at start of block, and
           we jump over the movs? *)
        let sl' = List.map (_add_seeds shadowmap) sl in
        Block(dl, List.rev_append movs sl')
    | s -> s
        
  in
  let stmt_block = match prog with (dl, sl) -> Block(dl, sl) in
  let stmt_block' = _add_seeds shadowmap stmt_block in
  match stmt_block' with Block(dl, sl) -> (dl, sl)
  
(** Adds "taint asserts" to indirect jumps. These are simply
    assignments to a boolean variable, s.t. the variable is set to
    true iff the expression used in the jump is tainted.
    @return updated program, and an IR expression for the
    BITOR of the assigned variables.
*)
let add_ijmp_asserts prog shadowmap =
  let vis =
object(o)
  inherit nop_vine_visitor
  val mutable ctr = 0
  val mutable decls = [] 

  method get_decls = decls

  method exp_to_assert exp =
    let var =  "tassert_" ^ (string_of_int ctr) in 
    ctr <- ctr + 1;
    let tmp = Temp(var, REG_1) in

    let t = Vine_typecheck.infer_type None exp in    
    decls <- (var, REG_1)::decls;
    Vine.Block([],
               [Move(tmp, 
                     BinOp(NEQ, 
                           tainted_exp exp shadowmap, 
                           Constant(t, Int(0L))));
                Move(Temp("post_vc", REG_1),
                     BinOp(BITOR,
                           Lval(tmp),
                           Lval(Temp("post_vc", REG_1))))])
      
  method visit_stmt stmt =
    match stmt with
    | Jmp(e) when (match e with Name _ -> false | _ -> true) ->
        ChangeTo(Block([], [o#exp_to_assert e; stmt]))
    | Block _ -> DoChildren
    | _ -> SkipChildren
end
  in
  let stmt_block = match prog with (dl, sl) -> Block(dl, sl) in
  let stmt_block = stmt_accept vis stmt_block in
  let assert_conj = 
    List.fold_left 
      (fun assert_conj (var, t) -> 
         BinOp(BITOR, Lval(Temp(var, t)), assert_conj))
      exp_false
      vis#get_decls
  in
  let (dl, sl) = match stmt_block with Block(dl, sl) -> (dl, sl) in
  ((List.rev_append (vis#get_decls) dl), sl), assert_conj
