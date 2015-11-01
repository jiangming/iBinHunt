(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(**
   Functions for finding the sets of values that a variable
   can take on in a program, using stp.
   Also some high-level interfaces for stp that may be generally
   useful.

   @author Jim Newsome
*)


module V = Vine ;;
module List = ExtList.List ;;
module D = Debug.Make(struct let name=Sys.argv.(0) and default=`Debug end)

(* ternary bool *)
type tbool_t = TRUE | FALSE | UNKNOWN ;;

type direction_t = LEFT | RIGHT ;;
type hole_t = int64 * int64 * direction_t ;; (* false pt, unknown pt,
                                            direction *)

(** set this to a valid fd to dump stp state *)
let stp_fd = ref Unix.stdout;;
let write_stp = ref false;;

let redirect_stp_to filename =
  let stp_out = open_out filename in
  stp_fd := Unix.descr_of_out_channel stp_out;
  write_stp := true

(* if write_stp_to has previously been called,
   call f with stdout remapped to stp_fd.
   otherwise, do nothing.
*)
let redirect_to_stp f =
  if !write_stp then
    Vine_util.run_with_remapped_fd !stp_fd Unix.stdout f
  else
    ()

let bool_of_tbool x =
  match x with
  | FALSE -> false
  | TRUE -> true
  | UNKNOWN -> raise (Invalid_argument "bool_of_tbool")
;;

let tbool_of_bool x = 
  if x then TRUE else FALSE
;;

type valset_t = {
  ranges : (int64 * int64 * tbool_t) list;
  vine_t : V.typ;
} ;;

type valset_state_t = {
  vc : Stpvc.vc;
  ctx : Vine_stpvc.ctx;
  exp_val_var : Vine.var;
} ;;

let counts_of_valset vs =
  List.fold_left
    (fun (tcount, fcount, ucount) (x,y,b) ->
       assert((Int64.compare x y) <= 0);
       let size = Int64.succ (Int64.sub y x) in
       match b with
       | TRUE -> 
           Int64.add tcount size, fcount, ucount
       | FALSE -> 
           tcount, Int64.add fcount size, ucount
       | UNKNOWN -> 
           tcount, fcount, Int64.add ucount size
    )
    (0L, 0L, 0L)
    vs.ranges
;;

let log2_of_int64 x =
  let x = Int64.to_float x in
  (log x) /. (log 2.0)
;;

let influence_bounds_of_valset vs =
  let tcount, fcount, ucount = counts_of_valset vs in
  let low = log2_of_int64 tcount in
  let high = log2_of_int64 (Int64.add tcount ucount) in
  (low, high)
;;

(** @param vs
    @return (lowest UNKNOWN\FALSE, highest UNKNOWN\FALSE 
*)
let lh_bounds_of_valset vs = 
  let first, last = 
    List.fold_left 
      (fun (first, last) (x,y,b) ->
         match b with
         | FALSE -> first, last
         | UNKNOWN 
         | TRUE -> 
             let first =
               match first with
               | None -> Some(x)
               | Some _ -> first
             in
             let last = Some(y) in
             first, last)
      (None, None)
      vs.ranges
  in
  match first, last with
  | Some(x), Some(y) -> x, y
  | _ -> raise Not_found
;;

let pp_range pr (x,y,b) =
  let s = Printf.sprintf "(%Lx, %Lx, %s)"
    x y (match b with 
           TRUE -> "T" | FALSE -> "F" | UNKNOWN -> "U")
  in
  pr s
;;

let pp_ranges pr ranges =
  List.iter
    (pp_range pr)
    ranges
;;

(** @param printer
    @param value set
    print value set 
*)
let pp_valset pr vs =
  pp_ranges pr vs.ranges
;;


(** use cairo to make a postscript visual representation
    of a valset *)
let valset_to_ps filename width height vs unknown_frac = 
  failwith "valset_to_ps disabled for the moment. code is in valset_cairo.ml"

(** @param vine expression, which should evaluate to an integer
    @return resulting int64
*)
let eval_exp expr =
  let raise_eval_exp_error x =
    failwith "operands did not evaluate to constants"
  in
  let folded = 
    Vine_opt.constant_fold
      raise_eval_exp_error
      expr
  in
  match folded with
  | V.Constant(V.Int(_,i)) -> i
  | _ -> 
      Printf.printf "%s simplified to %s\n" 
        (V.exp_to_string expr)
        (V.exp_to_string folded);
      failwith "eval_exp: expected a constant int"
;;

(** @param hole specification
    @param vine type that the hole corresponds to
    @return difference between true and false points
*)
let hole_size ((f_pt, u_pt, dir):hole_t) vine_t =
  eval_exp
    (V.BinOp(V.MINUS,
             V.const_of_int64 
               vine_t
               (match dir with RIGHT -> u_pt | LEFT -> f_pt),
             V.const_of_int64
               vine_t
               (match dir with RIGHT -> f_pt | LEFT -> u_pt)))
;;

let hole_to_string (f,t,d) =
  Printf.sprintf "(f:%Ld, u:%Ld, %s)"
    f t (match d with LEFT -> "L" | RIGHT -> "R")
;;


let pp_hole pr (f,t,d) =
  let s = hole_to_string (f,t,d) in
  pr s;
  flush_all ()
;;

(** @param sorted ranges
    @param range to insert
    @return sorted ranges with range inserted, merging
    with other ranges when appropriate
*)
let insert_range ranges range =
  let rec foo acc ((l_i, h_i, b_i) as range) ranges =
    match ranges with
      (* end of list *)
    | [] -> (l_i,h_i,b_i)::acc
      (* inserted range goes here *)
    | (l,h,b) :: tl when l > h_i ->
        if b = b_i && (Int64.succ h_i) = l then
          List.rev_append tl ((l_i,h,b)::acc) (* merge *)
        else
          List.rev_append ranges ((l_i,h_i,b_i)::acc)
      (* delete ranges contained in range to insert *)
    | (l,h,b) :: tl when l >= l_i && h <= h_i ->
        assert (b = b_i || b = UNKNOWN); 
        foo acc (l_i, h_i, b_i) tl
      (* before irange - add to accumulator *)
    | (l,h,b) :: tl when l < l_i && h < l_i ->
        if b = b_i && (Int64.succ h) = l_i then 
          (* merge *)
          foo acc (l, h_i, b_i) tl
        else
          foo ((l,h,b)::acc) (l_i,h_i,b_i) tl
    (* overlapping cases *)
    | (l,h,b) :: tl ->
        (* break off part after inserted range *)
        let tl = 
          if (h > h_i) then  (
            assert (l <= h_i);
            (Int64.succ h_i, h, b) :: tl
          ) else
            tl
        in
        
        (* drop part overlapping with inserted range *)
        (* (no action) *)

        (* break off part before inserted range *)
        let tl = 
          if (l < l_i) then (
            assert (h >= l_i);
            (l, Int64.pred l_i, b) :: tl
          ) else
            tl
        in
        
        foo acc (l_i,h_i,b_i) tl
  in
  let ranges = 
    List.rev (foo [] range ranges)
  in
  ranges
;;

(** @param valset with sorted ranges
    @param range to insert
    @return valset with with range inserted, merging
    with other ranges when appropriate
*)
let valset_insert_range valset range =
  {valset with ranges = insert_range valset.ranges range}
;;

let rec ranges_point ranges x =
  match ranges with
  | [] -> 
      raise Not_found
  | (l,h,b) :: _ when x > h ->
      raise Not_found
  | (l,h,b) :: tl when x < l ->
      ranges_point tl x
  | (_,_,b) :: _ -> b
;;

(* let optimize_cfg (chop:Vine.stmt list #Vine_cfg.cfg) varsused =  *)
(*   let () = Vine_dataflow.do_dce ~globals:varsused chop in *)
(*   let () = Vine_dataflow.cp_cfg_substitution true chop in *)
(*   let () = Vine_dataflow.do_dce ~globals:varsused chop in *)
(*   let () = Vine_dataflow.cp_cfg_substitution true chop in *)
(*   let () = Vine_dataflow.do_dce ~globals:varsused chop in *)
(*   let () = Vine_dataflow.cp_cfg_substitution true chop in *)
(*   let () = Vine_dataflow.do_dce ~globals:varsused chop in *)

(*   let () = Vine_cfg.coalesce_bb chop in *)
(*   let () = Vine_dataflow.cp_cfg_substitution true chop in *)
(*   let () = Vine_dataflow.do_dce ~globals:varsused chop in *)
(*   let () = Vine_dataflow.cp_cfg_substitution true chop in *)
(*   let () = Vine_dataflow.do_dce ~globals:varsused chop in *)
(*   let () = Vine_dataflow.cp_cfg_substitution true chop in *)
(*   let () = Vine_dataflow.do_dce ~globals:varsused chop in *)

(* (\*   let () = Vine_dataflow.do_dce ~globals:varsused chop in *\) *)
(* (\*   let () = chop#iter_bb *\) *)
(* (\*     (fun bb -> *\) *)
(* (\*        let stmts = chop#get_info bb in  *\) *)
(* (\*        let stmts = Vine_opt.coalesce_stmts stmts 2 in *\) *)
(* (\* 	 chop#set_info bb stmts *\) *)
(* (\*     )   *\) *)
(* (\*   in  *\) *)
(* (\*   let () = Vine_dataflow.do_dce ~globals:varsused chop in *\) *)
(*   chop *)

let name_of_var v =
  let (_,n,_) = v in 
  n

let typ_of_var v =
  let (_,_,t) = v in 
  t

let max_of_typ t =
  Int64.shift_right_logical 
    0xffffffffffffffffL
    (64 - (V.bits_of_width t))

let exp_to_stp_bool vc ctx e =
  let e = Vine_stpvc.vine_to_stp vc ctx e in
  Stpvc.e_bvbitextract vc e 0

let rename_all_prog (dl, sl) =
  (* maps old vars to new vars *)
  let varmap = V.VarHash.create 1000 in
  let replace_var v =
    if (not (V.VarHash.mem varmap v)) then (
      let (_,s,t) = v in
      V.VarHash.add varmap v (V.newvar s t));
    V.VarHash.find varmap v
  in
  
  let vis = 
object (self)
  inherit V.nop_vine_visitor 

  method replace_lval lv =
    match lv with
    | V.Temp(v) ->
        V.Temp(replace_var v)
    | V.Mem(v,e,t) -> 
        V.Mem(replace_var v, e, t)

  method visit_rlvalue lv = 
    V.ChangeDoChildrenPost(self#replace_lval lv, Vine_util.id)

  method visit_alvalue = 
    self#visit_rlvalue

  (* when we visit a binding, we first visit the rhs, then add the
     binding to the context *)
(*   method visit_binding (lv,e) =   *)
(*     V.ChangeDoChildrenPost((self#replace_lval lv, e), Vine_util.id) *)

  method visit_decl v = 
    V.ChangeTo(replace_var v)
end
  in
  (List.map replace_var dl, List.map (V.stmt_accept vis) sl)

(* XXX icky hack *)
let rename_all_exp e =
  let stmt = V.ExpStmt(e) in
  let ([], [stmt]) = rename_all_prog ([], [stmt]) in
  match stmt with
  | V.ExpStmt(e) -> e
  | _ -> failwith "rename_all_exp"
  
let gamma_of_prog prog = 
  let ds = Exectrace.varset_of_prog prog in
  Exectrace.gamma_of_varset (Asmir.x86_mem) ds

let t0 = Unix.gettimeofday ();;
let time () = 
  ((Unix.gettimeofday ()) -. t0)

(** do some work in a child process. blocks until child finishes;
    i.e. this is intended for isolation, not parallelism.
    TODO: think about extending this to support parallelism
    @param child_f does some work and writes to a pipe.
    @param parent_f reads from a pipe and reconstitutes an answer,
    which is returned.
*)
let fork_and_call parent_f child_f =
  (* IO module pipes don't seem to do the right thing across
     fork. So, create a unix pipe, and wrap it in IO objects
     after the fork.
  *)
  let (pipe_input_pid, pipe_output_pid) = Unix.pipe () in

  let child_pid = Unix.fork () in
  if child_pid = 0 then (
    (* child. do query. *)
    let pipe_output = Unix.out_channel_of_descr pipe_output_pid in
    let pipe_output = IO.output_channel pipe_output in

    child_f pipe_output;
    exit 0
  ) else (
    (* parent *)
    let pipe_input = Unix.in_channel_of_descr pipe_input_pid in
    let pipe_input = IO.input_channel pipe_input in

    (* read from pipe, 
       signifying whether a counterexample exists *)
    let rv = parent_f pipe_input in

    (* clean up child process *)
    let (term_child, status) = Unix.waitpid [] child_pid in
    (match status with
     | Unix.WEXITED i -> 
         assert (i = 0)
     | _ -> failwith "unhandled child exit");

    (* clean up pipes *)
    Unix.close pipe_output_pid;
    Unix.close pipe_input_pid;
    
    (* return answer *)
    rv
  )
  

(** queries stp to determine if the boolean expression q
    is satisfiable. If so, returns a value of variable 
    for which q can be satisfied. Otherwise returns None.
    Implemented by calling stp in a child process, hence
    no destructive updates to the validity checker.
    @param vc is an stp validity checker
    @param ctx an stpvc context
    @param q query- an IR expression with type REG_1
    @param expr is a vine exp, for which the list of counter-examples will
    be generated XXX: stp seems to have a bug s.t. using a non-lval
    here will always return 0 in the counterexample.
*)
(* let fork_and_query_old vc ctx q expr = *)
(*   (\* make sure stp bug doesn't bite us until i can get it figured out... *\) *)
(*   (match expr with *)
(*    | V.Lval _ -> () *)
(*    | _ ->  *)
(*        raise (V.Unimplemented "fork_and_query with non-lval. stp will silently give wrong answer")); *)

(*   (\* IO module pipes don't seem to do the right thing across *)
(*      fork. So, create a unix pipe, and wrap it in IO objects *)
(*      after the fork. *)
(*   *\) *)
(*   let (pipe_input_pid, pipe_output_pid) = Unix.pipe () in *)

(*   let child_pid = Unix.fork () in *)
(*   if child_pid = 0 then ( *)
(*     (\* child. do query. *\) *)
(*     let pipe_output = Unix.out_channel_of_descr pipe_output_pid in *)
(*     let pipe_output = IO.output_channel pipe_output in *)


(*     (\* convert vine expr to an stp expression *\) *)
(*     let expr =  *)
(*       Vine_stpvc.vine_to_stp  *)
(*         vc  *)
(*         ctx *)
(*         expr *)
(*     in *)

(*     (\* invert query *\) *)
(*     let q = V.UnOp(V.NOT,q) in *)

(*     (\* simplify q *\) *)
(* (\*     let q = Vine_opt.simplify q in *\) *)
(* (\*     Printf.printf "Query exp: %s\n" (V.exp_to_string q); *\) *)

(*     (\* convert query to an stp boolean *\) *)
(*     let q =  *)
(*       Vine_stpvc.vine_to_stp  *)
(*         vc  *)
(*         ctx  *)
(*         q *)
(*     in *)
(*     let q = (Stpvc.e_bvbitextract vc q 0) in *)

(*     Printf.printf "%f issuing stp query\n%!" *)
(*       (time ()); *)
(* (\*       (Stpvc.to_string q); *\) *)

(*     let qresult = Stpvc.query vc q in *)
(* (\*     Libstp.vc_printQuery vc; *\) *)
(* (\*     flush_all (); *\) *)

(*     if qresult then ( *)
(*       (\* write 0 *\) *)
(*       IO.write_byte pipe_output 0; *)
(*     ) else ( *)
(*       (\* write 1 *\) *)
(*       IO.write_byte pipe_output 1; *)
(*       Libstp.vc_printCounterExample vc; *)
(* (\*       flush_all (); *\) *)
(*       (\* write counterexample *\) *)
(*       let e_ctrex = Stpvc.get_counterexample vc expr in  *)
(*       let e_ctrex = Stpvc.int64_of_e e_ctrex in *)
(*       D.dprintf "Got counterexample %Lx%!" e_ctrex; *)
(*       IO.write_i64 pipe_output e_ctrex; *)
(*     ); *)
(*     (\* IO.close_out pipe_output; *\) *)
(*     exit 0 *)
(*   ) else ( *)
(*     (\* parent *\) *)
(*     let pipe_input = Unix.in_channel_of_descr pipe_input_pid in *)
(*     let pipe_input = IO.input_channel pipe_input in *)

(*     (\* read from pipe,  *)
(*        signifying whether a counterexample exists *\) *)
(*     let rv =  *)
(*       (match (IO.read_byte pipe_input) with *)
(*        | 0 -> *)
(*            None *)
(*        | 1 ->  *)
(*            Some(IO.read_i64 pipe_input) *)
(*        | _ -> failwith ("unexpected value from pipe") *)
(*       ) in *)
(*     (\* IO.close_in pipe_input; *\) *)

(*     (\* clean up child process *\) *)
(*     let (term_child, status) = Unix.waitpid [] child_pid in *)
(*     (match status with *)
(*      | Unix.WEXITED i ->  *)
(*          assert (i = 0) *)
(*      | _ -> failwith "unhandled child exit"); *)

(*     (\* return final answer *\) *)
(*     Unix.close pipe_output_pid; *)
(*     Unix.close pipe_input_pid; *)
(*     rv *)
(*   ) *)


(** queries stp to determine if the boolean expression q
    is satisfiable. If so, returns a value of variable 
    for which q can be satisfied. Otherwise returns None.
    Implemented by calling stp in a child process, hence
    no destructive updates to the validity checker.
    @param vc is an stp validity checker
    @param ctx an stpvc context
    @param q query- an IR expression with type REG_1
    @param expr is a vine exp, for which the list of counter-examples will
    be generated XXX: stp seems to have a bug s.t. using a non-lval
    here will always return 0 in the counterexample.
*)
let fork_and_query vc ctx q expr =
  (* make sure stp bug doesn't bite us until i can get it figured out... *)
  (match expr with
   | V.Lval _ -> ()
   | _ -> 
       raise (V.Unimplemented "fork_and_query with non-lval. stp will silently give wrong answer"));

  let child_f pipe_output =
    (* convert vine expr to an stp expression *)
    let expr = 
      Vine_stpvc.vine_to_stp 
        vc 
        ctx
        expr
    in

    (* invert query *)
    let q = V.UnOp(V.NOT,q) in

    (* convert query to an stp boolean *)
    let q = 
      Vine_stpvc.vine_to_stp 
        vc 
        ctx 
        q
    in
    let q = (Stpvc.e_bvbitextract vc q 0) in

    Printf.printf "%f issuing stp query\n%!"
      (time ());
    (*       (Stpvc.to_string q); *)

    let qresult = Stpvc.query vc q in

    redirect_to_stp (fun () -> Libstp.vc_printQuery vc);

    if qresult then (
      (* write 0 *)
      IO.write_byte pipe_output 0;
    ) else (
      (* write 1 *)
      IO.write_byte pipe_output 1;
(*       Libstp.vc_printCounterExample vc; *)
      (*       flush_all (); *)
      (* write counterexample *)
      let e_ctrex = Stpvc.get_counterexample vc expr in 
      let e_ctrex = Stpvc.int64_of_e e_ctrex in
      D.dprintf "Got counterexample %Lx%!" e_ctrex;
      IO.write_i64 pipe_output e_ctrex;
    )
  in

  let parent_f pipe_input =
    (* read from pipe, 
       signifying whether a counterexample exists *)
    let rv = 
      (match (IO.read_byte pipe_input) with
       | 0 ->
           None
       | 1 -> 
           Some(IO.read_i64 pipe_input)
       | _ -> failwith ("unexpected value from pipe")
      ) in
    rv
  in
  fork_and_call parent_f child_f


(** uses stp to return a list of all values of v for which 
    q can be satisfied. non-destructive.
    @param vc is an stp validity checker
    @param q is a vine expression, which should evaluate to a boolean
    @param e is a vine exp, for which the list of counter-examples will
    be generated
*)
let rec all_counter_exs ?(acc=[]) vc ctx q e =
  match fork_and_query vc ctx q e with
  | None -> acc
  | Some(i) -> 
      D.dprintf "%f Got example %Lx\n%!" (time ()) i;
      let t = Vine_typecheck.infer_type None e in
      (* side-effect method (faster) *)
(*       Stpvc.do_assert  *)
(*         vc  *)
(*         (Stpvc.e_not  *)
(*            vc  *)
(*            (Stpvc.e_eq  *)
(*               vc  *)
(*               (Vine_stpvc.vine_to_stp  *)
(*                  vc  *)
(*                  ctx  *)
(*                  (V.Lval(V.Temp(v)))) *)
(*               (Stpvc.e_bv_of_int64 vc (V.bits_of_width t) i))); *)
      
      (* no-side-effect method (slower) *)
      let q =
        V.BinOp(
          V.BITAND,
          q,
          V.UnOp(
            V.NOT,
            (V.BinOp(
               V.EQ,
               e,
               V.Constant(V.Int(t,i)))))) in
      all_counter_exs ~acc:(i::acc) vc ctx q e

let add_last_block cfg sl =
  (* create new bb *)
  let bb = cfg#create_bb cfg#newid sl in

  (* move all edges went to exit to go to the new bb *)
  (* XXX: may need to alter last jmp stmt of each block *)
  let exit_bb = cfg#find Vine_cfg.BB_Exit in
  let exit_edges = ref [] in
  cfg#iter_edges 
    (fun src dst ->
       if (cfg#get_id dst) = Vine_cfg.BB_Exit then
         exit_edges := src::!exit_edges);
  List.iter 
    (fun src ->
       cfg#remove_edge src exit_bb;
       cfg#add_edge src bb)
    !exit_edges;

  (* add Exit as successor to new bb *)
  cfg#add_edge bb exit_bb;

  (* return a callback that removes the added block *)
  let f () =
    List.iter
      (fun src ->
         cfg#remove_edge src bb;
         cfg#add_edge src exit_bb)
      !exit_edges
  in
  f

(* let add_first_block cfg sl = *)
(*   () *)

let prog_dataflow_simplify prog post =
  let ssaref =
    let cfg = Vine_cfg.prog_to_cfg prog in
    (* XXX need to make sure this gets removed later. better yet,
       use globals option to simplify. waiting for variable to
       ssa-variable mapping from ivan *)
    let kill_block =
      add_last_block cfg [V.Assert(post)]; (* ensures we don't simplify
                                              away what we care abt *)
    in
    Vine_cfg.coalesce_bb cfg;
    Vine_cfg.remove_unreachable cfg;
    ref (Ssa.cfg2ssa cfg)
  in

  let changed = ref true in
  while !changed; do
    let ssacfg = !ssaref in
    (* alias analysis *)
    D.dprintf "%f Performing alias analysis%!" (time ());
    let alias = Vine_alias.vsa_alias ssacfg in
    let x = Vine_alias.alias_replace alias ssacfg in
    let y = Vine_alias.remove_dead_stores alias ssacfg in
    D.dprintf "%f Done performing alias analysis%!" (time ());

    D.dprintf "%f Simplifying graph%!" (time ());
    (*   let globals = V.freerefs_exp post in *)
    let (ssacfg,z) = Vine_dataflow.SsaDataflow.simplify_graph ssacfg 1 in
    D.dprintf "%f Done simplifying graph%!" (time ());
    ssaref := ssacfg;
    changed := x || y || z
  done;

  let cfg = Ssa.to_vine !ssaref in
  let prog = Vine_cfg.normal_cfg_to_prog cfg in
  prog


let wp_of_prog prog post =
  D.dprintf "%f Building cfg\n%!" (time ());

  let cfg = Vine_cfg.prog_to_cfg prog in
(*   let kill_block =  *)
(*     add_last_block cfg [V.Assert(post)]; (\* ensures we don't simplify *)
(*                                             away what we care abt *\) *)
  
(*   D.dprintf "%f Simplifying graph%!" (time ()); *)
(*   let (cfg,_) = Vine_dataflow.simplify_graph cfg 1 in *)
(*   D.dprintf "%f Done simplifying graph%!" (time ()); *)

(*   let prog = Vine_cfg.normal_cfg_to_prog cfg in *)
(*   D.dprintf "%f simplified program:" (time ()); *)
(*   V.pp_program print_string prog; *)

  D.dprintf "%f Writing gcl\n%!" (time ());
  let gcl =
    Gcl.of_cfg
      cfg
      (Vine_cfg.exit_node cfg)
      (Vine_cfg.entry_node cfg)
  in
  D.dprintf "%f Calcing wp\n%!" (time ());
  Wp.calculate_wp Vine_util.id post gcl (* post is already
                                           asserted *)

let kill_all_asserts prog =
  let vis = object(self)
    inherit V.nop_vine_visitor
    method visit_stmt s =
      match s with
      | V.Assert _ ->
          V.ChangeTo(V.Comment("removed assert"))
      | _ ->
          V.DoChildren
  end
  in
  let dl, sl = prog in
  let sl = List.map (V.stmt_accept vis) sl in
  (dl, sl)

(** experimental optimization using stp to identify and remove
    assertions that must hold, given that preceding assertions
    hold. 
    Does not appear to be an over-all performance win due to 
    the time taken to do this analysis, but interesting for
    research purposes.
*)
let kill_asserts prog post =
  (* label every assert *)
(*   let lbls = ref [] in *)
(*   let vis = object(self) *)
(*     inherit V.nop_vine_visitor *)
(*     method visit_stmt s = *)
(*       match s with *)
(*       | V.Assert(x) -> *)
(*           let newlbl = V.newlab "assert" in *)
(*           lbls := newlbl :: !lbls; *)
(*           V.ChangeTo(V.Block([], [V.Label(newlbl); s])) *)
(*       | _ -> *)
(*           V.DoChildren *)
(*   end *)
(*   in *)
(*   let _ = *)
(*     let dl, sl = prog in *)
(*     V.stmt_accept vis (V.Block(dl, sl)) *)
(*   in *)
(*   let lbls = !lbls in *)

  (* flatten blocks *)
  let prog = Vine_alphavary.descope_program prog in
  let dl, sl = prog in
  let killed = ref 0 in
  let kept = ref 0 in
  let rec foo sl_acc sl =
    match sl with
    | V.Assert(x)::tl ->
(*     | V.Label(lbl)::V.Assert(x)::tl -> *)
(*         assert(lbl = (List.hd lbls)); (\* XXX not actually using
  lbl list *\) *)
        let child_f pipe_out =
          (* reconstruct program *)
          let prog = dl, (List.rev sl_acc) in

          (* XXX experimental. asserts found to be tautologies
             are, but we may miss some. *)
(*           let prog = kill_all_asserts prog in *)
          
          (* compute wp of inverse of this assert *)
          let wp = wp_of_prog prog (V.exp_not(x)) in

          (* set up stp *)
          let vc = Stpvc.create_validity_checker () in
          let ctx = V.get_req_ctx wp in
          let ctx = Vine_stpvc.new_ctx vc ctx in
          D.dprintf "%f asserting wp formula\n%!" (time ());
          Stpvc.do_assert vc (exp_to_stp_bool vc ctx wp);

          (* use stp to find out if assert is a tautology *)
          let qresult = Stpvc.query vc (Stpvc.e_false vc) in
          if qresult then (
            IO.write_byte pipe_out 0;
          ) else (
            (* write 1 *)
            IO.write_byte pipe_out 1;
          )
        in
        let parent_f pipe_in =
          match IO.read_byte pipe_in with
          | 0 -> false
          | 1 -> true
        in
        let sl_acc, re_dataflow =
          if fork_and_call parent_f child_f then (
            (* not a tautology. keep the assert *)
            incr kept;
            Printf.printf "%f KEEPING assert %d\n%!" (time ()) !kept;
            V.Assert(x)::sl_acc, false
          ) else (
            incr killed;
            Printf.printf "%f KILLING assert %d\n%!" (time ()) !killed;
            let s = 
              Printf.sprintf "REMOVED assert: %s" (V.exp_to_string x)
            in
            V.Comment(s)::sl_acc, (!killed mod 200) = 0
          )
        in

        let sl_acc, sl =
          if re_dataflow then (
            Printf.printf "Redoing dataflow\n%!";
            let sl = List.rev_append sl_acc tl in
            let _, sl = prog_dataflow_simplify (dl,sl) post in

            (* skip past the ones we've already checked keeping *)
            let rec f sl_acc sl skipped =
              if skipped = !kept then
                sl_acc, sl
              else
                let s, tl = List.hd sl, List.tl sl in
                match s with
                | V.Assert _ -> 
                    f (s::sl_acc) tl (skipped+1)
                | _ ->
                    f (s::sl_acc) tl skipped
            in
            f [] sl 0
          ) else (
            sl_acc, tl
          )
        in
        foo sl_acc sl (* (List.tl lbls) *)
    | s::tl ->
        foo (s::sl_acc) tl (* lbls *)
    | [] ->
        (* XXX make sure lbls is empty? *)
        sl_acc
  in
  let sl = List.rev (foo [] sl) in
  (dl, sl)


(** creates fresh variable exp_val_var, 
    and takes wp of (expr=exp_val_var).
    returns (wp, exp_val_var)
*)
let prog_to_exp prog expr =
  Vine_typecheck.typecheck prog;
  let exp_type = Vine_typecheck.infer_type None expr in

  (* create fresh variables for value of expression,
     and for value of post-condition *)
  let exp_val_name = "exp_val" in
  let exp_val_var = V.newvar exp_val_name exp_type in
  let prog = 
    let dl, sl = prog in
    let dl = exp_val_var :: dl in
    (dl, sl)
  in

  let post_condition = 
    V.BinOp(V.EQ,
            expr,
            V.Lval(V.Temp(exp_val_var))) in

  let stmt_count prog =
    let _, sl = prog in
    List.length sl
  in
  
  Printf.printf "Stmts before DCE: %d\n" (stmt_count prog);
  let prog = prog_dataflow_simplify prog post_condition in
  Printf.printf "Stmts after DCE: %d\n" (stmt_count prog);
  Printf.printf "Program after simplification:\n";
  V.pp_program print_string prog;
(*   let prog = kill_asserts prog post_condition in *)
(*   Printf.printf "Stmts after removing asserts: %d\n" (stmt_count prog); *)
(*   let prog = prog_dataflow_simplify prog post_condition in *)
(*   Printf.printf "Stmts after 2nd DCE: %d\n" (stmt_count prog); *)

  (* get wp of (exp = expval) *)
  let wp1 = 
    wp_of_prog prog post_condition
  in
  (wp1, exp_val_var)

(** create initial valset and stp state
    @param prog IR program
    @param exp expression of interest
*)
let prog_to_valset prog expr =
  (* convert program to appropriate expression *)
  let wp, exp_val_var = prog_to_exp prog expr in

  (* set up stp *)
  let vc = Stpvc.create_validity_checker () in
  let ctx = V.get_req_ctx wp in  
  let ctx = Vine_stpvc.new_ctx vc ctx in

  (* XXX experimental: do stp simplification *)
(*   let wp = Vine_stpvc.vc_simplify vc ctx wp in *)

  D.dprintf "%f asserting wp formula\n%!" (time ());
(*   V.pp_exp print_string wp; *)
  Stpvc.do_assert vc (exp_to_stp_bool vc ctx wp);

  redirect_to_stp
    (fun () ->
       Libstp.vc_printVarDecls vc;
       Libstp.vc_printAsserts vc
    );

  (* set up valset *)
  let exp_type = Vine_typecheck.infer_type None expr in
  let max_val = max_of_typ exp_type in
  let vs = 
    {ranges = [(0L, max_val, UNKNOWN)]; vine_t = exp_type}
  in

  let valset_state = 
    {
      vc = vc;
      ctx = ctx;
      exp_val_var = exp_val_var;
    }
  in
  vs, valset_state

(** @param an stp validity checker, with an asserted formula
    @param an stpvc context
    @param a free variable to be used in queries
    @param value expression
    @param known value set
    @param hole
    @return updated value set, halved hole
*)
let halve_hole vc ctx offset_var expr valset 
    ((f_pt, u_pt, dir):hole_t) =
  let diff = hole_size (f_pt, u_pt, dir) valset.vine_t in
  assert(diff > 0L);
  (* ceil(diff / 2) *)
  let max_offset = (Int64.add
                      (Int64.rem diff 2L)
                      (Int64.div diff 2L))
  in

  let lo, hi = 
    match dir with
    | LEFT -> Int64.sub f_pt max_offset, (Int64.pred f_pt)
    | RIGHT -> (Int64.succ f_pt), Int64.add f_pt max_offset
  in
  assert(lo <= hi); (* not handling circular number line for now *)

  D.dprintf "halve_hole (%s) max_off: %Ld, lo: %Ld, hi: %Ld%!"
    (hole_to_string (f_pt, u_pt, dir))
    max_offset lo hi;

  (* offset_var <= max_offset && expr = neg+offset_var *)
  let query =
    V.BinOp(V.BITAND,
            V.BinOp(V.LE,
                    V.Lval(V.Temp(offset_var)),
                    V.Constant(V.Int(valset.vine_t, max_offset))
                   ),
            V.BinOp(V.EQ,
                    expr,
                    V.BinOp((match dir with
                               RIGHT -> V.PLUS | LEFT -> V.MINUS),
                            V.Constant(V.Int(valset.vine_t, f_pt)),
                            V.Lval(V.Temp(offset_var))
                           )
                   )
           )
  in
  D.dprintf "STP Query: %s\n" (V.exp_to_string query);

  let valset, f_pt, u_pt = 
    match fork_and_query vc ctx query expr with
    | None -> 
        D.dprintf "STP Example: none\n";
        let new_f_pt = 
          eval_exp
            (V.BinOp((match dir with 
                        RIGHT -> V.PLUS | LEFT -> V.MINUS),
                     V.Constant(V.Int(valset.vine_t, f_pt)),
                     V.Constant(V.Int(valset.vine_t, max_offset))))
        in
        let (nr_l, nr_h, _) as new_range = 
          match dir with 
          | RIGHT -> (f_pt, new_f_pt, FALSE)
          | LEFT -> (new_f_pt, f_pt, FALSE)
        in
        D.dprintf "Adding new false range: %Ld to %Ld" nr_l nr_h;
        let new_ranges = 
          (* we've been treating the number line as circular.
             if the new range crosses the 0 boundary, split it *)
          if nr_l <= nr_h then
            insert_range valset.ranges (nr_l, nr_h, FALSE)
          else
            let r = insert_range valset.ranges (0L, nr_h, FALSE) in
            insert_range r (nr_l, max_of_typ valset.vine_t, FALSE)
        in
        {valset with ranges = new_ranges}, new_f_pt, u_pt
    | Some(i) -> 
        D.dprintf "STP Example: %Ld\n" i;
        {valset with ranges = (insert_range valset.ranges (i, i, TRUE))},
        f_pt, 
        i
  in
  valset, (f_pt, u_pt, dir)

let halve_hole_new (stp:valset_state_t) (vs:valset_t) (f_pt, u_pt, dir) =
  let diff = hole_size (f_pt, u_pt, dir) vs.vine_t in
  assert(diff > 0L);
  (* ceil(diff / 2) *)
  let max_offset = (Int64.add
                      (Int64.rem diff 2L)
                      (Int64.div diff 2L))
  in

  let lo, hi = 
    match dir with
    | LEFT -> Int64.sub f_pt max_offset, (Int64.pred f_pt)
    | RIGHT -> (Int64.succ f_pt), Int64.add f_pt max_offset
  in
  assert(lo <= hi); (* not handling circular number line for now *)

  D.dprintf "halve_hole (%s) max_off: %Ld, lo: %Ld, hi: %Ld%!"
    (hole_to_string (f_pt, u_pt, dir))
    max_offset lo hi;

  let query =
    V.BinOp(V.BITAND,
            V.BinOp(V.LE,
                    V.Lval(V.Temp(stp.exp_val_var)),
                    V.Constant(V.Int(vs.vine_t, hi))
                   ),
            V.BinOp(V.LE,
                    V.Constant(V.Int(vs.vine_t, lo)),
                    V.Lval(V.Temp(stp.exp_val_var))
                   )
           )
  in
  D.dprintf "STP Query: %s\n" (V.exp_to_string query);

  let learned_range = 
    match 
      fork_and_query stp.vc stp.ctx query (V.Lval(V.Temp(stp.exp_val_var))) 
    with
    | None -> 
        D.dprintf "No counterexamples. Marking %Lx to %Lx FALSE"
          lo hi;
        (lo, hi, FALSE)
    | Some(i) ->
        D.dprintf "Got STP example %Lx" i;
        (i, i, TRUE)
  in

  let vs = 
    {vs with ranges = (insert_range vs.ranges learned_range)}
  in

  vs

(** @param an stp validity checker, with an asserted formula
    @param an stpvc context
    @param a free variable to be used in queries
    @param value expression
    @param known value set
    @param hole
    @param granularity to shrink hole to
    @return updated value set, hole (now no larger than gran)
*)
let rec halve_hole_to_gran
    vc ctx offset_var expr valset hole gran =
  Printf.printf "halve_hole_to_gran ";
  pp_valset print_string valset;
  Printf.printf "\n%!";
  if (hole_size hole valset.vine_t) <= gran then
    valset
  else
    let (valset, hole) = 
      halve_hole
        vc ctx offset_var expr valset hole 
    in
    halve_hole_to_gran 
      vc 
      ctx 
      offset_var 
      expr 
      valset 
      hole
      gran
;;

let holes_of_valset valset =
  let rec foo holes ranges =
    match ranges with
    | (l1, r1, FALSE) :: (((l2, r2, UNKNOWN) :: _) as tl) ->
        let holes = (r1, r2, RIGHT) :: holes in
        foo holes tl
    | (l1, r1, UNKNOWN) :: (((l2, r2, FALSE) :: _) as tl) ->
        let holes = (l2, l1, LEFT) :: holes in
        foo holes tl
    | r1 :: r2 :: tl ->
        foo holes (r2 :: tl)
    | _ ->
        holes
  in
  foo [] valset.ranges
;;

(* sort holes, largest first *)
let sort_holes holes vine_t =
  List.sort 
    ~cmp:(fun h1 h2 -> Int64.compare (hole_size h2 vine_t) (hole_size h1 vine_t))
    holes
;;

let rec shrink_holes_to 
    vc ctx offset_var expr valset gran =
  let holes = holes_of_valset valset in
  let holes = sort_holes holes valset.vine_t in
  Printf.printf "Valset: ";
  pp_valset print_string valset;
  Printf.printf "\nHoles: ";
  List.iter
    (pp_hole print_string)
    holes;
  Printf.printf "\n%!";
  match holes with
  | [] -> 
      valset
  | biggest :: rest ->
      if (hole_size biggest valset.vine_t) <= gran then
        valset
      else
        let valset, hole = 
          halve_hole 
            vc ctx offset_var expr valset biggest
        in
        shrink_holes_to 
          vc ctx offset_var expr valset gran
;;
          
let rec shrink_holes_to_new stp vs gran =
  let holes = holes_of_valset vs in
  let holes = sort_holes holes vs.vine_t in
  Printf.printf "Valset: ";
  pp_valset print_string vs;
  Printf.printf "\nHoles: ";
  List.iter
    (pp_hole print_string)
    holes;
  Printf.printf "\n%!";
  match holes with
  | [] -> 
      vs
  | biggest :: rest ->
      if (hole_size biggest vs.vine_t) <= gran then
        vs
      else
        let vs = 
          halve_hole_new stp vs biggest
        in
        shrink_holes_to_new 
          stp vs gran
;;

let check_expval_pt vc ctx exp_val_var exp_typ pt =
  let ans = 
    fork_and_query 
      vc 
      ctx 
      (V.BinOp(V.EQ,
               V.Lval(V.Temp(exp_val_var)),
               V.Constant(V.Int(exp_typ, pt))))
      (Vine.Lval(V.Temp(exp_val_var)))
  in
  match ans with
  | None -> 
      false
  | Some(i) ->
      assert(i = pt);
      true

(** find lowest and highest satisfiable value in valset,
    and update valset appropriately
    @param stp stp state
    @param valset current valset
    @return updated valset
*)
let establish_valset_bounds stp vs =
  (* make sure we have at least one t point *)
  let vs =
    let tcount, _, _ = counts_of_valset vs in
    if tcount = 0L then
      (* find one concrete value for expr, which will be our
         starting point when searching for bounds *)
      D.dprintf "%f Finding start_pt\n%!" (time ());
    let start_pt =
      fork_and_query
        stp.vc
        stp.ctx
        (Vine.exp_true)
        (Vine.Lval(Vine.Temp(stp.exp_val_var )))
    in
    let start_pt =
      match start_pt with
      | None -> failwith "not satisfiable!"
      | Some(start_pt) -> start_pt
    in
    valset_insert_range vs (start_pt, start_pt, TRUE)
  in
  
  (* check lowest possible value *)
  D.dprintf "%f Checking 0 pt\n%!" (time ());
  let vs =
    valset_insert_range
      vs
      (0L, 0L,
       tbool_of_bool
         (check_expval_pt stp.vc stp.ctx stp.exp_val_var vs.vine_t 0L))
  in

  (* check highest possible value *)
  let max_val = max_of_typ vs.vine_t in
  D.dprintf "%f Checking max pt %Ld\n%!" (time ()) max_val;
  let vs =
    valset_insert_range
      vs
      (max_val, max_val,
       tbool_of_bool
         (check_expval_pt stp.vc stp.ctx stp.exp_val_var vs.vine_t max_val))
  in

  (* use range queries to efficiently learn about space between t & f
     points, thus establishing lower and upper bounds *)
  D.dprintf "%f calling shrink_holes_to\n%!" (time ());
  let vs =
    shrink_holes_to_new stp vs 0L
  in
  vs

(** randomly choose points in the current 'UNKNOWN' space,
    asking stp if they can satisfied. use this to establish
    probabilistic bounds of how much of the UNKNOWN regions are
    satisfiable.
    @param stp stp state
    @param valset current valset
    @param n number of samples to check
    @return valset with sampled points filled in 
    * number of sampled points that were satisfiable.
*)
let sample_unknowns stp vs num_samples =
  let count_unknowns vs =
    let _, _, ucount = counts_of_valset vs in
    ucount
  in
  let rec nth_unknown ranges n =
    match (List.hd ranges) with
    | (_, _, TRUE) 
    | (_, _, FALSE)
      -> 
        nth_unknown (List.tl ranges) n
    | (lo, hi, UNKNOWN)
      ->
        let size = Int64.succ (Int64.sub hi lo) in
        if size <= n then
          nth_unknown (List.tl ranges) (Int64.sub n size)
        else
          Int64.add lo n
  in

  Random.init 42;
  let rec do_sample vs sat_ct num_unknowns pts_to_check =
    if pts_to_check = 0L then
      vs, sat_ct
    else (
      assert(num_unknowns <> 0L);

      (* get random number from [0, num_unknowns) *)
      let i = Random.int64 num_unknowns in
      
      (* get ith unknown point *)
      let n = nth_unknown vs.ranges i in

      (* test this point *)
      let sat =
        check_expval_pt 
          stp.vc 
          stp.ctx 
          stp.exp_val_var 
          vs.vine_t
          n
      in

(*       D.dprintf "Current valset:"; *)
(*       pp_valset print_string vs; *)
(*       D.dprintf "\ntesting unknown number %Ld -> 0x%Lx" i n; *)
(*       D.dprintf "Unknown point 0x%Lx satisfiable: %b\n" n sat; *)

      let sat_ct = 
        if sat then (Int64.succ sat_ct) else sat_ct
      in
      
      let vs =
        valset_insert_range vs (n, n, tbool_of_bool sat)
      in

      do_sample vs sat_ct (Int64.pred num_unknowns) (Int64.pred pts_to_check)
    )
  in

  do_sample vs 0L (count_unknowns vs) num_samples
    
(** keep asking stp for new counterexamples, updating valset
    appropriately. stops when no more counterexamples or 
    query limit is reached.
    @param stp stp state
    @param valset current valset
    @param n max number of samples to query for
    @return updated valset
*)
let rec find_up_to_n_samples stp vs n =
  if n = 0L then
    vs
  else
    let query = Vine.exp_true in
    (* don't allow repeat counter-examples *)
    let query =
      List.fold_left
        (fun query (x,y,b) ->
           match b with
           | FALSE | UNKNOWN -> query
           | TRUE ->
               let exp_val_tmp = V.Lval(V.Temp(stp.exp_val_var)) in
               let x = V.const_of_int64 vs.vine_t x in
               let y = V.const_of_int64 vs.vine_t y in
               V.BinOp(V.BITAND,
                       query,
                       V.UnOp(V.NOT,
                              V.BinOp(V.BITAND,
                                      V.BinOp(V.LE,
                                              x,
                                              exp_val_tmp),
                                      V.BinOp(V.LE,
                                              exp_val_tmp,
                                              y)))))
        query
        vs.ranges
    in

    let example = 
      fork_and_query stp.vc stp.ctx query
        (V.Lval(V.Temp(stp.exp_val_var))) 
    in

    match example with
    | None ->
        D.dprintf "No more samples. Stopping.";
        let ranges = 
          List.map
            (fun (x,y,b) -> 
               match b with
               | TRUE
               | FALSE -> (x,y,b)
               | UNKNOWN -> (x,y, FALSE))
            vs.ranges
        in
        {vs with ranges = ranges}
    | Some(x) ->
        D.dprintf "Got STP example 0x%Lx" x;
        let vs = valset_insert_range vs (x,x,TRUE) in
        find_up_to_n_samples stp vs (Int64.pred n)

(** estimate influence by sampling UNKNOWN space.
    @param stp stp state
    @param valset current valset
    @param n max number of samples to take
    @return probable influence * sat count * samples taken * unknown count.
    (use latter three to reason about sampling confidence)
*)
let probable_influence stp vs num_samples =
  let t_ct, _, u_ct = counts_of_valset vs in
  let num_samples = min num_samples u_ct in
  let vs, sat_ct = 
    sample_unknowns stp vs num_samples 
  in
  (* note- important to use u_ct from before updating valset *)
  let frac = (Int64.to_float sat_ct) /. (Int64.to_float
                                           num_samples) in
  let sat_est = frac *. (Int64.to_float u_ct) in
  let prob_inf = 
    log ((Int64.to_float t_ct) +. sat_est) /. (log 2.0)
  in
  prob_inf, sat_ct, num_samples, u_ct

let hybrid_estimate stp vs =
  let vs = find_up_to_n_samples stp vs 64L in

  let vs = establish_valset_bounds stp vs in

  let t_ct, _, u_ct = counts_of_valset vs in
  let num_samples = min 100L u_ct in
  let vs, samp_inf =
    if false then
      let vs, sat_ct = 
        sample_unknowns stp vs num_samples 
      in
      (* note- important to use u_ct from before updating valset *)
      let frac = (Int64.to_float sat_ct) /. (Int64.to_float
                                               num_samples) in
      let sat_est = frac *. (Int64.to_float u_ct) in
      let inf = 
        log ((Int64.to_float t_ct) +. sat_est) /. (log 2.0)
      in
      D.dprintf 
        "Found %Ld of %Ld unknowns satisfiable, estimating %Ld of %Ld unknowns satisfiable, giving influence of %f bits" 
        sat_ct num_samples (Int64.of_float sat_est) u_ct inf;
      vs, inf
    else
      vs, 0.0
  in

  D.dprintf "Total run time %f" (time ());
  D.dprintf "Final valset: ";
  pp_valset D.pdebug vs;
  let t_ct, f_ct, u_ct = counts_of_valset vs in
  D.dprintf "Final counts: %Ld true %Ld false %Ld unknown"
    t_ct f_ct u_ct;
  let lo, hi = influence_bounds_of_valset vs in
  D.dprintf "Final influence bounds: %f to %f bits" lo hi;
  D.dprintf "Estimated influence via sampling: %f" samp_inf;
  let lo, hi = lh_bounds_of_valset vs in
  D.dprintf "Lowest and highest possible values: 0x%Lx to 0x%Lx"
    lo hi;
  vs

(** finds lowest and highest values that expr may take on in program
    prog
    @param prog IR program
    @param expr expression of interest.
*)
(* let find_bounds prog expr =  *)
(*   let exp_type = Vine_typecheck.infer_type None expr in *)
(*   let wp, exp_val_var = prog_to_exp prog expr in *)
(*   let offset_var = V.newvar "exp_offset" exp_type in *)

(*   let req_ctx = offset_var :: (V.get_req_ctx wp) in   *)
(*   let vc = Stpvc.create_validity_checker () in *)
(*   let ctx = Vine_stpvc.new_ctx vc (req_ctx) in *)

(*   D.dprintf "%f asserting wp formula\n%!" (time ()); *)
(*   Stpvc.do_assert vc (exp_to_stp_bool vc ctx wp); *)

(*   (\* find one concrete value for expr, which will be our *)
(*      starting point when searching for bounds *\) *)
(*   D.dprintf "%f Finding start_pt\n%!" (time ()); *)
(*   let start_pt =  *)
(*     fork_and_query  *)
(*       vc  *)
(*       ctx  *)
(*       Vine.exp_true *)
(*       (Vine.Lval(Vine.Temp(exp_val_var ))) *)
(*   in *)
(*   let start_pt = *)
(*     match start_pt with *)
(*     | None -> raise Not_found *)
(*     | Some(start_pt) -> start_pt *)
(*   in *)

(*   let max_val = max_of_typ exp_type in *)
(*   let valset =  *)
(*     {ranges = [(0L, max_val, UNKNOWN)]; vine_t = exp_type} *)
(*   in *)
(*   let valset =  *)
(*     valset_insert_range valset (start_pt, start_pt, TRUE) *)
(*   in *)
(*   D.dprintf "%f Checking 0 pt\n%!" (time ()); *)
(*   let valset = *)
(*     valset_insert_range  *)
(*       valset  *)
(*       (0L, 0L,  *)
(*        tbool_of_bool *)
(*          (check_expval_pt vc ctx exp_val_var exp_type 0L)) *)
(*   in *)
(*   D.dprintf "%f Checking max pt\n%!" (time ()); *)
(*   let valset = *)
(*     valset_insert_range  *)
(*       valset  *)
(*       (max_val, max_val,  *)
(*        tbool_of_bool *)
(*          (check_expval_pt vc ctx exp_val_var exp_type max_val)) *)
(*   in *)
(*   D.dprintf "%f calling shrink_holes_to\n%!" (time ()); *)
(*   let valset = *)
(*     shrink_holes_to  *)
(*       vc ctx offset_var (V.Lval(V.Temp(exp_val_var))) *)
(*       valset 0L *)
(*   in *)
(*   lh_bounds_of_valset valset  *)
    
(** finds lowest and highest values that expr may take on in program
    prog
    @param prog IR program
    @param expr expression of interest.
*)
let sample prog expr num_samples = 
  let exp_type = Vine_typecheck.infer_type None expr in
  let wp, exp_val_var = prog_to_exp prog expr in
  let offset_var = V.newvar "exp_offset" exp_type in

  let req_ctx = offset_var :: (V.get_req_ctx wp) in  
  let vc = Stpvc.create_validity_checker () in
  let ctx = Vine_stpvc.new_ctx vc (req_ctx) in
  Stpvc.do_assert vc (exp_to_stp_bool vc ctx wp);

  (* find one concrete value for expr, which will be our
     starting point when searching for bounds *)
  let start_pt = 
    fork_and_query 
      vc 
      ctx 
      V.exp_true
      (Vine.Lval(Vine.Temp(exp_val_var )))
  in
  let start_pt =
    match start_pt with
    | None -> raise Not_found
    | Some(start_pt) -> start_pt
  in

  let max_val = max_of_typ exp_type in
  let valset = 
    {ranges = [(0L, max_val, UNKNOWN)]; vine_t = exp_type}
  in
  let valset = 
    valset_insert_range valset (start_pt, start_pt, TRUE)
  in

  let inc = Int64.div max_val num_samples in
  let gran = 1L in
  let rec do_sample valset i =
    if i < max_val then
      let valset =
        valset_insert_range 
          valset 
          (i, i, 
           tbool_of_bool
             (check_expval_pt vc ctx exp_val_var exp_type i))
      in
      do_sample valset (Int64.add i inc)
    else
      valset
  in
  let valset = do_sample valset 0L in
  let valset =
    shrink_holes_to
      vc ctx offset_var (V.Lval(V.Temp(exp_val_var)))
      valset 0L
  in
  valset

(** finds ranges of possible values for vine expression expr
    in program prog 
    All values in the returned ranges will satisfy the post-condition,
    however it may be impossible for expr to actually take on some
    of the values.
    XXX: this is broken. DO NOT USE. can get spurious boundaries. see below
    @param prog IR program
    @param expr IR expression of interest
    @return (list of l-boundaries, list of r-boundaries)
*)
(* let lr_val_bounds prog expr = *)
(*   Printf.eprintf "Warning! Using broken query strategy lr_val_bounds! You will likely get spurious results!\n"; *)
(*   let exp_type = Vine_typecheck.infer_type None expr in *)
(*   let wp1, post_val_var, exp_val_var = prog_to_exp prog expr in *)

(*   (\* duplicate, renaming all variables *\) *)
(*   let wp2 = rename_all_exp wp1 in *)
(*   let post_val_var2, exp_val_var2 = *)
(*     let gamma = gamma_of_prog (V.get_req_ctx wp2, [V.ExpStmt(wp2)]) in *)
(*     Asmir.gamma_lookup gamma (name_of_var post_val_var), *)
(*     Asmir.gamma_lookup gamma (name_of_var exp_val_var) *)
(*   in *)

(*   (\* set up stp *\) *)
(*   D.dprintf "%f Getting req context\n%!" (time ()); *)
(*   let req_ctx = *)
(*     let req_ctx1 = V.get_req_ctx wp1 in *)
(*     let req_ctx2 = V.get_req_ctx wp2 in *)
(*     let req_ctx_set = Exectrace.DeclSet.empty in *)
(*     let f ds d = Exectrace.DeclSet.add d ds in *)
(*     let req_ctx_set = List.fold_left f req_ctx_set req_ctx1 in *)
(*     let req_ctx_set = List.fold_left f req_ctx_set req_ctx2 in *)
(*     Exectrace.DeclSet.elements req_ctx_set *)
(*   in *)
(*   D.dprintf "%f Creating validity checker\n%!" (time ()); *)
(*   let vc = Stpvc.create_validity_checker () in *)
(*   let ctx = Vine_stpvc.new_ctx vc (req_ctx) in *)

(*   (\* assert both formulas *\) *)
(* (\*   print_string "\nwp1: "; *\) *)
(* (\*   V.pp_exp print_string wp1; *\) *)
(* (\*   print_string "\n\nwp2: "; *\) *)
(* (\*   V.pp_exp print_string wp2; *\) *)
(* (\*   print_string "\n"; *\) *)
(* (\*   flush_all (); *\) *)
(*   let wp1 = exp_to_stp_bool vc ctx wp1 in *)
(*   let wp2 = exp_to_stp_bool vc ctx wp2 in *)
(*   Stpvc.do_assert vc wp1; *)
(*   Stpvc.do_assert vc wp2; *)

(*   Libstp.vc_printVarDecls vc; *)
(*   Libstp.vc_printAsserts vc; *)
(*   flush_all; *)

(*   (\* find the right boundaries *\) *)
(*   (\*  post1 && !post2 && (val2 = val1 + 1) *\) *)
(*   (\* XXX: broken. in the case of free variables i, stp can *)
(*      return a val2 s.t. post2 is not satisfied for some i, *)
(*      but IS satisfied for other i *)
(*   *\) *)
(*   let query = *)
(*     V.BinOp(V.BITAND, *)
(*             V.BinOp(V.EQ, *)
(*                     V.Lval(V.Temp(exp_val_var2)), *)
(*                     V.BinOp(V.PLUS, *)
(*                             V.Lval(V.Temp(exp_val_var)), *)
(*                             V.Constant(V.Int(exp_type, 1L)))), *)
(*             V.BinOp(V.BITAND, *)
(*                     V.Lval(V.Temp(post_val_var)), *)
(*                     V.UnOp(V.NOT, V.Lval(V.Temp(post_val_var2))))) *)
(*   in *)
(*   let right_boundaries =  *)
(*     all_counter_exs  *)
(*       vc  *)
(*       ctx  *)
(*       query *)
(*       (Vine.Lval(Vine.Temp(exp_val_var ))) *)
(*   in *)

(*   (\* find the left boundaries *\) *)
(*   (\*  post1 && !post2 && (val2 = val1 - 1) *\) *)
(*   let query = *)
(*     V.BinOp(V.BITAND, *)
(*             V.BinOp(V.EQ, *)
(*                     V.Lval(V.Temp(exp_val_var2)), *)
(*                     V.BinOp(V.MINUS, *)
(*                             V.Lval(V.Temp(exp_val_var)), *)
(*                             V.Constant(V.Int(exp_type, 1L)))), *)
(*             V.BinOp(V.BITAND, *)
(*                     V.Lval(V.Temp(post_val_var)), *)
(*                     V.UnOp(V.NOT, V.Lval(V.Temp(post_val_var2))))) *)
(*   in *)
(*   let left_boundaries =  *)
(*     all_counter_exs  *)
(*       vc  *)
(*       ctx  *)
(*       query *)
(*       (Vine.Lval(Vine.Temp(exp_val_var ))) *)
(*   in *)

(*   let left_boundaries = List.sort left_boundaries in *)
(*   let right_boundaries = List.sort right_boundaries in *)
(*   let rec bounds_to_ranges ranges left_boundaries right_boundaries = *)
(*     match (left_boundaries, right_boundaries) with *)
(*     | [], [] ->  *)
(*         ranges *)
(*     | [], [rb] -> *)
(*         (0L, rb)::ranges *)
(*     | [lb], [] -> *)
(*         (lb, max_of_typ exp_type) :: ranges *)
(*     | lb::lb_tl, rb::rb_tl -> *)
(*         if lb <= rb then *)
(*           bounds_to_ranges ((lb, rb)::ranges) lb_tl rb_tl *)
(*         else *)
(*           bounds_to_ranges ((0L, rb)::ranges) (lb::lb_tl) rb_tl *)
(*   in *)

(*   let ranges = bounds_to_ranges [] left_boundaries right_boundaries in *)
(*   let ranges = List.rev ranges in *)

(*   ranges *)
(* ;; *)

