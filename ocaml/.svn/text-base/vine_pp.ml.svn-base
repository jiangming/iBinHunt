(** Newer pretty printing for Vine.

    FIXME: This needs to be merged/replace the pretty printing stuff currently
    in vine.ml.
*)

open Vine_util
open Vine

(*module D = Debug.Make(struct let name = "Vine_pp" and default=`Debug end)
open D *)

class pp ?(with_varids=false) ft =
  let varctx = Hashtbl.create 113 in
  let pp = Format.pp_print_string ft
  and pp_int = Format.pp_print_int ft
  and space = Format.pp_print_space ft
  and cut = Format.pp_print_cut ft
  and open_box = Format.pp_open_hovbox ft
  (* and open_vbox = Format.pp_open_vbox ft *)
  and open_hvbox = Format.pp_open_hvbox ft
  and close_box = Format.pp_close_box ft in
  let comma () = pp ","; space() in
object(self)
  
  method format_name ((vid,name,typ) as var) =
    if with_varids then (
      pp name;
      pp "_";
      pp_int vid )
    else
      let strings =
	Stream.from (function
		       | 0 -> Some name
		       | 1 -> Some(name^"_"^string_of_int vid)
		       | 2 -> Some(name^"__"^string_of_int vid)
		       | n -> Some(name^"_"^string_of_int (n-2))
		    )
      in
      let rec pp_next() =
	let s = Stream.next strings in
	  try
	    let var' = Hashtbl.find varctx s in
	      if var == var' then pp s else
		pp_next()
	  with Not_found ->
	    Hashtbl.add varctx s var;
	    pp s
      in
	pp_next()

  (* FIXME: Maybe move the optional argument to the class? *)
  method format_var ?(print_type=true) ((_,_,typ) as var) =
    self#format_name var;
    if print_type then (
      pp ":";
      self#format_typ typ
    )
      
  method format_decl v = 
    self#format_decls [v]

  method format_decls dl = 
    let var_compare (i1,n1,_) (i2,n2,_) =
      let sc = String.compare n1 n2 in
	if sc <> 0 then sc
	else compare i1 i2
    in
    let ctx = Hashtbl.create 19009 in 
      (* map type -> list of variables with that type *)
    let () = List.iter (fun ((_,_,t) as v) -> 
			  if Hashtbl.mem ctx t then
			    Hashtbl.replace ctx t (v::(Hashtbl.find ctx t))
			  else
			    Hashtbl.add ctx t [v]) dl in
    let rec pd vars =  (
      match vars with
	  [] -> ()
	| x::[] -> 	    
	    self#format_name x;
	    (* close_box (); *)
	    cut ();
	    pp ":";
	    let (_,_,t) = x in self#format_typ t;
	      pp ";"
	| x::ys -> 
	    self#format_name x; pp ","; space();
	    pd ys
    ) in
    let keys = Hashtbl.fold (fun k _ acc -> k::acc) ctx [] in 
    let ints,others = List.partition (is_integer_type) keys in 
    let ints =
      List.sort 
	(fun t1 t2 -> compare (bits_of_width t2) (bits_of_width t1))
	ints
    in
    let keys = List.rev_append ints others in
      open_hvbox 0;
      List.iter 
	(fun typ ->
	   let vars = Hashtbl.find ctx typ in 
	   let sorted_vars = List.stable_sort var_compare vars in
	     match vars with
		 [] -> ()
	       | _ -> 
		   open_box 4;
		   pp "var ";
		   (* open_box 0; (* <- box closed by pd *) *)
		   pd sorted_vars;
		   close_box ();
		   cut()
	) keys;
      close_box()
	
  method format_typ = function
    | REG_1 -> pp "reg1_t" 
    | REG_8  -> pp "reg8_t"
    | REG_16 -> pp "reg16_t"
    | REG_32 -> pp "reg32_t"
    | REG_64 -> pp "reg64_t"
    | TString -> pp "string_t"
    | TMem(REG_32, Little) -> pp "mem32l_t"
    | TMem(REG_64, Little) -> pp "mem64l_t"
    | TMem _ -> failwith "Unimplemented memory type"
    | Array(t1,i ) -> 
	self#format_typ t1;
	pp "[";
	Format.fprintf ft "%Ld" i;
	pp "]"
    | TFun(rettype, argtypes, is_extern) ->
	open_box 0;
	(* we can't read this back in, but its something for now *)
	pp "(";
	(match argtypes with
	   | [] -> ()
	   | x::xs ->
	       self#format_typ x;
	       List.iter (fun x -> pp ","; space(); self#format_typ x) xs
	);
	pp ")";
	space();
	pp "-> ";
	(match rettype with
	     None ->  pp "void"
	   | Some(rt') -> self#format_typ rt'
	);
	if (is_extern) then
	  pp ":extern";
	close_box ()
    | TAttr(t', a) ->
	self#format_typ t';
	pp "_attr_(";
	pp (print_separated_list id ", " a);
	pp ")"


  method format_value = function
    | Int(REG_1, 1L) -> pp "true"
    | Int(REG_1, 0L) -> pp "false"
    | Int(t,x) -> 
	(* No moding here, since the value should have been modded earlier,
	   and if it wasn't, it's better not to hide it. *)
	pp (if 0L <= x && x < 10L
	    then Int64.to_string x
	    else Printf.sprintf "0x%Lx" x);
	pp ":";
	self#format_typ t
    | Str(x) -> pp "\""; pp x; pp "\""	  

  method format_let lparen rparen fe l e1 e2 = 
    lparen 100;
    pp "let ";
    open_box 0;
    self#format_lval l;
    pp " ="; space();
    fe 0 e1;
    close_box();
    space();
    pp "in";
    space();
    fe 0 e2;
    rparen 100

  method format_cast fe ct t e = 
    pp "cast(";
    fe 0 e;
    pp (")"^casttype_to_string ct^":");
    self#format_typ t
      

  method binop_to_string b =
    binop_to_string b

  method format_exp e =
    (* FIXME: Needs  some way to know when to parenthesize expressions.
       Eg: let x = y in (let x = 2:reg32_t in x) + x
       Eg: let x = y in x + let x = 2:reg32_t in x
       so just specifying a minimal binding strength isn't optimal, although
       it may be good enough.
    *)
    let rec fe prec e =
      (* prec tells us how much parenthization we need. 0 means it doesn't need
	 to be parenthesized. Larger numbers means it has higher precedence.
	 Maximum prec before paretheses are added are as follows:
	 100 LET
	 200 OR XOR AND
	 300 EQUAL NEQ
	 400 LT SLT SLE LE
	 500 LSHIFT RSHIFT ARSHIFT
	 600 PLUS MINUS
	 700 TIMES DIVIDE SDIVIDE MOD
	 800 UMINUS NOT
	 
      (* We intentiorally print parentheses around things with precedence
	 200 because those should have different precedences to match what
	 C does. *)
      *)
      let lparen bind = if bind < prec then pp "(" in
      let rparen bind = if bind < prec then pp ")" in
	open_box 0;
	(match e with
	     Let(l,e1,e2) ->  self#format_let lparen rparen fe l e1 e2
	   | BinOp(b,e1,e2) ->
	       let op_prec = match b with
		 | BITOR | XOR | BITAND	          -> 200
		 | EQ | NEQ			  -> 300
		 | LT | SLT | SLE | LE	          -> 400
		 | LSHIFT | RSHIFT | ARSHIFT      -> 500
		 | PLUS | MINUS		          -> 600
		 | TIMES|DIVIDE|SDIVIDE|MOD|SMOD  -> 700
	       in
		 lparen op_prec;
		 open_box 0;
		 (* all binops are left associative *)
		 (* but we want parentheses for things of the same precedence,
		    because some of our precedences are counterintuitive *)
		 fe (if op_prec = 200 then 201 else op_prec) e1;
		 space();
		 pp (self#binop_to_string b);
		 pp " ";
		 fe (op_prec+1) e2;
		 close_box();
		 rparen op_prec;
		 cut()
	   | UnOp(u,e) ->
	       lparen 800;
	       pp(unop_to_string u);
	       fe 800 e;
	       rparen 800
	   | Constant(v) ->
	       self#format_value v
	   | Lval l ->
	       self#format_lval l
	   | Name l ->
	       pp "name("; pp l; pp ")"
	   | Cast(ct,t,e) -> self#format_cast fe ct t e 
	   | Unknown u ->
	       pp "unknown \""; pp u; pp "\""
	);
	close_box()
    in
      fe 0 e
	
  (** Pretty print an lvalue using the given formater *)
  method format_lval = function
    | Temp var ->
	self#format_var var
    | Mem(var, idx, wt) ->
	self#format_name var;
	pp "[";
	self#format_exp idx;
	pp "]:";
	self#format_typ wt
	  
  method format_jmp e = 
    pp "jmp(";
    self#format_exp e;
    pp ");"

  method format_cjmp e1 e2 e3 = 
    pp "cjmp(";
    cut();
    self#format_exp e1;
    comma();
    self#format_exp e2;
    comma();
    self#format_exp e3;
    pp ");"

  method format_move l e = 
    self#format_lval l;
    pp " =";
    space();
    self#format_exp e;
    pp ";"

  method format_special s = 
    pp "special(\"";
    pp s;
    pp "\");"
    

  method format_label l = 
    pp "label ";
    pp l;
    pp ":"

  method format_expstmt e = 
    self#format_exp e;
    pp ";"

  method format_comment s = 
    pp "/*";
    pp s;
    pp "*/"

  method format_block dl sl' = 
    open_hvbox 0;
    pp "{";
    open_hvbox 4;
    space();
    self#format_decls dl;
    List.iter self#format_stmt sl';
    close_box();
    cut();
    pp "}";
    close_box()

      
  method format_attr s a =  
    pp (attr_to_string a);
    self#format_stmt s
    

  method format_function v ropt al is_ext bopt = (
    if is_ext then (pp "extern"; space());
    (match ropt with
	 None -> pp "void"
       | Some(rt') -> self#format_typ rt'
    );
    space();
    pp v;
    (match al with
	 [] -> pp "()"
       | x::xs ->
	   pp "(";
	   self#format_var x;
	   List.iter (fun y -> comma(); self#format_decl y) xs;
	   pp ")"
    );
    match bopt with
	None -> pp ";"
      | Some(blk) -> 
	  space();
	  self#format_stmt blk
  )

  method format_call lv_o e al = 
    (match lv_o with
       | None -> ()
       | Some lv ->
	   self#format_lval lv; pp " ="; space()
    );
    pp "call"; space();
    self#format_exp e;
    pp "(";
    ignore(List.fold_left
	     (fun c a ->
		self#format_exp a; (if c then comma());true)
	     false al);
    pp ");"

  method format_return e = 
    match e with 
	None -> pp "return;"
      | Some(e') -> 
	  pp "return";
	  space();
	  self#format_exp e';
	  pp ";"

  method format_assert e = 
    pp "assert(";
    self#format_exp e;
    pp ");"

  method format_halt e = 
    pp "halt(";
    self#format_exp e;
    pp ");"
	
  (** Pretty print a statement using the given formater *)
  method format_stmt s =
    let rec fs s =
      open_box 2;
      (match s with
	   Jmp e -> self#format_jmp e
	 | CJmp(e1,e2,e3) -> self#format_cjmp e1 e2 e3
	 | Move(l,e) -> self#format_move l e
	 | Special s -> self#format_special s 
	 | Label l -> self#format_label l
	 | ExpStmt e -> self#format_expstmt e
	 | Comment s -> self#format_comment s
	 | Block(dl,sl') -> self#format_block dl sl'
	 | Attr(s,a) -> self#format_attr s a
	 | Function(v,ropt,al,is_ext,bopt) -> 
	     self#format_function v ropt al is_ext bopt
	 | Call (lv_o, e, al) -> self#format_call lv_o e al
	 | Return eo ->  self#format_return eo
	 | Assert e -> self#format_assert e
	 | Halt e -> self#format_halt e
      );
      close_box();
      space()
    in
      fs s

  method format_stmts  sl = 
    List.iter (self#format_stmt) sl

  (** Pretty print a program using the given formater *)
  method format_program (dl,sl) =
    open_hvbox 0;
    self#format_decls dl;
    close_box();
    Format.pp_force_newline ft ();
    open_hvbox 0;
    List.iter self#format_stmt sl;
    close_box();
    Format.pp_print_newline ft ()
end
