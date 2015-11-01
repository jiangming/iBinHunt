(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
Author: Zhenkai Liang
$Id: ir2c.ml 1277 2007-05-01 20:13:59Z zliang $
*)

open Vine
open Vine_typecheck
open Printf
module List=ExtList.List;;

let debug s =
  print_string s;
  flush stdout

let printed = ref false
let pr_deprecated () = 
  if not(!printed) then (
    prerr_string "WARNING: Vine_ir2c is deprecated. Use To_c instead.\n";
    printed := true
  )

let width_of_exp e = 
  pr_deprecated ();
  let i = Vine_typecheck.infer_type None e in
    match i with
	REG_1 -> "1"
      | REG_8 -> "8"
      | REG_16 -> "16"
      | REG_32 -> "32"
      | REG_64 -> "64"
      | _ -> raise (Invalid_argument "Expression type not a scalar")

let val_to_string = function
    Int(t, x) -> 
      (
	match t with 
	    REG_1 
	  | REG_8
	  | REG_16
	  | REG_32 ->
	      "0x" ^ sprintf "%lX" (Int64.to_int32 x)
	  | REG_64 ->
	      "0x"^ sprintf "%LX" x (*Int64.to_string x*)
	  | _ -> failwith "Unknown type"
      )
  | _ -> failwith  "Strings not supported. See Zhenkai."
      
let binop_prefix = function
    ARSHIFT
  | SDIVIDE
  | SMOD
  | SLT
  | SLE ->
      "(int64_t)"
  | _ -> ""

let binop_to_c = function
    PLUS -> "+"
  | MINUS -> "-"
  | TIMES -> "*"
  | DIVIDE -> "/"
  | SDIVIDE -> "/ (int64_t)" 
  | MOD -> "%"
  | SMOD -> "% (int64_t)"
  | LSHIFT -> "<<"
  | RSHIFT -> ">>"
  | ARSHIFT -> ">>"
  | BITAND -> "&"
  | BITOR -> "|"
  | XOR -> "^"
  | EQ -> "=="
  | NEQ -> "!="
  | LT -> "<"
  | LE -> "<="
  | SLT -> "< (int64_t)"
  | SLE -> "<= (int64_t)"

let width_to_str w = 
  pr_deprecated ();
  match w with
      REG_1 ->  "8"
    | REG_8 ->  "8"
    | REG_16 ->  "16"
    | REG_32 ->  "32"
    | REG_64 ->  "64"
    | _ -> ""

let rec type_to_c t =
  pr_deprecated ();
  match (Vine.unwind_type t) with 
      REG_1 -> "u_int8_t"
    | REG_8 -> "u_int8_t"
    | REG_16 -> "u_int16_t"
    | REG_32 -> "u_int32_t"
    | REG_64 -> "u_int64_t"
    | Array(t2,_) -> type_to_c t2
    | TMem _ -> type_to_string t
    | _ -> failwith  "Strings not supported. See Zhenkai."

let cast_to_c c w =
  pr_deprecated ();
  match (c, w) with
      (CAST_LOW, w)
    | (CAST_HIGH, w)
    | (CAST_UNSIGNED, w) -> "(u_int" ^ width_to_str w ^"_t)"
    | (CAST_SIGNED, w) -> "(int" ^ width_to_str w ^"_t)"


let list_to_string item_to_string al = 
  pr_deprecated ();
  match al with 
    [] -> "()"
    | hd :: tail ->
       let hd' = item_to_string hd in 
           "("^hd'^(
             List.fold_left (fun x y -> x^", "^(item_to_string y)) 
                      "" tail
           )^")"


let rename_regs (num, name, t) =
  (* remove the number from register names *)
  let newname = 
(*     if (ExitString.String.starts_with name "R_") *)
(*     then  *)
(*       let offset = String.rindex name '_' in *)
(* 	String.sub name 0 offset *)
(*     else if (ExtString.String.starts_with name "EFLAGS") *)
(*     then *)
(*       "EFLAGS" *)
(*     else *)
      name
  in
    (num, newname, t)
	
let var_to_c x = 
  pr_deprecated ();
  let var_to_name (_,name,_) = name in
  let renamedx = rename_regs x in
  let name = var_to_name renamedx
  in
    if ExtString.String.starts_with name "post_"
    then "post"
    else name

let arg_to_string ((_,_,t) as x) = type_to_c t ^" "^ var_to_c x
let declare_var x = arg_to_string x ^";\n"


(* let varset = ref [] *)

(* let var_def l = *)
(*   if List.mem l !varset or List.mem l regset *)
(*   then "" *)
(*   else let () = varset := l :: !varset in *)
(* 	 "" *)
(* let visit_var str l = *)
(*   match l with *)
(*       Temp(s,t) -> str ^ type_to_c t ^ " " ^ s ^ ";\n" *)
(*     | Mem(s,t,e) -> str *)

let rec exp_to_c e = 
  pr_deprecated ();
  match e with
      BinOp(op, e1, e2) -> 
	let prefix = binop_prefix op in
	let exp =exp_to_c e1^" "^binop_to_c op^" "^exp_to_c e2 in
	  (*if prefix="" then prefix ^ exp else*) "(" ^ prefix ^ exp ^ ")"
    | UnOp(op, e) -> "("^unop_to_c op e^")"
    | Constant(v) -> val_to_string v
    | Lval l -> lval_to_c l
    | Name s -> s
    | Cast(c,t,e) ->  
	( match c with 
	    CAST_LOW
	  | CAST_UNSIGNED ->
	      (cast_to_c c t) ^ "(" ^(exp_to_c e) ^ ")"
	  | CAST_SIGNED ->
	      if (width_of_exp e) <> (width_to_str t)
	      then 
		(cast_to_c c t) ^ "(int" ^ (width_of_exp e) ^ "_t) (" ^ 
		(exp_to_c e) ^ ")"
	      else
		(cast_to_c c t) ^ "(" ^(exp_to_c e) ^ ")"
	  | CAST_HIGH ->
	      cast_to_c c t ^ "do_cast('" ^ casttype_to_string c ^ 
		"', " ^ width_to_str t ^ ", " ^ exp_to_c e ^ ", " ^
		width_of_exp e ^ ")")
    | Unknown s -> "/* Unknown("^s^") */"
    | Let(l,e1,e2) -> "{\n" ^ 
	(match l with 
	    Temp v -> declare_var v
	   | Mem _ -> ""
	       (* FIXME: this will mutate the original memory *)
	)
	^ lval_to_c l ^ " = " ^ exp_to_c e1 ^ ";\n" ^ 
	  exp_to_c e2 ^ ";\n" ^ "}\n"

and lval_to_c x = 
  pr_deprecated ();
  let rec strip_leading_zeroes x i =
    if (String.length x) <= i then
      "0"
    else
      if (String.get x i) = '0' then
        strip_leading_zeroes x (i+1)
    else
      Str.string_after x i
  in
    match x with 
	(Temp(_,s,t)) when (ExtString.String.starts_with s "INPUT_") &&
	    not (ExtString.String.starts_with s "INPUT_missed") ->
	  let sl = Str.split (Str.regexp "_") s in
	  let offset = List.nth sl 2 in 
	    "INPUT[" ^ (strip_leading_zeroes offset 0)  ^ "]"
      | (Temp(_,s,t)) when ExtString.String.starts_with s "FIELD_" ->
	  let sl = Str.split (Str.regexp "_") s in
	  let offset = List.nth sl 2 in 
	    "getinput(format, data, " ^ (strip_leading_zeroes offset 0)  ^ 
	      ", " ^ (List.nth sl 3) ^ ")"
      | Temp x -> var_to_c x
      | (Mem((_,_,t),e,t2)) -> "*(" ^ type_to_c t ^ "*)" ^ "addrmap(" ^ exp_to_c e ^ ")" 
and unop_to_c op e= 
  pr_deprecated ();
  match op with
      NEG -> "-"^(exp_to_c e)
    | NOT -> 
	if ((width_of_exp e) = "1") then (exp_to_c e)^" == 0? 1: 0"
	else "~"^(exp_to_c e)



let jmp_to_c e = 
  pr_deprecated ();
  match e with
      Name s -> let a = "L" ^ s in
	"goto " ^ a ^ ";"
    | _ -> "ind_jmp("^exp_to_c e^ ");"


let rec stmt_to_cstring s =
  pr_deprecated ();
  let debugging_cond = function
      (Temp(_,s,t)) -> if (ExtString.String.starts_with s "post_cjmp")
	then "\nif (" ^ s ^ "==0) printf(\"Unsatisfied condition " ^ s ^"\\n\");"
	else ""
    | Mem _ -> ""
  in
  match s with
      Move(l,e) -> lval_to_c l ^ " = " ^ exp_to_c e ^ ";" ^
	debugging_cond l
    | Comment s -> "// "^s
    | ExpStmt e -> "ExpStmt(" ^ exp_to_c e ^ ")"
    | Label l -> "L"^l^":;" ^ "SHOWLABEL(\"%s\\n\", \"" ^ l ^ "\");"

    | Jmp e -> jmp_to_c e
    | CJmp(c, e1, e2) ->
	"if (" ^ exp_to_c c ^ ") {"
	^ jmp_to_c e1 ^ "} else { "
	^ jmp_to_c e2^"} "
    | Special s -> 
	if (s = "exploited")
	then "chop_exploited();"
	else "/* Special("^s^") */"
    | Call (lv_o, Name(lbl), al) -> 
	(match lv_o with
	  | None -> ""
	  | Some(lv) -> (lval_to_c lv) ^ " = ") ^
	  lbl^(list_to_string exp_to_c al)^";"
    | Call _ -> failwith "#error: indirect calls not supported"
    | Block(_) -> failwith "#error: block should be handled by p2c_stmt"
    | Function(_) -> failwith "#error: function should be handled by p2c_stmt"
    | Return _ -> failwith "#error: return should be handled  by p2c_stmt"
    | Assert(e) -> "assert("^(exp_to_c e)^");"
    | Halt(e) -> "exit("^(exp_to_c e)^");"
    | Attr(s',_) -> stmt_to_cstring s' 

let func_proto_to_string v ropt al is_ext = 
  pr_deprecated ();
  let rstring = (
      match ropt with
	  None -> "void"
	| Some(t) -> type_to_string  t) in 
  let argstring = list_to_string arg_to_string al in 
    if is_ext then 
      "extern "^rstring^" "^v^argstring
    else
      rstring^" "^v^argstring
	
let program_to_c pr (dl, sl) isReg =
  pr_deprecated ();
  let indent_level = ref 0 in
  let print_indent () = 
    let rec ind = function
      | 0 -> ()
      | x -> pr " "; ind (x-1)
    in 
      ind !indent_level
  in
  let p2c_var ((num,name,t) as x) =
    let isinput () = 
      ((ExtString.String.starts_with name "INPUT_") && 
      not (ExtString.String.starts_with name "INPUT_missed")) || 
	ExtString.String.starts_with name "FIELD_"
    in
      (* removing the trailing number from register variables *)
    let (newnum, newname, newtype) = rename_regs x in
      (* we cannot use List.mem to check whether it is a register because
	 of the differnece in number of reg variable *)
      if List.exists (fun (nn,ss,tt) -> ss = newname) Asmir.x86_regs or isinput () then ()
      else (
	  print_indent();
	  pr (declare_var x)
	)
  in
  let vardecl dl =
    let f (i1, _,_) (i2,_,_) = compare i1 i2 in 
    let sorteddl = List.sort ~cmp:f dl in
      (* Sorry, removed some bits. Now we will get warnings in the C code
	 for broken IR -aij *)
      List.iter p2c_var sorteddl
  in
  let rec p2c_stmt s = 
    match s with
      Jmp _ 
      | CJmp _ 
      | Move _ 
      | Special _
      | Label _ 
      | ExpStmt _ 
      | Call _
      | Assert _ 
      | Halt _ 
      | Comment _ ->
	  print_indent(); 
	  pr (stmt_to_cstring s);
	  pr "\n"
      | Block(dl, sl) -> 
	  print_indent(); 
	  pr "{\n";
	  indent_level := !indent_level + 2;
	  vardecl dl; 
	  List.iter (fun x -> p2c_stmt x) sl;
	  indent_level := !indent_level -2;
	  print_indent(); 
	  pr "}\n";
      | Attr(s, _) -> 
	  p2c_stmt s
      | Return(eo) -> (
	    print_indent ();
	    match eo with
		None -> pr "return;\n"
	      | Some(e) -> 
		  pr "return ";
		  pr (exp_to_c e);
		  pr ";\n"
	  )
      | Function(_) ->
	  ()
  in
  let rec p2c_func s =
    match s with
      Jmp _ 
      | CJmp _ 
      | Move _ 
      | Special _
      | Label _ 
      | ExpStmt _ 
      | Call _
      | Comment _ 
      | Assert _ 
      | Halt _ 
      | Return _ ->
	  ()
      | Attr (s,_) -> 
	  p2c_func s
      | Block(dl, sl) -> 
	  List.iter (fun x -> p2c_func x) sl;
      | Function(v,ropt,al,is_ext,bopt) -> (
	    let protostr = func_proto_to_string v ropt al is_ext
	    in
	      pr protostr;
	      match bopt with
		  None -> pr ";\n"
		| Some(blk) -> p2c_stmt blk
	  )
	  
  in
  let () = pr ("#include \"irtest.h\"\n") in
  let () = pr ("#define SHOWLABEL(...)\n") in
  let () = vardecl dl in
  let () = List.iter (fun x -> p2c_func x) sl in
  let () = if not isReg then
      pr ("void (*entry_function)(void) = 0;\n"^
	     "void init_signature()\n"^
	     "{\n"^
	     "    /* replace the following variables */\n"^
	     "    open_state(STATE_FILE_NAME_HERE);\n"^
	     "    entry_function = ENTRY_TO_SIGNATURE;\n"^
	     "}\n\n"^
	     "void cleanup_signature()\n"^
	     "{\n"^
	     "    close_state();\n"^
	     "    cleanup(); /* cleanup memory */\n"^
	     "}\n\n") in
  let () = if not isReg then 
      pr ("int signature" ^ 
	     "(const char *INPUT, int size)\n" ^ 
	     "{\n" ^ 
	     "    u_int8_t post;\n" ^
	     "    init_input(INPUT, size);\n" ^
	     "    init_signature();\n" ^
	     "    init_regs();\n"^
	     "    cleanup(); /* cleanup memory */\n"^
	     "    int jmpresult = setjmp(jmpenv);\n" ^
	     "    switch (jmpresult) {\n" ^
	     "    case 0:\n" ^
	     "        if (entry_function != 0) {\n"^
	     "            entry_function();\n" ^
	     "            post = 0;\n"^
	     "        } else\n"^
	     "            return -1;\n"^
	     "        break;\n" ^
	     "    case 1:\n" ^
	     "        post = 1;\n" ^
	     "        break;\n" ^
	     "    case 2:\n" ^
	     "        post = 0;\n" ^
	     "        break;\n" ^
	     "    default:\n" ^
	     "        post = 0;\n" ^
	     "    }\n" 
	 )
    else 
      pr ("int ir_tester" ^
	"(const char *INPUT, int size)\n" ^ 
	"{\n" ^ 
	"    u_int8_t post = 0;\n")
	
  in 
  let () = List.iter (fun x -> p2c_stmt x) sl in
    pr "    return post;\n}\n";;
