(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(** File: vine_xml.ml
 * @author: Ivan Jager
 * 
 * Parse a vine XML file into a statement list.
 * See the of_xml and of_xmluri functions.
 *)

open Gdome
open Vine



(* Should be in List *)
let list_map_some f l = 
  let rec m n o =
    match o with
	[] -> n
      | x::xs ->
	  (match f x with
	       Some v -> m (v::n) xs
	     | None -> m n xs )
  in List.rev(m [] l)

(* stollen from missinglib, to avoid dependency *)
let wschars = [' '; '\t'; '\r'; '\n'];;
let rec lstrip s = 
  if String.length s < 1 then s else
  if List.mem (String.get s 0) wschars then
    lstrip (String.sub s 1 ((String.length s) - 1))
  else
    s;;

let rec rstrip s =
  if String.length s < 1 then s else
    let len = String.length s in
    if List.mem (String.get s (len - 1)) wschars then
      rstrip (String.sub s 0 (len - 1))
    else
      s;;

let strip s = lstrip(rstrip s);;
(* end stollen from missinglib *)


(* convert XML document to program*)
let of_xml (doc:Gdome.document) =
  let attr1 (n:Gdome.element) a = ((n#getAttribute(domString a))#to_string : string)
  in
  let subnodes (n:Gdome.element) =
    let l = n#get_childNodes in
      Array.to_list (Array.init
		       (l#get_length)
		       (fun i -> let Some v = l#item i in v))
  in
  let subelements n = 
      list_map_some
	(fun v ->
	   try Some(new element_of_node v)
	   with GdomeInit.DOMCastException e ->
	     let t = match v#get_nodeType with
		 GdomeNodeTypeT.NOT_USED_0 -> "NOT_USED_0"
	       | GdomeNodeTypeT.ELEMENT_NODE -> "ELEMENT_NODE"
	       | GdomeNodeTypeT.ATTRIBUTE_NODE -> "ATTRIBUTE_NODE"
	       | GdomeNodeTypeT.TEXT_NODE ->
		   (match v#get_nodeValue with
			None -> "TEXT_NODE"
		      | Some ds ->
			  if strip (ds#to_string) = ""
			  then ""
			  else "TEXT_NODE" )
	       | GdomeNodeTypeT.CDATA_SECTION_NODE -> "CDATA_SECTION_NODE"
	       | GdomeNodeTypeT.ENTITY_REFERENCE_NODE -> "ENTITY_REFERENCE_NODE"
	       | GdomeNodeTypeT.ENTITY_NODE -> "ENTITY_NODE"
	       | GdomeNodeTypeT.PROCESSING_INSTRUCTION_NODE -> "PROSSESSING_INSTRUCTION_NODE"
	       | GdomeNodeTypeT.COMMENT_NODE -> ""
	       | GdomeNodeTypeT.DOCUMENT_NODE -> "DOCUMENT_NODE"
	       | GdomeNodeTypeT.DOCUMENT_TYPE_NODE -> "DOCUMENT_TYPE_NODE"
	       | GdomeNodeTypeT.DOCUMENT_FRAGMENT_NODE -> "DOCUMENT_FRAGMENT_NODE"
	       | GdomeNodeTypeT.NOTATION_NODE -> "NOTATION_NODE"
	     in
	       ((if t <> ""
		 then Printf.printf "Unexpected '%s%s' node.\n" t 
		     (match v#get_nodeValue with
			  None -> ""
			| Some ds -> "("^ds#to_string^")"));
		None) )
	(subnodes n)
  in
  let data n =
    let [c] = subnodes n in
    let Some s = c#get_nodeValue in s#to_string
  in
  let el2type n =
    type_of_string (attr1 n "type")
  in
  let rec node_to_exp n =
    match n#get_tagName#to_string with
	"binop" ->
	  let [lhs;rhs] = subelements n in
	    BinOp(binop_of_string (attr1 n "type"),
		  node_to_exp lhs,
		  node_to_exp rhs )
      | "unop" ->
	  let [operand] = subelements n in
	    UnOp(unop_of_string (attr1 n "type"),
		 node_to_exp operand )
      | "constant" ->
	  let tw = el2type n in
	    Constant(tw, const_of_stringt tw (data n))
      | "name" ->  Name(data n)
      | "unknown" -> Unknown(data n)
      | "cast" -> let [sub] = subelements n in
		    Cast(casttype_of_string(attr1 n "casttype"),
			el2type n,
			node_to_exp sub )
      | "phi" ->
	  let names = Str.split (Str.regexp " ") (data n)
	  in
	    raise(ParseError "FIXME: XML parsing of phi not implemented")
      | "temp" | "mem" ->
	  Lval(node_to_lval n)
      | "let" ->
	  let [n1;n2;n3] = subelements n in
	    Let(node_to_lval n1,
	       node_to_exp n2,
	       node_to_exp n3 )
      | "if" ->
	  let [n1;n2;n3] = subelements n in
	  let (e1,e2,e3) = (node_to_exp n1, node_to_exp n2, node_to_exp n3 ) in
	  let t = Vine_typecheck.infer_type None e2 in
	  let cond = Temp(newvar "cond", bool_t) in
	    Let(cond,  Cast(CAST_SIGNED, t, e1),
	       exp_or(exp_and(Lval cond,e2), exp_and(exp_not(Lval cond), e3)) )

      | s -> raise(ParseError("node <"^s^"> is  not a known exp"))
  and node_to_lval n =
    match n#get_tagName#to_string with
	"temp" ->
	  Temp(data n, el2type n)
      | "mem" -> let [addr] = subelements n in
		   Mem("mem", el2type n, node_to_exp addr)
      | s -> raise(ParseError("node <"^s^"> is  not a known lvalue"))
  in
  let node_to_stmt n =
    match n#get_tagName#to_string with 
	"jmp" ->
	  let [t] = subelements n in
	    Jmp(node_to_exp t)
      | "cjmp" ->
	  let [c;t;f] = subelements n in
	    CJmp(node_to_exp c,
		 node_to_exp t,
		 node_to_exp f )
      | "label" ->
	  Label(data n)
      | "move" ->
	  let [lhs;rhs] = subelements n in
	    Move(node_to_lval lhs,
		 node_to_exp rhs)
      | "comment" ->
	    Comment(data n)
      | "special" ->
	    Special(data n)
      | "expstmt" ->
	  let [e] = subelements n in
	    ExpStmt(node_to_exp e)
      | s -> raise(ParseError("node <"^s^"> is  not a known stmt"))
  in
    List.map node_to_stmt (subelements (doc#get_documentElement))


(* read XML from a URI and convert to program *)
let of_xmluri u =
  let di = domImplementation() in
    of_xml (di#createDocumentFromURI ~uri:u ~validatingMode:IDOMImplementation.Validating ())

