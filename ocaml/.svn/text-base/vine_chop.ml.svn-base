(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
*  vine_chop.ml
*
*  Made by (David Brumley)
*  Login   <dbrumley@rtfm.ece.cmu.edu>
*
*  Started on  Thu May  3 11:35:21 2007 David Brumley
*  Last update Fri Jul 27 17:11:18 2007 David Brumley
*)

open Vine

let std_chop_end_name = "__chop_end"

let std_chop_end_fun = Function(std_chop_end_name, 
				None, [], false,
				Some(Block([], [Return(None);])))

let std_chop_outside_name = "chop_outside"

let std_chop_outside_fun = Function(std_chop_outside_name,
				    None, [], true, None) 

(* let std_chop_outside_fun = Function(std_chop_outside_name,  *)
(* 				    None, [], false, *)
(* 				    Some(Block([], [Return(None);]))) *)

let std_chop_call_end_marker = "chop_marker"
  
let rewrite_stmt call marker eal s : (stmt option * stmt list) = 
  try
    let e = List.find (fun x -> x = s) eal in
      (Some(e), [s;marker;call;])
  with
      Not_found -> (None, [s])

let rewrite_function eal call marker = function
    Function(v,topt,dl,b,Some(Block(blkdl,blksl))) ->
      let (ealfound, blksl) = 
	List.fold_left (fun (accel, accsl) s ->
			  let (eopt, s') = rewrite_stmt call marker eal s 
			  in
			    match eopt with
				None -> (accel, s'@accsl)
			      | Some(e) -> 
				  (e::accel, s'@accsl)
		       ) ([], [])  blksl in 
	(ealfound, Function(v,topt,dl,b,Some(Block(blkdl, List.rev blksl))))
  | _ as s -> ([], s)

let prepare_chop_program (dl,sl) eal marker  = function
  Function(a,None,[],d,e) as f ->
    let call = Call(None, Name(a), []) in 
    let (ealfound, sl) = List.fold_left 
      (fun (ealacc,slacc) s ->
	 let (ealfound, s) = rewrite_function eal call marker s in
	   (ealfound @ ealacc, s::slacc)
      ) ([],[]) sl in
      if (List.length ealfound) <> (List.length eal) then (
	Printf.eprintf "not all chop end addresses found\n";
	Printf.eprintf "Specified:\n";
	List.iter (fun x -> Printf.eprintf "\t%s" (stmt_to_string
						       x)) eal ;
	Printf.eprintf "Found:\n";
	List.iter (fun x -> Printf.eprintf "\t%s" (stmt_to_string
						       x)) ealfound 

      );
      (dl,f::sl)
  | Function(a,b,c,d,e) -> 
      raise (Invalid_argument 
	       "Chop function must take no arguments and return nothing")
  | _ -> raise (Invalid_argument 
		  "must specify function to call as chop destination")
	       

