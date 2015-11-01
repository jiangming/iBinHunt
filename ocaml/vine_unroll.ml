(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(** Loop unrolling
    
    In a reducible CFG, a loop can be identified by the loop header.

 *)

open Vine
open Vine_cfg
open ExtList

(** Unroll a single loop n times

    This  function works as follows:
    1. Duplicate all the BBs in the loop replacing all labels with new labels.
    2. For every backedge in the original loop, make the edge point to the
    new BB corresponding to the old one, and replace the label.
    3. Repeat n times.
    4. Map all backedges in the new BBs according to the [fwd_jmps] function.

    By setting the optional [fwd_jmps] argument, you can control what happens
    at the last unrolled iteration. (default is to go back to the begining
    of the loop)
 *)
let unroll_loop ?fwd_jmps cfg blocks n = failwith "Unimplemented"
(*  let fwd_jmps = match fwd_jmps with
      None -> (fun s -> (s, find_label cfg s))
    | Some f -> f
  in
  let size = List.length blocks in
  let ordering = Hashtbl.create size in
  let () = List.iteri (fun i b -> Hashtbl.add ordering b i) blocks in
  let lt b1 b2 = Hashtbl.find ordering b1 < Hashtbl.find ordering b2 in
  let rec extract_labels ?(labs=[]) stmts =
    match stmts with
	Label l::xs -> extract_labels ~labs:(l::labs) xs
      | Attr(x,_)::xs -> extract_labels ~labs:labs (x::xs)
      | _::xs -> extract_labels ~labs:labs xs
      | [] -> labs
  in
  let loop_labels =
    List.flatten(List.map (fun bb -> extract_labels (bb_stmts cfg bb)) blocks)
  in
    (* maps old bb to new bb *)
  let bbmap = Hashtbl.create size in
    (* maps old lable to new lable *)
  let labmap = Hashtbl.create (List.length loop_labels) in
  let () = List.iter (fun l -> Hashtbl.add labmap l (newlab l)) loop_labels in
  let loop_jmps l =
    (* like fwd_jmps, but maps to the labels in the newly unrolled part of the
       loop *)
    (Hashtbl.find labmap l,
     Hashtbl.find bbmap (find_label cfg l))
  in
  let labrenamer = object
    inherit nop_vine_visitor
    method visit_stmt =
      function
	  Label l ->
	    (try
	       let l' = Hashtbl.find labmap l in
		 ChangeTo(Label l')
	     with Not_found ->
	       SkipChildren
	    )
	| _ -> SkipChildren
  end
  in
  let () = List.iter (fun bb -> ()) blocks in
    (* renaming targets is harder, because we need to determine whether they
       were backedges *)
(*  let targrenamer = object
    inherit nop_vine_visitor
    method visit_exp =
      function
	  Name l ->
	    (try
	       let l' = Hashtbl.find labmap l in
		 ChangeTo(Name l')
	     with Not_found ->
	       SkipChildren
	    )
	| _ -> DoChildren
  end *)
  in
    

    ()
*)
