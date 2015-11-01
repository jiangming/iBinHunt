(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
*  vine_frame.ml
*
*  Made by (David Brumley)
*  Login   <dbrumley@rtfm.ece.cmu.edu>
*
*  Started on  Wed Apr  4 18:26:01 2007 David Brumley
*  Last update Wed Apr  4 19:53:13 2007 David Brumley
*)


module type TEMP = 
sig
  type temp
  val new_temp : unit -> temp
  val to_string : temp -> string

  type label
  val new_label : unit -> label
end

module MyTemp : TEMP = 
struct
  type temp = int
  type label = int

  let next_temp = ref 0
  let next_label = ref 0

  let newtemp () = 
    let r = !next_temp in 
      next_temp := !next_temp + 1;
      r

  let to_string t = "t_"^(int_to_string t)

  let newlabel () = 
    let r = !next_label in 
      next_label := !next_label + 1;
      r
end

module TEMP = MyTemp;;

module type FRAME = 
sig
  type frame
  type access
  val new_frame : string * bool list -> frame
  val name : frame -> string
  val alloc_local : frame -> bool -> access
  val fp : int
end



module X86Frame : FRAME = 
struct

  type access = InReg of int | InFrame of int

  type frame = {name : string; 
		mutable formals : access list;
		mutable next_frame_slot : int;
		mutable next_reg : int;
	       } 
      

  let rv = 0

  let alloc_local frame b = 
    if b then  (
      let s = frame.next_frame_slot in
	frame.next_frame_slot <- frame.next_frame_slot + 1;
	InFrame(s)
    ) else (
      let s = frame.next_reg in 
	frame.next_reg <- frame.next_reg + 1;
	InReg(s)
    )
 
  let new_frame (nm,frmls) =
    let r = {name = nm; formals = []; 
	     next_frame_slot = 0;
	     next_reg = 0;
	    } in
    let frmls' = List.map (fun x -> alloc_local r x ) frmls in 
      r.formals <- frmls';
      r
    
  let name f = f.name
    

end;;

module Frame : FRAME= X86Frame;;

module type TRANSLATE  = 
sig
  type level
  type access
  val outermost : level
  val new_level : (level * string * bool list) -> level
  val formals : level -> access list
  val alloc_local : level -> bool -> access
end


module MyTrans = 
struct

  type level = { scope : int;
		 name : string;
		 parent : level option;
		 frame : Frame.frame;
		 mutable formals : access list;
	       } 
  and access = level * Frame.access

  let outermost = { name = "_global"; 
		    scope = 0; 
		    parent = None; 
		    frame = Frame.new_frame ("_global", []);
		    formals = []; }

  let alloc_local l b =
    let x = Frame.alloc_local l.frame b in
      (l,x)

  let new_level (parent,name,formals) = 
    let r = 
      { scope = parent.scope + 1; 
	name = name; 
	frame = Frame.new_frame (name,formals);
	formals = [];
	parent = Some(parent);
      }   in  
    let f' = List.map (fun x -> alloc_local r x ) (true::formals) in
      r.formals <- f';
      r

  let formals l = List.tl l.formals

end

module Translate : TRANSLATE = MyTrans;;
