(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
*  vine_chop.mli
*
*  Made by (David Brumley)
*  Login   <dbrumley@rtfm.ece.cmu.edu>
*
*  Started on  Thu May  3 12:09:14 2007 David Brumley
*  Last update Thu May  3 16:47:58 2007 David Brumley
*)


(** This is a utility file to help calculate the chop.  *)

(** the standard name for the chop end *)
val std_chop_end_name : string
val std_chop_end_fun : Vine.stmt

(** the standard name for the chop outside *)
val std_chop_outside_name : string
val std_chop_outside_fun : Vine.stmt

(** a standard marker name. Markers are inserted after calls to the
    chop end *)
val std_chop_call_end_marker : string

(** [prepare_chop_program p sl m stmt] assumes [sl] is a list of Label
    statements in which we wish to insert calls to [stmt], and [m] is
    a marker we insert directly after the call.  For
    example, if we want to compute the chop at address 804000 for
    chop_end, we would:
    - create a list sl containing the label Label(Int64.of_string 804000)
    - pass in {std_chop_end_fun} as the statement
    - pass in {std_chop_marker} as the marker
    and we would get out a program in which after every label for
    address 804000 there is a call to {std_chop_end_fun}, followed by
    marker {std_chop_marker}.
*)
val prepare_chop_program :
  Vine.program -> Vine.stmt list -> Vine.stmt -> Vine.stmt -> Vine.program
