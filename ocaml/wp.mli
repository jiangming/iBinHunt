(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)

(*
*  wp.mli
*
*  Made by (David Brumley)
*  Login   <dbrumley@dbrumley-ubuntu.symantec.com>
*
*  Started on  Wed Jun 20 10:50:55 2007 David Brumley
*  Last update Wed Jun 20 10:51:51 2007 David Brumley
*)


val calculate_wp : (Gcl.exp -> Gcl.exp) -> Gcl.exp -> Gcl.t -> Gcl.exp
val dijkstra_wp : (Gcl.exp -> Gcl.exp) -> Gcl.exp -> Gcl.t -> Gcl.exp
val calculate_wlp : (Gcl.exp -> Gcl.exp) -> Gcl.exp -> Gcl.t -> Gcl.exp
val calculate_wp_ssa :
  (Vine.exp -> Vine.exp) -> Vine.exp -> Gcl.gcl -> Vine.exp
val leino_wp : (Gcl.exp -> Gcl.exp) -> Gcl.exp -> Gcl.t -> Vine.exp
val simp_skip : ('a -> 'b) -> int -> ('a -> 'b) -> 'a -> 'b
val simp_debug : ('a -> unit) -> ('b -> unit) -> ('a -> 'b) -> 'a -> 'b
val simp_print : (Vine.exp -> Vine.exp) -> Vine.exp -> Vine.exp

val globalize_wp : Vine.exp -> Vine.var list * Vine.exp
