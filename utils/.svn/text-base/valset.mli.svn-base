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

type tbool_t = TRUE | FALSE | UNKNOWN
type valset_t = {
  ranges : (int64 * int64 * tbool_t) list;
  vine_t : Vine.typ;
}
type valset_state_t = {
  vc : Stpvc.vc;
  ctx : Vine_stpvc.ctx;
  exp_val_var : Vine.var;
} 

(** @param printer
    @param value set
    print value set 
*)
val pp_valset : (string -> unit) -> valset_t -> unit

val valset_to_ps : string -> int -> int -> valset_t -> float -> unit

(** queries stp to determine if the boolean expression q
    is satisfiable. If so, returns a value of variable 
    for which q can be satisfied. Otherwise returns None.
    Implemented by calling stp in a child process, hence
    no destructive updates to the validity checker.
    @param vc is an stp validity checker
    @param ctx an stpvc context
    @param q query- an IR expression with type REG_1
    @param e is a vine exp, for which the list of counter-examples will
    be generated
*)
val fork_and_query :
  Stpvc.vc -> Vine_stpvc.ctx -> Vine.exp -> Vine.exp -> int64 option

(** uses stp to return a list of all values of v for which 
    q can be satisfied. non-destructive.
    @param vc is an stp validity checker
    @param q is a vine expression, which should evaluate to a boolean
    @param e is a vine exp, for which the list of counter-examples will
    be generated
*)
val all_counter_exs :
  ?acc:int64 list ->
  Stpvc.vc -> Vine_stpvc.ctx -> Vine.exp -> Vine.exp -> int64 list

(** returns max int64 value for given type. 
    XXX should move to vine_util
*)
val max_of_typ : Vine.typ -> int64
val name_of_var : Vine.var -> string
val typ_of_var : Vine.var -> Vine.typ

val insert_range : (int64 * int64 * tbool_t) list -> (int64 * int64 * tbool_t) -> (int64 * int64 * tbool_t) list

(**  Print a range 
    @param printer
    @param range
    @return void
*)
val pp_range : (string -> unit) -> (int64 * int64 * tbool_t) -> unit

(**  Print a list of ranges 
    @param printer
    @param range list
    @return void
*)
val pp_ranges : (string -> unit) -> (int64 * int64 * tbool_t) list -> unit
  
(** Print a valset
    @param printer
    @param value set
    @return void
*)
val pp_valset : (string -> unit) -> valset_t -> unit

(** @param vs
    @return (lowest UNKNOWN\FALSE, highest UNKNOWN\FALSE 
*)
val lh_bounds_of_valset : valset_t -> int64 * int64

(** calculate lowest and highest possible influence
    @param vs valset
    @return low * high
*)
val influence_bounds_of_valset : valset_t -> float * float


(** create initial valset and stp state
    @param prog IR program
    @param exp expression of interest
    @return initial valset * initial stp state
*)
val prog_to_valset :
  Vine.program -> Vine.exp -> valset_t * valset_state_t

(** find lowest and highest satisfiable value in valset,
    and update valset appropriately. 
    useful for identifying table boundaries, and (loose)
    upper bound on influence
    @param stp stp state
    @param valset current valset
    @return updated valset
*)
val establish_valset_bounds : valset_state_t -> valset_t -> valset_t

(** estimate influence by sampling UNKNOWN space.
    @param stp stp state
    @param valset current valset
    @param n max number of samples to take
    @return probable influence * sat count * samples taken * unknown count.
    (use latter three to reason about sampling confidence)
*)
val probable_influence : valset_state_t -> valset_t -> Int64.t
  -> float * Int64.t * Int64.t * Int64.t

(** keep asking stp for new counterexamples, updating valset
    appropriately. stops when no more counterexamples or 
    query limit is reached. useful for establishing lower bound
    on influence, or exact influence value when influence is low.
    @param stp stp state
    @param valset current valset
    @param n max number of samples to query for
    @return updated valset
*)
val find_up_to_n_samples : valset_state_t -> valset_t -> int64 -> valset_t

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
val sample_unknowns : valset_state_t -> valset_t -> int64 -> valset_t * int64


(** open given filename and redirect stp dumps to that fd. *)
val redirect_stp_to : string -> unit




(** finds lowest and highest values that expr may take on in program
    prog
    @param prog IR program
    @param expr expression of interest.
*)
(* val find_bounds : Vine.var list * Vine.stmt list -> Vine.exp -> int64 * int64 *)

val hybrid_estimate : valset_state_t -> valset_t -> valset_t

val sample : Vine.program -> Vine.exp -> int64 -> valset_t

(** Insert a range into an existing list of ranges 
    @param sorted ranges
    @param range to insert
    @return sorted ranges with range inserted, merging
    with other ranges when appropriate
*)
