(**
   Alias analysis.

   The functions in this module will perform alias analysis optimizations on
   array operations. In order to benefit from these optimizations, all memory
   operations must be translate to array operations first.

*)


(** A function which tells whether two SSA values are the same.
    [Some true] means always the same, [Some false] means always different,
    and [None] means unable to determine.
*)
type is_aliased = Ssa.value -> Ssa.value -> bool option


(** Generates an is_aliased function based on VSA information. *)
val vsa_alias : ?init:Ssa.var list -> Ssa.stmt list Vine_cfg.cfg -> is_aliased


(** Uses the given is_aliased function to optimize away Gets. *)
val alias_replace : is_aliased ->  Ssa.stmt list #Vine_cfg.cfg -> bool

(** Uses the given is_aliased function to optimize away unneeded array Sets. *)
val remove_dead_stores : is_aliased ->
  ?live_ends:(Ssa.var -> (Ssa.value -> bool option) option) ->
  Ssa.stmt list #Vine_cfg.cfg -> bool

