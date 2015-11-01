(*
  Owned and copyright BitBlaze, 2007. All rights reserved.
  Do not copy, disclose, or distribute without explicit written
  permission.
*)
(*
 *  vine_tovine.ml
 *
 *  Made by (David Brumley)
 *  Login   <dbrumley@gs3102.sp.cs.cmu.edu>
 *)
(** Generic dissasembly interface.
    
    This module lets you disassemble a program without caring whether it
    came from an elf file or an IDApro database.
*)
val flag_is_elf : bool ref
val flag_is_ida : bool ref
val flag_idadb_file : string ref
val flag_elf_file : string ref
val flag_idadb_fileid : int ref

val function_heuristic : bool ref
val speclist : (string * Arg.spec * string) list
type funinfo_t = {
  name : string;
  start_address : int64;
  end_address : int64;
  is_extern : bool;
  tails : (int64 * int64) list;
}
val unknown_addrs_function : funinfo_t
val check_function_overlap : funinfo_t list -> unit
val print_syms : (int64 * string * bool * bool) list -> unit
val remove_duplicate_syms :
  ('a * string * 'b * 'c) list -> ('a * string * 'b * 'c) list
val heuristic_test : funinfo_t -> bool
val do_function_heuristics : funinfo_t list -> funinfo_t list
val fix_syms_atsigns :
  (Int64.t * string * bool * bool) list ->
  (Int64.t * string * bool * bool) list
val syms_to_funinfo :
  (Int64.t * string * bool * bool) list -> int64 -> funinfo_t list
val populate_function :
  Asmir.varctx -> Libasmir.instmap_t -> funinfo_t -> Vine.stmt

val populate_functions :
 Asmir.varctx ->
  funinfo_t list -> Libasmir.instmap_t -> Vine.stmt list * funinfo_t list

(** [ida_to_funfos filename i ] will return from the ida database
    given by [filename] for program with file_id = [i] the list of
    functions defined
*)
val ida_to_funinfos : string -> int -> funinfo_t list 
(*pm*)
val ida_to_funinfos_flat : string -> int -> funinfo_t list
(*pm end*) 

(** [ida_address_range_to_ir filename i sa ea] will return the IR for
    instructions in the range [sa] to [ea] in IDA database named by
    [filename] for program with index [i]. The returned declarations
    include the global declarations for the entire program.  
*)
val ida_address_range_to_ir : string -> int -> int64 -> int64 
  -> Vine.program
    
val elf_address_range_to_ir : string -> int64 -> int64 
  -> Vine.program

val mk_fun_decls : funinfo_t list -> Vine.stmt list
val from_elf :
  bool -> string -> Vine.program * funinfo_t list
val from_ida :    bool ->
    string ->
    int -> Vine.program * funinfo_t list
		(*pm*)
val from_ida_flat :    bool ->
    string ->
    int -> Vine.program * funinfo_t list

		(*pm end*)

val to_program :
  bool ->  (Vine.decl list * Vine.stmt list) * funinfo_t list

val address_range_to_ir : int64 -> int64 -> Vine.program


val add_call_to_non_function : 'a -> unit
val replace_calls_and_returns : Vine.program -> funinfo_t list -> Vine.program
val eliminate_interprocedural_jumps :
  Vine.program -> funinfo_t list -> Vine.program

(** [function_to_ir_by_address ()] returns a generic function [f] (works
    with both sqlite3 database and elf directly).  [f addr] will return
    (funinfo, Vine.program) for the function at [addr], else raise Not_found
    if no function starts with addr [addr] *)
val function_to_ir_by_address : unit -> int64 -> funinfo_t * Vine.program


(** types of exectables supported *)
type exeType =  Elf of string | IdaDB of string * int 


(** common interface to executables. *)
class exe :
  exeType ->
object
    val funinfos : funinfo_t list
    val gamma : Asmir.varctx
    val instmap : Libasmir.instmap_t
    val mutable x86trans : int64

    (** return register declarations *)
    method globals : Vine.decl list

    (** return a list of thunk functions. Returns the
	empty list  if using thunks are not enabled *)
    method thunks : unit -> Vine.stmt list

    (** return base program consisting of register declarations,
	and if appropriate, eflag thunk functions *)
    method base_program : unit -> Vine.program

    (**  get a list of all funinfos *)
    method get_funinfos : funinfo_t list

    (** get function information by name. 
	@raise Not_found if name not found *)
    method get_funinfo_by_name : string -> funinfo_t

    (** get function information by start address. 
	@raise Not_found if no function is associated with
	that start address *)
    method get_funinfo_by_start_address : int64 -> funinfo_t

    (** get function information by any address of the function body. 
	@raise Not_found if no function is associated with
	that start address *)
    method get_funinfo_by_any_address : int64 -> funinfo_t

    (** reset the transition count of x86 instructions to 0 *)
    method reset_translation_count : unit -> unit
      
    (** translate a single address. 
	@raise Not_found if no such instruction with that address *)
    method tr_address : Libasmir.address_t -> Vine.stmt list

    (** translate a function. @raise Not_found if an unknown
	address is encountered. *)
    method tr_function : funinfo_t -> Vine.stmt

    (** translate an address range.  @raise Not_found if an
	unknown address is encountered. *)
    method tr_range :
      Libasmir.address_t -> Libasmir.address_t -> Vine.stmt list

    (** return the total number of translated x86 instructions *)
    method x86translated : int64
  end

(** return an exe based on the cmd line arguments *)
val get_cmdline_exe : unit -> exe
