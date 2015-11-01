(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
*  vine_idadb.mli
*
*  Made by (David Brumley)
*  Login   <dbrumley@rtfm.ece.cmu.edu>
*
*  Started on  Wed Jun  6 13:48:12 2007 David Brumley
*  Last update Thu Jun 21 22:27:55 2007 David Brumley
*)

(**
Utilities for reading IDA Pro database created using the ida2sql
   plugin.  The database declarations are given in the plugin source,
   as well as in comments below.

At a high level, the database table 'info' contains information about
   each file that has been analyzed. A file is considered unique not
   by name, but by md5sum. So 2 files with the same name but different
   md5sum's can exist in the database.  The part of the info that is
   most important is the file_id.  To get information about a
   particular file, you find its file_id, then query subsequent tables
   providing this file_id.


*)

(** an error, usually because of an unexpected entry format in the DB *)
exception Ida_db_error of string

(** the versions of the idadb plugin that we currently support in this
    library *)
val supported_versions : int list


(** function flags -- taken from IDA SDK 5 funcs.hpp *)
type fflag = 
    FUNC_NORET      (**  function doesn't return *)
  | FUNC_FAR        (** far function *)
  | FUNC_LIB        (** library function *)
  | FUNC_STATIC     (** static function *)
  | FUNC_FRAME      (** function uses frame pointer (BP) *)
  | FUNC_USERFAR    (** user has specified far-ness *)
  | FUNC_HIDDEN     (** a hidden function chunk *)
  | FUNC_THUNK      (** thunk (jump) function *)
  | FUNC_BOTTOMBP   (** BP points to the bottom of the stack frame *)
  | FUNC_TAIL       (** This is a function tail. 
			May occur onlyw ith FUNC_HIDDEN *)
  | FUNC_MEMBER     (** member function *)
  | FUNC_VIRTUAL    (** virtual function *)
  | FUNC_CTR        (** constructor *)
  | FUNC_DTR        (** destructor *)
  | FUNC_VARARG     (** vararg function *)
;;

(** filetypes we currently support *)
type filetype = Pe | Elf

(** Corresponds to table:
    "CREATE TABLE info(\n"
    "file_id INTEGER PRIMARY KEY AUTOINCREMENT,\n"
    "fullname TEXT,\n"
    "filename TEXT,\n"
    "filetype TEXT,\n"
    "img_base INTEGER,\n"
    "start_ip INTEGER,\n"
    "start_sp INTEGER,\n"
    "instruction_size INTEGER,\n"
    "md5sum TEXT UNIQUE,\n"
    "generating_host TEXT,\n"
    "generated_on TEXT,\n"
    "plugin_version INTEGER\n"
    ");"
    
    Note that when img_base, start_ip, or start_sp are unknown,
    they are set to 0xffffffffL.
*)
type idainfo = int * (* file_id *)
    string *      (* fullname *)
    string *      (* filename *)
    filetype *    (* filetype *)
    int64 *       (* img_base *)
    int64 *       (* start_ip *)
    int64 *       (* start_sp *)
    int *         (* instruction size *)
    string *      (* md5sum as text where each byte is in hex *)
    string *      (* generating_host *)
    string *      (* generated_on *)
    int           (* plugin_version *)
;;

(** corresponds to table
  CREATE TABLE segments (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    file_id INTEGER,
    name TEXT,
    number INTEGER,
    start_address INTEGER,
    end_address INTEGER);
*)
type idasegment = int * (* id *)
    int * (* file_id *)
    string * (* name *)
    int *    (* number *)
    int64 *  (* start_address *)
    int64    (* end_address *)

(** corresponds to table
    "CREATE TABLE instrs (\n"
    "id INTEGER PRIMARY KEY AUTOINCREMENT,\n"
    "file_id INTEGER,\n"
    "address INTEGER,\n"
    "length INTEGER,\n"
    "bytes_0_3 INTEGER,\n"
    "bytes_4_7 INTEGER,\n"
    "bytes_8_11 INTEGER,\n"
    "bytes_12_15 INTEGER\n"
    ");"
*)
type idainstr = int * (* id *)
    int *              (* file_id *)
    int64 *            (* address *)
    int *              (* length *)
    int array        (* bytes of instruction *)


(** corresponds to table:
    "CREATE TABLE functions(\n"
    "id INTEGER PRIMARY KEY AUTOINCREMENT,\n"
    "file_id INTEGER,\n"
    "name TEXT,\n"
    "typedecl TEXT,\n"
    "flags INTEGER,\n"
    "start_address INTEGER,\n"
    "end_address INTEGER\n"
    ");"
*)
type idafunc = int *  (* id *)
    int *             (* file_id *)
    string *          (* function name *)
    string *          (* function type signature *)
    fflag list *      (* function IDA Pro flags *)
    int64 *           (* start_address *)
    int64             (* end_address *)
;;

(** corresponds to table:
    "CREATE TABLE exports(\n"
    "id INTEGER PRIMARY KEY AUTOINCREMENT,\n"
    "file_id INTEGER,\n"
    "name TEXT,\n"
    "ordinal INTEGER,\n"
    "address INTEGER\n"
    ");"
*)
type idaexport = int * (* id *)
    int *              (* file_id *)
    string *           (* exported function name *)
    int *              (* ordinal *)
    int64              (* exported function address *)
;;


(** corresponds to table:
    "CREATE TABLE strings(\n"
    "id INTEGER PRIMARY KEY AUTOINCREMENT,\n"
    "file_id INTEGER,\n"
    "address INTEGER,\n"
    "typ INTEGER,\n"
    "length INTEGER,\n"
    "bytes VARCHAR\n"
    ");"
*)
type idastring = int * (* id *)
    int *              (* file_id *)
    int64 *            (* address of string *)
    int *              (* IDA Pro type of string *)
    int *              (* length of string *)
    int array          (* string bytes *)
;;


(** corresponds to table:
    "CREATE TABLE vars (\n"
    "id INTEGER PRIMARY KEY AUTOINCREMENT,\n"
    "file_id INTEGER,\n"
    "function_address INTEGER,\n"
    "name TEXT,\n"
    "start_offset INTEGER,\n"
    "end_offset INTEGER\n"
    ");"
*)
type idavar = int * (* id *)
    int *           (* file_id *)
    int64 *         (* function address *)
    string *        (* variable name *)
    int64 *         (* variable start offset *)
    int64           (* variable end offset *)
;;


(** corresponds to table:
    "CREATE TABLE imports(\n"
    "id INTEGER PRIMARY KEY AUTOINCREMENT,\n"
    "file_id INTEGER,\n"
    "name TEXT,\n"
    "address INTEGER);"
*)
type idaimport = int * (* id *)
    int *              (* file_id *)
    string *           (* name *)
    int64              (* address *)

(** [filetype_to_string x] returns the string representation of X,
    e.g. "elf" or "pe" *)
val filetype_to_string : filetype -> string

(** [filetype_of_string x] returns the type representation of X,
    e.g. Elf or Pe *)
val filetype_of_string : string -> filetype

(** [flag_to_string flag] returns the string representation of
    flag. The string representation looks like the type name *)
val flag_to_string : fflag -> string

(** [flags_to_string flags] returns the string representation of
    flags. The string representation looks like the type name *)
val flags_to_string : fflag list -> string

(** [pr_idainfo pr info] prints the ida info [info] using [pr]. For
    example, [pr] can be print_string  *)
val pr_idainfo : (string -> 'a) -> idainfo -> 'a

(** [pr_idafunc pr func] prints [func] using [pr]. For
    example, [pr] can be print_string  *)
val pr_idafunc : (string -> 'a) -> idafunc -> 'a

(** [pr_idainstr pr x] prints [x] using [pr]. For
    example, [pr] can be print_string  *)
val pr_idainstr : (string -> unit) -> idainstr -> unit

(** [pr_idaexport pr x] prints [x] using [pr]. For
    example, [pr] can be print_string  *)
val pr_idaexport : (string -> 'a) -> idaexport -> 'a

(** [pr_idaexport pr x] prints [x] using [pr]. For
    example, [pr] can be print_string  *)
val pr_idastring : (string -> unit) -> idastring -> unit

(** [pr_idaexport pr x] prints [x] using [pr]. For
    example, [pr] can be print_string  *)
val pr_idaimport : (string -> 'a) -> idaimport -> 'a

(** [get_idainfos] returns all the ida info's in the database *)
val get_idainfos : Sqlite3.db -> idainfo list

(** [get_idafuncs_where db clause] returns all function entries
    satisfying the sql where clause [clause] *)
val get_idafuncs_where : Sqlite3.db -> string -> idafunc list

(** [get_idafuncs_by_id db i] returns all function entries
    corresponding to the database entry for file with id [i] *)
val get_idafuncs_by_id : Sqlite3.db -> int -> idafunc list

(** [get_ftails_for_function db i] returns the address ranges of the function
    tails for the function with id [i]. *)
val get_ftails_for_function : Sqlite3.db -> int -> (int64 * int64) list

(** [get_idainstr_where db clause] returns all disassembly
    entries satisfying the sql where clause [clause] *)
val get_idainstr_where : Sqlite3.db -> string -> idainstr list

(** [get_idafuncs_by_id db i] returns all disassembly entries
    corresponding to the database entry for file with id [i] *)
val get_idainstr_by_id : Sqlite3.db -> int -> idainstr list


(** [get_idaexports_where db clause] returns all exports
    entries satisfying the sql where clause [clause] *)
val get_idaexports_where : Sqlite3.db -> string -> (int * int * string
    * int * int64) list

(** [get_idaexports_by_id db i] returns all exports entries
    corresponding to the database entry for file with id [i] *)
val get_idaexports_by_id :
  Sqlite3.db -> int -> (int * int * string * int * int64) list

(** [get_idastrings_where db clause] returns all strings
    entries satisfying the sql where clause [clause] *)
val get_idastrings_where : Sqlite3.db -> string -> 
  (int * int * int64 * int * int * int array) list

(** [get_idastrings_by_id db i] returns all string entries
    corresponding to the database entry for file with id [i] *)
val get_idastrings_by_id :
  Sqlite3.db -> int -> (int * int * int64 * int * int * int array) list

(** [get_idastrings_where db clause] returns all vars
    entries satisfying the sql where clause [clause] *)
val get_idavars_where :
  Sqlite3.db -> string -> (int * int * int64 * string * int64 * int64) list


(** [get_idavars_by_id db i] returns all var entries
    corresponding to the database entry for file with id [i] *)
val get_idavars_by_id :
  Sqlite3.db -> int -> (int * int * int64 * string * int64 * int64) list

(** [get_idaimports_where db clause] returns all imports entries
    entries satisfying the sql where clause [clause] *)
val get_idaimports_where :
  Sqlite3.db -> string -> (int * int * string * int64) list

(** [get_idaimports_by_id db i] returns all imports entries
    corresponding to the database entry for file with id [i] *)
val get_idaimports_by_id :
  Sqlite3.db -> int -> (int * int * string * int64) list


(** [of_int64_data d] returns an int64 for the sqlite3 data. Raises
    Invalid_argument if [d] is not an sqlite3 integer *)
val of_int64_data : Sqlite3.Data.t -> int64

(** [of_text_data d] returns a string for the sqlite3 data. Raises
    Invalid_argumetn if [d] is not sqlite3 TEXT *)
val of_text_data : Sqlite3.Data.t -> string

(** [bytestr_to_array s i] converts a string [s] representation of [i]
    ints into an int array. This is a utility function for reading out
    the instruction bytes from the database *)
val bytestr_to_array : string -> int -> int array
