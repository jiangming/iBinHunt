(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
*  vine_idadb.ml
*
*  Made by (David Brumley)
*  Login   <dbrumley@wideload>
*
*  Started on  Mon Jun  4 17:53:25 2007 David Brumley
*  Last update Fri Jun 22 14:20:25 2007 David Brumley
*)

open Sqlite3;;
module List = ExtList.List
(* module D = Debug.Make(struct let name = "vine_idadb" end)  *)
module D = Debug.NoDebug;; 

let supported_versions = [4; 5; 6];;

(** an error in our IDA DB *)
exception Ida_db_error of string;;

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

type filetype = Pe | Elf
;;


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
    "bytes VARCHAR(32)\n"
    ");"
*)
type idainstr = int *  (* id *)
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

let filetype_to_string = function
    Pe -> "pe"
  | Elf -> "elf"
;;

let filetype_of_string s = 
  if s = "pe" then Pe else
    ( if s = "elf" then Elf else 
	raise (Ida_db_error  "Unexpected filetype in IDA database"))

(** conversion from flags as specified in IDA Pro SDK 5.0 funcs.hpp
    from an integer to our fflag type *)
let to_fflag i =
  let setflags num flags newflag = 
    if (Int32.logand i num) <> 0l then newflag :: flags else flags
  in
  let flags = setflags 0x1l [] FUNC_NORET in 
  let flags = setflags 0x2l flags FUNC_FAR in 
  let flags = setflags 0x4l flags FUNC_LIB in 
  let flags = setflags 0x8l flags FUNC_STATIC in
  let flags = setflags 0x10l flags FUNC_FRAME in 
  let flags = setflags 0x20l flags FUNC_USERFAR in 
  let flags = setflags 0x40l flags FUNC_HIDDEN in 
  let flags = setflags 0x80l flags FUNC_THUNK in 
  let flags = setflags 0x100l flags FUNC_BOTTOMBP in 
  let flags = setflags 0x8000l flags FUNC_TAIL in 
  let flags = setflags 0x200l flags FUNC_MEMBER in
  let flags = setflags 0x400l flags FUNC_VIRTUAL in
  let flags = setflags 0x800l flags FUNC_CTR in 
  let flags = setflags 0x1000l flags FUNC_DTR in 
  let flags = setflags 0x2000l flags FUNC_VARARG in 
    flags

let flag_to_string = function
    FUNC_NORET     -> "FUNC_NOTRET"  
  | FUNC_FAR       -> "FUNC_FAR"
  | FUNC_LIB       -> "FUNC_LIB"  
  | FUNC_STATIC    -> "FUNC_STATIC"
  | FUNC_FRAME     -> "FUNC_FRAME"
  | FUNC_USERFAR   -> "FUNC_USERFAR"
  | FUNC_HIDDEN    -> "FUNC_HIDDEN"
  | FUNC_THUNK     -> "FUNC_THUNK"
  | FUNC_BOTTOMBP  -> "FUNC_BOTTOMBP"
  | FUNC_TAIL      -> "FUNC_TAIL"
  | FUNC_MEMBER    -> "FUNC_MEMBER"
  | FUNC_VIRTUAL   -> "FUNC_VIRTUAL"
  | FUNC_CTR       -> "FUNC_CTR"
  | FUNC_DTR       -> "FUNC_DTR"
  | FUNC_VARARG    -> "FUNC_VARARG"

(*  | _ -> raise (Invalid_argument "flag_to_string: Unknown type") *)


let flags_to_string flags = 
  let str = 
    List.fold_left (fun acc x -> 
		      let s = flag_to_string x in 
			s^" "^acc) "" flags in
    "["^str^"]"



let md5_of_string s = 
  (* Printf.printf "%s\n%!" s; *)
  Scanf.sscanf  s    ("%x %x %x %x %x %x %x"^^
    " %x %x %x %x %x %x %x %x %x")
    (fun a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
       ->
	 [a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15;a16]
    )

let pr_idainfo pr ((file_id,fullname,filename,filetype,img_base,
		    start_ip,start_sp,instruction_size,
		    md5sum, generating_host,
		    generated_on,plugin_version):idainfo) =
  pr (string_of_int file_id);
  pr ", ";
  pr fullname;
  pr ", ";
  pr filename;
  pr ", ";
  pr (filetype_to_string filetype);
  pr ", ";
  pr (Int64.to_string img_base);
  pr ", ";
  pr (Int64.to_string start_ip);
  pr ", ";
  pr (Int64.to_string start_sp);
  pr ", ";
  pr (string_of_int instruction_size);
  pr ", ";
  pr md5sum;
  pr ", ";
  pr generating_host;
  pr ", ";
  pr generated_on;
  pr ", ";
  pr (string_of_int plugin_version)
;;


let pr_idafunc pr ((id,file_id,name,typedecl,flags,sa,ea):idafunc) = 
  pr (string_of_int id);
  pr ", ";
  pr (string_of_int file_id);
  pr ", ";
  pr name;
  pr ", ";
  pr typedecl;
  pr ", ";
  pr (flags_to_string flags);
  pr ", ";
  pr (Int64.to_string sa);
  pr ", ";
  pr (Int64.to_string ea)
;;


let pr_idasegment pr ((id,file_id,name,number,sa,ea):idasegment) = 
  pr (string_of_int id);
  pr ", ";
  pr (string_of_int file_id);
  pr ", ";
  pr name;
  pr ", ";
  pr (string_of_int number);
  pr ", ";
  pr (Int64.to_string sa);
  pr ", ";
  pr (Int64.to_string ea)
;;

let pr_idainstr pr ((id,file_id, addr, len, bytearr):idainstr) = 
  pr (string_of_int id);
  pr ", ";
  pr (string_of_int file_id);
  pr ", ";
  pr (Int64.to_string addr);
  pr ", ";
  pr (string_of_int len);
  pr ", ";
  pr "[";
  Array.iter (fun x -> 
	       let s = Printf.sprintf "%x " x in 
	       pr s) bytearr;
  pr "]"
;;

let pr_idaexport pr ((id,file_id, name, ord, addr):idaexport) = 
  pr (string_of_int id);
  pr ", ";
  pr (string_of_int file_id);
  pr ", ";
  pr name;
  pr ", ";
  pr (string_of_int ord);
  pr ", ";
  pr (Int64.to_string addr)
;;

let pr_idastring pr ((id,file_id,addr,typ,len,bytes):idastring) = 
  pr (string_of_int id);
  pr ", ";
  pr (string_of_int file_id);
  pr ", ";
  pr (Int64.to_string addr);
  pr ", ";
  pr (string_of_int typ);
  pr ", ";
  pr (string_of_int len);
  pr ", ";
  pr "[";
  Array.iter (fun x -> 
	       let s = Printf.sprintf "%x " x in 
	       pr s) bytes;
  pr "]"

let pr_idaimport pr ((id, file_id, name, address):idaimport) = 
  pr (string_of_int id);
  pr ", ";
  pr (string_of_int file_id);
  pr ", ";
  pr name;
  pr ", ";
  pr (Int64.to_string address)
;;
  

let of_int64_data = function
  Data.INT(d) -> d
  | _ -> raise (Invalid_argument "SQL column not INTEGER")
      
let of_text_data = function
    Data.TEXT(s) -> s
  | _ -> raise (Invalid_argument "SQL column not TEXT")
	  
let get_idainfos_v4 db  = 
  let sql = "SELECT "^
    "file_id, fullname, filename, filetype, "^
    "start_ip,start_sp,instruction_size,"^
    "md5sum,generating_host,generated_on,plugin_version"^
    " from info;" 
  in
  let infos = ref [] in 
  let stepbystep s = 
    while step s == Rc.ROW do
      let plugin_ver = Int64.to_int (of_int64_data (column s 10)) in
      let (info:idainfo) = (
	Int64.to_int (of_int64_data (column s 0)),
	of_text_data (column s 1), (* fullname *)
	of_text_data (column s 2), (* filename *)
	filetype_of_string (of_text_data (column s 3)),
	4294967295L, (* img_base = BADADDR *)
	(of_int64_data (column s 4)), (* start_ip *)
	(of_int64_data (column s 5)), (* start_sp *)
	Int64.to_int (of_int64_data (column s 6)), (* instruction_size *)
	(of_text_data (column s 7)), (* md5sum *)
	of_text_data (column s 8), (* generating host *)
	of_text_data (column s 9), (* generated_on *)
	plugin_ver
      )  in 
	infos := info :: !infos
    done
  in
  let stmt = prepare db sql in 
    stepbystep stmt;
    List.rev !infos
;;

let get_idainfos_v5 db  = 
  let sql = "SELECT "^
    "file_id, fullname, filename, filetype, "^
    "img_base,start_ip,start_sp,instruction_size,"^
    "md5sum,generating_host,generated_on,plugin_version"^
    " from info;" 
  in
  let infos = ref [] in 
  let stepbystep s = 
    while step s == Rc.ROW do
      let plugin_ver = Int64.to_int (of_int64_data (column s 11)) in
      let (info:idainfo) = (
	Int64.to_int (of_int64_data (column s 0)),
	of_text_data (column s 1), (* fullname *)
	of_text_data (column s 2), (* filename *)
	filetype_of_string (of_text_data (column s 3)),
	(of_int64_data (column s 4)), (* img_base *)
	(of_int64_data (column s 5)), (* start_ip *)
	(of_int64_data (column s 6)), (* start_sp *)
	Int64.to_int (of_int64_data (column s 7)), (* instruction_size *)
	(of_text_data (column s 8)), (* md5sum *)
	of_text_data (column s 9), (* generating host *)
	of_text_data (column s 10), (* generated_on *)
	plugin_ver
      )  in 
	infos := info :: !infos
    done
  in
  let stmt = prepare db sql in 
    stepbystep stmt;
    List.rev !infos
;;

let get_idainfos db =
  let sql = "SELECT MAX(plugin_version) from info;" in
  let stmt = prepare db sql in
  let highest_version =
    if step stmt == Rc.ROW 
    then Int64.to_int (of_int64_data (column stmt 0))
    else raise(Invalid_argument "Database is not in IDADB format")
  in
    match highest_version with
      | x when not (List.mem x supported_versions) ->
	  raise (Invalid_argument "Database has unsupported version")
      |	x when x >= 5 -> get_idainfos_v5 db
      | _ -> get_idainfos_v4 db
;;

let get_idasegments_where db clause = 
  let sqltext = Printf.sprintf 
    ("SELECT id,file_id,name,number,start_address,end_address "^^
       "from segments where %s;") clause in 
  let segs = ref [] in 
  let stepbystep s = 
    while step s == Rc.ROW do
      let (f:idasegment) = (
	Int64.to_int (of_int64_data (column s 0)),
	Int64.to_int (of_int64_data (column s 1)),
	of_text_data (column s 2),
	Int64.to_int (of_int64_data (column s 3)),
	(of_int64_data (column s 4)),
	(of_int64_data (column s 5))
      ) in
	segs := f::!segs
    done
  in
  let stmt = prepare db sqltext in
    stepbystep stmt;
    List.rev !segs
;;  


let get_idafuncs_where db clause = 
  let sqltext = Printf.sprintf 
    ("SELECT id,file_id,name,typedecl,flags,start_address,end_address "^^
       "from functions where %s;") clause in 
  let funcs = ref [] in 
  let stepbystep s = 
    while step s == Rc.ROW do
      let (f:idafunc) = (
	Int64.to_int (of_int64_data (column s 0)),
	Int64.to_int (of_int64_data (column s 1)),
	of_text_data (column s 2),
	of_text_data (column s 3),
	to_fflag (Int64.to_int32 (of_int64_data (column s 4))),
	(of_int64_data (column s 5)),
	(of_int64_data (column s 6))
      ) in
	funcs := f::!funcs
    done
  in
  let stmt = prepare db sqltext in
    stepbystep stmt;
    List.rev !funcs
;;  

let get_idafuncs_by_id db file_id = 
  get_idafuncs_where db (Printf.sprintf "file_id = %d" file_id)


let get_ftails_for_function db function_id =
  let sqltext = Printf.sprintf 
    ("SELECT start_address,end_address from ftails where function_id = %d;")
    function_id
  in
  let tails = ref [] in
    (try 
       let s = prepare db sqltext in
	 while step s = Rc.ROW do
	   tails :=
	     ((of_int64_data (column s 0)), (of_int64_data (column s 1))) :: !tails
	 done;
     with Sqlite3.Error("Sqlite3.prepare: no such table: ftails") -> ());
    List.rev !tails

let bytestr_to_array str numitems  = 
  let arr = Array.make numitems 0  in 
  let scanbuf = Scanf.Scanning.from_string str in 
    for i=0 to (numitems-1) do 
      Scanf.bscanf scanbuf "%2x" (fun d -> 
				     Array.set arr i d)
    done;
    arr


let get_idainstr_where db clause = 
  let sql = Printf.sprintf 
    ("SELECT id,file_id,address,length,bytes "^^
	       "from instrs where %s;") clause in
  let instrs = ref [] in 
  let stepbystep s =  (
    while step s == Rc.ROW do
      let len = Int64.to_int (of_int64_data (column s 3)) in 
      let bytestr = of_text_data (column s 4) in
      let bytearr = bytestr_to_array bytestr len in 
      let addr =  (of_int64_data (column s 2)) in 
      let (d:idainstr) = (
	Int64.to_int (of_int64_data (column s 0)),
	Int64.to_int (of_int64_data (column s 1)),
	addr,
	len,
	bytearr)
      in
	instrs := d::!instrs
    done
  ) in 
  let stmt = prepare db sql in
    stepbystep stmt;
    List.rev !instrs
  

let get_idainstr_by_id db file_id = 
  get_idainstr_where db (Printf.sprintf "file_id = %d" file_id)

let get_idaexports_where db clause = 
  let sql = Printf.sprintf
    ("SELECT id,file_id,name,ordinal,address from "^^
       "exports where %s;") clause in
  let exports = ref [] in 
  let stepbystep s =  (
    while step s == Rc.ROW do
      let export = (
	Int64.to_int (of_int64_data (column s 0)),
	Int64.to_int (of_int64_data (column s 1)),
	(of_text_data (column s 2)),
	Int64.to_int (of_int64_data (column s 3)),
	(of_int64_data (column s 4))
      ) in 
	exports := export :: !exports
    done
  ) in 
  let stmt = prepare db sql in
    stepbystep stmt;
    List.rev !exports


let get_idaexports_by_id db file_id = 
  get_idaexports_where db (Printf.sprintf "file_id = %d" file_id)

let get_idastrings_where db clause = 
  let sql = Printf.sprintf
    ("SELECT id,file_id,address,typ,length,bytes from "^^
       "strings where %s;") clause in
  let idastrings = ref [] in 
  let stepbystep s =  (
    while step s == Rc.ROW do
      let bytestr = of_text_data (column s 5) in 
      let len = Int64.to_int (of_int64_data (column s 4)) in 
      let bytearr = bytestr_to_array bytestr len in 
      let idastr = (
	Int64.to_int (of_int64_data (column s 0)),
	Int64.to_int (of_int64_data (column s 1)),
	(of_int64_data (column s 2)),
	Int64.to_int (of_int64_data (column s 3)),
	len,
	bytearr
      ) in 
	idastrings := idastr :: !idastrings
    done
  ) in 
  let stmt = prepare db sql in
    stepbystep stmt;
    List.rev !idastrings


let get_idastrings_by_id db file_id = 
  get_idastrings_where db (Printf.sprintf "file_id = %d" file_id)

let get_idavars_where db clause = 
  let sql = Printf.sprintf
    ("SELECT "^^
       "id,file_id,function_address,name,start_offset,end_offset"^^
       " from vars where %s;") clause in
  let vars = ref [] in 
  let stepbystep s =  (
    while step s == Rc.ROW do
      let idavar = (
	Int64.to_int (of_int64_data (column s 0)),
	Int64.to_int (of_int64_data (column s 1)),
	(of_int64_data (column s 2)),
	(of_text_data (column s 3)),
	(of_int64_data (column s 4)),
	(of_int64_data (column s 5))
      ) in 
	vars := idavar :: !vars
    done
  ) in 
  let stmt = prepare db sql in
    stepbystep stmt;
    List.rev !vars

let get_idavars_by_id db file_id = 
  get_idavars_where db (Printf.sprintf "file_id = %d" file_id)

let get_idaimports_where db clause = 
  let sql = Printf.sprintf
    ("SELECT "^^
       "id,file_id,name,address"^^
       " from imports where %s;") clause in
  let imports = ref [] in 
  let stepbystep s =  (
    while step s == Rc.ROW do
      let idimp = (
	Int64.to_int (of_int64_data (column s 0)),
	Int64.to_int (of_int64_data (column s 1)),
	(of_text_data (column s 2)),
	(of_int64_data (column s 3))
      ) in 
	imports := idimp :: !imports
    done
  ) in 
  let stmt = prepare db sql in
    stepbystep stmt;
    List.rev !imports

let get_idaimports_by_id db file_id = 
  get_idaimports_where db (Printf.sprintf "file_id = %d" file_id)


