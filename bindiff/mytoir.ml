

open Vine_util;;
open Vine;;
open Vine_tovine;;
open Utils_common;;

module D = Debug.Make(struct let name = "toir" and default=`Debug end)
open D

module List = ExtList.List 
let version = "$Id: toir.ml 2732 2008-01-26 20:42:06Z dbrumley $";;

(* statistics *)
let total_x86 = ref 0L;;
let total_irstmts = ref 0L;;
let final_irstmts = ref 0L;;
let flag_dostats = ref false;;

type transaction = 
    TransRange of int64 * int64
  | TransFun of string
  | TransFunBySAddr of int64
  | TransFunByBAddr of int64
  | SetFile of exeType
  | DoAll 
;;



let print_stats  time = 
  if !flag_dostats then (
    let diff = Int64.sub !total_irstmts !final_irstmts in 
      Printf.printf "Total time: %f sec\n%!" time;
      Printf.printf "Total x86 instructions translated: %Ld\n%!"
	!total_x86;
      Printf.printf "Total IR executable stmts translated: %Ld\n%!" 
	!total_irstmts;
      Printf.printf 
	"Final IR executable stmts: %Ld (%Ld difference = %f percent)\n%!" 
	!final_irstmts diff 
	((Int64.to_float diff /. Int64.to_float !total_irstmts) *. 100.0);
      Printf.printf "Total blowup from x86 -> IR: %f percent\n%!"
	((Int64.to_float !final_irstmts /. Int64.to_float !total_x86)*.100.0)
  ) else ()
;;




let optimize (dl,sl)  = function
    [] -> (dl,sl)
  | _ as opts -> 
      let optimize_one prog = 
	let cfg = Vine_cfg.prog_to_cfg prog in 
	  let () = Vine_cfg.remove_unreachable  ~from:Vine_cfg.BB_Entry cfg in 
	    if Vine_cfg.well_defined cfg then 
	      Vine_cfg.normal_cfg_to_prog (optimize_cfg cfg dl opts)
	    else (  
  	      wprintf ("Skipping optimizations due to non-well-formed CFG."); 
	      prog
	    )
      in
      let funcs,rest = 
	List.partition (function Function _ -> true | _ -> false)  sl 
      in
      let (_,rest) = optimize_one (dl,rest) in 
      let funcs = List.map 
	(function Function(a,b,c,d,Some(Block(dl,sl))) ->
	   let dl',sl' = optimize_one (dl,sl) in 
	     Function(a,b,c,d,Some(Block(dl',sl')))
	   | _ as a -> a) funcs in 
	(dl,funcs @rest)
;;

let normalize_info_name info = 
  let copy_str_from str i =
    String.sub str i (String.length str - i)
  in
  let method_name = 
    try 
      let regex = Str.regexp "::" in 
      let i = Str.search_forward regex info.name 0 in 
      let i = i + 2 in 
	String.sub info.name i (String.length info.name - i)
    with
	Not_found -> info.name 
  in
  let regex = Str.regexp "[@|(|)\\.]" in
  let strlist = Str.split regex method_name in 
    { name = List.hd strlist;
      start_address = info.start_address;
      end_address = info.end_address;
      is_extern = info.is_extern;
			tails=[];
    }
;;


let translate_files worklist = 
  let total_x86 = ref 0L in 
  let exe = (match worklist with
      [] -> failwith "no exe specified."
     | SetFile((Elf _) as a)::ys -> new exe a
     | SetFile((IdaDB _) as a)::ys -> new exe a
     | _ -> failwith ("must specify executable before ranges or"^
			" functions to translate")
  ) in
  let rec f ((exe:Vine_tovine.exe),(dl:decl list),(sl:stmt list list)) lst = 
    match lst with
	[] -> (dl,List.flatten (List.rev sl))
      | TransRange(i,j)::ys -> 
	  f (exe,dl,(exe#tr_range i j)::sl) ys
      | TransFun(name)::ys ->
	  let info = exe#get_funinfo_by_name name in 
	  let info = normalize_info_name info in 
	    f (exe,dl,[(exe#tr_function info)]::sl) ys
      | TransFunBySAddr(a)::ys ->
	  let info = exe#get_funinfo_by_start_address a in 
	  let info = normalize_info_name info in 
	    f (exe,dl,[(exe#tr_function info)]::sl) ys
      | TransFunByBAddr(a)::ys ->
	  let info = exe#get_funinfo_by_any_address a in 
	  let info = normalize_info_name info in 
	    f (exe,dl,[(exe#tr_function info)]::sl) ys
      | SetFile(typ)::ys ->
	  let () = total_x86 := Int64.add !total_x86 exe#x86translated  
	  in 
	  let exe = new exe typ in 
	    f (exe,(Vine_util.list_union dl (exe#globals)), sl) ys
      | DoAll::ys ->
	  let rest = List.map (fun i -> TransFun(i.name)) exe#get_funinfos in
	    f (exe,dl,sl) (rest @ ys)
  in
    (!total_x86, f (exe,exe#globals,[]) (List.tl worklist), exe#get_funinfos) 
;;

let translateFromElf fileName =

let usage = "toir [options]* : translate to IR. Use ./toir -help for options." in
let infile = ref "1" in
let infile_set = ref false in 
let flag_idadb_file = ref "" in 
let flag_use_thunks = ref false in 
let flag_use_calls = ref true in 
let flag_descope = ref true in 
let flag_save_globals = ref true in 
let outfile = ref stdout in 
let flag_translate = ref [] in 
let trans_add item = flag_translate := item :: !flag_translate in
let arg_name s = infile := s; infile_set := true in
let print_version () = 
  Printf.printf "Version: %s\n%!" version
in
let start = ref "" in


 
let () = trans_add (SetFile(IdaDB(fileName,1))) in
let () = trans_add DoAll in

let () = opt_flags := "default" :: !opt_flags in

(*
let translateFromIda fileName fileID
	let () = trans_add (SetFile(IdaDB(fileName,fileID)))
	let () = trans_add DoAll in
*)



let starttime = Unix.gettimeofday () in 

(*let () = Arg.parse speclist arg_name usage in *)



let () = (match !flag_translate with
       [] -> Printf.printf "%s\n%!" usage; exit(0)
     | _ -> ()
  ) in 
let () = Libasmir.set_use_eflags_thunks !flag_use_thunks in 
let () = Libasmir.set_call_return_translation !flag_use_calls in 
let (totalx86,(dl,sl),finfo_l) = translate_files (List.rev !flag_translate) in
let () = total_irstmts := if !flag_dostats then count_stmts sl else 0L in 
let (dl,sl) = 
  if !flag_save_globals then 
    let mem = newvar "globals" (TMem(addr_t,Little)) in 
      ([mem],x86_globals_to_args mem (dl,sl))
  else
    (dl,sl)
in
let (dl,sl) = 
  if !flag_descope then Vine_alphavary.descope_program (dl,sl) 
  else (dl,sl) 
in 
let (dl, sl) = optimize (dl,sl) !opt_flags in
let () = final_irstmts := if !flag_dostats then count_stmts sl else 0L in  
(*let ft = Format.formatter_of_out_channel (!outfile) in 
let pp = new Vine_pp.pp ft in 
  pp#format_program (dl,sl);
  print_stats ( (Unix.gettimeofday ()) -. starttime)*)
 (dl, sl, finfo_l)
;;	


