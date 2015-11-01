(**
 * Translate a binary to the IR. This handles idapro
 * databases and elf. It could be extended if there is enough desired
 *  to handle traces as well.
*)

open Vine_util;;
open Vine;;
open Vine_tovine;;
open Utils_common;;

module D = Debug.Make(struct let name = Sys.argv.(0) and default=`Debug end)
open D

module List = ExtList.List 
let version = "$Id: toir.ml 3326 2008-08-20 20:43:31Z aij $";;

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
	  let () = Vine_cfg.remove_unreachable cfg in 
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
    { info with name = List.hd strlist }
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
    (!total_x86, f (exe,exe#globals,[]) (List.tl worklist)) 
;;

let usage = "toir [options]* : translate to IR. Use ./toir -help for options." in
let infile = ref "" in
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
let speclist =  [
  ("-elf", 
   Arg.String (fun s -> trans_add (SetFile(Elf(s)))),
   "Set input source to be elf"
  );
  ("-ida",
   Arg.Tuple [Arg.Set_string(flag_idadb_file);
	      Arg.Int (fun i -> 
			 trans_add (SetFile(IdaDB(!flag_idadb_file,i))));
	     ],
   ("<idadb> <file_id> Process executable with file id <fileid>"^
      " in IDA database <idadb>.")
  );
  ("-range",
   Arg.Tuple([Arg.String(fun s -> start := s);
	      Arg.String(fun e -> 
			   let si = Int64.of_string !start in
			   let ei = Int64.of_string e in 
			     trans_add (TransRange(si,ei)));
	     ]),
   " <start,end> translate range <start,end>"
  );
  ("-fun",
   Arg.String (fun s -> trans_add (TransFun(s))),
   " <function> translate function named <function>"
  );
  ("-funaddr",
   Arg.String (fun s -> let i = Int64.of_string s in 
		 trans_add (TransFunBySAddr(i))),
   "<addr> translate function with start address <addr>"
  );
  ("-funanyaddr",
   Arg.String (fun s -> let i = Int64.of_string s in 
		 trans_add (TransFunByBAddr(i))),
   "<addr> translate function with any address <addr> in the function"
  );
  ("-all",
   Arg.Unit (fun () -> trans_add DoAll),
   " translate everything in current file"
  );
  ("-o",
   Arg.String (fun s -> outfile := open_out s),
   " <outfile> set output file (default is stdout)"
  );
  ("-nodescope",
   Arg.Clear(flag_descope),
     " Do not perform descoping. (Ignored when optimizations specified)"
  );
  ("-thunks",
   Arg.Set (flag_use_thunks),
   " use eflags thunks when translating (default is not to)"
  );
  ("-nocall",
   Arg.Clear (flag_use_calls),
   " do not use call/ret when translating (default is to use them)"
  );
  ("-stats",
   Arg.Set (flag_dostats),
   " print out translation stats"
  );
  ("-version",
   Arg.Unit (fun () -> print_version (); exit 0),
   " print version and exit"
  );
  ("-nosaveglobals",
   Arg.Clear(flag_save_globals),
   " Do not collect/restore globals in functions"
  );
] @ opts_speclist in
let starttime = Unix.gettimeofday () in 
let () = Arg.parse speclist arg_name usage in 
let () = (match !flag_translate with
       [] -> Printf.printf "%s\n%!" usage; exit(0)
     | _ -> ()
  ) in 
let () = Libasmir.set_use_eflags_thunks !flag_use_thunks in 
let () = Libasmir.set_call_return_translation !flag_use_calls in 
let (totalx86,(dl,sl)) = translate_files (List.rev !flag_translate) in
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
let ft = Format.formatter_of_out_channel (!outfile) in 
let pp = new Vine_pp.pp ft in 
  pp#format_program (dl,sl);
  print_stats ( (Unix.gettimeofday ()) -. starttime)
;;	
	
  (*   let () = if  not opts.descope &&  *)
  (*     (match opts.opts with [] -> false | _ -> true)  then ( *)
  (*       failwith "Optimizations require descoping" *)
  (*     ) else ()  *)
  (*   in *)
  (*     (\* translate and do optimizations in the order specified on the *)
  (*        command line *\) *)
  (*   let () = opts.translate <- List.rev opts.translate in *)
  (*   let () = opts.opts <- List.rev opts.opts in  *)
  (*   let () = Libasmir.set_use_eflags_thunks opts.usethunks in *)
  (*   let () = Libasmir.set_call_return_translation opts.usecalls in *)
  (*   let pp = output_string opts.outfile in  *)
  (*   let starttime = Unix.gettimeofday () in  *)
  (*   let exe = Vine_tovine.get_cmdline_exe () in *)
  (*   let () = if !doall then set_all_functions exe opts else () in *)
  (*   let ctx = new Vine_alphavary.var_renamer in  *)
  (*   let mem = newvar "globals" (TMem(addr_t,Little)) in  *)
  (*   let x86_globals = exe#globals in  *)
  (*   let globals = if opts.saveglobals then [mem] else x86_globals in  *)
  (*   let thunks = exe#thunks () in *)
  (*   let rewrite_globals p =  *)
  (*     if opts.saveglobals then  ([],x86_globals_to_args mem p) else p *)
  (*   in *)
  (*     ctx#init_ctx globals; *)
  (*     List.iter (fun x -> pp "var "; pp_var pp x; pp ";\n") globals; *)
  (*     pp_program pp (rewrite_globals (x86_globals,thunks)); *)
(*     List.iter (function *)
  (* 		   TransRange(s,e) -> ( *)
  (* 		     let sl = exe#tr_range s e in  *)
  (* 		     let (dl,sl) = rewrite_globals (x86_globals, sl) *)
  (* 		     in  *)
  (* 		     let (dl,sl) = do_common sl globals ctx opts.descope opts.opts *)
(* 		     in *)
  (* 		       pp_stmt pp (Block(dl,sl)) *)
  (* 		   ) *)
  (* 		 | TransFun(f) -> ( *)
  (* 		     let () = dprintf "Translating function %s" f in *)
  (* 		     let fi = exe#get_funinfo_by_name f in  *)
  (* 		     let sl = exe#tr_range fi.start_address fi.end_address  *)
(* 		     in *)
(* 		     let (dl,sl) = do_common sl globals ctx opts.descope opts.opts in  *)
(* 		     let f = (Function(fi.name, None, [], false, Some(Block(dl,sl))))  in *)
(* 		     let _,sl = rewrite_globals (x86_globals,[f]) in  *)

(* 		       List.iter (pp_stmt pp) sl  *)
(* 			 (\* Printf.printf "\n-------\n%!";  *)
(* 		       pp_program pp (x86_globals_to_args *)
(* 		   (globals,[f])) *\) *)
(* 		   ) *)
(* 	      ) opts.translate; *)

