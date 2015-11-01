open Vine;;

exception EARLY_TERMINATE;;


let debug_flag = true;;(*peng*)

let diagonal_optimization = true;;(*peng*)
let num_stp_queries = ref 0;;
let num_testv_calls = ref 0;;

(*
let rec typ_to_string t =
  match t with
    | REG_1 -> "REG_1"
    | REG_8 -> "REG_8"
    | REG_16 -> "REG_16"
    | REG_32 -> "REG_32"
    | REG_64 -> "REG_64"
    | TString -> "TString"
    | Array(a,b) -> 
        "Array(" ^ (typ_to_string a) ^ ", " ^ (Int64.to_string b) ^ ")"
    | TAttr(c,d) -> "TAttr(" ^ (typ_to_string c) ^ ", " ^ 
        (List.fold_left (fun acc s -> acc ^ ";" ^ s) "" d) ^ ")"
;;


let lvalue_to_string l =
  match l with
    | Temp (v) -> "Temp(n=" ^ n ^ ")"
    | Mem (v, e, t) -> "Mem(n=" ^ n ^ ", e=" ^ (exp_to_string e) ^ ", e=" ^ 
        (typ_to_string t) ^ ")"
;;
*)

let stp_test p1 p2 b1 b2 debug_ch =
  let print_post post1 post2 =
    if debug_flag then Printf.fprintf debug_ch "\tprinting post: ";
    if debug_flag then Printf.fprintf debug_ch "p1=%s p2=%s\n" (lval_to_string post1) (lval_to_string post2);
    flush debug_ch 
  in


  let lvalue_same_type l1 l2 =
    let typ1 = match l1 with
      | Temp ((i,s,t)) -> t
      | Mem ((i,s,t1), e, t2) -> t2
    in
    let typ2 = match l2 with
      | Temp ((i,s,t)) -> t
      | Mem ((i,s,t1), e, t2) -> t2
    in
    typ1 = typ2
  in


  let get_wp blk post = 
    let gcl = Gcl.of_straightline blk in
    let simp = (fun x->x) in
    Wp.calculate_wp simp post gcl
  in


  let () = if debug_flag
    then 
      (
      print_post p1 p2
      )
  in
  let ret = if (lvalue_same_type p1 p2)
    then
      (
      let wp1 = get_wp b1 (Lval p1) in
      let wp2 = get_wp b2 (Lval p2) in
      let ctx1 = get_req_ctx wp1 in
      let ctx2 = get_req_ctx wp2 in

      (*let () = Printf.fprintf debug_ch "\tctx1=\n" in
      let () = List.iter (fun d ->
		Printf.fprintf debug_ch "\t\t%s\n"(decl_to_string d)
	) ctx1 in
      let () = Printf.fprintf debug_ch "\tctx2=\n" in
      let () = List.iter (fun d ->
		Printf.fprintf debug_ch "\t\t%s\n"(decl_to_string d)
	) ctx2 in
      let () = flush debug_ch  in*)

      let vc = Stpvc.create_validity_checker () in
      let stp_wp1 = 
        Vine_stpvc.vine_to_stp vc (Vine_stpvc.new_ctx vc ctx1) wp1 
      in
      let stp_wp2 = 
        Vine_stpvc.vine_to_stp vc (Vine_stpvc.new_ctx vc ctx2) wp2 
      in
      let () = num_stp_queries := !num_stp_queries + 1  in
      (*let () = Printf.printf "before stpvc.query--\n" in*)
      Stpvc.query vc (Stpvc.e_eq vc stp_wp1 stp_wp2) 
      )
    else false  

  in
  if debug_flag
  then 
    (
    Printf.fprintf debug_ch "\tstp: ";
    if ret
    then Printf.fprintf debug_ch "true\n"
    else Printf.fprintf debug_ch "false\n"
    )
  ; ret
;;


let test_v v v_size debug_ch =
  let rec test_v_aux v1 r1 =
    let () = if debug_flag
      then
        (
        Printf.fprintf debug_ch "printing v\n";
        for i = 0 to v_size - 1
        do
          (
          for j = 0 to v_size - 1
          do
            (
            if v1.(i).(j)
            then Printf.fprintf debug_ch "1,"
            else Printf.fprintf debug_ch "0,"
            )
          done;
          Printf.fprintf debug_ch "\n"
          )
        done
        ;
				
        Printf.fprintf debug_ch "printing r\n";
        List.iter (fun x ->
          Printf.fprintf debug_ch "%d, " x
          ) r1
        ;
        Printf.fprintf debug_ch "\n"
        )
    in
		
		
    let r_size = List.length r1 in
    if r_size = v_size (*pm: Exit condition*)
    then 
      (
      let () = if debug_flag
        then
          (
          Printf.fprintf debug_ch "found solution:\n";
          List.iter (fun x ->
            Printf.fprintf debug_ch "%d, " x
            ) r1
          ;
          Printf.fprintf debug_ch "\n\n"
          )
      in
      true
      )
    else
      (
      let candidates = ref [] in
      for i = 0 to v_size - 1
      do
        (
        if v1.(r_size).(i)
        then
          (
          let v2 = Array.make_matrix v_size v_size false in
          for j = 0 to v_size - 1
          do
            (
            for k = 0 to v_size - 1
            do
              (
              if k <> i
              then v2.(j).(k) <- v1.(j).(k)
              )
            done
            )
          done;
          candidates := (v2, i :: r1) :: !candidates(*pm: increase r. *)
          )
        )
      done;
      List.fold_left (fun acc (v3, r3) ->
        acc || test_v_aux v3 r3
        ) false !candidates
      )
  in


  let () = if debug_flag
    then Printf.fprintf debug_ch "start testing v\n\n"
  in
  test_v_aux v []
;;


let test_blk post1 post2 post_size b1 b2 debug_ch =
  let () = if debug_flag
    then 
      (
      Printf.fprintf debug_ch "post_length: %d\n\n" post_size;
      Printf.fprintf debug_ch "printing post1:\n";
      List.iter (fun x ->
        Printf.fprintf debug_ch "%s\n" (lval_to_string x)
        ) post1
      ;
      Printf.fprintf debug_ch "\nprinting post2:\n";
      List.iter (fun x ->
        Printf.fprintf debug_ch "%s\n" (lval_to_string x)
        ) post2
      ;
      Printf.fprintf debug_ch "\n"
      )
  in
  let v = Array.make_matrix post_size post_size true in

  let () = if debug_flag
    then Printf.fprintf debug_ch "beginning calling stp_test for optimized post pairs:\n\n"
  in

  let simple_test3 = if diagonal_optimization then (
	List.fold_left2 (fun acc p1 p2 ->
        	let result = stp_test p1 p2 b1 b2 debug_ch in
        	let () = if debug_flag then Printf.fprintf debug_ch "called Optimized stp_test, result=%b\n\n" result in 
		let () = flush debug_ch in
        	acc && result;
  	) true post1 post2
  ) else false
  in

  if simple_test3
  then (   if debug_flag then Printf.fprintf debug_ch "simple_test3 succeeded\n"; flush debug_ch; (true,true))
  else (
	if debug_flag then Printf.fprintf debug_ch "simple_test3 FAILED!\n"; flush debug_ch;

  	 let () = if debug_flag
	    then Printf.fprintf debug_ch "beginning calling stp_test for different post pairs:\n\n"
	  in
	  let simple_test1 = ref false in
	  let simple_test2 = ref true in
	  let _ = try List.fold_left (fun acc1 p1 ->
	      let () = (simple_test1 := false) in
	      let _ = List.fold_left (fun acc2 p2 ->
	        let result = stp_test p1 p2 b1 b2 debug_ch in
	        if debug_flag then Printf.fprintf debug_ch "called stp_test, result=%b\n\n" result; 
		flush debug_ch;
	        simple_test1 := !simple_test1 || result;
	        v.(acc1).(acc2) <- result;
	        acc2 + 1
	        ) 0 post2
	      in 
	      if !simple_test1
	      then (   if debug_flag then Printf.fprintf debug_ch "simple_test1 succeeded\n"; flush debug_ch; acc1 + 1)
	      else (if debug_flag then Printf.fprintf debug_ch "simple_test1 FAILED!\n"; flush debug_ch; raise EARLY_TERMINATE )
	      ) 0 post1
	    with 
	      | EARLY_TERMINATE -> (
	  	  if debug_flag then Printf.fprintf debug_ch "EARLY_TERMINATE!\n"; flush debug_ch;
	          simple_test2 := false;
	          0
	          )
	  in
	  if !simple_test2
	  then (
	      let () = num_testv_calls := !num_testv_calls + 1  in
(*	      let r = test_v v post_size debug_ch in flush debug_ch; 
	     (r, false)*) (*MJ*)
		(true, false)
	  )
	  else 
	  (
	    let () = if debug_flag then (if debug_flag then Printf.fprintf debug_ch "skip testing v\n"; flush debug_ch) in
	   (false, false)
	  )
  )
;;


let main argc argv = 
(
  let () = output_string stdout "ready\n" in
  let () = flush stdout in
  let (post1, post2, post_size, b1, b2, debug_file) = 
    (Marshal.from_channel stdin : lvalue list * lvalue list * int * 
      stmt list * stmt list * string )
  in
  let debug_descr = Unix.openfile debug_file 
    [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_APPEND] 0o644 in
  let debug_ch = Unix.out_channel_of_descr debug_descr in
  let () = set_binary_mode_out debug_ch false in
  let () = Printf.fprintf debug_ch "pid: %d\nrequest received\n" 
    (Unix.getpid ())in
  let () = flush debug_ch in
	(*let () = Printf.fprintf debug_ch "before test_blk sending result, b1=%s, b2=%s\n" (b1) (b2) in
  let () = flush debug_ch in*)
 
	let (ret, quick_ret) = test_blk post1 post2 post_size b1 b2 debug_ch in(*pm*)
	let (ret, quick_ret) = (false, false) in
	
  (*let () = Printf.fprintf debug_ch "after test_blk sending result, b1=%s, b2=%s\n" (b1) (b2) in
  let () = flush debug_ch in*)
  let () = Marshal.to_channel stdout (!num_stp_queries,!num_testv_calls,ret,quick_ret) [] in

  let () = flush stdout in

  let () = Printf.fprintf debug_ch "result sent\n" in
  (*let () = Printf.fprintf debug_ch "%s\n" (input_line stdin) in*)
  let () = flush debug_ch in
  Unix.close debug_descr
)
in
main (Array.length Sys.argv) Sys.argv
