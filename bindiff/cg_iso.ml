open Vine;;
open Mycg;;

let score_same_inst = 1.00;;
let score_same_stp = 0.85;;
(*let score_same_type = 0.7;;*)
let score_timeout = 0.5;;
let score_same_name = 0.0;;
(*let score_same_size = 0.05;;*)
let score_empty = 1.00;;
let score_diff = 0.0;;

let max_size_step = 0.001;;

let connectivity_factor1 = 0.1;;
let connectivity_factor2 = 0.8;;
let connectivity_factor3 = 0.6;;
let connectivity_factor4 = 0.2;;
let use_connectivity_factors = false;;

let init_max_size_ratio_cg = 0.999;;
let init_max_score_ratio_cg = 0.2;;

let timeout_length_cg1 = 1000.0;;
let timeout_length_cg2 = 1000.0;;

let timeout_count_cg1 = 10000;;
let timeout_count_cg2 = 10000;;

let skip_blk_diff_test_length = 50;;
let skip_init_d_filter = 50;;

let extendable_count_score = false;;

let bad_vertex_id = -1;;

exception ISO_TIMEOUT1;;


type id_pos_t = Id_first | Id_second;;


let get_max_score max_size max_score_ratio =
  float_of_int(max_size) *. max_score_ratio *. score_same_inst
;;


let id_exist id tbl pos =
  Hashtbl.fold (fun (id1, id2) score acc ->
    if pos = Id_first 
    then 
      (
      if id1 = id 
      then (true, id2, score) 
      else acc
      )
    else 
      (
      if id2 = id 
      then (true, id1, score) 
      else acc
      )
    ) tbl (false, bad_vertex_id, 0.0)
;;


let isomorphism g1 g2 g1_size init_matched score max_size_ratio1 max_score_ratio1 to_length to_count debug_ch debug_flag =
  let global_result = ref (Hashtbl.create 0) in
  let max_size1 = int_of_float(max_size_ratio1 *. float_of_int(g1_size)) in
  let max_score1 = get_max_score max_size1 max_score_ratio1 in
  let max_size2 = ref 0 in
  let max_score2 = ref 0.0 in


  let print_matched matched =
    Printf.fprintf debug_ch "---printing matched\n";
    Hashtbl.iter (fun (id1, id2) b -> 
      Printf.fprintf debug_ch "(%d,%d)%f\n" id1 id2 b
      ) matched;
    Printf.fprintf debug_ch "---\n\n"
  in


  let print_d d =
    Printf.fprintf debug_ch "---printing d\n";
    Hashtbl.iter (fun a b ->
      Printf.fprintf debug_ch "%d: " a;
      List.iter (fun (id, score) -> 
        if score = 0.0
        then Printf.fprintf debug_ch "%d," id
        else Printf.fprintf debug_ch "(%d,%f)" id score
        ) b;
      Printf.fprintf debug_ch "\n"
      ) d;
    Printf.fprintf debug_ch "---\n\n"
  in  


  let get_score id1 id2 score =
    try
      Hashtbl.find score (id1, id2)
    with
      Not_found -> (*Printf.eprintf "cannot find (%d,%d) in score\n" id1 id2;*) 0.0
  in


  let weighted_score vid1 vid2 score =
   if use_connectivity_factors then (
    let v1 = Hashtbl.find g1.v_tbl vid1 in
    let v2 = Hashtbl.find g2.v_tbl vid2 in
    let pred1 = List.length (pred g1 v1) in (*pred returns a vertex List*)
    let succ1 = List.length (succ g1 v1) in
    let pred2 = List.length (pred g2 v2) in
    let succ2 = List.length (succ g2 v2) in
    let mul = float_of_int ((min pred1 pred2) + (min succ1 succ2)) in
    if score > 0.0
    then
      (
      if mul > 0.0
      then score *. (mul ** connectivity_factor1)
      else score *. connectivity_factor2
      )
    else
      connectivity_factor3 ** (1.0 /. mul) *. connectivity_factor4
   )
   else score
  in



   let init_d matched = 
    let possible = Hashtbl.fold (fun id blk acc ->
      if id <> bad_vertex_id
      then (
        let (test_exist, test_id, test_score) = 
          id_exist id matched Id_second 
        in
        if test_exist 
        then acc
        else id :: acc
      ) else acc
    ) g2.v_tbl []
    in
    let ret1 = Hashtbl.create (Hashtbl.length g1.v_tbl - 5) in
    let ret2 = Hashtbl.create (Hashtbl.length g1.v_tbl - 5) in
    Hashtbl.iter (fun id blk ->
      if id <> bad_vertex_id
      then (
        let (test_exist, test_id, test_score) = id_exist id matched Id_first in
        if (not test_exist) 
        then 
          (
          let candidates = List.map (fun x -> 
            (x, (get_score id x score))
            ) possible 
          in
          let candidates_filtered = if g1_size > skip_init_d_filter
            then 
              (
              List.filter (fun (y1, y2) ->
                y2 > 0.0
                ) candidates
              )
            else candidates
          in
          let candidates_sorted = 
            if candidates_filtered = [] 
            then candidates
            else
              (
              List.sort (fun (x1, x2) (y1, y2) ->
                if x2 > y2
                then -1
                else
                  (
                  if x2 = y2 
                  then 0 
                  else 1
                  )
                ) candidates_filtered
              )
          in
          let candidates_weighted_sorted = 
            if candidates_filtered = [] 
            then candidates
            else
              (
              let candidates_weighted = List.map (fun (x, y) ->
                (x, weighted_score (Hashtbl.find g1.v_rev_tbl blk) x y)
                ) candidates_filtered in
              List.sort (fun (x1, x2) (y1, y2) ->
                if x2 > y2
                then -1
                else
                  (
                  if x2 = y2 
                  then 0 
                  else 1
                  )
                ) candidates_weighted
              )
          in
          Hashtbl.add ret1 id candidates_sorted;
          Hashtbl.add ret2 id candidates_weighted_sorted
          )
        else 
          (
          Hashtbl.add ret1 id [(test_id, test_score)];
          Hashtbl.add ret2 id [(test_id, test_score)]
          )
      ) 
      ) g1.v_tbl; 
    print_d ret1;
    print_d ret2;
    Printf.fprintf debug_ch "init_size: %d, init_score: %f\n" 
      max_size1 max_score1; 
    ret2
  in


  let get_highest_score id d =
    let candidate = Hashtbl.find d id in
    match candidate with
      | [] -> (bad_vertex_id, 0.0)
      | head :: tail -> head
  in


  let extendable d matched =
    let d_size = Hashtbl.length d in
    let matched_size = Hashtbl.length matched in
    let (local_max1, local_max2) = Hashtbl.fold (fun id blk (acc1, acc2) ->
      if id <> bad_vertex_id 
      then (
        let (test_exist, id1, score1) = id_exist id matched Id_first in
        if test_exist 
        then (acc1 +. score1, acc2)
        else 
        (
          let (id2, score2) = 
            try get_highest_score id d 
            with Not_found -> (bad_vertex_id, 0.0)
          in
          (acc1, acc2 +. score2)
        )
      ) else (acc1,acc2)
    ) g1.v_tbl (0.0, 0.0)
    in
    if extendable_count_score
    then
      (
      if local_max1 > !max_score2 && matched_size > !max_size2 
      then
        (
        global_result := matched;
        max_size2 := matched_size;
        max_score2 := local_max1;
        d_size > 0
        )
      else d_size > 0 && d_size + matched_size > max_size1 && 
        (local_max1 +. local_max2) > max_score1
      )
    else
      (
      if matched_size >= !max_size2
      then
        (
        if local_max1 > !max_score2
        then
          (
          global_result := matched;
          max_size2 := matched_size;
          max_score2 := local_max1;
          d_size > 0
          )
        else d_size > 0
        )
      else d_size > 0 && d_size + matched_size > max_size1
      )
  in


  let pick_any2 d matched =
    let rec count_candidate c =
      match c with
        | (id, score) :: tail ->
            (
            if score = 0.0
            then (0.0, 1 + List.length tail)
            else
              (
              let (t_score, t_count) = count_candidate tail in
              if score = t_score
              then (t_score, t_count + 1)
              else (score, 1)
              )
            )
        | [] -> (0.0, 0)
    in

    let (v, _, _) = Hashtbl.fold (fun id candidates (id1, score1, count1) ->
      let (score2, count2) = count_candidate candidates in
      if count2 < count1 
      then (id, score2, count2)
      else
        (
        if count2 = count1 
        then
          (
          if score2 > score1 
          then (id, score2, count2)
          else (id1, score1, count1)
          )
        else (id1, score1, count1)
        )
      ) d (bad_vertex_id, 0.0, 99999)
    in
    v
  in


(*  let pick_any1 d matched =
    let (v, _, _) = Hashtbl.fold (fun id2 candidates (id1, count1, max1) ->
      let count2 = List.length candidates in
      let max2 = 
        match candidates with
          | [] -> 0.0
          | (id3, score3) :: _ -> score3
      in
      if count2 > 0 && (count2 < count1 || (count2 = count1 && max2 > max1))
      then (id2, count2, max2)
      else (id1, count1, max1)
      ) d (BB(0), 99999, 0.0) 
    in
    v
  in
*)

  let redefine d new1 new2 =
    let pred1 = pred g1 (Hashtbl.find g1.v_tbl new1) in
    let succ1 = succ g1 (Hashtbl.find g1.v_tbl new1) in
    let pred2 = pred g2 (Hashtbl.find g2.v_tbl new2) in
    let succ2 = succ g2 (Hashtbl.find g2.v_tbl new2) in
    let d1 = Hashtbl.create (Hashtbl.length d - 1) in    
    Hashtbl.iter (fun id1 candidates ->
      if id1 <> new1
      then
        (
        let candidates_filtered = List.filter (fun (id2, id_score) ->
          (id2 <> new2) && 
          ((List.exists (fun test1 -> (Hashtbl.find g1.v_rev_tbl test1) = id1) pred1) = 
          (List.exists (fun test2 -> (Hashtbl.find g2.v_rev_tbl test2) = id2) pred2)) && 
          ((List.exists (fun test3 -> (Hashtbl.find g1.v_rev_tbl test3) = id1) succ1) = 
          (List.exists (fun test4 -> (Hashtbl.find g2.v_rev_tbl test4) = id2) succ2))
          ) candidates
        in
        if not (candidates_filtered = [])
        then Hashtbl.add d1 id1 candidates_filtered
        )
      ) d; 
    d1
  in    


  let rec iso d matched to_start to_c1=
    let to_c2 = ref (to_c1 + 1) in
    let to_end = Sys.time () in
    let () = if (to_end -. to_start) > to_length
    then
      (
      Printf.printf "timeout(%f - %f > %f): init_size=%d ret_size=%d\n" 
        to_end to_start to_length max_size1 !max_size2;
      Printf.fprintf debug_ch 
        "timeout(%f - %f > %f): init_size=%d ret_size=%d\n" to_end to_start 
        to_length max_size1 !max_size2;
      raise ISO_TIMEOUT1
      )
    in
    let () = if extendable d matched
    then 
      (
      let v = pick_any2 d matched in
      if v <> bad_vertex_id
      then
        (
        let () = if debug_flag then Printf.fprintf debug_ch 
          "picking %d\n" v in
        let z = Hashtbl.find d v in
        let () = List.iter (fun (id, id_score) ->
          let matched1 = Hashtbl.copy matched in
          let () = Hashtbl.add matched1 (v, id) id_score in
          let () = 
            if debug_flag 
            then Printf.fprintf debug_ch "[%d] adding (%d, %d) to matched\n" 
              !to_c2 v id
          in
          let d1 = redefine d v id in
          let () = 
            if debug_flag 
            then print_matched matched1 
          in
(*
          let () = 
            if debug_flag 
            then print_d d1
          in
*)
          let (_, to_c3) = iso d1 matched1 to_start !to_c2 in 
          to_c2 := to_c3
          ) z
        in
        let matched2 = Hashtbl.copy matched in
        let d2 = Hashtbl.copy d in
        let () = Hashtbl.remove d2 v in
        let () = 
          if debug_flag 
          then Printf.fprintf debug_ch "[%d] removing %d from d\n" !to_c2 v
        in
        let () = 
          if debug_flag 
          then print_matched matched2 
        in
(*
        let () = 
          if debug_flag 
          then print_d d2 
        in
*)
        let (_, to_c3) = iso d2 matched2 to_start !to_c2 in 
        to_c2 := to_c3
        )
      )
    in
    let () = if !to_c2 > to_count
    then
      (
      Printf.printf "timeout(%d > %d): init_size=%d ret_size=%d\n" !to_c2 
        to_count max_size1 !max_size2;
      Printf.fprintf debug_ch 
        "timeout(%d > %d): init_size=%d ret_size=%d\n" !to_c2 to_count 
        max_size1 !max_size2;
      raise ISO_TIMEOUT1
      )
    in
    (true, !to_c2)
  in


  let () = print_matched init_matched in
  let d = init_d init_matched in
  let to_start = Sys.time () in
  let (ret_condition, _) = 
    try iso d (Hashtbl.create 0) to_start 0
    with 
      | ISO_TIMEOUT1 -> (false, 0)
      | x -> 
          (
          Printf.printf "%s\n" (Printexc.to_string x); 
          Printf.fprintf debug_ch "%s\n" (Printexc.to_string x); 
          (false, 0)
          )
  in
  print_matched !global_result;
  (ret_condition, !max_size2, !max_score2, !global_result)
;;


let rec isomorphism_accurate g1 g2 g1_size matched score max_size_ratio1 max_score_ratio1 to_length1 to_length2 to_count1 to_count2 debug_ch debug_flag =
  let (ret1, max_size1, max_score1, result1) = 
    isomorphism g1 g2 g1_size matched score max_size_ratio1 max_score_ratio1 
    to_length1 to_count1 debug_ch debug_flag 
  in
  if ret1
  then
  (
    if max_size1 > 0
    then 
      (
      Printf.printf "\ndone isomorphism\n\n";
      Printf.fprintf debug_ch "\ndone isomorphism\n\n";
      (ret1, max_size1, max_score1, result1)
      )
    else 
      (
      Printf.printf "\nretrying isomorphism\n\n";
      Printf.fprintf debug_ch "\nretrying isomorphism\n\n";
      isomorphism_accurate g1 g2 g1_size matched score 
        (max_size_ratio1 -. max_size_step) max_score_ratio1 to_length1 
        to_length2 to_count1 to_count2 debug_ch debug_flag
      )
  )
  else 
    (
    Printf.printf "\n2nd round of isomorphism\n\n";
    Printf.fprintf debug_ch "\n2nd round of isomorphism\n\n";
    isomorphism g1 g2 g1_size result1 score 0.0 0.0 to_length2 to_count2 
      debug_ch debug_flag
    )
;;
