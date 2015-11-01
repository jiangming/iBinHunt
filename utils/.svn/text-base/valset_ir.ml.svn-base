module VS = Valset
module V = Vine

type cmdlineargs_t = {
  mutable irin_file : string;
  mutable tmp_name : string;
  mutable get_val_bounds : bool;
  mutable low_bound_to : float;
  mutable sample_pts : int;
  mutable stp_file : string;
  mutable ps_file : string;
} ;;

(* XXX cut-and paste. should put similar functionality into
   main vine library.
*)
let gamma_of_prog prog = 
  let ds = Exectrace.varset_of_prog prog in
  Exectrace.gamma_of_varset (Asmir.x86_mem) ds

let range_size (s, e) =
  Int64.succ (Int64.sub e s)

let ranges_size ranges =
  List.fold_left
    (fun sum range -> Int64.add sum (range_size range))

(* let ranges_invert ranges = *)
(*   let rec foo inverted prev_end ranges =  *)
(*     match ranges with *)
(*     | (a, b) :: tl -> *)
(*         let new_rng = Int64.succ prev_end, Int64.pred a in *)
(*         foo (new_rng::inverted) b tl *)
(*     | [] ->  *)
(*         inverted, prev_end *)
(*   in *)
(*   let (first_start, first_end) = List.hd ranges in *)
(*   let inverted, last_end = foo [] first_end (List.tl ranges) in *)
    

let parse_cmdline =
  let cmdlineargs = {
    irin_file = "";
    tmp_name = "";
    get_val_bounds = true;
    low_bound_to = 6.0;
    sample_pts = 20;
    stp_file = "";
    ps_file = "";
  } in
  
  let arg_spec = 
    [
      ("-ir-in", 
       Arg.String (fun s -> cmdlineargs.irin_file <- s),
       "FILE  \tread ir trace from FILE") ;

      ("-tmp-name", 
       Arg.String (fun s -> cmdlineargs.tmp_name <- s),
       "NAME  \tname of Temp to be queried") ;

      ("-get-val-bounds",
       Arg.Bool (fun b -> cmdlineargs.get_val_bounds <- b),
       "BOOL  \tUse binary search to find upper and lower bound");

      ("-low-bound-to",
       Arg.Float (fun f -> cmdlineargs.low_bound_to <- f),
       "N  \tEstablish low influence bound of N bits");

      ("-sample-pts",
       Arg.Int (fun f -> cmdlineargs.sample_pts <- f),
       "N  \tEstimate density of UNKNOWN regions with N samples");

      ("-stp-file", 
       Arg.String (fun s -> cmdlineargs.stp_file <- s),
       "FILE  \t print STP to FILE") ;

      ("-ps-file", 
       Arg.String (fun s -> cmdlineargs.ps_file <- s),
       "FILE  \t draw valset to FILE") ;

    (*      ("-ranges", *)
    (*       Arg.Unit (fun () -> cmdlineargs.do_ranges <- true), *)
    (*       "\tFind ranges that satisfy post-condition"); *)
    ]
  in
  let () = 
    Arg.parse 
      arg_spec 
      (fun s -> ()) 
      "Usage: influence" 
  in
  cmdlineargs
;;

let strip_varnums (dl,sl) =
  let rename_var (i,s,t) =
    let suffix_pos = String.rindex s '_' in
    let s' = String.sub s 0 suffix_pos in
    (i,s',t)
  in
  let rename_lval lv =
    match lv with
    | V.Temp(v) -> V.Temp(rename_var v)
    | V.Mem(v,e,t) -> V.Mem(rename_var v,e,t)
  in

  let vis =
object
  inherit V.nop_vine_visitor
  method visit_decl d =
    V.ChangeTo(rename_var d)
  method visit_alvalue lv =
    V.ChangeDoChildrenPost(rename_lval lv, Vine_util.id)
  method visit_rlvalue lv =
    V.ChangeDoChildrenPost(rename_lval lv, Vine_util.id)
  method visit_binding (lv,e) =
    failwith "FIXME: visit_binding unimplemented"
end
  in
  let dl = List.map rename_var dl in
  let sl = List.map (V.stmt_accept vis) sl in
  (dl, sl)
;;

if not !Sys.interactive then (
  let clean_exit i =
    Printf.printf "Caught signal %d, exiting\n" i;
    exit 1
  in
  Sys.set_signal Sys.sigint (Sys.Signal_handle(clean_exit));

  (* parse parse parse *)
  let args = parse_cmdline in
  Vine_parser.flag_track_lines := false;
  let prog = Vine_parser.parse_file args.irin_file in
  Vine_typecheck.typecheck prog;

  (* find the variable-of-interest by name *)
  let gamma = gamma_of_prog prog in
  let tmp_var = Asmir.gamma_lookup gamma args.tmp_name in
  let expr = V.Lval(V.Temp(tmp_var)) in

  (* redirect stp output *)
  if args.stp_file <> "" then
    VS.redirect_stp_to args.stp_file;

  (* initialization *)
  let vs, stp = VS.prog_to_valset prog expr in

  (* will add onto this function to give final summary *)
  let summarize = fun () -> Printf.printf "\n\nSummary:\n" in

  (* follow options to progressively fill in valset info,
     and provide other estimates *)
  let vs, summarize = 
    if args.get_val_bounds then
      let vs = VS.establish_valset_bounds stp vs in
      let summarize = 
        fun () ->
          summarize ();
          let lo_v, hi_v = VS.lh_bounds_of_valset vs in
          Printf.printf 
            "Lowest and highest possible values: 0x%Lx to 0x%Lx\n"
            lo_v hi_v;
          let lo, hi = VS.influence_bounds_of_valset vs in
          Printf.printf 
            "Influence bounds after establishing value bounds: %f to %f\n"
            lo hi
      in
      vs, summarize
    else
      vs, summarize
  in

  let vs, summarize = 
    if args.low_bound_to >= 1.0 then
      let vs = 
        VS.find_up_to_n_samples stp vs (Int64.of_float
                                          (2.0**args.low_bound_to))
      in
      let summarize = 
        fun () ->
          summarize ();
          let lo, hi = VS.influence_bounds_of_valset vs in
          Printf.printf 
            "Influence bounds after asking for counterexamples: %f to %f\n"
            lo hi
      in
      vs, summarize
    else
      vs, summarize
  in

  let summarize, unknown_frac = 
    if args.sample_pts > 0 then (
      let inf_est, sat_ct, sample_ct, unk_ct =
        VS.probable_influence stp vs (Int64.of_int args.sample_pts)
      in
      (fun () ->
         summarize ();
         Printf.printf "Probable influence: %f (%Ld hits of %Ld samples in population %Ld)\n"
           inf_est sat_ct sample_ct unk_ct), 
      (Int64.to_float sat_ct) /. (Int64.to_float sample_ct)
    ) else
      (summarize, 0.0)
  in
  summarize ();
  if args.ps_file <> "" then
    VS.valset_to_ps args.ps_file 50 8 vs unknown_frac;
)
    
