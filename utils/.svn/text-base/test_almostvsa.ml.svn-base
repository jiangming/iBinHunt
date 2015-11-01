
let (dl,_) as ir = Vine_parser.parse_file Sys.argv.(1)
let () = List.iter (fun x -> print_endline (Vine.var_to_string x)) dl
let Vine.Lval(Vine.Temp sp) = Vine_parser.parse_exp_from_string dl Sys.argv.(2)
let init = Vsa.AlmostVSA.DFP.init_vars [sp]
let cfg = Vine_cfg.prog_to_cfg ir
let ssa = Ssa.cfg2ssa cfg
let input,output = Vsa.AlmostVSA.DF.worklist_iterate ~init:init ssa
let p = print_string
;;


Vine.VarMap.iter
  (fun k v ->
     Vine.pp_var p k;
     p " -> ";
     Vsa.VS.pp p v;
     p "\n"
  )
  (fst (output Vine_cfg.BB_Exit))
