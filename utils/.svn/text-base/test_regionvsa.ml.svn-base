
let (dl,_) as ir = Vine_parser.parse_file Sys.argv.(1)
let () = List.iter (fun x -> print_endline (Vine.var_to_string x)) dl
let Vine.Lval(Vine.Temp sp) = Vine_parser.parse_exp_from_string dl Sys.argv.(2)
let init = Vine.VarMap.add sp [(sp, Vsa.SI.zero)] Vine.VarMap.empty
let cfg = Vine_cfg.prog_to_cfg ir
let ssa = Ssa.cfg2ssa cfg
let input,output = Vsa.RegionVSA.DF.worklist_iterate ~init:init ssa
let p = print_string
;;


Vine.VarMap.iter
  (fun k v ->
     Vine.pp_var p k;
     p " -> ";
     Vsa.VS.pp p v;
     p "\n"
  )
  (output Vine_cfg.BB_Exit)
