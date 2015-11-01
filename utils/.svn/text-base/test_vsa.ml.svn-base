
let ir = Vine_parser.parse_file Sys.argv.(1)

let cfg = Vine_cfg.prog_to_cfg ir
let ssa = Ssa.cfg2ssa cfg
let input,output = Vsa.SimpleVSA.DF.worklist_iterate ssa
;;

Vine.VarMap.iter
  (fun k v ->
     Printf.printf "%s -> %s\n" (Vine.var_to_string k) (Vsa.SI.to_string v)
  )
  (output Vine_cfg.BB_Exit)
