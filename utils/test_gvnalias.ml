
let (dl,_) as ir = Vine_parser.parse_file Sys.argv.(1)
let () = List.iter (fun x -> print_endline (Vine.var_to_string x)) dl
let cfg = Vine_cfg.prog_to_cfg ir
let ssa = Ssa.cfg2ssa cfg
let alias = Vine_dataflow.SsaDataflow.SCCVN.aliased ssa
let changed = Vine_alias.alias_replace alias ssa
;;

flush stderr;
if changed then
  Vine_graphviz.SsaStmtsDot.output_graph stdout ssa
else prerr_endline "Nothing changed"
