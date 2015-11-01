
let (dl,_) as ir = Vine_parser.parse_file Sys.argv.(1)
let () = List.iter (fun x -> print_endline (Vine.var_to_string x)) dl
let cfg = Vine_cfg.prog_to_cfg ir
let ssa = Ssa.cfg2ssa cfg
let opt () =
  let alias = Vine_alias.vsa_alias ssa in
  let x = Vine_alias.alias_replace alias ssa in
  let y = Vine_alias.remove_dead_stores alias ssa in
  let z = Vine_dataflow.SsaDataflow.do_dce ssa in
    if x then print_endline "replaced loads";
    if y then print_endline "removed stores";
    if z then print_endline "removed dead code";
    x || y || z
let changed = if opt() then (while opt(); do (); done; true) else false
;;
flush stderr;
if changed then
  Vine_graphviz.SsaStmtsDot.output_graph stdout ssa
else prerr_endline "Nothing changed";
print_string "\n"
