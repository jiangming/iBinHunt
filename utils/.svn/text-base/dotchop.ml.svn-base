open Dot_helper

let tmpvertex = ((Graph.Dot_ast.Ident "_$@#choptmpnode", None),[])

let chop g starts ends =
  let () = assert (not(G.mem_vertex g tmpvertex)) in
  let g' = G.add_vertex g tmpvertex in
  let g' = List.fold_left (fun g p -> G.add_edge g p tmpvertex) g' ends in
  let g' = List.fold_left (fun g s -> G.add_edge g tmpvertex s) g' starts in
  let (_,scc) = Comp.scc g' in
  let myid = scc tmpvertex in
  let keep v = scc v = myid in
  let remove g v =
    (* FIXME: add edges to v_outside? *)
    G.remove_vertex g v
  in
    G.fold_vertex (fun v g -> if keep v then g else remove g v) g g


let parse_args () =
  let input = ref "" in
  let output = ref "" in
  let starts = ref [] in
  let ends = ref [] in
  let usage = "Take the chop of a graph in graphviz format.\n"^
    "  Usage: "^Sys.argv.(0)^" <input.dot> [-o <output.dot>] (-start <start node>)+ (-end <end node>)+"
  in
  let speclist = [
    ("-start", Arg.String (fun x -> starts := x :: !starts),
     "<vertex>  Adds vertex to the chop start.");
    ("-end", Arg.String (fun x -> ends := x :: !ends),
     "<vertex> Adds vertex to the chop end.");
    ("-o", Arg.Set_string output,
     "<file> Sets the output file (stdout otherwise)")
  ] in
  let setinput f =
    if !input = "" then
      input := f
    else raise(Arg.Bad "Only one input file must be specified")
  in
  let () =
    Arg.parse speclist setinput usage;
    if !input = "" || !starts = [] || !ends = [] then (
      Arg.usage speclist usage;
      exit(1)
    )
  in
  let outfd = if !output = "" then stdout else open_out !output in
      (!input, outfd, !starts, !ends)
      
;;

let () =
  let (input, outfd, start_names, end_names) = parse_args() in
  let g = Parser.parse input in
  let findv x = 
    try find_vertex g x
    with Not_found -> failwith("vertex not found: "^x)
  in
  let starts = List.map findv start_names in
  let ends = List.map findv end_names in
  let g' = chop g starts ends in
    Printer.output_graph outfd g'
