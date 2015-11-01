(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(* if at eol, consume \n and return true.
   else return false.
*)
let eat_eol sbuf =
  try Scanf.bscanf sbuf "\n" true
  with Scanf.Scan_failure _ -> false

(* Takes a partial application of bscanf, and the desired callback.
   Keeps attempting the scan and advancing by one character until
   scan is successful
*)
let rec skip_to sbuf ptl cb =
  let rv = 
    try
      Some(ptl cb)
    with
    | Scanf.Scan_failure x -> 
(*         Printf.printf "failure: %s\n" x; *)
        None
  in
  match rv with
  | None -> 
      Scanf.bscanf sbuf "%c" (fun x -> ()); (* advance 1 char *)
      skip_to sbuf ptl cb (* and try again *)
  | Some(x) -> x

(* add entries for imports from one module to import table *)
let read_module_imports sbuf imptable base =
  (* read imports from one module *)
  let imp_module =
    Scanf.bscanf 
      sbuf
      " offset %_Lx %s\n"
      Vine_util.id
  in
  let first_thunk_rva = 
    skip_to
      sbuf
      (Scanf.bscanf sbuf " First thunk RVA: %Lx\n")   
      Vine_util.id 
  in
  skip_to sbuf (Scanf.bscanf sbuf " Ordn Name\n") ();

  (* get the import table *)
  let imp_base = Int64.add base first_thunk_rva in
  let offset = ref 0L in
  let imptable = ref imptable in
  while not (eat_eol sbuf)
  do
    let ord =
      Scanf.bscanf
        sbuf
        " %d"
        Vine_util.id
    in
    let fnname = 
      try
        Scanf.bscanf
          sbuf
          " <by ordinal>\n"
          None
      with
        Scanf.Scan_failure _ ->
          Scanf.bscanf 
            sbuf 
            " %s %_Lx\n" 
            (fun fnname -> Some(fnname))
    in
    let address = Int64.add imp_base !offset in
    offset := Int64.add !offset 4L;
    imptable := PMap.add address (imp_module, ord, fnname) !imptable;
    Printf.printf "%Lx %s %d %s\n" address imp_module ord 
      (match fnname with None -> "ord" | Some(x) -> x);
  done;
  !imptable

(** Parse the output of "winedump -x all" to get the import and
    export tables from a PE binary.
    @param filename path of file containing winedump output
    @return (import table, export table)
    import table is a PMap from import slot address to
    (module name, ordinal, function name option).
    export table is a PMap from (module name, ordinal) to
    (function address, function name)
*)
let parse filename =
  let sbuf = Scanf.Scanning.from_file filename in

  (* get image base. addresses expressed in rest of output
     are relative to this address *)
  let base =
    skip_to 
      sbuf 
      (Scanf.bscanf sbuf "image base 0x%Lx")
      Vine_util.id
  in
  
  (* find beginning of import table *)
  skip_to
    sbuf
    (Scanf.bscanf sbuf "Import Table size: %_Lx\n")   
    ();

  let imp_table = ref PMap.empty in
  while not (eat_eol sbuf) do
    imp_table := 
      read_module_imports sbuf !imp_table base;
  done;

  (* look for beginning of exports table, which may
     not be present. *)
  let exp_table = 
    (try
       (* find beginning of exports table *)
       let module_name = 
         skip_to
           sbuf
           (Scanf.bscanf sbuf "Exports table:\n\n Name: %s")
           Vine_util.id
       in
       skip_to
         sbuf
         (Scanf.bscanf sbuf " Entry Pt Ordn Name\n")
         ();

       (* read export table entries *)
       let exp_table = ref PMap.empty in
       while not (eat_eol sbuf) do
         let rel_addr, ord, fnname =
           Scanf.bscanf sbuf " %Lx %d %s" (fun x y z -> x,y,z)
         in
         skip_to sbuf (Scanf.bscanf sbuf "\n") (); (* skip rest of line *)
         let addr = Int64.add rel_addr base in
         exp_table := PMap.add 
           (module_name, ord) 
           (addr, fnname) 
           !exp_table;
         Printf.printf "%Lx %s %d %s\n" addr module_name ord fnname;
       done;
       !exp_table
     with
     | End_of_file -> PMap.empty)
  in

  !imp_table, exp_table
              

    
