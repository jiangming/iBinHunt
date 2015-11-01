(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(** Parse the output of "winedump -x all" (a utility included in wine)
    to get the import and
    export tables from a PE binary.
    @param filename path of file containing winedump output
    @return (import table, export table)
    import table is a PMap from import slot address to
    (module name, ordinal, function name option).
    export table is a PMap from (module name, ordinal) to
    (function address, function name)
*)
val parse :
  string ->
  (int64, string * int * string option) PMap.t *
  (string * int, int64 * string) PMap.t
