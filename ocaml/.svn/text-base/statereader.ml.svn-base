(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
open Vine

(* mirrors user_regs_struct from sys/user.h *)
type user_regs_struct = {
  ebx : Int32.t;
  ecx : Int32.t;
  edx : Int32.t;
  esi : Int32.t;
  edi : Int32.t;
  ebp : Int32.t;
  eax : Int32.t;
  xds : Int32.t;
  xes : Int32.t;
  xfs : Int32.t;
  xgs : Int32.t;
  orig_eax : Int32.t;
  eip : Int32.t;
  xcs : Int32.t;
  eflags : Int32.t;
  esp : Int32.t;
  xss : Int32.t;
}

class state_handle filename = 
  let read_user_regs_struct inp =
    (* tried doing the reads directly in the struct
       creation. they did not execute from first
       to last *)
    let ebx = IO.read_real_i32 inp in
    let ecx = IO.read_real_i32 inp in
    let edx = IO.read_real_i32 inp in
    let esi = IO.read_real_i32 inp in
    let edi = IO.read_real_i32 inp in
    let ebp = IO.read_real_i32 inp in
    let eax = IO.read_real_i32 inp in
    let xds = IO.read_real_i32 inp in
    let xes = IO.read_real_i32 inp in
    let xfs = IO.read_real_i32 inp in
    let xgs = IO.read_real_i32 inp in
    let orig_eax = IO.read_real_i32 inp in
    let eip = IO.read_real_i32 inp in
    let xcs = IO.read_real_i32 inp in
    let eflags = IO.read_real_i32 inp in
    let esp = IO.read_real_i32 inp in
    let xss = IO.read_real_i32 inp in
    {
      ebx = ebx;
      ecx = ecx;
      edx = edx;
      esi = esi;
      edi = edi;
      ebp = ebp;
      eax = eax;
      xds = xds;
      xes = xes;
      xfs = xfs;
      xgs = xgs;
      orig_eax = orig_eax;
      eip = eip;
      xcs = xcs;
      eflags = eflags;
      esp = esp;
      xss = xss;
    } 
  in

object(self)
  val mutable inp = IO.input_channel (open_in filename)
  val mutable map_begin = 0l
  val mutable map_end = 0l
  val mutable cur_address = 0l
  val mutable urs = {ebx=0l;ecx=0l;edx=0l;esi=0l;edi=0l;ebp=0l;
                     eax=0l;xds=0l;xes=0l;xfs=0l;xgs=0l;orig_eax=0l;
                     eip=0l;xcs=0l;eflags=0l;esp=0l;xss=0l}
  method get_urs = urs

  method private read_map_hdr =
    map_begin <- IO.read_real_i32 inp;
    map_end <- IO.read_real_i32 inp;
    cur_address <- map_begin;
    assert(map_end > map_begin)

  method private fix_map =
    if cur_address >= map_end then (
      self#read_map_hdr;
    )

  initializer
    urs <- read_user_regs_struct inp;
    self#read_map_hdr;

  method next_mem =
    let addr = cur_address in
    cur_address <- Int32.add cur_address 1l;
    self#fix_map;
    let value = Int32.of_int (IO.read_byte inp) in
    (addr, value)
end

let user_regs_struct_to_inits urs =
  let init_reg regstring value =
    Move(Temp(regstring, REG_32),
         Constant(REG_32, Int(Int64.of_int32 value)))
  in
  [
    init_reg "R_EBX" urs.ebx;
    init_reg "R_ECX" urs.ecx;
    init_reg "R_EDX" urs.edx;
    init_reg "R_ESI" urs.esi;
    init_reg "R_EDI" urs.edi;
    init_reg "R_EBP" urs.ebp;
    init_reg "R_EAX" urs.eax;
    (*     init_reg "" urs.xds; *)
    (*     init_reg "" urs.xes; *)
    (*     init_reg "" urs.xfs; *)
    (*     init_reg "" urs.xgs; *)
    (*     init_reg "" urs.orig_eax; *)
    (*     init_reg "" urs.eip; *)
    (*     init_reg "" urs.xcs; *)
    init_reg "R_EFLAGS" urs.eflags;
    init_reg "R_ESP" urs.esp;
    (*     init_reg "" urs.xss; *)
  ]

let mem_to_init addr value = 
  Move(Mem("mem", REG_8, Constant(REG_32, Int(Int64.of_int32 addr))),
       Constant(REG_8, Int(Int64.of_int32 value)))
    
(* runs out of memory *)
let get_inits filename =
  let state = new state_handle filename in
  let reg_inits = user_regs_struct_to_inits state#get_urs in
  let mem_inits = ref [] in
  (try
     while true do
       let (addr, value) = state#next_mem in
       mem_inits := (mem_to_init addr value) :: !mem_inits
     done
   with IO.No_more_input -> ()
  );
  List.rev_append reg_inits !mem_inits

