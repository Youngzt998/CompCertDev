(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Printing PPC assembly code in asm syntax *)

open Printf
open Datatypes
open Camlcoq
open AST
open Asm

(* Recognition of target ABI and asm syntax *)

type target = MacOS | Linux | Diab

let target = 
  match Configuration.system with
  | "macosx" -> MacOS
  | "linux"  -> Linux
  | "diab"   -> Diab
  | _        -> invalid_arg ("System " ^ Configuration.system ^ " not supported")

(* On-the-fly label renaming *)

let next_label = ref 100

let new_label() =
  let lbl = !next_label in incr next_label; lbl

let current_function_labels = (Hashtbl.create 39 : (label, int) Hashtbl.t)

let transl_label lbl =
  try
    Hashtbl.find current_function_labels lbl
  with Not_found ->
    let lbl' = new_label() in
    Hashtbl.add current_function_labels lbl lbl';
    lbl'

(* Record identifiers of functions that need a special stub *)

module IdentSet = Set.Make(struct type t = ident let compare = compare end)

let stubbed_functions = ref IdentSet.empty

(* Basic printing functions *)

let coqint oc n =
  fprintf oc "%ld" (camlint_of_coqint n)

let raw_symbol oc s =
  match target with
  | MacOS      -> fprintf oc "_%s" s
  | Linux|Diab -> fprintf oc "%s" s

let symbol oc symb =
  match target with
  | MacOS ->
      if IdentSet.mem symb !stubbed_functions
      then fprintf oc "L%s$stub" (extern_atom symb)
      else fprintf oc "_%s" (extern_atom symb)
  | Linux | Diab ->
      if IdentSet.mem symb !stubbed_functions
      then fprintf oc ".L%s$stub" (extern_atom symb)
      else fprintf oc "%s" (extern_atom symb)

let symbol_offset oc (symb, ofs) =
  symbol oc symb;
  if ofs <> 0l then fprintf oc " + %ld" ofs

let label oc lbl =
  match target with
  | MacOS      -> fprintf oc "L%d" lbl
  | Linux|Diab -> fprintf oc ".L%d" lbl

let label_low oc lbl =
  match target with
  | MacOS      -> fprintf oc "lo16(L%d)" lbl
  | Linux|Diab -> fprintf oc ".L%d@l" lbl

let label_high oc lbl =
  match target with
  | MacOS      -> fprintf oc "ha16(L%d)" lbl
  | Linux|Diab -> fprintf oc ".L%d@ha" lbl

let constant oc cst =
  match cst with
  | Cint n ->
      fprintf oc "%ld" (camlint_of_coqint n)
  | Csymbol_low(s, n) ->
      begin match target with
      | MacOS -> 
          fprintf oc "lo16(%a)" symbol_offset (s, camlint_of_coqint n)
      | Linux|Diab ->
          fprintf oc "(%a)@l" symbol_offset (s, camlint_of_coqint n)
      end
  | Csymbol_high(s, n) ->
      begin match target with
      | MacOS ->
          fprintf oc "ha16(%a)" symbol_offset (s, camlint_of_coqint n)
      | Linux|Diab ->
          fprintf oc "(%a)@ha" symbol_offset (s, camlint_of_coqint n)
      end
  | Csymbol_sda(s, n) ->
      assert false  (* treated specially in ireg_with_offset below *)

let num_crbit = function
  | CRbit_0 -> 0
  | CRbit_1 -> 1
  | CRbit_2 -> 2
  | CRbit_3 -> 3

let crbit oc bit =
  fprintf oc "%d" (num_crbit bit)

let int_reg_name = function
  | GPR0 -> "0"  | GPR1 -> "1"  | GPR2 -> "2"  | GPR3 -> "3"
  | GPR4 -> "4"  | GPR5 -> "5"  | GPR6 -> "6"  | GPR7 -> "7"
  | GPR8 -> "8"  | GPR9 -> "9"  | GPR10 -> "10" | GPR11 -> "11"
  | GPR12 -> "12" | GPR13 -> "13" | GPR14 -> "14" | GPR15 -> "15"
  | GPR16 -> "16" | GPR17 -> "17" | GPR18 -> "18" | GPR19 -> "19"
  | GPR20 -> "20" | GPR21 -> "21" | GPR22 -> "22" | GPR23 -> "23"
  | GPR24 -> "24" | GPR25 -> "25" | GPR26 -> "26" | GPR27 -> "27"
  | GPR28 -> "28" | GPR29 -> "29" | GPR30 -> "30" | GPR31 -> "31"

let float_reg_name = function
  | FPR0 -> "0"  | FPR1 -> "1"  | FPR2 -> "2"  | FPR3 -> "3"
  | FPR4 -> "4"  | FPR5 -> "5"  | FPR6 -> "6"  | FPR7 -> "7"
  | FPR8 -> "8"  | FPR9 -> "9"  | FPR10 -> "10" | FPR11 -> "11"
  | FPR12 -> "12" | FPR13 -> "13" | FPR14 -> "14" | FPR15 -> "15"
  | FPR16 -> "16" | FPR17 -> "17" | FPR18 -> "18" | FPR19 -> "19"
  | FPR20 -> "20" | FPR21 -> "21" | FPR22 -> "22" | FPR23 -> "23"
  | FPR24 -> "24" | FPR25 -> "25" | FPR26 -> "26" | FPR27 -> "27"
  | FPR28 -> "28" | FPR29 -> "29" | FPR30 -> "30" | FPR31 -> "31"

let ireg oc r =
  begin match target with
  | MacOS|Diab -> output_char oc 'r'
  | Linux      -> ()
  end;
  output_string oc (int_reg_name r)

let ireg_or_zero oc r =
  if r = GPR0 then output_string oc "0" else ireg oc r

let freg oc r =
  begin match target with
  | MacOS|Diab -> output_char oc 'f'
  | Linux      -> ()
  end;
  output_string oc (float_reg_name r)

let creg oc r =
  match target with
  | MacOS|Diab -> fprintf oc "cr%d" r
  | Linux      -> fprintf oc "%d" r

let ireg_with_offset oc (r, cst) =
  match cst with
  | Csymbol_sda(s, n) ->
      begin match target with
      | MacOS ->
          assert false
      | Linux ->
          fprintf oc "(%a)@sdarel(%a)" symbol_offset (s, camlint_of_coqint n) ireg r
      | Diab ->
          fprintf oc "(%a)@sdarx(r0)" symbol_offset (s, camlint_of_coqint n)
      end
  | _ ->
      fprintf oc "%a(%a)" constant cst ireg r

let section oc name =
  fprintf oc "	%s\n" name

(* Names of sections *)

let (text, data, const_data, sdata, float_literal) =
  match target with
  | MacOS ->
      (".text",
       ".data",
       ".const",
       ".data",  (* unused *)
       ".const_data")
  | Linux ->
      (".text",
       ".data",
       ".rodata",
       ".section	.sdata,\"aw\",@progbits",
       ".section	.rodata.cst8,\"aM\",@progbits,8")
  | Diab ->
      (".text",
       ".data",
       ".data",  (* to check *)
       ".sdata", (* to check *)
       ".data")  (* to check *)

(* Encoding masks for rlwinm instructions *)

let rolm_mask n =
  let mb = ref 0       (* location of last 0->1 transition *)
  and me = ref 32      (* location of last 1->0 transition *)
  and last = ref ((Int32.logand n 1l) <> 0l)  (* last bit seen *)
  and count = ref 0    (* number of transitions *)
  and mask = ref 0x8000_0000l in
  for mx = 0 to 31 do
    if Int32.logand n !mask <> 0l then
      if !last then () else (incr count; mb := mx; last := true)
    else
      if !last then (incr count; me := mx; last := false) else ();
    mask := Int32.shift_right_logical !mask 1
  done;
  if !me = 0 then me := 32;
  assert (!count = 2 || (!count = 0 && !last));
  (!mb, !me-1)

(* Printing of instructions *)

module Labelset = Set.Make(struct type t = label let compare = compare end)

let print_instruction oc labels = function
  | Padd(r1, r2, r3) ->
      fprintf oc "	add	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Paddi(r1, r2, c) ->
      fprintf oc "	addi	%a, %a, %a\n" ireg r1 ireg_or_zero r2 constant c
  | Paddis(r1, r2, c) ->
      fprintf oc "	addis	%a, %a, %a\n" ireg r1 ireg_or_zero r2 constant c
  | Paddze(r1, r2) ->
      fprintf oc "	addze	%a, %a\n" ireg r1 ireg r2
  | Pallocframe(lo, hi, ofs) ->
      let lo = camlint_of_coqint lo
      and hi = camlint_of_coqint hi
      and ofs = camlint_of_coqint ofs in
      let sz = Int32.sub hi lo in
      (* Keep stack 16-aligned *)
      let sz16 = Int32.logand (Int32.add sz 15l) 0xFFFF_FFF0l in
      assert (ofs = 0l);
      fprintf oc "	stwu	%a, %ld(%a)\n" ireg GPR1 (Int32.neg sz16) ireg GPR1
  | Pand_(r1, r2, r3) ->
      fprintf oc "	and.	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pandc(r1, r2, r3) ->
      fprintf oc "	andc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pandi_(r1, r2, c) ->
      fprintf oc "	andi.	%a, %a, %a\n" ireg r1 ireg r2 constant c
  | Pandis_(r1, r2, c) ->
      fprintf oc "	andis.	%a, %a, %a\n" ireg r1 ireg r2 constant c
  | Pb lbl ->
      fprintf oc "	b	%a\n" label (transl_label lbl)
  | Pbctr ->
      fprintf oc "	bctr\n"
  | Pbctrl ->
      fprintf oc "	bctrl\n"
  | Pbf(bit, lbl) ->
      fprintf oc "	bf	%a, %a\n" crbit bit label (transl_label lbl)
  | Pbl s ->
      fprintf oc "	bl	%a\n" symbol s
  | Pbs s ->
      fprintf oc "	b	%a\n" symbol s
  | Pblr ->
      fprintf oc "	blr\n"
  | Pbt(bit, lbl) ->
      fprintf oc "	bt	%a, %a\n" crbit bit label (transl_label lbl)
  | Pcmplw(r1, r2) ->
      fprintf oc "	cmplw	%a, %a, %a\n" creg 0 ireg r1 ireg r2
  | Pcmplwi(r1, c) ->
      fprintf oc "	cmplwi	%a, %a, %a\n" creg 0 ireg r1 constant c
  | Pcmpw(r1, r2) ->
      fprintf oc "	cmpw	%a, %a, %a\n" creg 0 ireg r1 ireg r2
  | Pcmpwi(r1, c) ->
      fprintf oc "	cmpwi	%a, %a, %a\n" creg 0 ireg r1 constant c
  | Pcror(c1, c2, c3) ->
      fprintf oc "	cror	%a, %a, %a\n" crbit c1 crbit c2 crbit c3
  | Pdivw(r1, r2, r3) ->
      fprintf oc "	divw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pdivwu(r1, r2, r3) ->
      fprintf oc "	divwu	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Peqv(r1, r2, r3) ->
      fprintf oc "	eqv	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pextsb(r1, r2) ->
      fprintf oc "	extsb	%a, %a\n" ireg r1 ireg r2
  | Pextsh(r1, r2) ->
      fprintf oc "	extsh	%a, %a\n" ireg r1 ireg r2
  | Pfreeframe ofs ->
      fprintf oc "	lwz	%a, %ld(%a)\n" ireg GPR1  (camlint_of_coqint ofs)  ireg GPR1
  | Pfabs(r1, r2) ->
      fprintf oc "	fabs	%a, %a\n" freg r1 freg r2
  | Pfadd(r1, r2, r3) ->
      fprintf oc "	fadd	%a, %a, %a\n" freg r1 freg r2 freg r3
  | Pfcmpu(r1, r2) ->
      fprintf oc "	fcmpu	%a, %a, %a\n" creg 0 freg r1 freg r2
  | Pfcti(r1, r2) ->
      fprintf oc "	fctiwz	%a, %a\n" freg FPR13 freg r2;
      fprintf oc "	stfdu	%a, -8(%a)\n" freg FPR13 ireg GPR1;
      fprintf oc "	lwz	%a, 4(%a)\n" ireg r1 ireg GPR1;
      fprintf oc "	addi	%a, %a, 8\n" ireg GPR1 ireg GPR1
  | Pfctiu(r1, r2) ->
      let lbl1 = new_label() in
      let lbl2 = new_label() in
      let lbl3 = new_label() in
      fprintf oc "	addis	%a, 0, %a\n" ireg GPR12  label_high lbl1;
      fprintf oc "	lfd	%a, %a(%a)\n" freg FPR13  label_low lbl1  ireg GPR12;
      fprintf oc "	fcmpu	%a, %a, %a\n" creg 7  freg r2  freg FPR13;
      fprintf oc "	cror	30, 29, 30\n";
      fprintf oc "	beq	%a, %a\n" creg 7  label lbl2;
      fprintf oc "	fctiwz	%a, %a\n" freg FPR13  freg r2;
      fprintf oc "	stfdu	%a, -8(%a)\n" freg FPR13  ireg GPR1;
      fprintf oc "	lwz	%a, 4(%a)\n" ireg r1  ireg GPR1;
      fprintf oc "	b	%a\n" label lbl3;
      fprintf oc "%a:	fsub	%a, %a, %a\n" label lbl2  freg FPR13  freg r2  freg FPR13;
      fprintf oc "	fctiwz	%a, %a\n" freg FPR13  freg FPR13;
      fprintf oc "	stfdu	%a, -8(%a)\n" freg FPR13  ireg GPR1;
      fprintf oc "	lwz	%a, 4(%a)\n" ireg r1  ireg GPR1;
      fprintf oc "	addis	%a, %a, 0x8000\n" ireg r1 ireg r1;
      fprintf oc "%a:	addi	%a, %a, 8\n" label lbl3  ireg GPR1  ireg GPR1;
      section oc float_literal;
      fprintf oc "%a:	.long	0x41e00000, 0x00000000\n" label lbl1;
      section oc text
  | Pfdiv(r1, r2, r3) ->
      fprintf oc "	fdiv	%a, %a, %a\n" freg r1 freg r2 freg r3
  | Pfmadd(r1, r2, r3, r4) ->
      fprintf oc "	fmadd	%a, %a, %a, %a\n" freg r1 freg r2 freg r3 freg r4
  | Pfmr(r1, r2) ->
      fprintf oc "	fmr	%a, %a\n" freg r1 freg r2
  | Pfmsub(r1, r2, r3, r4) ->
      fprintf oc "	fmsub	%a, %a, %a, %a\n" freg r1 freg r2 freg r3 freg r4
  | Pfmul(r1, r2, r3) ->
      fprintf oc "	fmul	%a, %a, %a\n" freg r1 freg r2 freg r3
  | Pfneg(r1, r2) ->
      fprintf oc "	fneg	%a, %a\n" freg r1 freg r2
  | Pfrsp(r1, r2) ->
      fprintf oc "	frsp	%a, %a\n" freg r1 freg r2
  | Pfsub(r1, r2, r3) ->
      fprintf oc "	fsub	%a, %a, %a\n" freg r1 freg r2 freg r3
  | Pictf(r1, r2) ->
      let lbl = new_label() in
      fprintf oc "	addis	%a, 0, 0x4330\n" ireg GPR12;
      fprintf oc "	stwu	%a, -8(%a)\n" ireg GPR12  ireg GPR1;
      fprintf oc "	addis	%a, %a, 0x8000\n" ireg GPR12  ireg r2;
      fprintf oc "	stw	%a, 4(%a)\n" ireg GPR12  ireg GPR1;
      fprintf oc "	addis	%a, 0, %a\n" ireg GPR12  label_high lbl;
      fprintf oc "	lfd	%a, %a(%a)\n" freg FPR13  label_low lbl  ireg GPR12;
      fprintf oc "	lfd	%a, 0(%a)\n" freg r1  ireg GPR1;
      fprintf oc "	addi	%a, %a, 8\n" ireg GPR1  ireg GPR1;
      fprintf oc "	fsub	%a, %a, %a\n" freg r1  freg r1  freg FPR13;
      section oc float_literal;
      fprintf oc "%a:	.long	0x43300000, 0x80000000\n" label lbl;
      section oc text
  | Piuctf(r1, r2) ->
      let lbl = new_label() in
      fprintf oc "	addis	%a, 0, 0x4330\n" ireg GPR12;
      fprintf oc "	stwu	%a, -8(%a)\n" ireg GPR12  ireg GPR1;
      fprintf oc "	stw	%a, 4(%a)\n" ireg r2  ireg GPR1;
      fprintf oc "	addis	%a, 0, %a\n" ireg GPR12  label_high lbl;
      fprintf oc "	lfd	%a, %a(%a)\n" freg FPR13  label_low lbl  ireg GPR12;
      fprintf oc "	lfd	%a, 0(%a)\n" freg r1  ireg GPR1;
      fprintf oc "	addi	%a, %a, 8\n" ireg GPR1  ireg GPR1;
      fprintf oc "	fsub	%a, %a, %a\n" freg r1  freg r1  freg FPR13;
      section oc float_literal;
      fprintf oc "%a:	.long	0x43300000, 0x00000000\n" label lbl;
      section oc text
  | Plbz(r1, c, r2) ->
      fprintf oc "	lbz	%a, %a\n" ireg r1 ireg_with_offset (r2, c)
  | Plbzx(r1, r2, r3) ->
      fprintf oc "	lbzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Plfd(r1, c, r2) ->
      fprintf oc "	lfd	%a, %a\n" freg r1 ireg_with_offset (r2, c)
  | Plfdx(r1, r2, r3) ->
      fprintf oc "	lfdx	%a, %a, %a\n" freg r1 ireg r2 ireg r3
  | Plfi(r1, c) ->
      let lbl = new_label() in
      fprintf oc "	addis	%a, 0, %a\n" ireg GPR12 label_high lbl;
      fprintf oc "	lfd	%a, %a(%a)\n" freg r1 label_low lbl ireg GPR12;
      section oc float_literal;
      let n = Int64.bits_of_float c in
      let nlo = Int64.to_int32 n
      and nhi = Int64.to_int32(Int64.shift_right_logical n 32) in
      fprintf oc "%a:	.long	0x%lx, 0x%lx\n" label lbl nhi nlo;
      section oc text
  | Plfs(r1, c, r2) ->
      fprintf oc "	lfs	%a, %a\n" freg r1 ireg_with_offset (r2, c)
  | Plfsx(r1, r2, r3) ->
      fprintf oc "	lfsx	%a, %a, %a\n" freg r1 ireg r2 ireg r3
  | Plha(r1, c, r2) ->
      fprintf oc "	lha	%a, %a\n" ireg r1 ireg_with_offset (r2, c)
  | Plhax(r1, r2, r3) ->
      fprintf oc "	lhax	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Plhz(r1, c, r2) ->
      fprintf oc "	lhz	%a, %a\n" ireg r1 ireg_with_offset (r2, c)
  | Plhzx(r1, r2, r3) ->
      fprintf oc "	lhzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Plwz(r1, c, r2) ->
      fprintf oc "	lwz	%a, %a\n" ireg r1 ireg_with_offset (r2, c)
  | Plwzx(r1, r2, r3) ->
      fprintf oc "	lwzx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pmfcrbit(r1, bit) ->
      fprintf oc "	mfcr	%a\n" ireg GPR12;
      fprintf oc "	rlwinm	%a, %a, %d, 31, 31\n" ireg r1  ireg GPR12  (1 + num_crbit bit)
  | Pmflr(r1) ->
      fprintf oc "	mflr	%a\n" ireg r1
  | Pmr(r1, r2) ->
      fprintf oc "	mr	%a, %a\n" ireg r1 ireg r2
  | Pmtctr(r1) ->
      fprintf oc "	mtctr	%a\n" ireg r1
  | Pmtlr(r1) ->
      fprintf oc "	mtlr	%a\n" ireg r1
  | Pmulli(r1, r2, c) ->
      fprintf oc "	mulli	%a, %a, %a\n" ireg r1 ireg r2 constant c
  | Pmullw(r1, r2, r3) ->
      fprintf oc "	mullw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pnand(r1, r2, r3) ->
      fprintf oc "	nand	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pnor(r1, r2, r3) ->
      fprintf oc "	nor	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Por(r1, r2, r3) ->
      fprintf oc "	or	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Porc(r1, r2, r3) ->
      fprintf oc "	orc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pori(r1, r2, c) ->
      fprintf oc "	ori	%a, %a, %a\n" ireg r1 ireg r2 constant c
  | Poris(r1, r2, c) ->
      fprintf oc "	oris	%a, %a, %a\n" ireg r1 ireg r2 constant c
  | Prlwinm(r1, r2, c1, c2) ->
      let (mb, me) = rolm_mask (camlint_of_coqint c2) in
      fprintf oc "	rlwinm	%a, %a, %ld, %d, %d\n"
                ireg r1 ireg r2 (camlint_of_coqint c1) mb me
(*
      fprintf oc "	rlwinm	%a, %a, %ld, 0x%lx\n"
                ireg r1 ireg r2 (camlint_of_coqint c1) (camlint_of_coqint c2)
*)
  | Pslw(r1, r2, r3) ->
      fprintf oc "	slw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Psraw(r1, r2, r3) ->
      fprintf oc "	sraw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Psrawi(r1, r2, c) ->
      fprintf oc "	srawi	%a, %a, %ld\n" ireg r1 ireg r2 (camlint_of_coqint c)
  | Psrw(r1, r2, r3) ->
      fprintf oc "	srw	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pstb(r1, c, r2) ->
      fprintf oc "	stb	%a, %a\n" ireg r1 ireg_with_offset (r2, c)
  | Pstbx(r1, r2, r3) ->
      fprintf oc "	stbx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pstfd(r1, c, r2) ->
      fprintf oc "	stfd	%a, %a\n" freg r1 ireg_with_offset (r2, c)
  | Pstfdx(r1, r2, r3) ->
      fprintf oc "	stfdx	%a, %a, %a\n" freg r1 ireg r2 ireg r3
  | Pstfs(r1, c, r2) ->
      fprintf oc "	frsp	%a, %a\n" freg FPR13 freg r1;
      fprintf oc "	stfs	%a, %a\n" freg FPR13 ireg_with_offset (r2, c)
  | Pstfsx(r1, r2, r3) ->
      fprintf oc "	frsp	%a, %a\n" freg FPR13 freg r1;
      fprintf oc "	stfsx	%a, %a, %a\n" freg FPR13 ireg r2 ireg r3
  | Psth(r1, c, r2) ->
      fprintf oc "	sth	%a, %a\n" ireg r1 ireg_with_offset (r2, c)
  | Psthx(r1, r2, r3) ->
      fprintf oc "	sthx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pstw(r1, c, r2) ->
      fprintf oc "	stw	%a, %a\n" ireg r1 ireg_with_offset (r2, c)
  | Pstwx(r1, r2, r3) ->
      fprintf oc "	stwx	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Psubfc(r1, r2, r3) ->
      fprintf oc "	subfc	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Psubfic(r1, r2, c) ->
      fprintf oc "	subfic	%a, %a, %a\n" ireg r1 ireg r2 constant c
  | Pxor(r1, r2, r3) ->
      fprintf oc "	xor	%a, %a, %a\n" ireg r1 ireg r2 ireg r3
  | Pxori(r1, r2, c) ->
      fprintf oc "	xori	%a, %a, %a\n" ireg r1 ireg r2 constant c
  | Pxoris(r1, r2, c) ->
      fprintf oc "	xoris	%a, %a, %a\n" ireg r1 ireg r2 constant c
  | Plabel lbl ->
      if Labelset.mem lbl labels then
        fprintf oc "%a:\n" label (transl_label lbl)

let rec labels_of_code = function
  | [] -> Labelset.empty
  | (Pb lbl | Pbf(_, lbl) | Pbt(_, lbl)) :: c ->
      Labelset.add lbl (labels_of_code c)
  | _ :: c -> labels_of_code c

let print_function oc name code =
  Hashtbl.clear current_function_labels;
  section oc text;
  fprintf oc "	.align 2\n";
  if not (Cil2Csyntax.atom_is_static name) then
    fprintf oc "	.globl %a\n" symbol name;
  fprintf oc "%a:\n" symbol name;
  List.iter (print_instruction oc (labels_of_code code)) code

(* Generation of stub functions *)

let re_variadic_stub = Str.regexp "\\(.*\\)\\$[if]*$"

(* Stubs for MacOS X *)

module Stubs_MacOS = struct

(* Generation of stub code for variadic functions, e.g. printf.
   Calling conventions for variadic functions are:
     - always reserve 8 stack words (offsets 24 to 52) so that the
       variadic function can save there the integer registers parameters
       r3 ... r10
     - treat float arguments as pairs of integers, i.e. if we
       must pass them in registers, use a pair of integer registers
       for this purpose.
   The code we generate is:
     - allocate large enough stack frame
     - save return address
     - copy our arguments (registers and stack) to the stack frame,
       starting at offset 24
     - load relevant integer parameter registers r3...r10 from the
       stack frame, limited by the actual number of arguments
     - call the variadic thing
     - deallocate stack frame and return
*)

let variadic_stub oc stub_name fun_name ty_args =
  (* Compute total size of arguments *)
  let arg_size =
    List.fold_left
     (fun sz ty -> match ty with Tint -> sz + 4 | Tfloat -> sz + 8)
     0 ty_args in
  (* Stack size is linkage area + argument size, with a minimum of 56 bytes *)
  let frame_size = max 56 (24 + arg_size) in
  fprintf oc "	mflr	r0\n";
  fprintf oc "	stwu	r1, %d(r1)\n" (-frame_size);
  fprintf oc "	stw	r0, %d(r1)\n" (frame_size + 4);
  (* Copy our parameters to our stack frame.
     As an optimization, don't copy parameters that are already in
     integer registers, since these stay in place. *)
  let rec copy gpr fpr src_ofs dst_ofs = function
    | [] -> ()
    | Tint :: rem ->
        if gpr > 10 then begin
          fprintf oc "	lwz	r0, %d(r1)\n" src_ofs;
          fprintf oc "	stw	r0, %d(r1)\n" dst_ofs
        end;
        copy (gpr + 1) fpr (src_ofs + 4) (dst_ofs + 4) rem
    | Tfloat :: rem ->
        if fpr <= 10 then begin
          fprintf oc "	stfd	f%d, %d(r1)\n" fpr dst_ofs
        end else begin
          fprintf oc "	lfd	f0, %d(r1)\n" src_ofs;
          fprintf oc "	stfd	f0, %d(r1)\n" dst_ofs
        end;
        copy (gpr + 2) (fpr + 1) (src_ofs + 8) (dst_ofs + 8) rem
  in copy 3 1 (frame_size + 24) 24 ty_args;
  (* Load the first parameters into integer registers.
     As an optimization, don't load parameters that are already
     in the correct integer registers. *)
  let rec load gpr ofs = function
    | [] -> ()
    | Tint :: rem ->
        load (gpr + 1) (ofs + 4) rem
    | Tfloat :: rem ->
        if gpr <= 10 then
          fprintf oc "	lwz	r%d, %d(r1)\n" gpr ofs;
        if gpr + 1 <= 10 then
          fprintf oc "	lwz	r%d, %d(r1)\n" (gpr + 1) (ofs + 4);
        load (gpr + 2) (ofs + 8) rem
  in load 3 24 ty_args;
  (* Call the function *)
  fprintf oc "	addis	r11, 0, ha16(L%s$ptr)\n" stub_name;
  fprintf oc "	lwz	r11, lo16(L%s$ptr)(r11)\n" stub_name;
  fprintf oc "	mtctr	r11\n";
  fprintf oc "	bctrl\n";
  (* Free our frame and return *)
  fprintf oc "	lwz	r0, %d(r1)\n" (frame_size + 4);
  fprintf oc "	mtlr	r0\n";
  fprintf oc "	addi	r1, r1, %d\n" frame_size;
  fprintf oc "	blr\n";
  (* The function pointer *)
  fprintf oc "	.non_lazy_symbol_pointer\n";
  fprintf oc "L%s$ptr:\n" stub_name;
  fprintf oc "	.indirect_symbol _%s\n" fun_name;
  fprintf oc "	.long	0\n"

(* Stubs for fixed-type functions are much simpler *)

let non_variadic_stub oc name =
  fprintf oc "	addis	r11, 0, ha16(L%s$ptr)\n" name;
  fprintf oc "	lwz	r11, lo16(L%s$ptr)(r11)\n" name;
  fprintf oc "	mtctr	r11\n";
  fprintf oc "	bctr\n";
  fprintf oc "	.non_lazy_symbol_pointer\n";
  fprintf oc "L%s$ptr:\n" name;
  fprintf oc "	.indirect_symbol _%s\n" name;
  fprintf oc "	.long	0\n"

let stub_function oc name ef =
  let name = extern_atom name in
  fprintf oc "	.text\n";
  fprintf oc "	.align 2\n";
  fprintf oc "L%s$stub:\n" name;
  if Str.string_match re_variadic_stub name 0
  then variadic_stub oc name (Str.matched_group 1 name) ef.ef_sig.sig_args
  else non_variadic_stub oc name

let function_needs_stub name = true

end

(* Stubs for EABI *)

module Stubs_EABI = struct

let variadic_stub oc stub_name fun_name args =
  fprintf oc "	.text\n";
  fprintf oc "	.align 2\n";
  fprintf oc ".L%s$stub:\n" stub_name;
  (* bit 6 must be set if at least one argument is a float; clear otherwise *)
  if List.mem Tfloat args
  then fprintf oc "	creqv	6, 6, 6\n"
  else fprintf oc "	crxor	6, 6, 6\n";
  fprintf oc "	b	%s\n" fun_name

let stub_function oc name ef =
  let name = extern_atom name in
  (* Only variadic functions need a stub *)
  if Str.string_match re_variadic_stub name 0
  then variadic_stub oc name (Str.matched_group 1 name) ef.ef_sig.sig_args

let function_needs_stub name =
  Str.string_match re_variadic_stub (extern_atom name) 0

end

let function_needs_stub =
  match target with
  | MacOS      -> Stubs_MacOS.function_needs_stub
  | Linux|Diab -> Stubs_EABI.function_needs_stub

let stub_function =
  match target with
  | MacOS       -> Stubs_MacOS.stub_function
  | Linux|Diab  -> Stubs_EABI.stub_function

let print_fundef oc (Coq_pair(name, defn)) =
  match defn with
  | Internal code -> print_function oc name code
  | External ef -> stub_function oc name ef

let record_extfun (Coq_pair(name, defn)) =
  match defn with
  | Internal _ -> ()
  | External _ -> 
      if function_needs_stub name then
        stubbed_functions := IdentSet.add name !stubbed_functions

let init_data_queue = ref []

let print_init oc = function
  | Init_int8 n ->
      fprintf oc "	.byte	%ld\n" (camlint_of_coqint n)
  | Init_int16 n ->
      fprintf oc "	.short	%ld\n" (camlint_of_coqint n)
  | Init_int32 n ->
      fprintf oc "	.long	%ld\n" (camlint_of_coqint n)
  | Init_float32 n ->
      fprintf oc "	.long	%ld\n" (Int32.bits_of_float n)
  | Init_float64 n ->
      (* .quad not working on all versions of the MacOSX assembler *)
      let b = Int64.bits_of_float n in
      fprintf oc "	.long	%Ld, %Ld\n"
                 (Int64.shift_right_logical b 32)
                 (Int64.logand b 0xFFFFFFFFL)
  | Init_space n ->
      let n = camlint_of_z n in
      if n > 0l then fprintf oc "	.space	%ld\n" n
  | Init_addrof(symb, ofs) ->
      fprintf oc "	.long	%a\n" 
                 symbol_offset (symb, camlint_of_coqint ofs)
  | Init_pointer id ->
      let lbl = new_label() in
      fprintf oc "	.long	%a\n" label lbl;
      init_data_queue := (lbl, id) :: !init_data_queue

let print_init_data oc id =
  init_data_queue := [];
  List.iter (print_init oc) id;
  let rec print_remainder () =
    match !init_data_queue with
    | [] -> ()
    | (lbl, id) :: rem ->
        init_data_queue := rem;
        fprintf oc "%a:\n" label lbl;
        List.iter (print_init oc) id;
        print_remainder()
  in print_remainder()

let print_var oc (Coq_pair(Coq_pair(name, init_data), _)) =
  match init_data with
  | [] -> ()
  | _  ->
      let sec =
        if Cil2Csyntax.atom_is_small_data name (coqint_of_camlint 0l) then
          sdata
        else if Cil2Csyntax.atom_is_readonly name then
          const_data
        else
          data in
      section oc sec;
      fprintf oc "	.align	3\n";
      if not (Cil2Csyntax.atom_is_static name) then
        fprintf oc "	.globl	%a\n" symbol name;
      fprintf oc "%a:\n" symbol name;
      print_init_data oc init_data

let print_program oc p =
  stubbed_functions := IdentSet.empty;
  List.iter record_extfun p.prog_funct;
  List.iter (print_var oc) p.prog_vars;
  List.iter (print_fundef oc) p.prog_funct

