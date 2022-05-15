(**************************************************************************)
(*  This file is part of CertrBPF,                                        *)
(*  a formally verified rBPF verifier + interpreter + JIT in Coq.         *)
(*                                                                        *)
(*  Copyright (C) 2022 Inria                                              *)
(*                                                                        *)
(*  This program is free software; you can redistribute it and/or modify  *)
(*  it under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation; either version 2 of the License, or     *)
(*  (at your option) any later version.                                   *)
(*                                                                        *)
(*  This program is distributed in the hope that it will be useful,       *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU General Public License for more details.                          *)
(*                                                                        *)
(**************************************************************************)

From Coq Require Import List ZArith.
Import ListNotations.

From compcert Require Import Integers Values AST Memory.

From bpf.comm Require Import MemRegion rBPFValues rBPFAST rBPFMemType Flag Regs BinrBPF State Monad rBPFMonadOp.
From bpf.monadicmodel Require Import Opcode.

Open Scope monad_scope.

Definition get_dst (ins: int64): M state reg := int64_to_dst_reg ins.

Definition reg64_to_reg32 (d: val): M state val := returnM (val_intuoflongu d).

Definition get_src (ins: int64): M state reg := int64_to_src_reg ins.

Definition get_offset (ins:int64): M state int := returnM (get_offset ins).

Definition get_immediate (ins:int64): M state int := returnM (get_immediate ins).

Definition eval_immediate (ins: int): M state val := returnM ((Val.longofint (sint32_to_vint ins))).

Definition get_src64 (x: nat) (ins: int64): M state val :=
  if Int.eq Int.zero (Int.and (Int.repr (Z.of_nat x)) (Int.repr 8)) then
(*
  if Nat.eqb 0 (Nat.land x 0x08) then *)
    do imm    <- get_immediate ins;
    do imm64  <- eval_immediate imm;
      returnM imm64
  else
    do src    <- get_src ins;
    do src64  <- eval_reg src;
      returnM src64.

Definition get_src32 (x: nat) (ins: int64): M state val := 
  if Int.eq Int.zero (Int.and (Int.repr (Z.of_nat x)) (Int.repr 8)) then (*
  if Nat.eqb 0 (Nat.land x 0x08) then *)
    do imm    <- get_immediate ins;
      returnM (sint32_to_vint imm)
  else
    do src    <- get_src ins;
    do src64  <- eval_reg src;
    do src32  <- reg64_to_reg32 src64;
      returnM src32.

Definition get_opcode_ins (ins: int64): M state nat :=
  returnM (get_opcode ins).

Definition get_opcode_alu64 (op: nat): M state opcode_alu64 :=
  returnM (byte_to_opcode_alu64 op).

Definition get_opcode_alu32 (op: nat): M state opcode_alu32 :=
  returnM (byte_to_opcode_alu32 op).

Definition get_opcode_branch (op: nat): M state opcode_branch :=
  returnM (byte_to_opcode_branch op).

Definition get_opcode_mem_ld_imm (op: nat): M state opcode_mem_ld_imm :=
  returnM (byte_to_opcode_mem_ld_imm op).

Definition get_opcode_mem_ld_reg (op: nat): M state opcode_mem_ld_reg :=
  returnM (byte_to_opcode_mem_ld_reg op).

Definition get_opcode_mem_st_imm (op: nat): M state opcode_mem_st_imm :=
  returnM (byte_to_opcode_mem_st_imm op).

Definition get_opcode_mem_st_reg (op: nat): M state opcode_mem_st_reg :=
  returnM (byte_to_opcode_mem_st_reg op).

Definition get_opcode (op: nat): M state opcode :=
  returnM (byte_to_opcode op).

Definition get_add (x y: val): M state val := returnM (Val.add x y).

Definition get_sub (x y: val): M state val := returnM (Val.sub x y).

Definition get_addr_ofs (x: val) (ofs: int): M state val := returnM (val_intuoflongu (Val.addl x (Val.longofint (sint32_to_vint ofs)))).

(*
Definition get_block_ptr (mr: memory_region) : M state val := returnM (block_ptr mr).*)

Definition get_start_addr (mr: memory_region): M state val := returnM (start_addr mr).

Definition get_block_size (mr: memory_region): M state val := returnM (block_size mr).

Definition get_block_perm (mr: memory_region): M state permission := returnM (block_perm mr).

Definition is_well_chunk_bool (chunk: memory_chunk) : M state bool :=
  match chunk with
  | Mint8unsigned | Mint16unsigned | Mint32 | Mint64 => returnM true
  | _ => returnM false
  end.

Definition check_mem_aux2 (mr: memory_region) (perm: permission) (addr: val) (chunk: memory_chunk): M state val := (*
  do well_chunk <- is_well_chunk_bool chunk;
    if well_chunk then *) (*
      do ptr    <- get_block_ptr mr; (**r Vptr b 0 *) *)
  do start  <- get_start_addr mr;
  do size   <- get_block_size mr;
  do mr_perm  <- get_block_perm mr;
  do lo_ofs <- get_sub addr start;
  do hi_ofs <- get_add lo_ofs (memory_chunk_to_valu32 chunk);
    if andb (andb
              (compu_lt_32 hi_ofs size)
              (andb (compu_le_32 lo_ofs (memory_chunk_to_valu32_upbound chunk))
                    (comp_eq_32 Vzero (val32_modu lo_ofs (memory_chunk_to_valu32 chunk)))))
            (perm_ge mr_perm perm) then
      returnM (Val.add (block_ptr mr) lo_ofs) (**r Vptr b lo_ofs *)
    else
      returnM Vnullptr. (*
    else
      returnM Vnullptr.*)


Fixpoint check_mem_aux (num: nat) (perm: permission) (chunk: memory_chunk) (addr: val) (mrs: MyMemRegionsType) {struct num}: M state val :=
  match num with
  | O => returnM Vnullptr
  | S n =>
    do cur_mr    <- get_mem_region n mrs;
    do check_mem <- check_mem_aux2 cur_mr perm addr chunk;
    do is_null   <- cmp_ptr32_nullM check_mem;
      if is_null then
        check_mem_aux n perm chunk addr mrs
      else
        returnM check_mem
  end.

Definition check_mem (perm: permission) (chunk: memory_chunk) (addr: val): M state val :=
  do well_chunk <- is_well_chunk_bool chunk;
    if well_chunk then
      do mem_reg_num <- eval_mrs_num;
      do mrs       <- eval_mrs_regions;
      do check_mem <- check_mem_aux mem_reg_num perm chunk addr mrs;
      do is_null   <- cmp_ptr32_nullM check_mem;
        if is_null then
          returnM Vnullptr
        else
          returnM check_mem
    else
      returnM Vnullptr.


(**r pc should be u32_t *)
Definition step_opcode_alu64 (dst64: val) (src64: val) (dst: reg) (op: nat): M state unit :=
  do opcode_alu64 <- get_opcode_alu64 op;
  match opcode_alu64 with
  | op_BPF_ADD64   => 
    do _ <- upd_reg dst (Val.addl    dst64 src64); returnM tt
  | op_BPF_SUB64   =>
    do _ <- upd_reg dst (Val.subl    dst64 src64); returnM tt
  | op_BPF_MUL64   =>
    do _ <- upd_reg dst (Val.mull    dst64 src64); returnM tt
  | op_BPF_DIV64   =>
    if compl_ne src64 (Vlong Int64.zero) then
      do _ <- upd_reg dst (val64_divlu dst64 src64); returnM tt
    else
      do _ <- upd_flag BPF_ILLEGAL_DIV; returnM tt (**r we do it for the clightproof , we could omit it later *)
  | op_BPF_OR64    =>
    do _ <- upd_reg dst (Val.orl     dst64 src64); returnM tt
  | op_BPF_AND64   =>
    do _ <- upd_reg dst (Val.andl    dst64 src64); returnM tt
  | op_BPF_LSH64   =>
    do src32 <- reg64_to_reg32 src64;
    if compu_lt_32 src32 (Vint (Int.repr 64)) then
      do _ <- upd_reg dst (Val.shll    dst64 src32); returnM tt
    else
      do _ <- upd_flag BPF_ILLEGAL_SHIFT; returnM tt
  | op_BPF_RSH64   =>
    do src32 <- reg64_to_reg32 src64;
    if compu_lt_32 src32 (Vint (Int.repr 64)) then
      do _ <- upd_reg dst (Val.shrlu   dst64 src32); returnM tt
    else
      do _ <- upd_flag BPF_ILLEGAL_SHIFT; returnM tt
  | op_BPF_NEG64    =>
    if Nat.eqb op 0x87 then
      do _ <- upd_reg dst (Val.negl    dst64); returnM tt
    else
      do _ <- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt
  | op_BPF_MOD64   =>
    if compl_ne src64 (Vlong Int64.zero) then
      do _ <- upd_reg dst (val64_modlu dst64 src64); returnM tt
    else
      do _ <- upd_flag BPF_ILLEGAL_DIV; returnM tt
  | op_BPF_XOR64   =>
    do _ <- upd_reg dst (Val.xorl      dst64 src64); returnM tt
  | op_BPF_MOV64   =>
    do _ <- upd_reg dst src64; returnM tt
  | op_BPF_ARSH64  =>
    do src32 <- reg64_to_reg32 src64;
    if compu_lt_32 src32 (Vint (Int.repr 64)) then
      do _ <- upd_reg dst (Val.shrl    dst64 src32); returnM tt
    else
      do _ <- upd_flag BPF_ILLEGAL_SHIFT; returnM tt
  | op_BPF_ALU64_ILLEGAL_INS => do _ <- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt
  end.

Definition step_opcode_alu32 (dst32: val) (src32: val) (dst: reg) (op: nat): M state unit :=
  do opcode_alu32 <- get_opcode_alu32 op;
  match opcode_alu32 with
  | op_BPF_ADD32   =>
    do _ <- upd_reg dst (Val.longofintu (Val.add dst32 src32)); returnM tt
  | op_BPF_SUB32   =>
    do _ <- upd_reg dst (Val.longofintu (Val.sub dst32 src32)); returnM tt
  | op_BPF_MUL32   =>
    do _ <- upd_reg dst (Val.longofintu (Val.mul dst32 src32)); returnM tt
  | op_BPF_DIV32   =>
    if comp_ne_32 src32 Vzero then
      do _ <- upd_reg dst (Val.longofintu (val32_divu dst32 src32)); returnM tt
    else
      upd_flag BPF_ILLEGAL_DIV
  | op_BPF_OR32   =>
    do _ <- upd_reg dst (Val.longofintu (Val.or  dst32 src32)); returnM tt
  | op_BPF_AND32   =>
    do _ <- upd_reg dst (Val.longofintu (Val.and dst32 src32)); returnM tt
  | op_BPF_LSH32   =>
    if compu_lt_32 src32 (Vint (Int.repr 32)) then
      do _ <- upd_reg dst (Val.longofintu (Val.shl dst32 src32)); returnM tt
    else
      upd_flag BPF_ILLEGAL_SHIFT
  | op_BPF_RSH32   =>
    if compu_lt_32 src32 (Vint (Int.repr 32)) then
      do _ <- upd_reg dst (Val.longofintu (Val.shru dst32 src32)); returnM tt
    else
      upd_flag BPF_ILLEGAL_SHIFT
  | op_BPF_NEG32    =>
    if Nat.eqb op 0x84 then
      do _ <- upd_reg dst (Val.longofintu (Val.neg dst32)); returnM tt
    else
      upd_flag BPF_ILLEGAL_INSTRUCTION
  | op_BPF_MOD32   =>
    if comp_ne_32 src32 Vzero then
      do _ <- upd_reg dst (Val.longofintu (val32_modu dst32 src32)); returnM tt
    else
      upd_flag BPF_ILLEGAL_DIV
  | op_BPF_XOR32   =>
    do _ <- upd_reg dst (Val.longofintu (Val.xor dst32 src32)); returnM tt
  | op_BPF_MOV32   =>
    do _ <- upd_reg dst (Val.longofintu src32); returnM tt
  | op_BPF_ARSH32  =>
    if compu_lt_32 src32 (Vint (Int.repr 32)) then
      do _ <- upd_reg dst (Val.longofint (Val.shr dst32 src32)); returnM tt
    else
      upd_flag BPF_ILLEGAL_SHIFT
  | op_BPF_ALU32_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.


(**r ofs should be sint16_t *)
Definition step_opcode_branch (dst64: val) (src64: val) (pc: int) (ofs: int) (op: nat) : M state unit :=
  do opcode_jmp <- get_opcode_branch op;
  match opcode_jmp with
  | op_BPF_JA       =>
    if Nat.eqb op 0x05 then
      do _ <- upd_pc (Int.add pc ofs); returnM tt
    else
      do _ <- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt
  | op_BPF_JEQ     =>
    if compl_eq dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JGT     =>
    if complu_gt dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JGE     =>
    if complu_ge dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JLT     =>
    if complu_lt dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JLE     =>
    if complu_le dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JSET     =>
    if complu_set dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JNE     =>
    if compl_ne dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JSGT     =>
    if compl_gt dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JSGE     =>
    if compl_ge dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JSLT     =>
    if compl_lt dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt
  | op_BPF_JSLE     =>
    if compl_le dst64 src64 then
      do _ <- upd_pc (Int.add pc ofs); returnM tt
    else
      returnM tt

  | op_BPF_CALL =>
    if Nat.eqb op 0x85 then
      do f_ptr    <- _bpf_get_call (val_intsoflongu src64);
      do is_null  <- cmp_ptr32_nullM f_ptr;
        if is_null then
          upd_flag BPF_ILLEGAL_CALL
        else
          do res  <- exec_function f_ptr;
            upd_reg R0 (Val.longofintu res)
    else
      do _ <- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt

  | op_BPF_RET =>
    if Nat.eqb op 0x95 then
      do _ <- upd_flag BPF_SUCC_RETURN; returnM tt
    else
      do _ <- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt
  | op_BPF_JMP_ILLEGAL_INS =>
      do _ <- upd_flag BPF_ILLEGAL_INSTRUCTION; returnM tt
  end.

Definition step_opcode_mem_ld_imm (imm: int) (dst64: val) (dst: reg) (op: nat): M state unit :=
  do opcode_ld <- get_opcode_mem_ld_imm op;
  match opcode_ld with
  | op_BPF_LDDW_low      =>
    do _ <- upd_reg dst (Val.longofintu (sint32_to_vint imm)); returnM tt
  | op_BPF_LDDW_high     =>
    do _ <- upd_reg dst (Val.orl dst64 (Val.shll  (Val.longofintu (sint32_to_vint imm)) (sint32_to_vint (Int.repr 32))));
      returnM tt
  | op_BPF_LDX_IMM_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step_opcode_mem_ld_reg (addr: val) (dst: reg) (op: nat): M state unit :=
  do opcode_ld <- get_opcode_mem_ld_reg op;
  match opcode_ld with
  | op_BPF_LDXW      =>
    do addr_ptr <- check_mem Readable Mint32 addr;
    do is_null   <- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <- load_mem Mint32 addr_ptr;
        do _ <- upd_reg dst v; returnM tt
  | op_BPF_LDXH      =>
    do addr_ptr <- check_mem Readable Mint16unsigned addr;
    do is_null   <- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <- load_mem Mint16unsigned addr_ptr;
        do _ <- upd_reg dst v; returnM tt
  | op_BPF_LDXB      =>
    do addr_ptr <- check_mem Readable Mint8unsigned addr;
    do is_null   <- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <- load_mem Mint8unsigned addr_ptr;
        do _ <- upd_reg dst v; returnM tt
  | op_BPF_LDXDW     =>
    do addr_ptr <- check_mem Readable Mint64 addr;
    do is_null   <- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do v <- load_mem Mint64 addr_ptr;
        do _ <- upd_reg dst v; returnM tt
  | op_BPF_LDX_REG_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step_opcode_mem_st_imm (imm: val) (addr: val) (dst: reg) (op: nat): M state unit :=
  do opcode_st <- get_opcode_mem_st_imm op;
  match opcode_st with
  | op_BPF_STW       =>
    do addr_ptr <- check_mem Writable Mint32 addr;
    do is_null   <- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_imm addr_ptr Mint32 imm; returnM tt
  | op_BPF_STH       =>
    do addr_ptr <- check_mem Writable Mint16unsigned addr;
    do is_null   <- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_imm addr_ptr Mint16unsigned imm; returnM tt
  | op_BPF_STB       =>
    do addr_ptr <- check_mem Writable Mint8unsigned addr;
    do is_null   <- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_imm addr_ptr Mint8unsigned imm; returnM tt
  | op_BPF_STDW      =>
    do addr_ptr <- check_mem Writable Mint64 addr;
    do is_null   <- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_imm addr_ptr Mint64 imm; returnM tt
  | op_BPF_ST_IMM_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step_opcode_mem_st_reg (src64: val) (addr: val) (dst: reg) (op: nat): M state unit :=
  do opcode_st <- get_opcode_mem_st_reg op;
  match opcode_st with
  | op_BPF_STXW      =>
    do addr_ptr <- check_mem Writable Mint32 addr;
    do is_null   <- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_reg addr_ptr Mint32 src64; returnM tt
  | op_BPF_STXH      =>
    do addr_ptr <- check_mem Writable Mint16unsigned addr;
    do is_null   <- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_reg addr_ptr Mint16unsigned src64; returnM tt
  | op_BPF_STXB      =>
    do addr_ptr <- check_mem Writable Mint8unsigned addr;
    do is_null   <- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_reg addr_ptr Mint8unsigned src64; returnM tt
  | op_BPF_STXDW     =>
    do addr_ptr <- check_mem Writable Mint64 addr;
    do is_null   <- cmp_ptr32_nullM addr_ptr;
      if is_null then
        upd_flag BPF_ILLEGAL_MEM
      else
        do _ <- store_mem_reg addr_ptr Mint64 src64; returnM tt
  | op_BPF_STX_REG_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Definition step: M state unit :=
  do pc   <- eval_pc;
  do ins  <- eval_ins pc;
  do op   <- get_opcode_ins ins;
  do opc  <- get_opcode op;
  do dst  <- get_dst ins;
  match opc with
  | op_BPF_ALU64   =>
    do dst64  <- eval_reg dst;
      (**r #define BPF_INSTRUCTION_ALU_S_MASK      0x08 *)
    do src64  <- get_src64 op ins;
      step_opcode_alu64 dst64 src64 dst op                     (**r 0xX7 / 0xXf *)
  | op_BPF_ALU32   =>
    do dst64  <- eval_reg dst;
    do dst32  <- reg64_to_reg32 dst64;
      (**r #define BPF_INSTRUCTION_ALU_S_MASK      0x08 *)
    do src32  <- get_src32 op ins;
      step_opcode_alu32 dst32 src32 dst op                     (**r 0xX4 / 0xXc *)
  | op_BPF_Branch  =>
    do dst64  <- eval_reg dst;
    do ofs    <- get_offset ins;
      (**r #define BPF_INSTRUCTION_ALU_S_MASK      0x08 *)
    do src64  <- get_src64 op ins;
      step_opcode_branch dst64 src64 pc ofs op                    (**r 0xX5 / 0xXd *)
  | op_BPF_Mem_ld_imm  =>
    do dst64  <- eval_reg dst;
    do imm    <- get_immediate ins;
    step_opcode_mem_ld_imm imm dst64 dst op              (**r 0xX8 *)
  | op_BPF_Mem_ld_reg  =>
    do src    <- get_src ins;
    do src64  <- eval_reg src;
    do ofs    <- get_offset ins;
    do addr   <- get_addr_ofs src64 ofs;
    step_opcode_mem_ld_reg addr dst op       (**r 0xX1/0xX9 *)
  | op_BPF_Mem_st_imm  =>
    do dst64  <- eval_reg dst;
    do ofs    <- get_offset ins;
    do imm    <- get_immediate ins;
    do addr   <- get_addr_ofs dst64 ofs;
    step_opcode_mem_st_imm (sint32_to_vint imm) addr dst op       (**r 0xX2/0xXa *)
  | op_BPF_Mem_st_reg  =>
    do dst64  <- eval_reg dst;
    do src    <- get_src ins;
    do src64  <- eval_reg src;
    do ofs    <- get_offset ins;
    do addr <- get_addr_ofs dst64 ofs;
    step_opcode_mem_st_reg src64 addr dst op       (**r 0xX3/0xXb *)
  | op_BPF_ILLEGAL_INS => upd_flag BPF_ILLEGAL_INSTRUCTION
  end.

Fixpoint bpf_interpreter_aux (fuel: nat) {struct fuel}: M state unit :=
  match fuel with
  | O => upd_flag BPF_ILLEGAL_LEN
  | S fuel0 =>
    do len  <- eval_ins_len;
    do pc <- eval_pc;
      if (Int.ltu pc len) then (**r pc < len: pc is less than the length of l *)
        do _ <- step;
        do f <- eval_flag;
          if flag_eq f BPF_OK then
            do len0  <- eval_ins_len;
            do pc0 <- eval_pc;
              if (Int.ltu (Int.add pc0 Int.one) len0) then
                do _ <- upd_pc_incr;
                  bpf_interpreter_aux fuel0
              else
                upd_flag BPF_ILLEGAL_LEN
          else
            returnM tt
      else
        upd_flag BPF_ILLEGAL_LEN
  end.

Definition bpf_interpreter (fuel: nat): M state val :=
  do mrs      <- eval_mrs_regions;
  do bpf_ctx  <- get_mem_region 0 mrs;
  do start  <- get_start_addr bpf_ctx;
  do _        <- upd_reg R1 (Val.longofintu start); (**r let's say the ctx memory region is also be the first one *)
  do _        <- bpf_interpreter_aux fuel;
  do f        <- eval_flag;
    if flag_eq f BPF_SUCC_RETURN then
      do res  <- eval_reg R0;
        returnM res
    else
      returnM (Vlong Int64.zero).

Close Scope monad_scope.