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

From compcert Require Import Memory Memtype Integers Values Ctypes AST.
From Coq Require Import ZArith Lia.

From bpf.comm Require Import Flag rBPFValues Regs BinrBPF State Monad MemRegion rBPFAST rBPFMemType rBPFMonadOp.
From bpf.model Require Import Syntax Decode.

Open Scope Z_scope.
Open Scope monad_scope.


Definition eval_src (s:reg+imm): M state val :=
  match s with
  | inl r => eval_reg r
  | inr i => returnM (Val.longofint (sint32_to_vint i)) (**r the immediate is always int *)
  end.

Definition eval_reg32 (r:reg): M state val :=
  do v <- eval_reg r; returnM (val_intuoflongu v).

Definition eval_src32 (s:reg+imm): M state val :=
  match s with
  | inl r => eval_reg32 r
  | inr i => returnM (sint32_to_vint i) (**r the immediate is always int *)
  end.

(*
Definition _to_vlong (v: val): val :=
  match v with
  | Vlong n => Vlong n (**r Mint64 *)
  | Vint  n => Vlong (Int64.repr (Int.unsigned n)) (**r Mint8unsigned, Mint16unsigned, Mint32 *) (* (u64) v *)
  | _       => Vundef
  end.

Definition vlong_to_vint_or_vlong (chunk: memory_chunk) (v: val): val :=
  match v with
  | Vlong n =>
    match chunk with
    | Mint8unsigned | Mint16unsigned | Mint32 => Vint (Int.repr (Int64.unsigned n))
    | Mint64 => Vlong n
    | _      => Vundef
    end
  | _       => Vundef
  end. *)

Lemma intu_to_long_intu_eq:
  forall i j, i = Vint j -> val_intuoflongu (Val.longofintu i) = i.
Proof.
  unfold Val.longofintu, val_intuoflongu.
  intros.
  rewrite H.
  assert (H1: Int64.unsigned (Int64.repr (Int.unsigned j)) = Int.unsigned j).
  - apply Int64.unsigned_repr.
    assert (Hrange: 0 <= Int.unsigned j <= Int.max_unsigned). { apply Int.unsigned_range_2. }
    assert (Hmax: Int.max_unsigned <= Int64.max_unsigned).
    + unfold Int.max_unsigned, Int64.max_unsigned.
    unfold Int.modulus, Int64.modulus.
    unfold Int.wordsize, Int64.wordsize.
    unfold Wordsize_32.wordsize, Wordsize_64.wordsize.
    simpl.
    lia.
    + lia.
  - rewrite H1.
    apply f_equal.
    apply Int.repr_unsigned.
Qed.
Close Scope Z_scope.

Definition val_intuoflonguM (vl: val) : M state val := returnM (val_intuoflongu vl).

Definition step_alu_binary_operation (a: arch) (bop: binOp) (d :reg) (s: reg+imm): M state unit :=
  match a with
  | A32 => 
    do d32 <- eval_reg32 d;
    do s32 <- eval_src32 s; (**r (u32) DST, (u32) SRC/IMM *)
    match bop with
    | BPF_ADD  => upd_reg d (Val.longofintu (Val.add  d32 s32))
    | BPF_SUB  => upd_reg d (Val.longofintu (Val.sub  d32 s32))
    | BPF_MUL  => upd_reg d (Val.longofintu (Val.mul  d32 s32))
    | BPF_DIV  => if comp_ne_32 s32 Vzero then (** run-time checking *)
                    match Val.divu d32 s32 with (**r Val.divu... *)
                    | Some res => upd_reg d (Val.longofintu res)
                    | None     => errorM
                    end
                  else
                    upd_flag BPF_ILLEGAL_DIV
    | BPF_OR   => upd_reg d (Val.longofintu (Val.or   d32 s32))
    | BPF_AND  => upd_reg d (Val.longofintu (Val.and  d32 s32))
    | BPF_LSH  => if compu_lt_32 s32 (Vint (Int.repr 32)) then
                    upd_reg d (Val.longofintu (Val.shl d32 s32))
                  else
                    upd_flag BPF_ILLEGAL_SHIFT  (**r if 's' of 'shl d s' is 's > 32', then there is a acceptable error *)
    | BPF_RSH  => if compu_lt_32 s32 (Vint (Int.repr 32)) then
                    upd_reg d (Val.longofintu (Val.shru d32 s32))
                  else
                    upd_flag BPF_ILLEGAL_SHIFT  (**r if 's' of 'shru d s' is 's > 32', then there is a acceptable error *)
    | BPF_MOD  => if comp_ne_32 s32 Vzero then (** run-time checking *)
                    match Val.modu d32 s32 with
                    | Some res => upd_reg d (Val.longofintu res)
                    | None     => errorM
                    end
                  else
                    upd_flag BPF_ILLEGAL_DIV
    | BPF_XOR  => upd_reg d (Val.longofintu (Val.xor  d32 s32))
    | BPF_MOV  => upd_reg d (Val.longofintu s32)
    | BPF_ARSH => if compu_lt_32 s32 (Vint (Int.repr 32)) then
                    upd_reg d (Val.longofint (Val.shr  d32 s32))
                  else
                    upd_flag BPF_ILLEGAL_SHIFT (**r if 's' of 'shr d s' is 's > 32', then there is a acceptable error *)
    end
  | A64 =>
      do d64 <- eval_reg d;
      do s64 <- eval_src s;
      match bop with
      | BPF_ADD  => upd_reg d (Val.addl  d64 s64)
      | BPF_SUB  => upd_reg d (Val.subl  d64 s64)
      | BPF_MUL  => upd_reg d (Val.mull  d64 s64)
      | BPF_DIV  => if compl_ne s64 val64_zero then (** run-time checking *)
                      match Val.divlu d64 s64 with (**r run-time checking *)
                      | Some res => upd_reg d res
                      | None     => errorM
                      end
                    else
                      upd_flag BPF_ILLEGAL_DIV
      | BPF_OR   => upd_reg d (Val.orl   d64 s64)
      | BPF_AND  => upd_reg d (Val.andl  d64 s64)
      (**r we must do type-checking of 's64' first, to ensure it is exactly 'vint' *)
      | BPF_LSH  => if compu_lt_32 (val_intuoflongu s64) (Vint (Int.repr 64)) then
                      upd_reg d (Val.shll d64 (val_intuoflongu s64))
                    else
                      upd_flag BPF_ILLEGAL_SHIFT  (**r if 's' of 'shl d s' is 's > 64', then there is a acceptable error *)
      | BPF_RSH  => if compu_lt_32 (val_intuoflongu s64) (Vint (Int.repr 64)) then
                      upd_reg d (Val.shrlu d64 (val_intuoflongu s64))
                    else
                      upd_flag BPF_ILLEGAL_SHIFT  (**r if 's' of 'shr d s' is 's > 64', then there is a acceptable error *)
      | BPF_MOD  => if compl_ne s64 val64_zero then (** run-time checking *)
                      match Val.modlu d64 s64 with (**r run-time checking *)
                      | Some res => upd_reg d res
                      | None     => errorM
                      end
                    else
                      upd_flag BPF_ILLEGAL_DIV
(**r to avoid translate option type to C, the refinement version defines a new division:
Definition val64_divlu (x y: val): val :=
  match Val.divlu x y with
  | Some res => res
  | None => Vundef
  end.
And the semantics function does:
  | op_BPF_DIV64   =>
    if compl_ne src64 val64_zero then
      do _ <- upd_reg dst (val64_divlu dst64 src64);
        upd_flag BPF_OK
    else
      upd_flag BPF_ILLEGAL_DIV

 *)
      | BPF_XOR  => upd_reg d (Val.xorl  d64 s64)
      | BPF_MOV  => upd_reg d s64
      | BPF_ARSH => if compu_lt_32 (val_intuoflongu s64) (Vint (Int.repr 64)) then
                      upd_reg d (Val.shrl d64 (val_intuoflongu s64))
                    else
                      upd_flag BPF_ILLEGAL_SHIFT  (**r if 's' of 'shru d s' is 's > 64', then there is a acceptable error? *)
      end
  end.

Definition step_branch_cond (c: cond) (d: reg) (s: reg+imm): M state bool :=
  do dst <- eval_reg d;
  do src <- eval_src s;
  returnM (match c with
  | Eq  => compl_eq   dst src
  | SEt => complu_set dst src
  | Ne  => compl_ne   dst src
  | Gt sign => 
    match sign with
    | Unsigned => complu_gt dst src
    | Signed   => compl_gt  dst src
    end
  | Ge sign =>
    match sign with
    | Unsigned => complu_ge dst src
    | Signed   => compl_ge  dst src
    end
  | Lt sign => 
    match sign with
    | Unsigned => complu_lt dst src
    | Signed   => compl_lt  dst src
    end
  | Le sign => 
    match sign with
    | Unsigned => complu_le dst src
    | Signed   => compl_le  dst src
    end
  end).

Definition get_add (x y: val): M state val := returnM (Val.add x y).

Definition get_sub (x y: val): M state val := returnM (Val.sub x y).

Definition get_addr_ofs (x: val) (ofs: int): M state val := returnM (val_intuoflongu (Val.addl x (Val.longofint (sint32_to_vint ofs)))).

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
    if well_chunk then *)
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
      returnM Vnullptr. *)

Fixpoint check_mem_aux (num: nat) (perm: permission) (chunk: memory_chunk) (addr: val) (mrs: MyMemRegionsType) {struct num}: M state val :=
  match num with
  | O => returnM Vnullptr
  | S n =>
    do cur_mr   <- get_mem_region n mrs;
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
      do mrs      <- eval_mrs_regions;
      do check_mem <- check_mem_aux mem_reg_num perm chunk addr mrs;
      do is_null   <- cmp_ptr32_nullM check_mem;
        if is_null then
          returnM Vnullptr
        else
          returnM check_mem
    else
      returnM Vnullptr.

Definition step_load_x_operation (chunk: memory_chunk) (d:reg) (s:reg) (ofs:off): M state unit :=
  do m    <- eval_mem;
  do mrs  <- eval_mem_regions;
  do sv   <- eval_reg s;
  do addr <- get_addr_ofs sv ofs;
  do ptr  <- check_mem Readable chunk addr;
  do is_null   <- cmp_ptr32_nullM ptr;
    if is_null then
      upd_flag BPF_ILLEGAL_MEM
    else
      do v <- load_mem chunk ptr;
      do _ <- upd_reg d v; returnM tt
.

Definition step_store_operation (chunk: memory_chunk) (d: reg) (s: reg+imm) (ofs: off): M state unit :=
  do m    <- eval_mem;
  do mrs  <- eval_mem_regions;
  do dv   <- eval_reg d;
  do addr <- get_addr_ofs dv ofs;

    match s with
    | inl r =>
      do src <- eval_reg r;
      do ptr  <- check_mem Writable chunk addr;
      do is_null   <- cmp_ptr32_nullM ptr;
        if is_null then
          upd_flag BPF_ILLEGAL_MEM
        else
          do _ <- store_mem_reg ptr chunk src; returnM tt
    | inr i =>
      do ptr  <- check_mem Writable chunk addr;
      do is_null   <- cmp_ptr32_nullM ptr;
        if is_null then
          upd_flag BPF_ILLEGAL_MEM
        else
          do _ <- store_mem_imm ptr chunk (sint32_to_vint i); returnM tt
    end
.

Definition decodeM (i: int64) : M state instruction := fun st =>
  match (decode i) with
  | Some ins => Some (ins, st)
  | None => None
  end.

Definition get_immediate (ins:int64): M state int := returnM (get_immediate ins).

Definition step : M state unit :=
  do pc   <- eval_pc;
  do ins64<- eval_ins pc;
  do ins  <- decodeM ins64;
    match ins with
    | BPF_NEG a d =>
      match a with
      | A32 => do d32 <- eval_reg d;
                 upd_reg d (Val.longofintu (Val.neg (val_intuoflongu d32)))
      | A64 => do d64 <- eval_reg d;
                 upd_reg d (Val.negl d64)
      end

    | BPF_BINARY a bop d s =>
      step_alu_binary_operation a bop d s

    | BPF_JA ofs => upd_pc (Int.add pc ofs)
    | BPF_JUMP c d s ofs =>
      do cond <- step_branch_cond c d s;
      if cond then
        upd_pc (Int.add pc ofs)
      else
        returnM tt

    | BPF_LDDW_low d i =>
      do _   <- upd_reg d (Val.longofintu (sint32_to_vint i));
        returnM tt
    | BPF_LDDW_high d i =>
      do d64 <- eval_reg d;
      do _   <- upd_reg d (Val.orl d64 (Val.shll  (Val.longofintu (sint32_to_vint i)) (sint32_to_vint (Int.repr 32))));
        returnM tt
    | BPF_LDX chunk d s ofs =>
      step_load_x_operation chunk d s ofs
    | BPF_ST chunk d s ofs =>
      step_store_operation chunk d s ofs

    | BPF_CALL i => (**r TODO: is this type-casting correct? this style is because of DxInstructions... *)
      do f_ptr    <- _bpf_get_call (Vint ((Int.repr (Int64.unsigned (Int64.repr (Int.signed i))))));
      do is_null  <- cmp_ptr32_nullM f_ptr;
        if is_null then
          upd_flag BPF_ILLEGAL_CALL
        else
          do res  <- exec_function f_ptr;
            upd_reg R0 (Val.longofintu res)
    | BPF_RET    => upd_flag BPF_SUCC_RETURN
    | BPF_ERR    => upd_flag BPF_ILLEGAL_INSTRUCTION
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
            do len0 <- eval_ins_len;
            do pc0 <- eval_pc; (**r step may modify pc: lddw *)
              if (Int.ltu (Int.add pc0 Int.one) len0) then (**r pc + 1 < len *)
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
  do mrs      <- eval_mem_regions;
  do bpf_ctx  <- get_mem_region 0 mrs;
  do start  <- get_start_addr bpf_ctx;
  do _        <- upd_reg R1 (Val.longofintu start); (**r let's say the ctx memory region is also be the first one *)
  do _        <- bpf_interpreter_aux fuel;
  do f        <- eval_flag;
    if flag_eq f BPF_SUCC_RETURN then
      do res  <- eval_reg R0;
        returnM res
    else
      returnM val64_zero.

Close Scope monad_scope.