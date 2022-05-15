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

From compcert Require Import Integers Values AST Memory Memtype.
From bpf.comm Require Import BinrBPF State Monad rBPFMonadOp.
From bpf.model Require Import Syntax Semantics.
From bpf.isolation Require Import CommonISOLib AlignChunk RegsInv MemInv VerifierOpcode VerifierInv CheckMem StateInv IsolationLemma Isolation1.

From Coq Require Import ZArith Lia.

Open Scope Z_scope.

Lemma inv_avoid_step_undef:
  forall st st0
    (Hpc: Int.cmpu Clt (State.eval_pc st) (Int.repr (Z.of_nat (ins_len st)))%bool = true)
    (Hlen_max: (length (ins st) <= Z.to_nat Ptrofs.max_unsigned)%nat)
    (Hlen: (ins_len st) = (List.length (ins st)))
    (Hreg: register_inv st)
    (Hmem: memory_inv st)
    (Hst0: state_include st0 st)
    (Hver: bpf_verifier st0 = true),
      step st <> None.
Proof.
  intros.
  unfold step.
  unfold_monad.
  (**r if-false is impossible because of the interpreter *)
  rewrite Hpc.
  unfold state_include in Hst0.
  destruct Hst0 as (Hst0 & Hst1).

  assert (Hverifier := Hver).
  unfold bpf_verifier in Hver.
  match goal with
  | H: (if ?X then _ else _) = _ |- _ =>
    destruct X eqn: Hlen_low;[| inversion H]
  end.
  rewrite Hst0 in *.
  rewrite Hlen in *.

  assert (Hlen_range: (Z.of_nat (length (ins st))) <= Ptrofs.max_unsigned). {
    apply inj_le in Hlen_max.
    rewrite Z2Nat.id in Hlen_max.
    assumption.
    change Ptrofs.max_unsigned with 4294967295.
    lia.
  }

  apply Cle_Zle_iff in Hlen_low.
  change (Int.unsigned Int.one) with 1 in Hlen_low.
  rewrite Int.unsigned_repr in Hlen_low; [| change Int.max_unsigned with Ptrofs.max_unsigned; lia].
  match goal with
  | H: (if ?X then _ else _) = _ |- _ =>
    destruct X eqn: Hlen_high;[ apply Cle_Zle_iff in Hlen_high | inversion H]
  end.
  

(*
  assert (Hlen_max: (length (ins st) <= Z.to_nat Ptrofs.max_unsigned)%nat). {
    clear - Hlen_high.
    assert (Hle: Z.of_nat (length (ins st)) <= Z.of_nat (Z.to_nat Ptrofs.max_unsigned / 8)) by lia.
    rewrite div_Zdiv in Hle; [| lia].
    change (Z.of_nat 8) with 8 in Hle.
    rewrite Z2Nat.id in Hle; [ | change Ptrofs.max_unsigned with 4294967295; lia].
    apply Zmult_gt_0_le_compat_r with (p:=8) in Hle; [| lia].
    change Ptrofs.max_unsigned with 4294967295 in *.
    change (4294967295 / 8 * 8) with 4294967288 in Hle.
    lia.
  } *)

  assert (Hlen_maxZ: Z.of_nat (length (ins st)) <= Ptrofs.max_unsigned) by lia.

  unfold State.eval_pc in Hpc.
  unfold State.eval_pc.
  unfold State.eval_ins, List64.MyListIndexs32, List64.MyList.index_s32.

  remember (Z.to_nat (Int.unsigned (pc_loc st))) as pc.

  assert (Hpc_range: (pc < List.length (ins st))%nat). {
    rewrite Heqpc.
    clear - Hpc Hlen_maxZ.
    unfold Int.cmpu in Hpc.
    apply Clt_Zlt_iff in Hpc.
    rewrite Int.unsigned_repr in Hpc.
    assert (Hpc_z: (Z.to_nat (Int.unsigned (pc_loc st)) < Z.to_nat (Z.of_nat (length (ins st))))%nat). {
      apply Z2Nat.inj_lt; auto.
      apply Int_unsigned_ge_0.
      lia.
    }
    rewrite Nat2Z.id in Hpc_z.
    assumption.
    change Int.max_unsigned with Ptrofs.max_unsigned.
    lia.
  }

  assert (Hpc_rangeZ: Z.of_nat pc <  Z.of_nat (length (ins st))) by lia.
  apply List.nth_error_nth' with (d:=Int64.zero) in Hpc_range as Hnth.
  rewrite Hnth in *.

  unfold Decode.decode.

  apply bpf_verifier_implies with (pc := pc) (op := get_opcode (List.nth pc (ins st) Int64.zero)) (ins := List.nth pc (ins st) Int64.zero) in Hverifier; [
    |
    rewrite Hst0, Hst1; reflexivity |
    rewrite Hst0; assumption |
    reflexivity |
    unfold List64.MyListIndexs32, List64.MyList.index_s32;
  rewrite Hst1, Int.unsigned_repr; [rewrite Nat2Z.id, Hnth; reflexivity | change Int.max_unsigned with Ptrofs.max_unsigned; lia]
  ].

  unfold bpf_verifier_aux2, nat_to_opcode in Hverifier.

  remember (Nat.land (get_opcode (List.nth pc (ins st) Int64.zero)) 7) as Hand.

  clear HeqHand.
  destruct Hand.
  { (**LD_IMM *)
    unfold Decode.get_instruction_ld.
    rewrite opcode_and_255.

    remember (get_opcode (List.nth pc (ins st) Int64.zero)) as Hand24.

    destruct nat_to_opcode_load_imm; [| inversion Hverifier].
    apply verifier_inv_is_well_dst in Hverifier.
    destruct Hverifier as (dst & Hdst).
    rewrite Hdst.

    do 16 (destruct Hand24; [intro Hfalse; inversion Hfalse |]).
    destruct Hand24.
    - unfold rBPFValues.sint32_to_vint; simpl.
      change (Int64.iwordsize') with (Int.repr 64).
      change (Int.ltu (Int.repr 32) (Int.repr 64)) with true.
      simpl.
      apply reg_inv_eval_reg with (r:= dst) in Hreg as Hdst_reg.
      destruct Hdst_reg as (i & Hdst_reg).
      rewrite Hdst_reg.
      simpl.
      intro Hfalse; inversion Hfalse.
    - do 7 (destruct Hand24; [intro Hfalse; inversion Hfalse |]).
      destruct Hand24.
      + unfold rBPFValues.sint32_to_vint; simpl.
        intro Hfalse; inversion Hfalse.
      + intro Hfalse; inversion Hfalse.
  }

  destruct Hand.
  { (**r LD_REG *)
    unfold Decode.get_instruction_ldx.
    rewrite opcode_and_255.

    remember (get_opcode (List.nth pc (ins st) Int64.zero)) as Hand.

    destruct nat_to_opcode_load_reg; [| inversion Hverifier].
    destruct is_well_dst eqn: Hdst; [| inversion Hverifier].

    apply verifier_inv_is_well_dst in Hdst.
    destruct Hdst as (dst & Hdst).
    rewrite Hdst.

    apply verifier_inv_is_well_src in Hverifier.
    destruct Hverifier as (src & Hsrc).
    rewrite Hsrc.

    unfold step_load_x_operation.
    unfold eval_mem, eval_mem_regions, eval_reg, get_addr_ofs.
    unfold bindM, returnM.
    unfold rBPFValues.val_intuoflongu, rBPFValues.sint32_to_vint.
    unfold Val.longofint.
    eapply reg_inv_eval_reg in Hreg.
    destruct Hreg as (i & Hreg).
    do 97 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P in Hmem as Hcheck_mem; [| constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember ((check_memP Readable Mint32
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (get_offset (List.nth pc (ins st) Int64.zero))))))))
         st)) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          eapply check_mem_load in Hcheck_mem; eauto.
          unfold load_mem, State.load_mem.
          destruct Hcheck_mem as (res & Hcheck_mem & His_long).
          rewrite Hcheck_mem.
          unfold is_vlong_or_vint in His_long.
          unfold _to_vlong.
          destruct res; inversion His_long.
          unfold upd_reg.
          intro Hfalse; inversion Hfalse.

          unfold upd_reg.
          intro Hfalse; inversion Hfalse.
          simpl. constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P in Hmem as Hcheck_mem; [| constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember ((check_memP Readable Mint16unsigned
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (get_offset (List.nth pc (ins st) Int64.zero))))))))
         st)) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          eapply check_mem_load in Hcheck_mem; eauto.
          unfold load_mem, State.load_mem.
          destruct Hcheck_mem as (res & Hcheck_mem & His_long).
          rewrite Hcheck_mem.
          unfold is_vlong_or_vint in His_long.
          unfold _to_vlong.
          destruct res; inversion His_long.
          unfold upd_reg.
          intro Hfalse; inversion Hfalse.

          unfold upd_reg.
          intro Hfalse; inversion Hfalse.
          simpl. constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P in Hmem as Hcheck_mem; [| constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember ((check_memP Readable Mint8unsigned
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (get_offset (List.nth pc (ins st) Int64.zero))))))))
         st)) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          eapply check_mem_load in Hcheck_mem; eauto.
          unfold load_mem, State.load_mem.
          destruct Hcheck_mem as (res & Hcheck_mem & His_long).
          rewrite Hcheck_mem.
          unfold is_vlong_or_vint in His_long.
          unfold _to_vlong.
          destruct res; inversion His_long.
          unfold upd_reg.
          intro Hfalse; inversion Hfalse.

          unfold upd_reg.
          intro Hfalse; inversion Hfalse.
          simpl. constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P in Hmem as Hcheck_mem; [| constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember ((check_memP Readable Mint64
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (get_offset (List.nth pc (ins st) Int64.zero))))))))
         st)) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          eapply check_mem_load in Hcheck_mem; eauto.
          unfold load_mem, State.load_mem.
          destruct Hcheck_mem as (res & Hcheck_mem & His_long).
          rewrite Hcheck_mem.
          unfold Mem.loadv in Hcheck_mem.
          apply Mem.load_type in Hcheck_mem.
          unfold Val.has_type in Hcheck_mem; simpl in Hcheck_mem.
          destruct res; inversion His_long; inversion Hcheck_mem.
          unfold upd_reg.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    intro Hfalse; inversion Hfalse.
  }

  destruct Hand.
  { (**r ST_IMM *)
    unfold Decode.get_instruction_st, bindM, returnM.
    rewrite opcode_and_255.

    destruct nat_to_opcode_store_imm; [| inversion Hverifier].
    apply verifier_inv_is_well_dst in Hverifier.
    destruct Hverifier as (dst & Hdst).
    rewrite Hdst.

    unfold step_store_operation.
    unfold eval_mem, eval_mem_regions, eval_reg, get_addr_ofs.
    unfold bindM, returnM.
    unfold rBPFValues.val_intuoflongu, Val.longofint, rBPFValues.sint32_to_vint.

    eapply reg_inv_eval_reg in Hreg.
    destruct Hreg as (i & Hreg).

    remember (get_opcode (List.nth pc (ins st) Int64.zero)) as Hand.
    do 98 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint32
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          remember (BinrBPF.get_immediate
                 (List.nth (Z.to_nat (Int.unsigned (pc_loc st))) (ins st) Int64.zero)) as imm.
          eapply check_mem_store with (v:= Vint imm) in Hcheck_mem; eauto.
          unfold store_mem_imm, State.store_mem_imm.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint16unsigned
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (BinrBPF.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          remember (BinrBPF.get_immediate
                 (List.nth (Z.to_nat (Int.unsigned (pc_loc st))) (ins st) Int64.zero)) as imm.
          eapply check_mem_store with (v:= Vint imm) in Hcheck_mem; eauto.
          unfold store_mem_imm, State.store_mem_imm.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint8unsigned
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (BinrBPF.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          remember (BinrBPF.get_immediate
                 (List.nth (Z.to_nat (Int.unsigned (pc_loc st))) (ins st) Int64.zero)) as imm.
          eapply check_mem_store with (v:= Vint imm) in Hcheck_mem; eauto.
          unfold store_mem_imm, State.store_mem_imm.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint64
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add i
                     (Int64.repr
                        (Int.signed (BinrBPF.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          remember (BinrBPF.get_immediate
                 (List.nth (Z.to_nat (Int.unsigned (pc_loc st))) (ins st) Int64.zero)) as imm.
          eapply check_mem_store with (v:= Vint imm) in Hcheck_mem; eauto.
          unfold store_mem_imm, State.store_mem_imm.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    intro Hfalse; inversion Hfalse.
  }

  destruct Hand.
  { (**r ST_REG *)
    unfold Decode.get_instruction_stx, bindM, returnM.
    rewrite opcode_and_255.

    destruct nat_to_opcode_store_reg; [| inversion Hverifier].
    destruct is_well_dst eqn: Hdst; [| inversion Hverifier].

    apply verifier_inv_is_well_dst in Hdst.
    destruct Hdst as (dst & Hdst).
    rewrite Hdst.

    apply verifier_inv_is_well_src in Hverifier.
    destruct Hverifier as (src & Hsrc).
    rewrite Hsrc.

    unfold step_store_operation.
    unfold eval_mem, eval_mem_regions, eval_reg, get_addr_ofs.
    unfold bindM, returnM.
    unfold rBPFValues.val_intuoflongu, Val.longofint, rBPFValues.sint32_to_vint.

    eapply reg_inv_eval_reg with (r:= dst) in Hreg as Hreg_dst.
    eapply reg_inv_eval_reg with (r:= src) in Hreg as Hreg_src.
    destruct Hreg_dst as (r_dst & Hreg_dst).
    destruct Hreg_src as (r_src & Hreg_src).

    remember (BinrBPF.get_opcode (List.nth pc (ins st) Int64.zero)) as Hand.
    do 99 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg_dst.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint32
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add r_dst
                     (Int64.repr
                        (Int.signed (BinrBPF.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      unfold store_mem_reg, State.store_mem_reg.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          rewrite Hreg_src.
          eapply check_mem_store with (v:= Vlong r_src) in Hcheck_mem; eauto.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold Mem.storev, vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg_dst.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint16unsigned
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add r_dst
                     (Int64.repr
                        (Int.signed (BinrBPF.get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      unfold store_mem_reg, State.store_mem_reg.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          rewrite Hreg_src.
          eapply check_mem_store with (v:= Vlong r_src) in Hcheck_mem; eauto.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold Mem.storev, vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg_dst.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint8unsigned
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add r_dst
                     (Int64.repr
                        (Int.signed (get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      unfold store_mem_reg, State.store_mem_reg.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          rewrite Hreg_src.
          eapply check_mem_store with (v:= Vlong r_src) in Hcheck_mem; eauto.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold Mem.storev, vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    do 7 (destruct Hand; [intro Hfalse; inversion Hfalse |]).
    destruct Hand.
    {
      rewrite Hreg_dst.
      simpl.
      eapply check_memM_P with (perm := Writable) in Hmem as Hcheck_mem; [|constructor].
      rewrite Hcheck_mem.
      unfold cmp_ptr32_nullM, bindM, returnM.

      remember (check_memP Writable Mint64
         (Vint
            (Int.repr
               (Int64.unsigned
                  (Int64.add r_dst
                     (Int64.repr
                        (Int.signed (get_offset (List.nth pc (ins st) Int64.zero))))))))
         st) as res.
      symmetry in Heqres.
      unfold State.eval_mem.
      unfold store_mem_reg, State.store_mem_reg.
      eapply mem_inv_check_mem_valid_pointer in Heqres; eauto.
      - destruct Heqres as [(b & ofs & Hptr & Hvalid)| Hptr]; subst.
        + simpl.
          rewrite Hvalid.
          rewrite Int.eq_true.
          simpl.
          rewrite Hreg_src.
          eapply check_mem_store with (v:= Vlong r_src) in Hcheck_mem; eauto.
          destruct Hcheck_mem as (res & Hcheck_mem & Hmem').
          unfold Mem.storev, vlong_or_vint_to_vint_or_vlong in Hcheck_mem.
          rewrite Hcheck_mem.
          intro Hfalse; inversion Hfalse.

          simpl. constructor.
          unfold is_vlong_or_vint; constructor.
          intro Hfalse; inversion Hfalse.
        + unfold rBPFValues.cmp_ptr32_null.
          unfold Val.cmpu_bool.
          change Vnullptr with (Vint Int.zero); simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
      - constructor.
    }
    intro Hfalse; inversion Hfalse.
  }

  destruct Hand.
  { (**r ALU32 *)
    remember (BinrBPF.get_opcode (List.nth pc (ins st) Int64.zero)) as Hand.

    unfold is_not_div_by_zero, is_shift_range in Hverifier.
    destruct nat_to_opcode_alu eqn: Halu; [

    apply Bool.andb_true_iff in Hverifier;
    destruct Hverifier as (Hdst & Hzero);
    apply verifier_inv_is_well_dst in Hdst;
    destruct Hdst as (dst & Hdst);
    rewrite Hdst;
    unfold Int.cmp in Hzero |

    apply Bool.andb_true_iff in Hverifier;
    destruct Hverifier as (Hdst & Hshift);
    apply verifier_inv_is_well_dst in Hdst;
    destruct Hdst as (dst & Hdst);
    rewrite Hdst |

    apply verifier_inv_is_well_dst in Hverifier;
    destruct Hverifier as (dst & Hdst);
    rewrite Hdst |

    apply Bool.andb_true_iff in Hverifier;
    destruct Hverifier as (Hdst & Hsrc);
    apply verifier_inv_is_well_dst in Hdst;
    destruct Hdst as (dst & Hdst);
    rewrite Hdst;
    apply verifier_inv_is_well_src in Hsrc;
    destruct Hsrc as (src & Hsrc);
    rewrite Hsrc |
    inversion Hverifier].

    - (**r ALU_DIV *)
      unfold nat_to_opcode_alu in Halu.
      assert (Hand_eq: Hand = 52%nat \/ Hand = 55%nat \/ Hand = 148%nat \/ Hand = 151%nat). {
        clear - Halu.
        do 52 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 92 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand. reflexivity.
        do 56 (destruct Hand; [inversion Halu |]).
        inversion Halu.
      }
      match goal with
      | |- context[if ?X then _ else _] =>
        destruct X eqn: Hif
      end.
      + (**r ALU_DIV_IMM *)

        remember (BinrBPF.get_immediate (List.nth pc (ins st) Int64.zero)) as imm.
        unfold Decode.get_instruction_alu32_imm.

        unfold step_alu_binary_operation, eval_reg32, eval_src32, bindM, returnM.
        unfold eval_reg.
        unfold rBPFValues.sint32_to_vint, rBPFValues.val_intuoflongu, Val.longofintu.

        apply reg_inv_eval_reg with (r:= dst) in Hreg.
        destruct Hreg as (i & Hreg).
        clear - Hzero Hreg Hand_eq.
        destruct Hand_eq as [ Hand_eq | Hand_eq].

        {
          rewrite Hand_eq.
          unfold rBPFValues.comp_ne_32, Vzero.
          rewrite Hzero.
          rewrite Hreg; simpl.
          rewrite Bool.negb_true_iff in Hzero.
          rewrite Hzero.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          unfold rBPFValues.comp_ne_32, Vzero.
          rewrite Hzero.
          rewrite Hreg; simpl.
          rewrite Bool.negb_true_iff in Hzero.
          rewrite Hzero.
          intro Hfalse; inversion Hfalse.
        }

        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }
      + (**r ALU_DIV_REG *)
        exfalso.
        clear - Hand_eq Hif.

        repeat (destruct Hand_eq as [ Hand_eq | Hand_eq]; [
        rewrite Hand_eq in Hif; inversion Hif| ]).
        rewrite Hand_eq in Hif; inversion Hif.

    - (**r ALU_SHIFT *)
      unfold nat_to_opcode_alu in Halu.
      assert (Hand_eq: Hand = 100%nat \/ Hand = 103%nat \/ Hand = 116%nat \/ Hand = 119%nat \/ Hand = 196%nat \/ Hand = 199%nat). {
        clear - Halu.
        do 100 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 12 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 76 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].

        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand. reflexivity.
        do 8 (destruct Hand; [inversion Halu |]).
        inversion Halu.
      }
      match goal with
      | |- context[if ?X then _ else _] =>
        destruct X eqn: Hif
      end.
      + (**r ALU_SHIFT_IMM *)

        remember (BinrBPF.get_immediate (List.nth pc (ins st) Int64.zero)) as imm.
        unfold Decode.get_instruction_alu32_imm.

        unfold step_alu_binary_operation, eval_reg32, eval_src32, bindM, returnM.
        unfold eval_reg.
        unfold rBPFValues.sint32_to_vint, rBPFValues.val_intuoflongu, Val.longofintu.

        apply reg_inv_eval_reg with (r:= dst) in Hreg.
        destruct Hreg as (i & Hreg).
        clear HeqHand Halu.
        clear - Hshift Hand_eq Hreg.
        unfold Int.cmpu in Hshift.

        destruct Hand_eq as [ Hand_eq | Hand_eq].

        {
          rewrite Hand_eq.
          unfold rBPFValues.compu_lt_32.
          rewrite Hshift.
          rewrite Hreg; simpl.
          change Int.iwordsize with (Int.repr 32).
          rewrite Hshift.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].

        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].

        {
          rewrite Hand_eq.
          unfold rBPFValues.compu_lt_32.
          rewrite Hshift.
          rewrite Hreg; simpl.
          change Int.iwordsize with (Int.repr 32).
          rewrite Hshift.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].

        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].

        {
          rewrite Hand_eq.
          unfold rBPFValues.compu_lt_32.
          rewrite Hshift.
          rewrite Hreg; simpl.
          change Int.iwordsize with (Int.repr 32).
          rewrite Hshift.
          intro Hfalse; inversion Hfalse.
        }
        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }
      + (**r ALU_SHIFT_REG *)
        exfalso.
        clear - Hand_eq Hif.

        repeat (destruct Hand_eq as [ Hand_eq | Hand_eq]; [
        rewrite Hand_eq in Hif; inversion Hif| ]).

        rewrite Hand_eq in Hif; inversion Hif.
    - (**r ALU_IMM_Normal *)
      unfold nat_to_opcode_alu in Halu.
      assert (Hand_eq: Hand = 4%nat \/ Hand = 7%nat \/ Hand = 20%nat \/ Hand = 23%nat \/ Hand = 36%nat \/ Hand = 39%nat \/ Hand = 68%nat \/ Hand = 71%nat \/ Hand = 84%nat \/ Hand = 87%nat \/ Hand = 132%nat \/ Hand = 135%nat \/ Hand = 164%nat \/ Hand = 167%nat \/ Hand = 180%nat \/ Hand = 183%nat). {
        clear - Halu.
        do 4 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 12 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 12 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 28 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 12 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 44 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 28 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 12 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand. reflexivity.
        do 24 (destruct Hand; [inversion Halu |]).
        inversion Halu.
      }
      match goal with
      | |- context[if ?X then _ else _] =>
        destruct X eqn: Hif
      end.
      + (**r ALU_IMM_Normal_IMM *)

        remember (BinrBPF.get_immediate (List.nth pc (ins st) Int64.zero)) as imm.
        unfold Decode.get_instruction_alu32_imm.

        unfold step_alu_binary_operation, eval_reg32, eval_src32, bindM, returnM.
        unfold eval_reg.
        unfold rBPFValues.sint32_to_vint, rBPFValues.val_intuoflongu, Val.longofintu.

        apply reg_inv_eval_reg with (r:= dst) in Hreg.
        destruct Hreg as (i & Hreg).
        clear - Hand_eq Hreg.

        repeat try (destruct Hand_eq as [ Hand_eq | Hand_eq]; [
          rewrite Hand_eq;
          rewrite Hreg; simpl;
          intro Hfalse; inversion Hfalse | 
          destruct Hand_eq as [ Hand_eq | Hand_eq]; [
           rewrite Hand_eq; intro Hfalse; inversion Hfalse |
          ]
        ]).

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }

        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }
      + (**r ALU_IMM_Normal_REG *)
        exfalso.
        clear - Hand_eq Hif.

        repeat (destruct Hand_eq as [ Hand_eq | Hand_eq]; [
        rewrite Hand_eq in Hif; inversion Hif| ]).

        rewrite Hand_eq in Hif; inversion Hif.

    - (**r ALU_REG_Normal *)
      unfold nat_to_opcode_alu in Halu.
      assert (Hand_eq: Hand = 12%nat \/ Hand = 15%nat \/ Hand = 28%nat \/ Hand = 31%nat \/ Hand = 44%nat \/ Hand = 
         47%nat \/ Hand = 60%nat \/ Hand = 63%nat \/ Hand = 76%nat \/ Hand = 79%nat \/ Hand = 
         92%nat \/ Hand = 95%nat \/ Hand = 108%nat \/ Hand = 111%nat \/ Hand = 124%nat \/ Hand = 
         127%nat \/ Hand = 156%nat \/ Hand = 159%nat \/ Hand = 172%nat \/ Hand = 175%nat \/ Hand = 
         188%nat \/ Hand = 191%nat \/ Hand = 204%nat \/ Hand = 207%nat). {
        clear - Halu.
        repeat try (do 12 (destruct Hand; [inversion Halu |]);
        destruct Hand; [left; reflexivity | right];
        do 2 (destruct Hand; [inversion Halu |]);
        destruct Hand; [left; reflexivity | right]).
        do 28 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        repeat try (do 12 (destruct Hand; [inversion Halu |]);
        destruct Hand; [left; reflexivity | right];
        do 2 (destruct Hand; [inversion Halu |]);
        destruct Hand; [left; reflexivity | right]).
        do 12 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand. reflexivity.
        inversion Halu.
      }
      match goal with
      | |- context[if ?X then _ else _] =>
        destruct X eqn: Hif
      end.
      + (**r ALU_REG_Normal_IMM *)
        exfalso.
        clear - Hand_eq Hif.

        repeat (destruct Hand_eq as [ Hand_eq | Hand_eq]; [
        rewrite Hand_eq in Hif; inversion Hif| ]).

        rewrite Hand_eq in Hif; inversion Hif.
      + (**r ALU_REG_Normal_REG *)

        unfold Decode.get_instruction_alu32_reg.

        unfold Decode.get_instruction_alu32_reg.
        unfold step_alu_binary_operation, eval_reg32, eval_src32, eval_reg32, rBPFValues.val_intuoflongu, Val.longofintu, eval_reg, bindM, returnM.

        eapply reg_inv_eval_reg with (r:= dst) in Hreg as Hreg_dst.
        eapply reg_inv_eval_reg with (r:= src) in Hreg as Hreg_src.
        destruct Hreg_dst as (r_dst & Hreg_dst).
        destruct Hreg_src as (r_src & Hreg_src).
        clear - Hand_eq Hreg_dst Hreg_src.

        destruct Hand_eq as [ Hand_eq | Hand_eq]; [
          rewrite Hand_eq;
          rewrite Hreg_dst, Hreg_src; simpl;
          intro Hfalse; inversion Hfalse |
          destruct Hand_eq as [ Hand_eq | Hand_eq]; [
            rewrite Hand_eq;
            intro Hfalse; inversion Hfalse |
          ]
        ].

        destruct Hand_eq as [ Hand_eq | Hand_eq]; [
          rewrite Hand_eq;
          rewrite Hreg_dst, Hreg_src; simpl;
          intro Hfalse; inversion Hfalse |
          destruct Hand_eq as [ Hand_eq | Hand_eq]; [
            rewrite Hand_eq;
            intro Hfalse; inversion Hfalse |
          ]
        ].

        destruct Hand_eq as [ Hand_eq | Hand_eq]; [
          rewrite Hand_eq;
          rewrite Hreg_dst, Hreg_src; simpl;
          intro Hfalse; inversion Hfalse |
          destruct Hand_eq as [ Hand_eq | Hand_eq]; [
            rewrite Hand_eq;
            intro Hfalse; inversion Hfalse |
          ]
        ].

        destruct Hand_eq as [ Hand_eq | Hand_eq].
          rewrite Hand_eq.
          rewrite Hreg_dst, Hreg_src; simpl.
          destruct negb eqn: Hif; [| intro Hfalse; inversion Hfalse].
          rewrite Bool.negb_true_iff in Hif.
          rewrite Hif.
          intro Hfalse; inversion Hfalse.
        destruct Hand_eq as [ Hand_eq | Hand_eq].
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.

        destruct Hand_eq as [ Hand_eq | Hand_eq]; [
          rewrite Hand_eq;
          rewrite Hreg_dst, Hreg_src; simpl;
          intro Hfalse; inversion Hfalse |
          destruct Hand_eq as [ Hand_eq | Hand_eq]; [
            rewrite Hand_eq;
            intro Hfalse; inversion Hfalse |
          ]
        ].

        destruct Hand_eq as [ Hand_eq | Hand_eq]; [
          rewrite Hand_eq;
          rewrite Hreg_dst, Hreg_src; simpl;
          intro Hfalse; inversion Hfalse |
          destruct Hand_eq as [ Hand_eq | Hand_eq]; [
            rewrite Hand_eq;
            intro Hfalse; inversion Hfalse |
          ]
        ].

        destruct Hand_eq as [ Hand_eq | Hand_eq].
          rewrite Hand_eq.
          rewrite Hreg_dst, Hreg_src; simpl.
          destruct Int.ltu eqn: Hif; [| intro Hfalse; inversion Hfalse].
          intro Hfalse; inversion Hfalse.
        destruct Hand_eq as [ Hand_eq | Hand_eq].
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.

        destruct Hand_eq as [ Hand_eq | Hand_eq].
          rewrite Hand_eq.
          rewrite Hreg_dst, Hreg_src; simpl.
          destruct Int.ltu eqn: Hif; [| intro Hfalse; inversion Hfalse].
          intro Hfalse; inversion Hfalse.
        destruct Hand_eq as [ Hand_eq | Hand_eq].
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.

        destruct Hand_eq as [ Hand_eq | Hand_eq].
          rewrite Hand_eq.
          rewrite Hreg_dst, Hreg_src; simpl.
          destruct negb eqn: Hif; [| intro Hfalse; inversion Hfalse].
          rewrite Bool.negb_true_iff in Hif.
          rewrite Hif.
          intro Hfalse; inversion Hfalse.
        destruct Hand_eq as [ Hand_eq | Hand_eq].
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.

        destruct Hand_eq as [ Hand_eq | Hand_eq]; [
          rewrite Hand_eq;
          rewrite Hreg_dst, Hreg_src; simpl;
          intro Hfalse; inversion Hfalse |
          destruct Hand_eq as [ Hand_eq | Hand_eq]; [
            rewrite Hand_eq;
            intro Hfalse; inversion Hfalse |
          ]
        ].

        destruct Hand_eq as [ Hand_eq | Hand_eq].
          rewrite Hand_eq.
          rewrite Hreg_src; simpl.
          intro Hfalse; inversion Hfalse.
        destruct Hand_eq as [ Hand_eq | Hand_eq].
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.

        destruct Hand_eq as [ Hand_eq | Hand_eq].
          rewrite Hand_eq.
          unfold rBPFValues.compu_lt_32.
          rewrite Hreg_dst, Hreg_src; simpl.
          destruct Int.ltu eqn: Hif; [| intro Hfalse; inversion Hfalse].
          intro Hfalse; inversion Hfalse.
        rewrite Hand_eq.
        intro Hfalse; inversion Hfalse.
  }

  destruct Hand.
  { (**r Branch *)
    remember (BinrBPF.get_opcode (List.nth pc (ins st) Int64.zero)) as Hand.

    destruct nat_to_opcode_branch eqn: Hbranch; [

    apply Bool.andb_true_iff in Hverifier;
    destruct Hverifier as (Hdst & Hjmp);
    apply verifier_inv_is_well_dst in Hdst;
    destruct Hdst as (dst & Hdst);
    rewrite Hdst |

    apply Bool.andb_true_iff in Hverifier;
    destruct Hverifier as (Hdst & Hjmp);
    apply Bool.andb_true_iff in Hdst;
    destruct Hdst as (Hdst & Hsrc);
    apply verifier_inv_is_well_dst in Hdst;
    destruct Hdst as (dst & Hdst);
    rewrite Hdst;
    apply verifier_inv_is_well_src in Hsrc;
    destruct Hsrc as (src & Hsrc);
    rewrite Hsrc | |
    inversion Hverifier]; unfold nat_to_opcode_branch in Hbranch.

    - (**r JMP_IMM *)

      assert (Hand_eq: Hand = 5%nat \/ Hand = 21%nat \/ Hand = 37%nat \/ Hand = 53%nat \/ Hand = 69%nat \/ Hand = 85%nat \/ Hand = 101%nat \/ Hand = 117%nat \/ Hand = 165%nat \/ Hand = 181%nat \/ Hand = 197%nat \/ Hand = 213%nat). {
        clear - Hbranch.
        do 5 (destruct Hand; [inversion Hbranch |]);
        destruct Hand; [left; reflexivity | right].
        repeat (do 15 (destruct Hand; [inversion Hbranch |]);
        destruct Hand; [left; reflexivity | right]).
        do 47 (destruct Hand; [inversion Hbranch |]);
        destruct Hand; [left; reflexivity | right].
        repeat (do 15 (destruct Hand; [inversion Hbranch |]);
        destruct Hand; [left; reflexivity | right]).
        do 15 (destruct Hand; [inversion Hbranch |]).
        destruct Hand. reflexivity.
        do 8 (destruct Hand; [inversion Hbranch |]).
        inversion Hbranch.
      }
      match goal with
      | |- context[if ?X then _ else _] =>
        destruct X eqn: Hif
      end.
      + (**r JMP_IMM_IMM *)
      remember (BinrBPF.get_immediate (List.nth pc (ins st) Int64.zero)) as imm.
      unfold is_well_jump in Hjmp.
      unfold Decode.get_instruction_branch_imm.
      remember (BinrBPF.get_offset (List.nth pc (ins st) Int64.zero)) as ofs.
      rewrite Heqpc in Hjmp.
      rewrite Z2Nat.id in Hjmp; [| apply Int_unsigned_ge_0].
      rewrite Int.repr_unsigned in Hjmp.
      rewrite Hst0 in Hjmp.
      rewrite <- Hlen in Hjmp.
      unfold step_branch_cond, eval_reg, eval_src, Val.longofint, rBPFValues.sint32_to_vint, rBPFValues.compl_eq, bindM, returnM.

Ltac destruct_if_jmp Hjmp :=
  match goal with
  | |- (if ?X then _ else _) _ <> None =>
    destruct X; [rewrite Hjmp |]; intro Hfalse; inversion Hfalse
  | |- Some _ <> None =>
      intro Hfalse; inversion Hfalse
  end.
      apply reg_inv_eval_reg with (r:= dst) in Hreg.
      destruct Hreg as (i & Hreg).
      clear - Hand_eq Hreg Hjmp.

      destruct Hand_eq as [ Hand_eq | Hand_eq].
        rewrite Hand_eq.
        rewrite Hjmp.
        intro Hfalse; inversion Hfalse.

      repeat (destruct Hand_eq as [ Hand_eq | Hand_eq]; [
        rewrite Hand_eq, Hreg;
        destruct_if_jmp Hjmp |
      ]).

      repeat (destruct Hand_eq as [ Hand_eq | Hand_eq]; [
        rewrite Hand_eq;
        destruct_if_jmp Hjmp |
      ]).

      rewrite Hand_eq.
      destruct_if_jmp Hjmp.

      + (**r JMP_IMM_REG *)
        exfalso.
        clear - Hand_eq Hif.
        repeat (destruct Hand_eq as [ Hand_eq | Hand_eq]; [
        rewrite Hand_eq in Hif; inversion Hif| ]).

        rewrite Hand_eq in Hif; inversion Hif.

    - (**r JMP_REG *)

      assert (Hand_eq: Hand = 29%nat \/ Hand = 45%nat \/ Hand = 61%nat \/ Hand = 77%nat \/ Hand = 93%nat \/ Hand = 109%nat \/ Hand = 125%nat \/ Hand = 173%nat \/ Hand = 189%nat \/ Hand = 205%nat \/ Hand = 221%nat). {
        clear - Hbranch.
        do 29 (destruct Hand; [inversion Hbranch |]);
        destruct Hand; [left; reflexivity | right].
        repeat (do 15 (destruct Hand; [inversion Hbranch |]);
        destruct Hand; [left; reflexivity | right]).
        do 47 (destruct Hand; [inversion Hbranch |]);
        destruct Hand; [left; reflexivity | right].
        repeat (do 15 (destruct Hand; [inversion Hbranch |]);
        destruct Hand; [left; reflexivity | right]).
        do 15 (destruct Hand; [inversion Hbranch |]).
        destruct Hand. reflexivity.
        inversion Hbranch.
      }
      match goal with
      | |- context[if ?X then _ else _] =>
        destruct X eqn: Hif
      end.
      + (**r JMP_REG_IMM *)
        exfalso.
        clear - Hand_eq Hif.
        repeat (destruct Hand_eq as [ Hand_eq | Hand_eq]; [
        rewrite Hand_eq in Hif; inversion Hif| ]).

        rewrite Hand_eq in Hif; inversion Hif.
      + (**r JMP_REG_REG *)
        unfold Decode.get_instruction_branch_reg.
        unfold is_well_jump in Hjmp.
        remember (BinrBPF.get_offset (List.nth pc (ins st) Int64.zero)) as ofs.
        rewrite Heqpc in Hjmp.
        rewrite Z2Nat.id in Hjmp; [| apply Int_unsigned_ge_0].
        rewrite Int.repr_unsigned in Hjmp.
        rewrite Hst0 in Hjmp.
        rewrite <- Hlen in Hjmp.

        unfold step_branch_cond, eval_src, eval_reg, Val.longofint, rBPFValues.sint32_to_vint, rBPFValues.compl_eq, bindM, returnM.

        eapply reg_inv_eval_reg with (r:= dst) in Hreg as Hreg_dst.
        eapply reg_inv_eval_reg with (r:= src) in Hreg as Hreg_src.
        destruct Hreg_dst as (r_dst & Hreg_dst).
        destruct Hreg_src as (r_src & Hreg_src).

        clear - Hreg_dst Hreg_src Hand_eq Hjmp.

        repeat (destruct Hand_eq as [ Hand_eq | Hand_eq]; [
          rewrite Hand_eq, Hreg_dst, Hreg_src;
          destruct_if_jmp Hjmp |
        ]).

        rewrite Hand_eq, Hreg_dst, Hreg_src;
        destruct_if_jmp Hjmp.
    - (**r JMP_SP *)
      assert (Hand_eq: Hand = 133%nat \/ Hand = 149%nat). {
        clear - Hbranch.
        do 133 (destruct Hand; [inversion Hbranch |]);
        destruct Hand; [left; reflexivity | right].
        do 15 (destruct Hand; [inversion Hbranch |]).
        destruct Hand. reflexivity.
        do 72 (destruct Hand; [inversion Hbranch |]).
        inversion Hbranch.
      }

      apply verifier_inv_dst_zero in Hverifier.
      clear - Hverifier Hand_eq.
      destruct Hand_eq as [ Hand_eq | Hand_eq]; rewrite Hand_eq, Hverifier.
        change (Int.eq Int.zero (Int.and (Int.repr (Z.of_nat 133)) (Int.repr 8))) with true.
        simpl.
        assert (H1:
  forall (i : int) (st1 : state),
exists ptr : val,
  _bpf_get_call (Vint i) st1 = Some (ptr, st1) /\
  (ptr = Vnullptr \/
   (exists (b : block) (ofs : ptrofs),
      ptr = Vptr b ofs /\
      (Mem.valid_pointer (bpf_m st1) b (Ptrofs.unsigned ofs)
       || Mem.valid_pointer (bpf_m st1) b (Ptrofs.unsigned ofs - 1))%bool =
      true))) by apply lemma_bpf_get_call.
        specialize (H1
       (Int.repr
          (Int64.unsigned
             (Int64.repr
                (Int.signed
                   (BinrBPF.get_immediate (List.nth pc (ins st) Int64.zero)))))) st).
        destruct H1 as (ptr & H1 & H2).
        rewrite H1.
        unfold cmp_ptr32_nullM.
        destruct H2 as [Hnull | Hptr].
          rewrite Hnull.
          simpl.
          rewrite Int.eq_true.
          intro Hfalse; inversion Hfalse.
          destruct Hptr as (b & ofs & Hptr & Hmem).
          rewrite Hptr; simpl.
          rewrite Int.eq_true.
          unfold State.eval_mem.
          rewrite Hmem.
          simpl.
          assert (H2:
  forall (b : block) (ofs : ptrofs) (st1 : state),
  exists (v : int) (st2 : state),
    exec_function (Vptr b ofs) st1 = Some (Vint v, st2) /\
    rBPFValues.cmp_ptr32_null (State.eval_mem st1) (Vptr b ofs) = Some false) by apply lemma_exec_function0.
          specialize (H2 b ofs st).
          destruct H2 as (v & st2 & H2 & Hcmp).
          rewrite H2.
          simpl.
          intro Hfalse; inversion Hfalse.

        change (Int.eq Int.zero (Int.and (Int.repr (Z.of_nat 149)) (Int.repr 8))) with true.
        simpl.
        intro Hfalse; inversion Hfalse.
      }

  destruct Hand.
  { (**r ILL_INS *)
    inversion Hverifier.
  }

  destruct Hand.
  { (**r ALU64 *)
    remember (BinrBPF.get_opcode (List.nth pc (ins st) Int64.zero)) as Hand.

    unfold is_not_div_by_zero64, is_shift_range64 in Hverifier.


    destruct nat_to_opcode_alu eqn: Halu; [

    apply Bool.andb_true_iff in Hverifier;
    destruct Hverifier as (Hdst & Hzero);
    apply verifier_inv_is_well_dst in Hdst;
    destruct Hdst as (dst & Hdst);
    rewrite Hdst;
    unfold Int64.cmp in Hzero |

    apply Bool.andb_true_iff in Hverifier;
    destruct Hverifier as (Hdst & Hshift);
    apply verifier_inv_is_well_dst in Hdst;
    destruct Hdst as (dst & Hdst);
    rewrite Hdst |

    apply verifier_inv_is_well_dst in Hverifier;
    destruct Hverifier as (dst & Hdst);
    rewrite Hdst |

    apply Bool.andb_true_iff in Hverifier;
    destruct Hverifier as (Hdst & Hsrc);
    apply verifier_inv_is_well_dst in Hdst;
    destruct Hdst as (dst & Hdst);
    rewrite Hdst;
    apply verifier_inv_is_well_src in Hsrc;
    destruct Hsrc as (src & Hsrc);
    rewrite Hsrc |
    inversion Hverifier].

    - (**r ALU_DIV *)
      unfold nat_to_opcode_alu in Halu.
      assert (Hand_eq: Hand = 52%nat \/ Hand = 55%nat \/ Hand = 148%nat \/ Hand = 151%nat). {
        clear - Halu.
        do 52 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 92 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand. reflexivity.
        do 56 (destruct Hand; [inversion Halu |]).
        inversion Halu.
      }
      match goal with
      | |- context[if ?X then _ else _] =>
        destruct X eqn: Hif
      end.
      + (**r ALU_DIV_IMM *)
        remember (BinrBPF.get_immediate (List.nth pc (ins st) Int64.zero)) as imm.
        unfold Decode.get_instruction_alu64_imm.

        unfold step_alu_binary_operation, eval_src, eval_reg, upd_reg, bindM, Val.longofint, rBPFValues.sint32_to_vint, returnM.

        apply reg_inv_eval_reg with (r:= dst) in Hreg.
        destruct Hreg as (i & Hreg).
        clear - Hzero Hreg Hand_eq.
        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          unfold rBPFValues.compl_ne, Regs.val64_zero.
          rewrite Hzero.
          rewrite Hreg; simpl.
          rewrite Bool.negb_true_iff in Hzero.
          rewrite Hzero.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq]; rewrite Hand_eq.
        {
          intro Hfalse; inversion Hfalse.
        }
        {
          unfold rBPFValues.compl_ne, Regs.val64_zero.
          rewrite Hzero.
          rewrite Hreg; simpl.
          rewrite Bool.negb_true_iff in Hzero.
          rewrite Hzero.
          intro Hfalse; inversion Hfalse.
        }
      + (**r ALU_DIV_REG *)
        exfalso.
        clear - Hand_eq Hif.

        repeat (destruct Hand_eq as [ Hand_eq | Hand_eq]; [
        rewrite Hand_eq in Hif; inversion Hif| ]).
        rewrite Hand_eq in Hif; inversion Hif.

    - (**r ALU_SHIFT *)
      unfold nat_to_opcode_alu in Halu.
      assert (Hand_eq: Hand = 100%nat \/ Hand = 103%nat \/ Hand = 116%nat \/ Hand = 119%nat \/ Hand = 196%nat \/ Hand = 199%nat). {
        clear - Halu.
        do 100 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 12 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 76 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].

        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand. reflexivity.
        do 8 (destruct Hand; [inversion Halu |]).
        inversion Halu.
      }
      match goal with
      | |- context[if ?X then _ else _] =>
        destruct X eqn: Hif
      end.
      + (**r ALU_SHIFT_IMM *)

        remember (BinrBPF.get_immediate (List.nth pc (ins st) Int64.zero)) as imm.
        unfold Decode.get_instruction_alu64_imm.

        unfold step_alu_binary_operation, eval_src, eval_reg, upd_reg, bindM, Val.longofint, rBPFValues.sint32_to_vint, returnM.

        apply reg_inv_eval_reg with (r:= dst) in Hreg.
        destruct Hreg as (i & Hreg).
        clear HeqHand Halu.
        clear - Hshift Hand_eq Hreg.
        unfold Int.cmpu in Hshift.

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          unfold rBPFValues.compu_lt_32, rBPFValues.val_intuoflongu.
          rewrite Hshift.
          rewrite Hreg; simpl.
          change Int64.iwordsize' with (Int.repr 64).
          rewrite Hshift.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          unfold rBPFValues.compu_lt_32, rBPFValues.val_intuoflongu.
          rewrite Hshift.
          rewrite Hreg; simpl.
          change Int64.iwordsize' with (Int.repr 64).
          rewrite Hshift.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }
        {
          rewrite Hand_eq.
          unfold rBPFValues.compu_lt_32, rBPFValues.val_intuoflongu.
          rewrite Hshift.
          rewrite Hreg; simpl.
          change Int64.iwordsize' with (Int.repr 64).
          rewrite Hshift.
          intro Hfalse; inversion Hfalse.
        }
      + (**r ALU_SHIFT_REG *)
        exfalso.
        clear - Hand_eq Hif.

        repeat (destruct Hand_eq as [ Hand_eq | Hand_eq]; [
        rewrite Hand_eq in Hif; inversion Hif| ]).

        rewrite Hand_eq in Hif; inversion Hif.
    - (**r ALU_IMM_Normal *)
      unfold nat_to_opcode_alu in Halu.
      assert (Hand_eq: Hand = 4%nat \/ Hand = 7%nat \/ Hand = 20%nat \/ Hand = 23%nat \/ Hand = 36%nat \/ Hand = 39%nat \/ Hand = 68%nat \/ Hand = 71%nat \/ Hand = 84%nat \/ Hand = 87%nat \/ Hand = 132%nat \/ Hand = 135%nat \/ Hand = 164%nat \/ Hand = 167%nat \/ Hand = 180%nat \/ Hand = 183%nat). {
        clear - Halu.
        do 4 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 12 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 12 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 28 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 12 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 44 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 28 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 12 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand. reflexivity.
        do 24 (destruct Hand; [inversion Halu |]).
        inversion Halu.
      }
      match goal with
      | |- context[if ?X then _ else _] =>
        destruct X eqn: Hif
      end.
      + (**r ALU_IMM_Normal_IMM *)

        remember (BinrBPF.get_immediate (List.nth pc (ins st) Int64.zero)) as imm.
        unfold Decode.get_instruction_alu64_imm.

        unfold step_alu_binary_operation, eval_src, eval_reg, upd_reg, bindM, Val.longofint, rBPFValues.sint32_to_vint, returnM.

        apply reg_inv_eval_reg with (r:= dst) in Hreg.
        destruct Hreg as (i & Hreg).
        clear - Hand_eq Hreg.

        repeat try( destruct Hand_eq as [ Hand_eq | Hand_eq]; [
          rewrite Hand_eq;
          intro Hfalse; inversion Hfalse |
          destruct Hand_eq as [ Hand_eq | Hand_eq]; [
            rewrite Hand_eq, Hreg; simpl;
            intro Hfalse; inversion Hfalse |
          ]
        ]).

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }
        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }

      + (**r ALU_IMM_Normal_REG *)
        exfalso.
        clear - Hand_eq Hif.

        repeat (destruct Hand_eq as [ Hand_eq | Hand_eq]; [
        rewrite Hand_eq in Hif; inversion Hif| ]).

        rewrite Hand_eq in Hif; inversion Hif.

    - (**r ALU_REG_Normal *)
      unfold nat_to_opcode_alu in Halu.
      assert (Hand_eq: Hand = 12%nat \/ Hand = 15%nat \/ Hand = 28%nat \/ Hand = 31%nat \/ Hand = 44%nat \/ Hand = 
         47%nat \/ Hand = 60%nat \/ Hand = 63%nat \/ Hand = 76%nat \/ Hand = 79%nat \/ Hand = 
         92%nat \/ Hand = 95%nat \/ Hand = 108%nat \/ Hand = 111%nat \/ Hand = 124%nat \/ Hand = 
         127%nat \/ Hand = 156%nat \/ Hand = 159%nat \/ Hand = 172%nat \/ Hand = 175%nat \/ Hand = 
         188%nat \/ Hand = 191%nat \/ Hand = 204%nat \/ Hand = 207%nat). {
        clear - Halu.
        repeat try (do 12 (destruct Hand; [inversion Halu |]);
        destruct Hand; [left; reflexivity | right];
        do 2 (destruct Hand; [inversion Halu |]);
        destruct Hand; [left; reflexivity | right]).
        do 28 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        repeat try (do 12 (destruct Hand; [inversion Halu |]);
        destruct Hand; [left; reflexivity | right];
        do 2 (destruct Hand; [inversion Halu |]);
        destruct Hand; [left; reflexivity | right]).
        do 12 (destruct Hand; [inversion Halu |]).
        destruct Hand; [left; reflexivity | right].
        do 2 (destruct Hand; [inversion Halu |]).
        destruct Hand. reflexivity.
        inversion Halu.
      }
      match goal with
      | |- context[if ?X then _ else _] =>
        destruct X eqn: Hif
      end.
      + (**r ALU_REG_Normal_IMM *)
        exfalso.
        clear - Hand_eq Hif.

        repeat (destruct Hand_eq as [ Hand_eq | Hand_eq]; [
        rewrite Hand_eq in Hif; inversion Hif| ]).

        rewrite Hand_eq in Hif; inversion Hif.
      + (**r ALU_REG_Normal_REG *)

        unfold Decode.get_instruction_alu64_reg.

        unfold step_alu_binary_operation, eval_src, eval_reg, upd_reg, rBPFValues.val_intuoflongu, Val.longofintu, eval_reg, bindM, returnM.

        eapply reg_inv_eval_reg with (r:= dst) in Hreg as Hreg_dst.
        eapply reg_inv_eval_reg with (r:= src) in Hreg as Hreg_src.
        destruct Hreg_dst as (r_dst & Hreg_dst).
        destruct Hreg_src as (r_src & Hreg_src).
        clear - Hand_eq Hreg_dst Hreg_src.

        destruct Hand_eq as [ Hand_eq | Hand_eq]; [
          rewrite Hand_eq; intro Hfalse; inversion Hfalse |
          destruct Hand_eq as [ Hand_eq | Hand_eq]; [
            rewrite Hand_eq;
            rewrite Hreg_dst, Hreg_src; simpl;
            intro Hfalse; inversion Hfalse |
          ]
        ].

        destruct Hand_eq as [ Hand_eq | Hand_eq]; [
          rewrite Hand_eq; intro Hfalse; inversion Hfalse |
          destruct Hand_eq as [ Hand_eq | Hand_eq]; [
            rewrite Hand_eq;
            rewrite Hreg_dst, Hreg_src; simpl;
            intro Hfalse; inversion Hfalse |
          ]
        ].

        destruct Hand_eq as [ Hand_eq | Hand_eq]; [
          rewrite Hand_eq; intro Hfalse; inversion Hfalse |
          destruct Hand_eq as [ Hand_eq | Hand_eq]; [
            rewrite Hand_eq;
            rewrite Hreg_dst, Hreg_src; simpl;
            intro Hfalse; inversion Hfalse |
          ]
        ].

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq; intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          unfold rBPFValues.compl_ne, Regs.val64_zero.
          rewrite Hreg_dst, Hreg_src; simpl.
          destruct negb eqn: Hif; [| intro Hfalse; inversion Hfalse].
          rewrite Bool.negb_true_iff in Hif.
          rewrite Hif.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq]; [
          rewrite Hand_eq; intro Hfalse; inversion Hfalse |
          destruct Hand_eq as [ Hand_eq | Hand_eq]; [
            rewrite Hand_eq;
            rewrite Hreg_dst, Hreg_src; simpl;
            intro Hfalse; inversion Hfalse |
          ]
        ].

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          rewrite Hreg_dst, Hreg_src; simpl.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          unfold rBPFValues.compu_lt_32.
          rewrite Hreg_dst, Hreg_src; simpl.
          destruct Int.ltu eqn: Hif; [| intro Hfalse; inversion Hfalse].
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          unfold rBPFValues.compu_lt_32.
          rewrite Hreg_dst, Hreg_src; simpl.
          destruct Int.ltu eqn: Hif; [| intro Hfalse; inversion Hfalse].
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq; intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          unfold rBPFValues.compl_ne, Regs.val64_zero.
          rewrite Hreg_dst, Hreg_src; simpl.
          destruct negb eqn: Hif; [| intro Hfalse; inversion Hfalse].
          rewrite Bool.negb_true_iff in Hif.
          rewrite Hif.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq]; [
          rewrite Hand_eq; intro Hfalse; inversion Hfalse |
          destruct Hand_eq as [ Hand_eq | Hand_eq]; [
            rewrite Hand_eq;
            rewrite Hreg_dst, Hreg_src; simpl;
            intro Hfalse; inversion Hfalse |
          ]
        ].

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq; intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq.
          rewrite Hreg_src; simpl.
          intro Hfalse; inversion Hfalse.
        }

        destruct Hand_eq as [ Hand_eq | Hand_eq].
        {
          rewrite Hand_eq; intro Hfalse; inversion Hfalse.
        }

        {
          rewrite Hand_eq.
          unfold rBPFValues.compu_lt_32.
          rewrite Hreg_dst, Hreg_src; simpl.
          destruct Int.ltu eqn: Hif; [| intro Hfalse; inversion Hfalse].
          intro Hfalse; inversion Hfalse.
        }
  }

  inversion Hverifier.
Qed.

Theorem inv_avoid_bpf_interpreter_aux_undef:
  forall f st st0
    (Hreg: register_inv st)
    (Hmem: memory_inv st)
    (Hlen: ins_len st = length (ins st))
    (Hlen_max: (length (ins st) <= Z.to_nat Ptrofs.max_unsigned)%nat)
    (Hst0: state_include st0 st)
    (Hver: bpf_verifier st0 = true),
      bpf_interpreter_aux f st <> None.
Proof.
  induction f.
  intros.
  - simpl.
    unfold upd_flag.
    intro Hfalse; inversion Hfalse.
  - simpl.
    intros.
    unfold eval_ins_len, eval_pc, eval_flag, upd_pc_incr, upd_flag, bindM, returnM.
    unfold State.eval_pc, State.eval_ins_len.

    destruct Int.ltu eqn: Hltu.
    + eapply inv_avoid_step_undef in Hreg as Hstep; eauto.
      destruct step eqn: H.
      * destruct p.
        destruct Flag.flag_eq; [| intro Hfalse; inversion Hfalse].
        destruct (Int.ltu (Int.add (pc_loc s) Int.one) (Int.repr (Z.of_nat (ins_len s)))) eqn: Hltu'.
        unfold Int.cmpu.
        rewrite Hltu'.
        eapply step_preserving_inv in H; eauto.
        unfold state_include in Hst0.

        clear - IHf H Hver Hlen Hlen_max Hst0.
        remember (State.upd_pc_incr s) as st1.
        assert (Hupd_inv: register_inv st1 /\ memory_inv st1 /\ state_include st0 st1). {
          destruct H as (Hreg & Hmem & Hver').
          subst.
          split; [eapply reg_inv_upd_pc_incr; eauto |
            split; [eapply mem_inv_upd_pc_incr; eauto | eapply state_include_upd_pc_incr; eauto]].
        }
        destruct Hupd_inv as (Hreg & Hmem & Hver').
        apply IHf with (st0 := st0); auto.
        unfold state_include in Hver'.
        destruct Hver' as (Hver0' & Hver1').
        rewrite <- Hver0'.
        destruct Hst0 as (Hst0 & Hst1).
        rewrite Hst0.
        rewrite <- Hver1'.
        rewrite Hst1.
        assumption.

        unfold state_include in Hver'.
        destruct Hver' as (Hver0' & Hver1').
        rewrite <- Hver1'.
        destruct Hst0 as (Hst0 & Hst1).
        rewrite Hst1.
        assumption.

        intro Hfalse; inversion Hfalse.
      * assumption.
    + intro Hfalse; inversion Hfalse.
Qed.

Theorem inv_avoid_bpf_interpreter_undef:
  forall st f st0
    (Hreg: register_inv st)
    (Hmem: memory_inv st)
    (Hlen: ins_len st = length (ins st))
    (Hlen_max: (length (ins st) <= Z.to_nat Ptrofs.max_unsigned)%nat)
    (Hst0: state_include st0 st)
    (Hver: bpf_verifier st0 = true),
      bpf_interpreter f st <> None.
Proof.
  intros.
  unfold bpf_interpreter.
  unfold eval_mem_regions, get_mem_region, get_start_addr, upd_reg, eval_flag, eval_reg, bindM, returnM.
  set (Hmem' := Hmem).
  unfold memory_inv in Hmem'.
  destruct Hmem' as (Hlen_low & Hlen0 & _ & Hinv_memory_regions).
  assert (Hlt: Nat.ltb 0 (mrs_num st) = true). {
    rewrite Nat.ltb_lt.
    lia.
  }
  rewrite Hlt. clear Hlt.
  unfold State.eval_mem_regions.
  assert (Hlt: (0 < length (bpf_mrs st))%nat). {
    rewrite Hlen0.
    lia.
  }
  set (Hneq := Hlt).
  rewrite <- List.nth_error_Some in Hneq.
  erewrite List.nth_error_nth' with (d:= MemRegion.default_memory_region); [| assumption].

  apply List.nth_In with (d:= MemRegion.default_memory_region) in Hlt.
  eapply In_inv_memory_regions in Hlt; eauto.
  remember (List.nth 0 (bpf_mrs st) MemRegion.default_memory_region) as mr.
  unfold inv_memory_region in Hlt.
  destruct Hlt as (b & _ & _ & _ & (base & len & Hstart & _)).
  rewrite Hstart.
  simpl.

  remember (State.upd_reg Regs.R1 (Vlong (Int64.repr (Int.unsigned base))) st) as st1.
  assert (Hinv: register_inv st1 /\ memory_inv st1 /\ state_include st0 st1). {
    subst.
    split.
    eapply reg_inv_upd_reg; eauto.
    split.
    eapply mem_inv_upd_reg; eauto.
    eapply state_include_upd_reg; eauto.
  }
  clear - Hinv Hlen Hlen_max Hver Hst0.
  destruct Hinv as (Hreg & Hmem & Hver').

  eapply inv_avoid_bpf_interpreter_aux_undef in Hmem; eauto.

  destruct (bpf_interpreter_aux f st1) eqn: Haux.
  destruct p.
  destruct Flag.flag_eq; intro Hfalse; inversion Hfalse.
  intro.
  apply Hmem.
  apply Haux.

  unfold state_include in Hver'.
  destruct Hver' as (Hver0' & Hver1').
  rewrite <- Hver0'.
  destruct Hst0 as (Hst0 & Hst1).
  rewrite Hst0.
  rewrite <- Hver1'.
  rewrite Hst1.
  assumption.

  unfold state_include in Hver'.
  destruct Hver' as (Hver0' & Hver1').
  rewrite <- Hver1'.
  destruct Hst0 as (Hst0 & Hst1).
  rewrite Hst1.
  assumption.
Qed.