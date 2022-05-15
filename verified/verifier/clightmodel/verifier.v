From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.9".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "32sse2".
  Definition abi := "standard".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "verifier.c".
  Definition normalized := false.
End Info.

Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _b : ident := $"b".
Definition _b0 : ident := $"b0".
Definition _bpf_verifier : ident := $"bpf_verifier".
Definition _bpf_verifier_aux : ident := $"bpf_verifier_aux".
Definition _bpf_verifier_aux2 : ident := $"bpf_verifier_aux2".
Definition _bpf_verifier_opcode_alu32_imm : ident := $"bpf_verifier_opcode_alu32_imm".
Definition _bpf_verifier_opcode_alu32_reg : ident := $"bpf_verifier_opcode_alu32_reg".
Definition _bpf_verifier_opcode_alu64_imm : ident := $"bpf_verifier_opcode_alu64_imm".
Definition _bpf_verifier_opcode_alu64_reg : ident := $"bpf_verifier_opcode_alu64_reg".
Definition _bpf_verifier_opcode_branch_imm : ident := $"bpf_verifier_opcode_branch_imm".
Definition _bpf_verifier_opcode_branch_reg : ident := $"bpf_verifier_opcode_branch_reg".
Definition _bpf_verifier_opcode_load_imm : ident := $"bpf_verifier_opcode_load_imm".
Definition _bpf_verifier_opcode_load_reg : ident := $"bpf_verifier_opcode_load_reg".
Definition _bpf_verifier_opcode_store_imm : ident := $"bpf_verifier_opcode_store_imm".
Definition _bpf_verifier_opcode_store_reg : ident := $"bpf_verifier_opcode_store_reg".
Definition _eval_ins : ident := $"eval_ins".
Definition _eval_ins_len : ident := $"eval_ins_len".
Definition _get_offset : ident := $"get_offset".
Definition _get_opcode : ident := $"get_opcode".
Definition _i : ident := $"i".
Definition _idx : ident := $"idx".
Definition _ins : ident := $"ins".
Definition _ins64 : ident := $"ins64".
Definition _ins_len : ident := $"ins_len".
Definition _is_dst_R0 : ident := $"is_dst_R0".
Definition _is_not_div_by_zero : ident := $"is_not_div_by_zero".
Definition _is_not_div_by_zero64 : ident := $"is_not_div_by_zero64".
Definition _is_shift_range : ident := $"is_shift_range".
Definition _is_shift_range64 : ident := $"is_shift_range64".
Definition _is_well_dst : ident := $"is_well_dst".
Definition _is_well_jump : ident := $"is_well_jump".
Definition _is_well_src : ident := $"is_well_src".
Definition _len : ident := $"len".
Definition _main : ident := $"main".
Definition _n : ident := $"n".
Definition _ofs : ident := $"ofs".
Definition _op : ident := $"op".
Definition _pc : ident := $"pc".
Definition _st : ident := $"st".
Definition _upper : ident := $"upper".
Definition _verifier_state : ident := $"verifier_state".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'30 : ident := 157%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'32 : ident := 159%positive.
Definition _t'33 : ident := 160%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_eval_ins_len := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _verifier_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef
                   (Etempvar _st (tptr (Tstruct _verifier_state noattr)))
                   (Tstruct _verifier_state noattr)) _ins_len tuint)))
|}.

Definition f_eval_ins := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _verifier_state noattr))) ::
                (_idx, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ederef
                 (Ebinop Oadd
                   (Efield
                     (Ederef
                       (Etempvar _st (tptr (Tstruct _verifier_state noattr)))
                       (Tstruct _verifier_state noattr)) _ins (tptr tulong))
                   (Etempvar _idx tuint) (tptr tulong)) tulong)))
|}.

Definition f_is_dst_R0 := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_i, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oeq
                 (Ecast
                   (Ebinop Oshr
                     (Ebinop Oand (Etempvar _i tulong)
                       (Econst_long (Int64.repr 4095) tulong) tulong)
                     (Econst_long (Int64.repr 8) tulong) tulong) tuint)
                 (Econst_int (Int.repr 0) tuint) tint)))
|}.

Definition f_is_well_dst := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_i, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Ole
                 (Ecast
                   (Ebinop Oshr
                     (Ebinop Oand (Etempvar _i tulong)
                       (Econst_long (Int64.repr 4095) tulong) tulong)
                     (Econst_long (Int64.repr 8) tulong) tulong) tuint)
                 (Econst_int (Int.repr 10) tuint) tint)))
|}.

Definition f_is_well_src := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_i, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Ole
                 (Ecast
                   (Ebinop Oshr
                     (Ebinop Oand (Etempvar _i tulong)
                       (Econst_long (Int64.repr 65535) tulong) tulong)
                     (Econst_long (Int64.repr 12) tulong) tulong) tuint)
                 (Econst_int (Int.repr 10) tuint) tint)))
|}.

Definition f_is_well_jump := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_pc, tuint) :: (_len, tuint) :: (_ofs, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Ole
                 (Ebinop Oadd (Etempvar _pc tuint) (Etempvar _ofs tint)
                   tuint)
                 (Ebinop Osub (Etempvar _len tuint)
                   (Econst_int (Int.repr 2) tuint) tuint) tint)))
|}.

Definition f_is_not_div_by_zero := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_i, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop One
                 (Ecast
                   (Ebinop Oshr (Etempvar _i tulong)
                     (Econst_long (Int64.repr 32) tulong) tulong) tint)
                 (Econst_int (Int.repr 0) tuint) tint)))
|}.

Definition f_is_not_div_by_zero64 := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_i, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop One
                 (Ecast
                   (Ecast
                     (Ebinop Oshr (Etempvar _i tulong)
                       (Econst_long (Int64.repr 32) tulong) tulong) tint)
                   tlong) (Econst_long (Int64.repr 0) tulong) tint)))
|}.

Definition f_is_shift_range := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_i, tulong) :: (_upper, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Olt
                 (Ecast
                   (Ebinop Oshr (Etempvar _i tulong)
                     (Econst_long (Int64.repr 32) tulong) tulong) tint)
                 (Etempvar _upper tuint) tint)))
|}.

Definition f_is_shift_range64 := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_i, tulong) :: (_upper, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Olt
                 (Ecast
                   (Ecast
                     (Ecast
                       (Ebinop Oshr (Etempvar _i tulong)
                         (Econst_long (Int64.repr 32) tulong) tulong) tint)
                     tulong) tuint) (Etempvar _upper tuint) tint)))
|}.

Definition f_get_opcode := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Etempvar _ins tulong)
                   (Econst_long (Int64.repr 255) tulong) tulong) tuchar)))
|}.

Definition f_get_offset := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_i, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ecast
                   (Ebinop Oshr
                     (Ebinop Oshl (Etempvar _i tulong)
                       (Econst_long (Int64.repr 32) tulong) tulong)
                     (Econst_long (Int64.repr 48) tulong) tulong) tshort)
                 tint)))
|}.

Definition f_bpf_verifier_opcode_alu32_imm := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: (_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tbool) :: (_t'5, tbool) :: (_t'4, tbool) ::
               (_t'3, tbool) :: (_t'2, tbool) :: (_t'1, tbool) :: nil);
  fn_body :=
(Sswitch (Etempvar _op tuchar)
  (LScons (Some 4)
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
    (LScons (Some 20)
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))
      (LScons (Some 36)
        (Sreturn (Some (Econst_int (Int.repr 1) tint)))
        (LScons (Some 52)
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _is_not_div_by_zero (Tfunction (Tcons tulong Tnil)
                                            tbool cc_default))
                ((Etempvar _ins tulong) :: nil))
              (Sset _b (Ecast (Etempvar _t'1 tbool) tbool)))
            (Sreturn (Some (Etempvar _b tbool))))
          (LScons (Some 68)
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))
            (LScons (Some 84)
              (Sreturn (Some (Econst_int (Int.repr 1) tint)))
              (LScons (Some 100)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'2)
                      (Evar _is_shift_range (Tfunction
                                              (Tcons tulong
                                                (Tcons tuint Tnil)) tbool
                                              cc_default))
                      ((Etempvar _ins tulong) ::
                       (Econst_int (Int.repr 32) tuint) :: nil))
                    (Sset _b (Ecast (Etempvar _t'2 tbool) tbool)))
                  (Sreturn (Some (Etempvar _b tbool))))
                (LScons (Some 116)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _is_shift_range (Tfunction
                                                (Tcons tulong
                                                  (Tcons tuint Tnil)) tbool
                                                cc_default))
                        ((Etempvar _ins tulong) ::
                         (Econst_int (Int.repr 32) tuint) :: nil))
                      (Sset _b (Ecast (Etempvar _t'3 tbool) tbool)))
                    (Sreturn (Some (Etempvar _b tbool))))
                  (LScons (Some 132)
                    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                    (LScons (Some 148)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'4)
                            (Evar _is_not_div_by_zero (Tfunction
                                                        (Tcons tulong Tnil)
                                                        tbool cc_default))
                            ((Etempvar _ins tulong) :: nil))
                          (Sset _b (Ecast (Etempvar _t'4 tbool) tbool)))
                        (Sreturn (Some (Etempvar _b tbool))))
                      (LScons (Some 164)
                        (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                        (LScons (Some 180)
                          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                          (LScons (Some 196)
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'5)
                                  (Evar _is_shift_range (Tfunction
                                                          (Tcons tulong
                                                            (Tcons tuint
                                                              Tnil)) tbool
                                                          cc_default))
                                  ((Etempvar _ins tulong) ::
                                   (Econst_int (Int.repr 32) tuint) :: nil))
                                (Sset _b (Ecast (Etempvar _t'5 tbool) tbool)))
                              (Sreturn (Some (Etempvar _b tbool))))
                            (LScons None
                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                              LSnil)))))))))))))))
|}.

Definition f_bpf_verifier_opcode_alu32_reg := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: (_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tbool) :: (_t'12, tbool) :: (_t'11, tbool) ::
               (_t'10, tbool) :: (_t'9, tbool) :: (_t'8, tbool) ::
               (_t'7, tbool) :: (_t'6, tbool) :: (_t'5, tbool) ::
               (_t'4, tbool) :: (_t'3, tbool) :: (_t'2, tbool) ::
               (_t'1, tbool) :: nil);
  fn_body :=
(Sswitch (Etempvar _op tuchar)
  (LScons (Some 12)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool cc_default))
          ((Etempvar _ins tulong) :: nil))
        (Sset _b (Ecast (Etempvar _t'1 tbool) tbool)))
      (Sreturn (Some (Etempvar _b tbool))))
    (LScons (Some 28)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                 cc_default))
            ((Etempvar _ins tulong) :: nil))
          (Sset _b (Ecast (Etempvar _t'2 tbool) tbool)))
        (Sreturn (Some (Etempvar _b tbool))))
      (LScons (Some 44)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                   cc_default))
              ((Etempvar _ins tulong) :: nil))
            (Sset _b (Ecast (Etempvar _t'3 tbool) tbool)))
          (Sreturn (Some (Etempvar _b tbool))))
        (LScons (Some 60)
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                     cc_default))
                ((Etempvar _ins tulong) :: nil))
              (Sset _b (Ecast (Etempvar _t'4 tbool) tbool)))
            (Sreturn (Some (Etempvar _b tbool))))
          (LScons (Some 76)
            (Ssequence
              (Ssequence
                (Scall (Some _t'5)
                  (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                       cc_default))
                  ((Etempvar _ins tulong) :: nil))
                (Sset _b (Ecast (Etempvar _t'5 tbool) tbool)))
              (Sreturn (Some (Etempvar _b tbool))))
            (LScons (Some 92)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'6)
                    (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                         cc_default))
                    ((Etempvar _ins tulong) :: nil))
                  (Sset _b (Ecast (Etempvar _t'6 tbool) tbool)))
                (Sreturn (Some (Etempvar _b tbool))))
              (LScons (Some 108)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'7)
                      (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                           cc_default))
                      ((Etempvar _ins tulong) :: nil))
                    (Sset _b (Ecast (Etempvar _t'7 tbool) tbool)))
                  (Sreturn (Some (Etempvar _b tbool))))
                (LScons (Some 124)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'8)
                        (Evar _is_well_src (Tfunction (Tcons tulong Tnil)
                                             tbool cc_default))
                        ((Etempvar _ins tulong) :: nil))
                      (Sset _b (Ecast (Etempvar _t'8 tbool) tbool)))
                    (Sreturn (Some (Etempvar _b tbool))))
                  (LScons (Some 156)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'9)
                          (Evar _is_well_src (Tfunction (Tcons tulong Tnil)
                                               tbool cc_default))
                          ((Etempvar _ins tulong) :: nil))
                        (Sset _b (Ecast (Etempvar _t'9 tbool) tbool)))
                      (Sreturn (Some (Etempvar _b tbool))))
                    (LScons (Some 172)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'10)
                            (Evar _is_well_src (Tfunction (Tcons tulong Tnil)
                                                 tbool cc_default))
                            ((Etempvar _ins tulong) :: nil))
                          (Sset _b (Ecast (Etempvar _t'10 tbool) tbool)))
                        (Sreturn (Some (Etempvar _b tbool))))
                      (LScons (Some 188)
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'11)
                              (Evar _is_well_src (Tfunction
                                                   (Tcons tulong Tnil) tbool
                                                   cc_default))
                              ((Etempvar _ins tulong) :: nil))
                            (Sset _b (Ecast (Etempvar _t'11 tbool) tbool)))
                          (Sreturn (Some (Etempvar _b tbool))))
                        (LScons (Some 204)
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'12)
                                (Evar _is_well_src (Tfunction
                                                     (Tcons tulong Tnil)
                                                     tbool cc_default))
                                ((Etempvar _ins tulong) :: nil))
                              (Sset _b (Ecast (Etempvar _t'12 tbool) tbool)))
                            (Sreturn (Some (Etempvar _b tbool))))
                          (LScons None
                            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                            LSnil))))))))))))))
|}.

Definition f_bpf_verifier_opcode_alu64_imm := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: (_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tbool) :: (_t'5, tbool) :: (_t'4, tbool) ::
               (_t'3, tbool) :: (_t'2, tbool) :: (_t'1, tbool) :: nil);
  fn_body :=
(Sswitch (Etempvar _op tuchar)
  (LScons (Some 7)
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
    (LScons (Some 23)
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))
      (LScons (Some 39)
        (Sreturn (Some (Econst_int (Int.repr 1) tint)))
        (LScons (Some 55)
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _is_not_div_by_zero64 (Tfunction (Tcons tulong Tnil)
                                              tbool cc_default))
                ((Etempvar _ins tulong) :: nil))
              (Sset _b (Ecast (Etempvar _t'1 tbool) tbool)))
            (Sreturn (Some (Etempvar _b tbool))))
          (LScons (Some 71)
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))
            (LScons (Some 87)
              (Sreturn (Some (Econst_int (Int.repr 1) tint)))
              (LScons (Some 103)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'2)
                      (Evar _is_shift_range64 (Tfunction
                                                (Tcons tulong
                                                  (Tcons tuint Tnil)) tbool
                                                cc_default))
                      ((Etempvar _ins tulong) ::
                       (Econst_int (Int.repr 64) tuint) :: nil))
                    (Sset _b (Ecast (Etempvar _t'2 tbool) tbool)))
                  (Sreturn (Some (Etempvar _b tbool))))
                (LScons (Some 119)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _is_shift_range64 (Tfunction
                                                  (Tcons tulong
                                                    (Tcons tuint Tnil)) tbool
                                                  cc_default))
                        ((Etempvar _ins tulong) ::
                         (Econst_int (Int.repr 64) tuint) :: nil))
                      (Sset _b (Ecast (Etempvar _t'3 tbool) tbool)))
                    (Sreturn (Some (Etempvar _b tbool))))
                  (LScons (Some 135)
                    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                    (LScons (Some 151)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'4)
                            (Evar _is_not_div_by_zero64 (Tfunction
                                                          (Tcons tulong Tnil)
                                                          tbool cc_default))
                            ((Etempvar _ins tulong) :: nil))
                          (Sset _b (Ecast (Etempvar _t'4 tbool) tbool)))
                        (Sreturn (Some (Etempvar _b tbool))))
                      (LScons (Some 167)
                        (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                        (LScons (Some 183)
                          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                          (LScons (Some 199)
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'5)
                                  (Evar _is_shift_range64 (Tfunction
                                                            (Tcons tulong
                                                              (Tcons tuint
                                                                Tnil)) tbool
                                                            cc_default))
                                  ((Etempvar _ins tulong) ::
                                   (Econst_int (Int.repr 64) tuint) :: nil))
                                (Sset _b (Ecast (Etempvar _t'5 tbool) tbool)))
                              (Sreturn (Some (Etempvar _b tbool))))
                            (LScons None
                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                              LSnil)))))))))))))))
|}.

Definition f_bpf_verifier_opcode_alu64_reg := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: (_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tbool) :: (_t'12, tbool) :: (_t'11, tbool) ::
               (_t'10, tbool) :: (_t'9, tbool) :: (_t'8, tbool) ::
               (_t'7, tbool) :: (_t'6, tbool) :: (_t'5, tbool) ::
               (_t'4, tbool) :: (_t'3, tbool) :: (_t'2, tbool) ::
               (_t'1, tbool) :: nil);
  fn_body :=
(Sswitch (Etempvar _op tuchar)
  (LScons (Some 15)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool cc_default))
          ((Etempvar _ins tulong) :: nil))
        (Sset _b (Ecast (Etempvar _t'1 tbool) tbool)))
      (Sreturn (Some (Etempvar _b tbool))))
    (LScons (Some 31)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                 cc_default))
            ((Etempvar _ins tulong) :: nil))
          (Sset _b (Ecast (Etempvar _t'2 tbool) tbool)))
        (Sreturn (Some (Etempvar _b tbool))))
      (LScons (Some 47)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                   cc_default))
              ((Etempvar _ins tulong) :: nil))
            (Sset _b (Ecast (Etempvar _t'3 tbool) tbool)))
          (Sreturn (Some (Etempvar _b tbool))))
        (LScons (Some 63)
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                     cc_default))
                ((Etempvar _ins tulong) :: nil))
              (Sset _b (Ecast (Etempvar _t'4 tbool) tbool)))
            (Sreturn (Some (Etempvar _b tbool))))
          (LScons (Some 79)
            (Ssequence
              (Ssequence
                (Scall (Some _t'5)
                  (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                       cc_default))
                  ((Etempvar _ins tulong) :: nil))
                (Sset _b (Ecast (Etempvar _t'5 tbool) tbool)))
              (Sreturn (Some (Etempvar _b tbool))))
            (LScons (Some 95)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'6)
                    (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                         cc_default))
                    ((Etempvar _ins tulong) :: nil))
                  (Sset _b (Ecast (Etempvar _t'6 tbool) tbool)))
                (Sreturn (Some (Etempvar _b tbool))))
              (LScons (Some 111)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'7)
                      (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                           cc_default))
                      ((Etempvar _ins tulong) :: nil))
                    (Sset _b (Ecast (Etempvar _t'7 tbool) tbool)))
                  (Sreturn (Some (Etempvar _b tbool))))
                (LScons (Some 127)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'8)
                        (Evar _is_well_src (Tfunction (Tcons tulong Tnil)
                                             tbool cc_default))
                        ((Etempvar _ins tulong) :: nil))
                      (Sset _b (Ecast (Etempvar _t'8 tbool) tbool)))
                    (Sreturn (Some (Etempvar _b tbool))))
                  (LScons (Some 159)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'9)
                          (Evar _is_well_src (Tfunction (Tcons tulong Tnil)
                                               tbool cc_default))
                          ((Etempvar _ins tulong) :: nil))
                        (Sset _b (Ecast (Etempvar _t'9 tbool) tbool)))
                      (Sreturn (Some (Etempvar _b tbool))))
                    (LScons (Some 175)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'10)
                            (Evar _is_well_src (Tfunction (Tcons tulong Tnil)
                                                 tbool cc_default))
                            ((Etempvar _ins tulong) :: nil))
                          (Sset _b (Ecast (Etempvar _t'10 tbool) tbool)))
                        (Sreturn (Some (Etempvar _b tbool))))
                      (LScons (Some 191)
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'11)
                              (Evar _is_well_src (Tfunction
                                                   (Tcons tulong Tnil) tbool
                                                   cc_default))
                              ((Etempvar _ins tulong) :: nil))
                            (Sset _b (Ecast (Etempvar _t'11 tbool) tbool)))
                          (Sreturn (Some (Etempvar _b tbool))))
                        (LScons (Some 207)
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'12)
                                (Evar _is_well_src (Tfunction
                                                     (Tcons tulong Tnil)
                                                     tbool cc_default))
                                ((Etempvar _ins tulong) :: nil))
                              (Sset _b (Ecast (Etempvar _t'12 tbool) tbool)))
                            (Sreturn (Some (Etempvar _b tbool))))
                          (LScons None
                            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                            LSnil))))))))))))))
|}.

Definition f_bpf_verifier_opcode_branch_imm := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_pc, tuint) :: (_len, tuint) :: (_op, tuchar) ::
                (_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ofs, tint) :: (_b, tbool) :: (_t'26, tbool) ::
               (_t'25, tbool) :: (_t'24, tbool) :: (_t'23, tint) ::
               (_t'22, tbool) :: (_t'21, tint) :: (_t'20, tbool) ::
               (_t'19, tint) :: (_t'18, tbool) :: (_t'17, tint) ::
               (_t'16, tbool) :: (_t'15, tint) :: (_t'14, tbool) ::
               (_t'13, tint) :: (_t'12, tbool) :: (_t'11, tint) ::
               (_t'10, tbool) :: (_t'9, tint) :: (_t'8, tbool) ::
               (_t'7, tint) :: (_t'6, tbool) :: (_t'5, tint) ::
               (_t'4, tbool) :: (_t'3, tint) :: (_t'2, tbool) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Sswitch (Etempvar _op tuchar)
  (LScons (Some 5)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint cc_default))
          ((Etempvar _ins tulong) :: nil))
        (Sset _ofs (Etempvar _t'1 tint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _is_well_jump (Tfunction
                                  (Tcons tuint
                                    (Tcons tuint (Tcons tint Tnil))) tbool
                                  cc_default))
            ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
             (Etempvar _ofs tint) :: nil))
          (Sset _b (Ecast (Etempvar _t'2 tbool) tbool)))
        (Sreturn (Some (Etempvar _b tbool)))))
    (LScons (Some 21)
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint cc_default))
            ((Etempvar _ins tulong) :: nil))
          (Sset _ofs (Etempvar _t'3 tint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _is_well_jump (Tfunction
                                    (Tcons tuint
                                      (Tcons tuint (Tcons tint Tnil))) tbool
                                    cc_default))
              ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
               (Etempvar _ofs tint) :: nil))
            (Sset _b (Ecast (Etempvar _t'4 tbool) tbool)))
          (Sreturn (Some (Etempvar _b tbool)))))
      (LScons (Some 37)
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint
                                  cc_default))
              ((Etempvar _ins tulong) :: nil))
            (Sset _ofs (Etempvar _t'5 tint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'6)
                (Evar _is_well_jump (Tfunction
                                      (Tcons tuint
                                        (Tcons tuint (Tcons tint Tnil)))
                                      tbool cc_default))
                ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                 (Etempvar _ofs tint) :: nil))
              (Sset _b (Ecast (Etempvar _t'6 tbool) tbool)))
            (Sreturn (Some (Etempvar _b tbool)))))
        (LScons (Some 53)
          (Ssequence
            (Ssequence
              (Scall (Some _t'7)
                (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint
                                    cc_default))
                ((Etempvar _ins tulong) :: nil))
              (Sset _ofs (Etempvar _t'7 tint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'8)
                  (Evar _is_well_jump (Tfunction
                                        (Tcons tuint
                                          (Tcons tuint (Tcons tint Tnil)))
                                        tbool cc_default))
                  ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                   (Etempvar _ofs tint) :: nil))
                (Sset _b (Ecast (Etempvar _t'8 tbool) tbool)))
              (Sreturn (Some (Etempvar _b tbool)))))
          (LScons (Some 165)
            (Ssequence
              (Ssequence
                (Scall (Some _t'9)
                  (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint
                                      cc_default))
                  ((Etempvar _ins tulong) :: nil))
                (Sset _ofs (Etempvar _t'9 tint)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'10)
                    (Evar _is_well_jump (Tfunction
                                          (Tcons tuint
                                            (Tcons tuint (Tcons tint Tnil)))
                                          tbool cc_default))
                    ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                     (Etempvar _ofs tint) :: nil))
                  (Sset _b (Ecast (Etempvar _t'10 tbool) tbool)))
                (Sreturn (Some (Etempvar _b tbool)))))
            (LScons (Some 181)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'11)
                    (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint
                                        cc_default))
                    ((Etempvar _ins tulong) :: nil))
                  (Sset _ofs (Etempvar _t'11 tint)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'12)
                      (Evar _is_well_jump (Tfunction
                                            (Tcons tuint
                                              (Tcons tuint (Tcons tint Tnil)))
                                            tbool cc_default))
                      ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                       (Etempvar _ofs tint) :: nil))
                    (Sset _b (Ecast (Etempvar _t'12 tbool) tbool)))
                  (Sreturn (Some (Etempvar _b tbool)))))
              (LScons (Some 69)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'13)
                      (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint
                                          cc_default))
                      ((Etempvar _ins tulong) :: nil))
                    (Sset _ofs (Etempvar _t'13 tint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'14)
                        (Evar _is_well_jump (Tfunction
                                              (Tcons tuint
                                                (Tcons tuint
                                                  (Tcons tint Tnil))) tbool
                                              cc_default))
                        ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                         (Etempvar _ofs tint) :: nil))
                      (Sset _b (Ecast (Etempvar _t'14 tbool) tbool)))
                    (Sreturn (Some (Etempvar _b tbool)))))
                (LScons (Some 85)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'15)
                        (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint
                                            cc_default))
                        ((Etempvar _ins tulong) :: nil))
                      (Sset _ofs (Etempvar _t'15 tint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'16)
                          (Evar _is_well_jump (Tfunction
                                                (Tcons tuint
                                                  (Tcons tuint
                                                    (Tcons tint Tnil))) tbool
                                                cc_default))
                          ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                           (Etempvar _ofs tint) :: nil))
                        (Sset _b (Ecast (Etempvar _t'16 tbool) tbool)))
                      (Sreturn (Some (Etempvar _b tbool)))))
                  (LScons (Some 101)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'17)
                          (Evar _get_offset (Tfunction (Tcons tulong Tnil)
                                              tint cc_default))
                          ((Etempvar _ins tulong) :: nil))
                        (Sset _ofs (Etempvar _t'17 tint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'18)
                            (Evar _is_well_jump (Tfunction
                                                  (Tcons tuint
                                                    (Tcons tuint
                                                      (Tcons tint Tnil)))
                                                  tbool cc_default))
                            ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                             (Etempvar _ofs tint) :: nil))
                          (Sset _b (Ecast (Etempvar _t'18 tbool) tbool)))
                        (Sreturn (Some (Etempvar _b tbool)))))
                    (LScons (Some 117)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'19)
                            (Evar _get_offset (Tfunction (Tcons tulong Tnil)
                                                tint cc_default))
                            ((Etempvar _ins tulong) :: nil))
                          (Sset _ofs (Etempvar _t'19 tint)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'20)
                              (Evar _is_well_jump (Tfunction
                                                    (Tcons tuint
                                                      (Tcons tuint
                                                        (Tcons tint Tnil)))
                                                    tbool cc_default))
                              ((Etempvar _pc tuint) ::
                               (Etempvar _len tuint) ::
                               (Etempvar _ofs tint) :: nil))
                            (Sset _b (Ecast (Etempvar _t'20 tbool) tbool)))
                          (Sreturn (Some (Etempvar _b tbool)))))
                      (LScons (Some 197)
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'21)
                              (Evar _get_offset (Tfunction
                                                  (Tcons tulong Tnil) tint
                                                  cc_default))
                              ((Etempvar _ins tulong) :: nil))
                            (Sset _ofs (Etempvar _t'21 tint)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'22)
                                (Evar _is_well_jump (Tfunction
                                                      (Tcons tuint
                                                        (Tcons tuint
                                                          (Tcons tint Tnil)))
                                                      tbool cc_default))
                                ((Etempvar _pc tuint) ::
                                 (Etempvar _len tuint) ::
                                 (Etempvar _ofs tint) :: nil))
                              (Sset _b (Ecast (Etempvar _t'22 tbool) tbool)))
                            (Sreturn (Some (Etempvar _b tbool)))))
                        (LScons (Some 213)
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'23)
                                (Evar _get_offset (Tfunction
                                                    (Tcons tulong Tnil) tint
                                                    cc_default))
                                ((Etempvar _ins tulong) :: nil))
                              (Sset _ofs (Etempvar _t'23 tint)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'24)
                                  (Evar _is_well_jump (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tuint
                                                            (Tcons tint Tnil)))
                                                        tbool cc_default))
                                  ((Etempvar _pc tuint) ::
                                   (Etempvar _len tuint) ::
                                   (Etempvar _ofs tint) :: nil))
                                (Sset _b
                                  (Ecast (Etempvar _t'24 tbool) tbool)))
                              (Sreturn (Some (Etempvar _b tbool)))))
                          (LScons (Some 133)
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'25)
                                  (Evar _is_dst_R0 (Tfunction
                                                     (Tcons tulong Tnil)
                                                     tbool cc_default))
                                  ((Etempvar _ins tulong) :: nil))
                                (Sset _b
                                  (Ecast (Etempvar _t'25 tbool) tbool)))
                              (Sreturn (Some (Etempvar _b tbool))))
                            (LScons (Some 149)
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'26)
                                    (Evar _is_dst_R0 (Tfunction
                                                       (Tcons tulong Tnil)
                                                       tbool cc_default))
                                    ((Etempvar _ins tulong) :: nil))
                                  (Sset _b
                                    (Ecast (Etempvar _t'26 tbool) tbool)))
                                (Sreturn (Some (Etempvar _b tbool))))
                              (LScons None
                                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                LSnil))))))))))))))))
|}.

Definition f_bpf_verifier_opcode_branch_reg := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_pc, tuint) :: (_len, tuint) :: (_op, tuchar) ::
                (_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ofs, tint) :: (_b0, tbool) :: (_b, tbool) ::
               (_t'33, tbool) :: (_t'32, tbool) :: (_t'31, tint) ::
               (_t'30, tbool) :: (_t'29, tbool) :: (_t'28, tint) ::
               (_t'27, tbool) :: (_t'26, tbool) :: (_t'25, tint) ::
               (_t'24, tbool) :: (_t'23, tbool) :: (_t'22, tint) ::
               (_t'21, tbool) :: (_t'20, tbool) :: (_t'19, tint) ::
               (_t'18, tbool) :: (_t'17, tbool) :: (_t'16, tint) ::
               (_t'15, tbool) :: (_t'14, tbool) :: (_t'13, tint) ::
               (_t'12, tbool) :: (_t'11, tbool) :: (_t'10, tint) ::
               (_t'9, tbool) :: (_t'8, tbool) :: (_t'7, tint) ::
               (_t'6, tbool) :: (_t'5, tbool) :: (_t'4, tint) ::
               (_t'3, tbool) :: (_t'2, tbool) :: (_t'1, tint) :: nil);
  fn_body :=
(Sswitch (Etempvar _op tuchar)
  (LScons (Some 29)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint cc_default))
          ((Etempvar _ins tulong) :: nil))
        (Sset _ofs (Etempvar _t'1 tint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                 cc_default))
            ((Etempvar _ins tulong) :: nil))
          (Sset _b0 (Ecast (Etempvar _t'2 tbool) tbool)))
        (Sifthenelse (Etempvar _b0 tbool)
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _is_well_jump (Tfunction
                                      (Tcons tuint
                                        (Tcons tuint (Tcons tint Tnil)))
                                      tbool cc_default))
                ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                 (Etempvar _ofs tint) :: nil))
              (Sset _b (Ecast (Etempvar _t'3 tbool) tbool)))
            (Sreturn (Some (Etempvar _b tbool))))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
    (LScons (Some 45)
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint cc_default))
            ((Etempvar _ins tulong) :: nil))
          (Sset _ofs (Etempvar _t'4 tint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                   cc_default))
              ((Etempvar _ins tulong) :: nil))
            (Sset _b0 (Ecast (Etempvar _t'5 tbool) tbool)))
          (Sifthenelse (Etempvar _b0 tbool)
            (Ssequence
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _is_well_jump (Tfunction
                                        (Tcons tuint
                                          (Tcons tuint (Tcons tint Tnil)))
                                        tbool cc_default))
                  ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                   (Etempvar _ofs tint) :: nil))
                (Sset _b (Ecast (Etempvar _t'6 tbool) tbool)))
              (Sreturn (Some (Etempvar _b tbool))))
            (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
      (LScons (Some 61)
        (Ssequence
          (Ssequence
            (Scall (Some _t'7)
              (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint
                                  cc_default))
              ((Etempvar _ins tulong) :: nil))
            (Sset _ofs (Etempvar _t'7 tint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'8)
                (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                     cc_default))
                ((Etempvar _ins tulong) :: nil))
              (Sset _b0 (Ecast (Etempvar _t'8 tbool) tbool)))
            (Sifthenelse (Etempvar _b0 tbool)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'9)
                    (Evar _is_well_jump (Tfunction
                                          (Tcons tuint
                                            (Tcons tuint (Tcons tint Tnil)))
                                          tbool cc_default))
                    ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                     (Etempvar _ofs tint) :: nil))
                  (Sset _b (Ecast (Etempvar _t'9 tbool) tbool)))
                (Sreturn (Some (Etempvar _b tbool))))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
        (LScons (Some 173)
          (Ssequence
            (Ssequence
              (Scall (Some _t'10)
                (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint
                                    cc_default))
                ((Etempvar _ins tulong) :: nil))
              (Sset _ofs (Etempvar _t'10 tint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'11)
                  (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                       cc_default))
                  ((Etempvar _ins tulong) :: nil))
                (Sset _b0 (Ecast (Etempvar _t'11 tbool) tbool)))
              (Sifthenelse (Etempvar _b0 tbool)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'12)
                      (Evar _is_well_jump (Tfunction
                                            (Tcons tuint
                                              (Tcons tuint (Tcons tint Tnil)))
                                            tbool cc_default))
                      ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                       (Etempvar _ofs tint) :: nil))
                    (Sset _b (Ecast (Etempvar _t'12 tbool) tbool)))
                  (Sreturn (Some (Etempvar _b tbool))))
                (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
          (LScons (Some 189)
            (Ssequence
              (Ssequence
                (Scall (Some _t'13)
                  (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint
                                      cc_default))
                  ((Etempvar _ins tulong) :: nil))
                (Sset _ofs (Etempvar _t'13 tint)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'14)
                    (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                         cc_default))
                    ((Etempvar _ins tulong) :: nil))
                  (Sset _b0 (Ecast (Etempvar _t'14 tbool) tbool)))
                (Sifthenelse (Etempvar _b0 tbool)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'15)
                        (Evar _is_well_jump (Tfunction
                                              (Tcons tuint
                                                (Tcons tuint
                                                  (Tcons tint Tnil))) tbool
                                              cc_default))
                        ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                         (Etempvar _ofs tint) :: nil))
                      (Sset _b (Ecast (Etempvar _t'15 tbool) tbool)))
                    (Sreturn (Some (Etempvar _b tbool))))
                  (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
            (LScons (Some 77)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'16)
                    (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint
                                        cc_default))
                    ((Etempvar _ins tulong) :: nil))
                  (Sset _ofs (Etempvar _t'16 tint)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'17)
                      (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                           cc_default))
                      ((Etempvar _ins tulong) :: nil))
                    (Sset _b0 (Ecast (Etempvar _t'17 tbool) tbool)))
                  (Sifthenelse (Etempvar _b0 tbool)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'18)
                          (Evar _is_well_jump (Tfunction
                                                (Tcons tuint
                                                  (Tcons tuint
                                                    (Tcons tint Tnil))) tbool
                                                cc_default))
                          ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                           (Etempvar _ofs tint) :: nil))
                        (Sset _b (Ecast (Etempvar _t'18 tbool) tbool)))
                      (Sreturn (Some (Etempvar _b tbool))))
                    (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
              (LScons (Some 93)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'19)
                      (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint
                                          cc_default))
                      ((Etempvar _ins tulong) :: nil))
                    (Sset _ofs (Etempvar _t'19 tint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'20)
                        (Evar _is_well_src (Tfunction (Tcons tulong Tnil)
                                             tbool cc_default))
                        ((Etempvar _ins tulong) :: nil))
                      (Sset _b0 (Ecast (Etempvar _t'20 tbool) tbool)))
                    (Sifthenelse (Etempvar _b0 tbool)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'21)
                            (Evar _is_well_jump (Tfunction
                                                  (Tcons tuint
                                                    (Tcons tuint
                                                      (Tcons tint Tnil)))
                                                  tbool cc_default))
                            ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                             (Etempvar _ofs tint) :: nil))
                          (Sset _b (Ecast (Etempvar _t'21 tbool) tbool)))
                        (Sreturn (Some (Etempvar _b tbool))))
                      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
                (LScons (Some 109)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'22)
                        (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint
                                            cc_default))
                        ((Etempvar _ins tulong) :: nil))
                      (Sset _ofs (Etempvar _t'22 tint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'23)
                          (Evar _is_well_src (Tfunction (Tcons tulong Tnil)
                                               tbool cc_default))
                          ((Etempvar _ins tulong) :: nil))
                        (Sset _b0 (Ecast (Etempvar _t'23 tbool) tbool)))
                      (Sifthenelse (Etempvar _b0 tbool)
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'24)
                              (Evar _is_well_jump (Tfunction
                                                    (Tcons tuint
                                                      (Tcons tuint
                                                        (Tcons tint Tnil)))
                                                    tbool cc_default))
                              ((Etempvar _pc tuint) ::
                               (Etempvar _len tuint) ::
                               (Etempvar _ofs tint) :: nil))
                            (Sset _b (Ecast (Etempvar _t'24 tbool) tbool)))
                          (Sreturn (Some (Etempvar _b tbool))))
                        (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
                  (LScons (Some 125)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'25)
                          (Evar _get_offset (Tfunction (Tcons tulong Tnil)
                                              tint cc_default))
                          ((Etempvar _ins tulong) :: nil))
                        (Sset _ofs (Etempvar _t'25 tint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'26)
                            (Evar _is_well_src (Tfunction (Tcons tulong Tnil)
                                                 tbool cc_default))
                            ((Etempvar _ins tulong) :: nil))
                          (Sset _b0 (Ecast (Etempvar _t'26 tbool) tbool)))
                        (Sifthenelse (Etempvar _b0 tbool)
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'27)
                                (Evar _is_well_jump (Tfunction
                                                      (Tcons tuint
                                                        (Tcons tuint
                                                          (Tcons tint Tnil)))
                                                      tbool cc_default))
                                ((Etempvar _pc tuint) ::
                                 (Etempvar _len tuint) ::
                                 (Etempvar _ofs tint) :: nil))
                              (Sset _b (Ecast (Etempvar _t'27 tbool) tbool)))
                            (Sreturn (Some (Etempvar _b tbool))))
                          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
                    (LScons (Some 205)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'28)
                            (Evar _get_offset (Tfunction (Tcons tulong Tnil)
                                                tint cc_default))
                            ((Etempvar _ins tulong) :: nil))
                          (Sset _ofs (Etempvar _t'28 tint)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'29)
                              (Evar _is_well_src (Tfunction
                                                   (Tcons tulong Tnil) tbool
                                                   cc_default))
                              ((Etempvar _ins tulong) :: nil))
                            (Sset _b0 (Ecast (Etempvar _t'29 tbool) tbool)))
                          (Sifthenelse (Etempvar _b0 tbool)
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'30)
                                  (Evar _is_well_jump (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tuint
                                                            (Tcons tint Tnil)))
                                                        tbool cc_default))
                                  ((Etempvar _pc tuint) ::
                                   (Etempvar _len tuint) ::
                                   (Etempvar _ofs tint) :: nil))
                                (Sset _b
                                  (Ecast (Etempvar _t'30 tbool) tbool)))
                              (Sreturn (Some (Etempvar _b tbool))))
                            (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
                      (LScons (Some 221)
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'31)
                              (Evar _get_offset (Tfunction
                                                  (Tcons tulong Tnil) tint
                                                  cc_default))
                              ((Etempvar _ins tulong) :: nil))
                            (Sset _ofs (Etempvar _t'31 tint)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'32)
                                (Evar _is_well_src (Tfunction
                                                     (Tcons tulong Tnil)
                                                     tbool cc_default))
                                ((Etempvar _ins tulong) :: nil))
                              (Sset _b0 (Ecast (Etempvar _t'32 tbool) tbool)))
                            (Sifthenelse (Etempvar _b0 tbool)
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'33)
                                    (Evar _is_well_jump (Tfunction
                                                          (Tcons tuint
                                                            (Tcons tuint
                                                              (Tcons tint
                                                                Tnil))) tbool
                                                          cc_default))
                                    ((Etempvar _pc tuint) ::
                                     (Etempvar _len tuint) ::
                                     (Etempvar _ofs tint) :: nil))
                                  (Sset _b
                                    (Ecast (Etempvar _t'33 tbool) tbool)))
                                (Sreturn (Some (Etempvar _b tbool))))
                              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
                        (LScons None
                          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                          LSnil)))))))))))))
|}.

Definition f_bpf_verifier_opcode_load_imm := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: (_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sswitch (Etempvar _op tuchar)
  (LScons (Some 24)
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
    (LScons (Some 16)
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))
      (LScons None (Sreturn (Some (Econst_int (Int.repr 0) tint))) LSnil))))
|}.

Definition f_bpf_verifier_opcode_load_reg := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: (_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tbool) :: (_t'4, tbool) :: (_t'3, tbool) ::
               (_t'2, tbool) :: (_t'1, tbool) :: nil);
  fn_body :=
(Sswitch (Etempvar _op tuchar)
  (LScons (Some 97)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool cc_default))
          ((Etempvar _ins tulong) :: nil))
        (Sset _b (Ecast (Etempvar _t'1 tbool) tbool)))
      (Sreturn (Some (Etempvar _b tbool))))
    (LScons (Some 105)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                 cc_default))
            ((Etempvar _ins tulong) :: nil))
          (Sset _b (Ecast (Etempvar _t'2 tbool) tbool)))
        (Sreturn (Some (Etempvar _b tbool))))
      (LScons (Some 113)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                   cc_default))
              ((Etempvar _ins tulong) :: nil))
            (Sset _b (Ecast (Etempvar _t'3 tbool) tbool)))
          (Sreturn (Some (Etempvar _b tbool))))
        (LScons (Some 121)
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                     cc_default))
                ((Etempvar _ins tulong) :: nil))
              (Sset _b (Ecast (Etempvar _t'4 tbool) tbool)))
            (Sreturn (Some (Etempvar _b tbool))))
          (LScons None (Sreturn (Some (Econst_int (Int.repr 0) tint))) LSnil))))))
|}.

Definition f_bpf_verifier_opcode_store_imm := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: (_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sswitch (Etempvar _op tuchar)
  (LScons (Some 98)
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
    (LScons (Some 106)
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))
      (LScons (Some 114)
        (Sreturn (Some (Econst_int (Int.repr 1) tint)))
        (LScons (Some 122)
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
          (LScons None (Sreturn (Some (Econst_int (Int.repr 0) tint))) LSnil))))))
|}.

Definition f_bpf_verifier_opcode_store_reg := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: (_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tbool) :: (_t'4, tbool) :: (_t'3, tbool) ::
               (_t'2, tbool) :: (_t'1, tbool) :: nil);
  fn_body :=
(Sswitch (Etempvar _op tuchar)
  (LScons (Some 99)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool cc_default))
          ((Etempvar _ins tulong) :: nil))
        (Sset _b (Ecast (Etempvar _t'1 tbool) tbool)))
      (Sreturn (Some (Etempvar _b tbool))))
    (LScons (Some 107)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                 cc_default))
            ((Etempvar _ins tulong) :: nil))
          (Sset _b (Ecast (Etempvar _t'2 tbool) tbool)))
        (Sreturn (Some (Etempvar _b tbool))))
      (LScons (Some 115)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                   cc_default))
              ((Etempvar _ins tulong) :: nil))
            (Sset _b (Ecast (Etempvar _t'3 tbool) tbool)))
          (Sreturn (Some (Etempvar _b tbool))))
        (LScons (Some 123)
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _is_well_src (Tfunction (Tcons tulong Tnil) tbool
                                     cc_default))
                ((Etempvar _ins tulong) :: nil))
              (Sset _b (Ecast (Etempvar _t'4 tbool) tbool)))
            (Sreturn (Some (Etempvar _b tbool))))
          (LScons None (Sreturn (Some (Econst_int (Int.repr 0) tint))) LSnil))))))
|}.

Definition f_bpf_verifier_aux2 := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_pc, tuint) :: (_len, tuint) :: (_op, tuchar) ::
                (_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tbool) :: (_t'10, tbool) :: (_t'9, tbool) ::
               (_t'8, tbool) :: (_t'7, tbool) :: (_t'6, tbool) ::
               (_t'5, tbool) :: (_t'4, tbool) :: (_t'3, tbool) ::
               (_t'2, tbool) :: (_t'1, tbool) :: nil);
  fn_body :=
(Sswitch (Ecast
           (Ebinop Oand (Etempvar _op tuchar) (Econst_int (Int.repr 7) tint)
             tint) tuchar)
  (LScons (Some 7)
    (Sifthenelse (Ebinop Oeq (Econst_int (Int.repr 0) tuint)
                   (Ebinop Oand (Etempvar _op tuchar)
                     (Econst_int (Int.repr 8) tuint) tuint) tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _bpf_verifier_opcode_alu64_imm (Tfunction
                                                   (Tcons tuchar
                                                     (Tcons tulong Tnil))
                                                   tbool cc_default))
            ((Etempvar _op tuchar) :: (Etempvar _ins tulong) :: nil))
          (Sset _b (Ecast (Etempvar _t'1 tbool) tbool)))
        (Sreturn (Some (Etempvar _b tbool))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _bpf_verifier_opcode_alu64_reg (Tfunction
                                                   (Tcons tuchar
                                                     (Tcons tulong Tnil))
                                                   tbool cc_default))
            ((Etempvar _op tuchar) :: (Etempvar _ins tulong) :: nil))
          (Sset _b (Ecast (Etempvar _t'2 tbool) tbool)))
        (Sreturn (Some (Etempvar _b tbool)))))
    (LScons (Some 4)
      (Sifthenelse (Ebinop Oeq (Econst_int (Int.repr 0) tuint)
                     (Ebinop Oand (Etempvar _op tuchar)
                       (Econst_int (Int.repr 8) tuint) tuint) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _bpf_verifier_opcode_alu32_imm (Tfunction
                                                     (Tcons tuchar
                                                       (Tcons tulong Tnil))
                                                     tbool cc_default))
              ((Etempvar _op tuchar) :: (Etempvar _ins tulong) :: nil))
            (Sset _b (Ecast (Etempvar _t'3 tbool) tbool)))
          (Sreturn (Some (Etempvar _b tbool))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _bpf_verifier_opcode_alu32_reg (Tfunction
                                                     (Tcons tuchar
                                                       (Tcons tulong Tnil))
                                                     tbool cc_default))
              ((Etempvar _op tuchar) :: (Etempvar _ins tulong) :: nil))
            (Sset _b (Ecast (Etempvar _t'4 tbool) tbool)))
          (Sreturn (Some (Etempvar _b tbool)))))
      (LScons (Some 5)
        (Sifthenelse (Ebinop Oeq (Econst_int (Int.repr 0) tuint)
                       (Ebinop Oand (Etempvar _op tuchar)
                         (Econst_int (Int.repr 8) tuint) tuint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _bpf_verifier_opcode_branch_imm (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tuint
                                                            (Tcons tuchar
                                                              (Tcons tulong
                                                                Tnil))))
                                                        tbool cc_default))
                ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                 (Etempvar _op tuchar) :: (Etempvar _ins tulong) :: nil))
              (Sset _b (Ecast (Etempvar _t'5 tbool) tbool)))
            (Sreturn (Some (Etempvar _b tbool))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'6)
                (Evar _bpf_verifier_opcode_branch_reg (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tuint
                                                            (Tcons tuchar
                                                              (Tcons tulong
                                                                Tnil))))
                                                        tbool cc_default))
                ((Etempvar _pc tuint) :: (Etempvar _len tuint) ::
                 (Etempvar _op tuchar) :: (Etempvar _ins tulong) :: nil))
              (Sset _b (Ecast (Etempvar _t'6 tbool) tbool)))
            (Sreturn (Some (Etempvar _b tbool)))))
        (LScons (Some 0)
          (Ssequence
            (Ssequence
              (Scall (Some _t'7)
                (Evar _bpf_verifier_opcode_load_imm (Tfunction
                                                      (Tcons tuchar
                                                        (Tcons tulong Tnil))
                                                      tbool cc_default))
                ((Etempvar _op tuchar) :: (Etempvar _ins tulong) :: nil))
              (Sset _b (Ecast (Etempvar _t'7 tbool) tbool)))
            (Sreturn (Some (Etempvar _b tbool))))
          (LScons (Some 1)
            (Ssequence
              (Ssequence
                (Scall (Some _t'8)
                  (Evar _bpf_verifier_opcode_load_reg (Tfunction
                                                        (Tcons tuchar
                                                          (Tcons tulong Tnil))
                                                        tbool cc_default))
                  ((Etempvar _op tuchar) :: (Etempvar _ins tulong) :: nil))
                (Sset _b (Ecast (Etempvar _t'8 tbool) tbool)))
              (Sreturn (Some (Etempvar _b tbool))))
            (LScons (Some 2)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'9)
                    (Evar _bpf_verifier_opcode_store_imm (Tfunction
                                                           (Tcons tuchar
                                                             (Tcons tulong
                                                               Tnil)) tbool
                                                           cc_default))
                    ((Etempvar _op tuchar) :: (Etempvar _ins tulong) :: nil))
                  (Sset _b (Ecast (Etempvar _t'9 tbool) tbool)))
                (Sreturn (Some (Etempvar _b tbool))))
              (LScons (Some 3)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'10)
                      (Evar _bpf_verifier_opcode_store_reg (Tfunction
                                                             (Tcons tuchar
                                                               (Tcons tulong
                                                                 Tnil)) tbool
                                                             cc_default))
                      ((Etempvar _op tuchar) :: (Etempvar _ins tulong) ::
                       nil))
                    (Sset _b (Ecast (Etempvar _t'10 tbool) tbool)))
                  (Sreturn (Some (Etempvar _b tbool))))
                (LScons None
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                  LSnil)))))))))
|}.

Definition f_bpf_verifier_aux := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _verifier_state noattr))) ::
                (_pc, tuint) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tuint) :: (_ins, tulong) :: (_b, tbool) ::
               (_op, tuchar) :: (_b0, tbool) :: (_t'5, tbool) ::
               (_t'4, tbool) :: (_t'3, tuchar) :: (_t'2, tbool) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _pc tuint) (Econst_int (Int.repr 0) tuint)
               tint)
  (Sreturn (Some (Econst_int (Int.repr 1) tint)))
  (Ssequence
    (Sset _n
      (Ebinop Osub (Etempvar _pc tuint) (Econst_int (Int.repr 1) tuint)
        tuint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _eval_ins (Tfunction
                            (Tcons (tptr (Tstruct _verifier_state noattr))
                              (Tcons tuint Tnil)) tulong cc_default))
          ((Etempvar _st (tptr (Tstruct _verifier_state noattr))) ::
           (Etempvar _n tuint) :: nil))
        (Sset _ins (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _is_well_dst (Tfunction (Tcons tulong Tnil) tbool
                                 cc_default))
            ((Etempvar _ins tulong) :: nil))
          (Sset _b (Ecast (Etempvar _t'2 tbool) tbool)))
        (Sifthenelse (Etempvar _b tbool)
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _get_opcode (Tfunction (Tcons tulong Tnil) tuchar
                                    cc_default))
                ((Etempvar _ins tulong) :: nil))
              (Sset _op (Ecast (Etempvar _t'3 tuchar) tuchar)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _bpf_verifier_aux2 (Tfunction
                                             (Tcons tuint
                                               (Tcons tuint
                                                 (Tcons tuchar
                                                   (Tcons tulong Tnil))))
                                             tbool cc_default))
                  ((Etempvar _n tuint) :: (Etempvar _len tuint) ::
                   (Etempvar _op tuchar) :: (Etempvar _ins tulong) :: nil))
                (Sset _b0 (Ecast (Etempvar _t'4 tbool) tbool)))
              (Sifthenelse (Etempvar _b0 tbool)
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _bpf_verifier_aux (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _verifier_state noattr))
                                                (Tcons tuint
                                                  (Tcons tuint Tnil))) tbool
                                              cc_default))
                    ((Etempvar _st (tptr (Tstruct _verifier_state noattr))) ::
                     (Etempvar _n tuint) :: (Etempvar _len tuint) :: nil))
                  (Sreturn (Some (Etempvar _t'5 tbool))))
                (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
|}.

Definition f_bpf_verifier := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _verifier_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_len, tuint) :: (_b, tbool) :: (_ins64, tulong) ::
               (_t'3, tulong) :: (_t'2, tbool) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _eval_ins_len (Tfunction
                            (Tcons (tptr (Tstruct _verifier_state noattr))
                              Tnil) tuint cc_default))
      ((Etempvar _st (tptr (Tstruct _verifier_state noattr))) :: nil))
    (Sset _len (Etempvar _t'1 tuint)))
  (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 1) tuint)
                 (Etempvar _len tuint) tint)
    (Sifthenelse (Ebinop Ole (Etempvar _len tuint)
                   (Ebinop Odiv (Econst_int (Int.repr (-1)) tuint)
                     (Econst_int (Int.repr 8) tuint) tuint) tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _bpf_verifier_aux (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _verifier_state noattr))
                                        (Tcons tuint (Tcons tuint Tnil)))
                                      tbool cc_default))
            ((Etempvar _st (tptr (Tstruct _verifier_state noattr))) ::
             (Etempvar _len tuint) :: (Etempvar _len tuint) :: nil))
          (Sset _b (Ecast (Etempvar _t'2 tbool) tbool)))
        (Sifthenelse (Etempvar _b tbool)
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _eval_ins (Tfunction
                                  (Tcons
                                    (tptr (Tstruct _verifier_state noattr))
                                    (Tcons tuint Tnil)) tulong cc_default))
                ((Etempvar _st (tptr (Tstruct _verifier_state noattr))) ::
                 (Ebinop Osub (Etempvar _len tuint)
                   (Econst_int (Int.repr 1) tuint) tuint) :: nil))
              (Sset _ins64 (Etempvar _t'3 tulong)))
            (Sreturn (Some (Ebinop Oeq (Etempvar _ins64 tulong)
                             (Econst_long (Int64.repr 149) tulong) tint))))
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition composites : list composite_definition :=
(Composite _verifier_state Struct
   ((_ins_len, tuint) :: (_ins, (tptr tulong)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons tint (Tcons tint Tnil)) tint
     cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_eval_ins_len, Gfun(Internal f_eval_ins_len)) ::
 (_eval_ins, Gfun(Internal f_eval_ins)) ::
 (_is_dst_R0, Gfun(Internal f_is_dst_R0)) ::
 (_is_well_dst, Gfun(Internal f_is_well_dst)) ::
 (_is_well_src, Gfun(Internal f_is_well_src)) ::
 (_is_well_jump, Gfun(Internal f_is_well_jump)) ::
 (_is_not_div_by_zero, Gfun(Internal f_is_not_div_by_zero)) ::
 (_is_not_div_by_zero64, Gfun(Internal f_is_not_div_by_zero64)) ::
 (_is_shift_range, Gfun(Internal f_is_shift_range)) ::
 (_is_shift_range64, Gfun(Internal f_is_shift_range64)) ::
 (_get_opcode, Gfun(Internal f_get_opcode)) ::
 (_get_offset, Gfun(Internal f_get_offset)) ::
 (_bpf_verifier_opcode_alu32_imm, Gfun(Internal f_bpf_verifier_opcode_alu32_imm)) ::
 (_bpf_verifier_opcode_alu32_reg, Gfun(Internal f_bpf_verifier_opcode_alu32_reg)) ::
 (_bpf_verifier_opcode_alu64_imm, Gfun(Internal f_bpf_verifier_opcode_alu64_imm)) ::
 (_bpf_verifier_opcode_alu64_reg, Gfun(Internal f_bpf_verifier_opcode_alu64_reg)) ::
 (_bpf_verifier_opcode_branch_imm, Gfun(Internal f_bpf_verifier_opcode_branch_imm)) ::
 (_bpf_verifier_opcode_branch_reg, Gfun(Internal f_bpf_verifier_opcode_branch_reg)) ::
 (_bpf_verifier_opcode_load_imm, Gfun(Internal f_bpf_verifier_opcode_load_imm)) ::
 (_bpf_verifier_opcode_load_reg, Gfun(Internal f_bpf_verifier_opcode_load_reg)) ::
 (_bpf_verifier_opcode_store_imm, Gfun(Internal f_bpf_verifier_opcode_store_imm)) ::
 (_bpf_verifier_opcode_store_reg, Gfun(Internal f_bpf_verifier_opcode_store_reg)) ::
 (_bpf_verifier_aux2, Gfun(Internal f_bpf_verifier_aux2)) ::
 (_bpf_verifier_aux, Gfun(Internal f_bpf_verifier_aux)) ::
 (_bpf_verifier, Gfun(Internal f_bpf_verifier)) :: nil).

Definition public_idents : list ident :=
(_bpf_verifier :: _bpf_verifier_aux :: _get_opcode :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___builtin_expect :: ___builtin_unreachable :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


