struct verifier_state;
struct verifier_state {
  unsigned int ins_len;
  unsigned long long *ins$756645;
};

extern _Bool is_dst_R0(unsigned long long);

extern _Bool is_well_dst(unsigned long long);

extern _Bool is_well_src(unsigned long long);

extern _Bool is_well_jump(unsigned int, unsigned int, int);

extern _Bool is_not_div_by_zero(unsigned long long);

extern _Bool is_not_div_by_zero64(unsigned long long);

extern _Bool is_shift_range(unsigned long long, unsigned int);

extern _Bool is_shift_range64(unsigned long long, unsigned int);

extern unsigned char get_opcode(unsigned long long);

extern int get_offset(unsigned long long);

extern _Bool bpf_verifier_opcode_alu32_imm(unsigned char, unsigned long long);

extern _Bool bpf_verifier_opcode_alu32_reg(unsigned char, unsigned long long);

extern _Bool bpf_verifier_opcode_alu64_imm(unsigned char, unsigned long long);

extern _Bool bpf_verifier_opcode_alu64_reg(unsigned char, unsigned long long);

extern _Bool bpf_verifier_opcode_branch_imm(unsigned int, unsigned int, unsigned char, unsigned long long);

extern _Bool bpf_verifier_opcode_branch_reg(unsigned int, unsigned int, unsigned char, unsigned long long);

extern _Bool bpf_verifier_opcode_load_imm(unsigned char, unsigned long long);

extern _Bool bpf_verifier_opcode_load_reg(unsigned char, unsigned long long);

extern _Bool bpf_verifier_opcode_store_imm(unsigned char, unsigned long long);

extern _Bool bpf_verifier_opcode_store_reg(unsigned char, unsigned long long);

extern _Bool bpf_verifier_aux2(unsigned int, unsigned int, unsigned char, unsigned long long);

extern _Bool bpf_verifier_aux(unsigned int, unsigned int);

extern _Bool bpf_verifier(void);

extern unsigned int eval_ins_len(void);

extern unsigned long long eval_ins(unsigned int);

_Bool is_dst_R0(unsigned long long i)
{
  return (unsigned int) ((i & 4095LLU) >> 8LLU) == 0U;
}

_Bool is_well_dst(unsigned long long i$54)
{
  return (unsigned int) ((i$54 & 4095LLU) >> 8LLU) <= 10U;
}

_Bool is_well_src(unsigned long long i$56)
{
  return (unsigned int) ((i$56 & 65535LLU) >> 12LLU) <= 10U;
}

_Bool is_well_jump(unsigned int pc, unsigned int len, int ofs)
{
  return pc + ofs <= len - 2U;
}

_Bool is_not_div_by_zero(unsigned long long i$64)
{
  return (int) (i$64 >> 32LLU) != 0U;
}

_Bool is_not_div_by_zero64(unsigned long long i$66)
{
  return (long long) (int) (i$66 >> 32LLU) != 0LLU;
}

_Bool is_shift_range(unsigned long long i$68, unsigned int upper)
{
  return (int) (i$68 >> 32LLU) < upper;
}

_Bool is_shift_range64(unsigned long long i$72, unsigned int upper$74)
{
  return (unsigned int) (unsigned long long) (int) (i$72 >> 32LLU) < upper$74;
}

unsigned char get_opcode(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

int get_offset(unsigned long long i$78)
{
  return (int) (short) (i$78 << 32LLU >> 48LLU);
}

_Bool bpf_verifier_opcode_alu32_imm(unsigned char op, unsigned long long ins$82)
{
  _Bool b;
  _Bool b$86;
  _Bool b$88;
  _Bool b$90;
  _Bool b$92;
  switch (op) {
    case 4:
      return 1;
    case 20:
      return 1;
    case 36:
      return 1;
    case 52:
      b = is_not_div_by_zero(ins$82);
      return b;
    case 68:
      return 1;
    case 84:
      return 1;
    case 100:
      b$86 = is_shift_range(ins$82, 32U);
      return b$86;
    case 116:
      b$88 = is_shift_range(ins$82, 32U);
      return b$88;
    case 132:
      return 1;
    case 148:
      b$90 = is_not_div_by_zero(ins$82);
      return b$90;
    case 164:
      return 1;
    case 180:
      return 1;
    case 196:
      b$92 = is_shift_range(ins$82, 32U);
      return b$92;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_alu32_reg(unsigned char op$94, unsigned long long ins$96)
{
  _Bool b$98;
  _Bool b$100;
  _Bool b$102;
  _Bool b$104;
  _Bool b$106;
  _Bool b$108;
  _Bool b$110;
  _Bool b$112;
  _Bool b$114;
  _Bool b$116;
  _Bool b$118;
  _Bool b$120;
  switch (op$94) {
    case 12:
      b$98 = is_well_src(ins$96);
      return b$98;
    case 28:
      b$100 = is_well_src(ins$96);
      return b$100;
    case 44:
      b$102 = is_well_src(ins$96);
      return b$102;
    case 60:
      b$104 = is_well_src(ins$96);
      return b$104;
    case 76:
      b$106 = is_well_src(ins$96);
      return b$106;
    case 92:
      b$108 = is_well_src(ins$96);
      return b$108;
    case 108:
      b$110 = is_well_src(ins$96);
      return b$110;
    case 124:
      b$112 = is_well_src(ins$96);
      return b$112;
    case 156:
      b$114 = is_well_src(ins$96);
      return b$114;
    case 172:
      b$116 = is_well_src(ins$96);
      return b$116;
    case 188:
      b$118 = is_well_src(ins$96);
      return b$118;
    case 204:
      b$120 = is_well_src(ins$96);
      return b$120;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_alu64_imm(unsigned char op$122, unsigned long long ins$124)
{
  _Bool b$126;
  _Bool b$128;
  _Bool b$130;
  _Bool b$132;
  _Bool b$134;
  switch (op$122) {
    case 7:
      return 1;
    case 23:
      return 1;
    case 39:
      return 1;
    case 55:
      b$126 = is_not_div_by_zero64(ins$124);
      return b$126;
    case 71:
      return 1;
    case 87:
      return 1;
    case 103:
      b$128 = is_shift_range64(ins$124, 64U);
      return b$128;
    case 119:
      b$130 = is_shift_range64(ins$124, 64U);
      return b$130;
    case 135:
      return 1;
    case 151:
      b$132 = is_not_div_by_zero64(ins$124);
      return b$132;
    case 167:
      return 1;
    case 183:
      return 1;
    case 199:
      b$134 = is_shift_range64(ins$124, 64U);
      return b$134;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_alu64_reg(unsigned char op$136, unsigned long long ins$138)
{
  _Bool b$140;
  _Bool b$142;
  _Bool b$144;
  _Bool b$146;
  _Bool b$148;
  _Bool b$150;
  _Bool b$152;
  _Bool b$154;
  _Bool b$156;
  _Bool b$158;
  _Bool b$160;
  _Bool b$162;
  switch (op$136) {
    case 15:
      b$140 = is_well_src(ins$138);
      return b$140;
    case 31:
      b$142 = is_well_src(ins$138);
      return b$142;
    case 47:
      b$144 = is_well_src(ins$138);
      return b$144;
    case 63:
      b$146 = is_well_src(ins$138);
      return b$146;
    case 79:
      b$148 = is_well_src(ins$138);
      return b$148;
    case 95:
      b$150 = is_well_src(ins$138);
      return b$150;
    case 111:
      b$152 = is_well_src(ins$138);
      return b$152;
    case 127:
      b$154 = is_well_src(ins$138);
      return b$154;
    case 159:
      b$156 = is_well_src(ins$138);
      return b$156;
    case 175:
      b$158 = is_well_src(ins$138);
      return b$158;
    case 191:
      b$160 = is_well_src(ins$138);
      return b$160;
    case 207:
      b$162 = is_well_src(ins$138);
      return b$162;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_branch_imm(unsigned int pc$164, unsigned int len$166, unsigned char op$168, unsigned long long ins$170)
{
  int ofs$172;
  _Bool b$174;
  int ofs$176;
  _Bool b$178;
  int ofs$180;
  _Bool b$182;
  int ofs$184;
  _Bool b$186;
  int ofs$188;
  _Bool b$190;
  int ofs$192;
  _Bool b$194;
  int ofs$196;
  _Bool b$198;
  int ofs$200;
  _Bool b$202;
  int ofs$204;
  _Bool b$206;
  int ofs$208;
  _Bool b$210;
  int ofs$212;
  _Bool b$214;
  int ofs$216;
  _Bool b$218;
  _Bool b$220;
  _Bool b$222;
  switch (op$168) {
    case 5:
      ofs$172 = get_offset(ins$170);
      b$174 = is_well_jump(pc$164, len$166, ofs$172);
      return b$174;
    case 21:
      ofs$176 = get_offset(ins$170);
      b$178 = is_well_jump(pc$164, len$166, ofs$176);
      return b$178;
    case 37:
      ofs$180 = get_offset(ins$170);
      b$182 = is_well_jump(pc$164, len$166, ofs$180);
      return b$182;
    case 53:
      ofs$184 = get_offset(ins$170);
      b$186 = is_well_jump(pc$164, len$166, ofs$184);
      return b$186;
    case 165:
      ofs$188 = get_offset(ins$170);
      b$190 = is_well_jump(pc$164, len$166, ofs$188);
      return b$190;
    case 181:
      ofs$192 = get_offset(ins$170);
      b$194 = is_well_jump(pc$164, len$166, ofs$192);
      return b$194;
    case 69:
      ofs$196 = get_offset(ins$170);
      b$198 = is_well_jump(pc$164, len$166, ofs$196);
      return b$198;
    case 85:
      ofs$200 = get_offset(ins$170);
      b$202 = is_well_jump(pc$164, len$166, ofs$200);
      return b$202;
    case 101:
      ofs$204 = get_offset(ins$170);
      b$206 = is_well_jump(pc$164, len$166, ofs$204);
      return b$206;
    case 117:
      ofs$208 = get_offset(ins$170);
      b$210 = is_well_jump(pc$164, len$166, ofs$208);
      return b$210;
    case 197:
      ofs$212 = get_offset(ins$170);
      b$214 = is_well_jump(pc$164, len$166, ofs$212);
      return b$214;
    case 213:
      ofs$216 = get_offset(ins$170);
      b$218 = is_well_jump(pc$164, len$166, ofs$216);
      return b$218;
    case 133:
      b$220 = is_dst_R0(ins$170);
      return b$220;
    case 149:
      b$222 = is_dst_R0(ins$170);
      return b$222;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_branch_reg(unsigned int pc$224, unsigned int len$226, unsigned char op$228, unsigned long long ins$230)
{
  int ofs$232;
  _Bool b0;
  _Bool b$236;
  int ofs$238;
  _Bool b0$240;
  _Bool b$242;
  int ofs$244;
  _Bool b0$246;
  _Bool b$248;
  int ofs$250;
  _Bool b0$252;
  _Bool b$254;
  int ofs$256;
  _Bool b0$258;
  _Bool b$260;
  int ofs$262;
  _Bool b0$264;
  _Bool b$266;
  int ofs$268;
  _Bool b0$270;
  _Bool b$272;
  int ofs$274;
  _Bool b0$276;
  _Bool b$278;
  int ofs$280;
  _Bool b0$282;
  _Bool b$284;
  int ofs$286;
  _Bool b0$288;
  _Bool b$290;
  int ofs$292;
  _Bool b0$294;
  _Bool b$296;
  switch (op$228) {
    case 29:
      ofs$232 = get_offset(ins$230);
      b0 = is_well_src(ins$230);
      if (b0) {
        b$236 = is_well_jump(pc$224, len$226, ofs$232);
        return b$236;
      } else {
        return 0;
      }
    case 45:
      ofs$238 = get_offset(ins$230);
      b0$240 = is_well_src(ins$230);
      if (b0$240) {
        b$242 = is_well_jump(pc$224, len$226, ofs$238);
        return b$242;
      } else {
        return 0;
      }
    case 61:
      ofs$244 = get_offset(ins$230);
      b0$246 = is_well_src(ins$230);
      if (b0$246) {
        b$248 = is_well_jump(pc$224, len$226, ofs$244);
        return b$248;
      } else {
        return 0;
      }
    case 173:
      ofs$250 = get_offset(ins$230);
      b0$252 = is_well_src(ins$230);
      if (b0$252) {
        b$254 = is_well_jump(pc$224, len$226, ofs$250);
        return b$254;
      } else {
        return 0;
      }
    case 189:
      ofs$256 = get_offset(ins$230);
      b0$258 = is_well_src(ins$230);
      if (b0$258) {
        b$260 = is_well_jump(pc$224, len$226, ofs$256);
        return b$260;
      } else {
        return 0;
      }
    case 77:
      ofs$262 = get_offset(ins$230);
      b0$264 = is_well_src(ins$230);
      if (b0$264) {
        b$266 = is_well_jump(pc$224, len$226, ofs$262);
        return b$266;
      } else {
        return 0;
      }
    case 93:
      ofs$268 = get_offset(ins$230);
      b0$270 = is_well_src(ins$230);
      if (b0$270) {
        b$272 = is_well_jump(pc$224, len$226, ofs$268);
        return b$272;
      } else {
        return 0;
      }
    case 109:
      ofs$274 = get_offset(ins$230);
      b0$276 = is_well_src(ins$230);
      if (b0$276) {
        b$278 = is_well_jump(pc$224, len$226, ofs$274);
        return b$278;
      } else {
        return 0;
      }
    case 125:
      ofs$280 = get_offset(ins$230);
      b0$282 = is_well_src(ins$230);
      if (b0$282) {
        b$284 = is_well_jump(pc$224, len$226, ofs$280);
        return b$284;
      } else {
        return 0;
      }
    case 205:
      ofs$286 = get_offset(ins$230);
      b0$288 = is_well_src(ins$230);
      if (b0$288) {
        b$290 = is_well_jump(pc$224, len$226, ofs$286);
        return b$290;
      } else {
        return 0;
      }
    case 221:
      ofs$292 = get_offset(ins$230);
      b0$294 = is_well_src(ins$230);
      if (b0$294) {
        b$296 = is_well_jump(pc$224, len$226, ofs$292);
        return b$296;
      } else {
        return 0;
      }
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_load_imm(unsigned char op$298, unsigned long long ins$300)
{
  switch (op$298) {
    case 24:
      return 1;
    case 16:
      return 1;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_load_reg(unsigned char op$302, unsigned long long ins$304)
{
  _Bool b$306;
  _Bool b$308;
  _Bool b$310;
  _Bool b$312;
  switch (op$302) {
    case 97:
      b$306 = is_well_src(ins$304);
      return b$306;
    case 105:
      b$308 = is_well_src(ins$304);
      return b$308;
    case 113:
      b$310 = is_well_src(ins$304);
      return b$310;
    case 121:
      b$312 = is_well_src(ins$304);
      return b$312;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_store_imm(unsigned char op$314, unsigned long long ins$316)
{
  switch (op$314) {
    case 98:
      return 1;
    case 106:
      return 1;
    case 114:
      return 1;
    case 122:
      return 1;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_store_reg(unsigned char op$318, unsigned long long ins$320)
{
  _Bool b$322;
  _Bool b$324;
  _Bool b$326;
  _Bool b$328;
  switch (op$318) {
    case 99:
      b$322 = is_well_src(ins$320);
      return b$322;
    case 107:
      b$324 = is_well_src(ins$320);
      return b$324;
    case 115:
      b$326 = is_well_src(ins$320);
      return b$326;
    case 123:
      b$328 = is_well_src(ins$320);
      return b$328;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_aux2(unsigned int pc$330, unsigned int len$332, unsigned char op$334, unsigned long long ins$336)
{
  _Bool b$338;
  _Bool b$340;
  _Bool b$342;
  _Bool b$344;
  _Bool b$346;
  _Bool b$348;
  _Bool b$350;
  _Bool b$352;
  _Bool b$354;
  _Bool b$356;
  switch ((unsigned char) (op$334 & 7)) {
    case 7:
      if (0U == (op$334 & 8U)) {
        b$338 = bpf_verifier_opcode_alu64_imm(op$334, ins$336);
        return b$338;
      } else {
        b$340 = bpf_verifier_opcode_alu64_reg(op$334, ins$336);
        return b$340;
      }
    case 4:
      if (0U == (op$334 & 8U)) {
        b$342 = bpf_verifier_opcode_alu32_imm(op$334, ins$336);
        return b$342;
      } else {
        b$344 = bpf_verifier_opcode_alu32_reg(op$334, ins$336);
        return b$344;
      }
    case 5:
      if (0U == (op$334 & 8U)) {
        b$346 =
          bpf_verifier_opcode_branch_imm(pc$330, len$332, op$334, ins$336);
        return b$346;
      } else {
        b$348 =
          bpf_verifier_opcode_branch_reg(pc$330, len$332, op$334, ins$336);
        return b$348;
      }
    case 0:
      b$350 = bpf_verifier_opcode_load_imm(op$334, ins$336);
      return b$350;
    case 1:
      b$352 = bpf_verifier_opcode_load_reg(op$334, ins$336);
      return b$352;
    case 2:
      b$354 = bpf_verifier_opcode_store_imm(op$334, ins$336);
      return b$354;
    case 3:
      b$356 = bpf_verifier_opcode_store_reg(op$334, ins$336);
      return b$356;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_aux(unsigned int pc$358, unsigned int len$360)
{
  unsigned int n;
  unsigned long long ins$364;
  _Bool b$366;
  unsigned char op$368;
  _Bool b0$370;
  if (pc$358 == 0U) {
    return 1;
  } else {
    n = pc$358 - 1U;
    ins$364 = eval_ins(n);
    b$366 = is_well_dst(ins$364);
    if (b$366) {
      op$368 = get_opcode(ins$364);
      b0$370 = bpf_verifier_aux2(n, len$360, op$368, ins$364);
      if (b0$370) {
        return bpf_verifier_aux(n, len$360);
      } else {
        return 0;
      }
    } else {
      return 0;
    }
  }
}

_Bool bpf_verifier(void)
{
  unsigned int len$372;
  _Bool b$374;
  unsigned long long ins64;
  len$372 = eval_ins_len();
  if (1U <= len$372) {
    if (len$372 <= 4294967295U / 8U) {
      b$374 = bpf_verifier_aux(len$372, len$372);
      if (b$374) {
        ins64 = eval_ins(len$372 - 1U);
        return ins64 == 149LLU;
      } else {
        return 0;
      }
    } else {
      return 0;
    }
  } else {
    return 0;
  }
}


