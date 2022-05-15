struct verifier_state;
struct verifier_state {
  unsigned int ins_len;
  unsigned long long *ins;
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

_Bool is_well_dst(unsigned long long i)
{
  return (unsigned int) ((i & 4095LLU) >> 8LLU) <= 10U;
}

_Bool is_well_src(unsigned long long i)
{
  return (unsigned int) ((i & 65535LLU) >> 12LLU) <= 10U;
}

_Bool is_well_jump(unsigned int pc, unsigned int len, int ofs)
{
  return pc + ofs <= len - 2U;
}

_Bool is_not_div_by_zero(unsigned long long i)
{
  return (int) (i >> 32LLU) != 0U;
}

_Bool is_not_div_by_zero64(unsigned long long i)
{
  return (long long) (int) (i >> 32LLU) != 0LLU;
}

_Bool is_shift_range(unsigned long long i, unsigned int upper)
{
  return (int) (i >> 32LLU) < upper;
}

_Bool is_shift_range64(unsigned long long i, unsigned int upper)
{
  return (unsigned int) (unsigned long long) (int) (i >> 32LLU) < upper;
}

unsigned char get_opcode(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

int get_offset(unsigned long long i)
{
  return (int) (short) (i << 32LLU >> 48LLU);
}

_Bool bpf_verifier_opcode_alu32_imm(unsigned char op, unsigned long long ins)
{
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  switch (op) {
    case 4:
      return 1;
    case 20:
      return 1;
    case 36:
      return 1;
    case 52:
      b = is_not_div_by_zero(ins);
      return b;
    case 68:
      return 1;
    case 84:
      return 1;
    case 100:
      b = is_shift_range(ins, 32U);
      return b;
    case 116:
      b = is_shift_range(ins, 32U);
      return b;
    case 132:
      return 1;
    case 148:
      b = is_not_div_by_zero(ins);
      return b;
    case 164:
      return 1;
    case 180:
      return 1;
    case 196:
      b = is_shift_range(ins, 32U);
      return b;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_alu32_reg(unsigned char op, unsigned long long ins)
{
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  switch (op) {
    case 12:
      b = is_well_src(ins);
      return b;
    case 28:
      b = is_well_src(ins);
      return b;
    case 44:
      b = is_well_src(ins);
      return b;
    case 60:
      b = is_well_src(ins);
      return b;
    case 76:
      b = is_well_src(ins);
      return b;
    case 92:
      b = is_well_src(ins);
      return b;
    case 108:
      b = is_well_src(ins);
      return b;
    case 124:
      b = is_well_src(ins);
      return b;
    case 156:
      b = is_well_src(ins);
      return b;
    case 172:
      b = is_well_src(ins);
      return b;
    case 188:
      b = is_well_src(ins);
      return b;
    case 204:
      b = is_well_src(ins);
      return b;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_alu64_imm(unsigned char op, unsigned long long ins)
{
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  switch (op) {
    case 7:
      return 1;
    case 23:
      return 1;
    case 39:
      return 1;
    case 55:
      b = is_not_div_by_zero64(ins);
      return b;
    case 71:
      return 1;
    case 87:
      return 1;
    case 103:
      b = is_shift_range64(ins, 64U);
      return b;
    case 119:
      b = is_shift_range64(ins, 64U);
      return b;
    case 135:
      return 1;
    case 151:
      b = is_not_div_by_zero64(ins);
      return b;
    case 167:
      return 1;
    case 183:
      return 1;
    case 199:
      b = is_shift_range64(ins, 64U);
      return b;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_alu64_reg(unsigned char op, unsigned long long ins)
{
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  switch (op) {
    case 15:
      b = is_well_src(ins);
      return b;
    case 31:
      b = is_well_src(ins);
      return b;
    case 47:
      b = is_well_src(ins);
      return b;
    case 63:
      b = is_well_src(ins);
      return b;
    case 79:
      b = is_well_src(ins);
      return b;
    case 95:
      b = is_well_src(ins);
      return b;
    case 111:
      b = is_well_src(ins);
      return b;
    case 127:
      b = is_well_src(ins);
      return b;
    case 159:
      b = is_well_src(ins);
      return b;
    case 175:
      b = is_well_src(ins);
      return b;
    case 191:
      b = is_well_src(ins);
      return b;
    case 207:
      b = is_well_src(ins);
      return b;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_branch_imm(unsigned int pc, unsigned int len, unsigned char op, unsigned long long ins)
{
  int ofs;
  _Bool b;
  int ofs;
  _Bool b;
  int ofs;
  _Bool b;
  int ofs;
  _Bool b;
  int ofs;
  _Bool b;
  int ofs;
  _Bool b;
  int ofs;
  _Bool b;
  int ofs;
  _Bool b;
  int ofs;
  _Bool b;
  int ofs;
  _Bool b;
  int ofs;
  _Bool b;
  int ofs;
  _Bool b;
  _Bool b;
  _Bool b;
  switch (op) {
    case 5:
      ofs = get_offset(ins);
      b = is_well_jump(pc, len, ofs);
      return b;
    case 21:
      ofs = get_offset(ins);
      b = is_well_jump(pc, len, ofs);
      return b;
    case 37:
      ofs = get_offset(ins);
      b = is_well_jump(pc, len, ofs);
      return b;
    case 53:
      ofs = get_offset(ins);
      b = is_well_jump(pc, len, ofs);
      return b;
    case 165:
      ofs = get_offset(ins);
      b = is_well_jump(pc, len, ofs);
      return b;
    case 181:
      ofs = get_offset(ins);
      b = is_well_jump(pc, len, ofs);
      return b;
    case 69:
      ofs = get_offset(ins);
      b = is_well_jump(pc, len, ofs);
      return b;
    case 85:
      ofs = get_offset(ins);
      b = is_well_jump(pc, len, ofs);
      return b;
    case 101:
      ofs = get_offset(ins);
      b = is_well_jump(pc, len, ofs);
      return b;
    case 117:
      ofs = get_offset(ins);
      b = is_well_jump(pc, len, ofs);
      return b;
    case 197:
      ofs = get_offset(ins);
      b = is_well_jump(pc, len, ofs);
      return b;
    case 213:
      ofs = get_offset(ins);
      b = is_well_jump(pc, len, ofs);
      return b;
    case 133:
      b = is_dst_R0(ins);
      return b;
    case 149:
      b = is_dst_R0(ins);
      return b;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_branch_reg(unsigned int pc, unsigned int len, unsigned char op, unsigned long long ins)
{
  int ofs;
  _Bool b0;
  _Bool b;
  int ofs;
  _Bool b0;
  _Bool b;
  int ofs;
  _Bool b0;
  _Bool b;
  int ofs;
  _Bool b0;
  _Bool b;
  int ofs;
  _Bool b0;
  _Bool b;
  int ofs;
  _Bool b0;
  _Bool b;
  int ofs;
  _Bool b0;
  _Bool b;
  int ofs;
  _Bool b0;
  _Bool b;
  int ofs;
  _Bool b0;
  _Bool b;
  int ofs;
  _Bool b0;
  _Bool b;
  int ofs;
  _Bool b0;
  _Bool b;
  switch (op) {
    case 29:
      ofs = get_offset(ins);
      b0 = is_well_src(ins);
      if (b0) {
        b = is_well_jump(pc, len, ofs);
        return b;
      } else {
        return 0;
      }
    case 45:
      ofs = get_offset(ins);
      b0 = is_well_src(ins);
      if (b0) {
        b = is_well_jump(pc, len, ofs);
        return b;
      } else {
        return 0;
      }
    case 61:
      ofs = get_offset(ins);
      b0 = is_well_src(ins);
      if (b0) {
        b = is_well_jump(pc, len, ofs);
        return b;
      } else {
        return 0;
      }
    case 173:
      ofs = get_offset(ins);
      b0 = is_well_src(ins);
      if (b0) {
        b = is_well_jump(pc, len, ofs);
        return b;
      } else {
        return 0;
      }
    case 189:
      ofs = get_offset(ins);
      b0 = is_well_src(ins);
      if (b0) {
        b = is_well_jump(pc, len, ofs);
        return b;
      } else {
        return 0;
      }
    case 77:
      ofs = get_offset(ins);
      b0 = is_well_src(ins);
      if (b0) {
        b = is_well_jump(pc, len, ofs);
        return b;
      } else {
        return 0;
      }
    case 93:
      ofs = get_offset(ins);
      b0 = is_well_src(ins);
      if (b0) {
        b = is_well_jump(pc, len, ofs);
        return b;
      } else {
        return 0;
      }
    case 109:
      ofs = get_offset(ins);
      b0 = is_well_src(ins);
      if (b0) {
        b = is_well_jump(pc, len, ofs);
        return b;
      } else {
        return 0;
      }
    case 125:
      ofs = get_offset(ins);
      b0 = is_well_src(ins);
      if (b0) {
        b = is_well_jump(pc, len, ofs);
        return b;
      } else {
        return 0;
      }
    case 205:
      ofs = get_offset(ins);
      b0 = is_well_src(ins);
      if (b0) {
        b = is_well_jump(pc, len, ofs);
        return b;
      } else {
        return 0;
      }
    case 221:
      ofs = get_offset(ins);
      b0 = is_well_src(ins);
      if (b0) {
        b = is_well_jump(pc, len, ofs);
        return b;
      } else {
        return 0;
      }
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_load_imm(unsigned char op, unsigned long long ins)
{
  switch (op) {
    case 24:
      return 1;
    case 16:
      return 1;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_load_reg(unsigned char op, unsigned long long ins)
{
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  switch (op) {
    case 97:
      b = is_well_src(ins);
      return b;
    case 105:
      b = is_well_src(ins);
      return b;
    case 113:
      b = is_well_src(ins);
      return b;
    case 121:
      b = is_well_src(ins);
      return b;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_opcode_store_imm(unsigned char op, unsigned long long ins)
{
  switch (op) {
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

_Bool bpf_verifier_opcode_store_reg(unsigned char op, unsigned long long ins)
{
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  switch (op) {
    case 99:
      b = is_well_src(ins);
      return b;
    case 107:
      b = is_well_src(ins);
      return b;
    case 115:
      b = is_well_src(ins);
      return b;
    case 123:
      b = is_well_src(ins);
      return b;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_aux2(unsigned int pc, unsigned int len, unsigned char op, unsigned long long ins)
{
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  _Bool b;
  switch ((unsigned char) (op & 7)) {
    case 7:
      if (0U == (op & 8U)) {
        b = bpf_verifier_opcode_alu64_imm(op, ins);
        return b;
      } else {
        b = bpf_verifier_opcode_alu64_reg(op, ins);
        return b;
      }
    case 4:
      if (0U == (op & 8U)) {
        b = bpf_verifier_opcode_alu32_imm(op, ins);
        return b;
      } else {
        b = bpf_verifier_opcode_alu32_reg(op, ins);
        return b;
      }
    case 5:
      if (0U == (op & 8U)) {
        b =
          bpf_verifier_opcode_branch_imm(pc, len, op, ins);
        return b;
      } else {
        b =
          bpf_verifier_opcode_branch_reg(pc, len, op, ins);
        return b;
      }
    case 0:
      b = bpf_verifier_opcode_load_imm(op, ins);
      return b;
    case 1:
      b = bpf_verifier_opcode_load_reg(op, ins);
      return b;
    case 2:
      b = bpf_verifier_opcode_store_imm(op, ins);
      return b;
    case 3:
      b = bpf_verifier_opcode_store_reg(op, ins);
      return b;
    default:
      return 0;
    
  }
}

_Bool bpf_verifier_aux(unsigned int pc, unsigned int len)
{
  unsigned int n;
  unsigned long long ins;
  _Bool b;
  unsigned char op;
  _Bool b0;
  if (pc == 0U) {
    return 1;
  } else {
    n = pc - 1U;
    ins = eval_ins(n);
    b = is_well_dst(ins);
    if (b) {
      op = get_opcode(ins);
      b0 = bpf_verifier_aux2(n, len, op, ins);
      if (b0) {
        return bpf_verifier_aux(n, len);
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
  unsigned int len;
  _Bool b;
  unsigned long long ins64;
  len = eval_ins_len();
  if (1U <= len) {
    if (len <= 4294967295U / 8U) {
      b = bpf_verifier_aux(len, len);
      if (b) {
        ins64 = eval_ins(len - 1U);
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


