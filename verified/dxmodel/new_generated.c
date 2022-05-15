struct memory_region;
struct memory_regions;
struct bpf_state;
struct memory_region {
  unsigned long long start_addr;
  unsigned long long block_size;
  unsigned long long block_ptr;
};

struct memory_regions {
  struct memory_region *bpf_ctx;
  struct memory_region *bpf_stk;
  struct memory_region *content;
};

struct bpf_state {
  unsigned int state_pc;
  unsigned long long regsmap[11];
  int bpf_flag;
  struct memory_regions *mrs;
};

extern unsigned long long list_get(unsigned long long *, unsigned long long);

extern unsigned int get_dst(unsigned long long);

extern unsigned int reg64_to_reg32(unsigned long long);

extern unsigned int get_src(unsigned long long);

extern unsigned long long get_offset(unsigned long long);

extern unsigned long long eval_offset(unsigned long long);

extern int get_immediate(unsigned long long);

extern unsigned long long eval_immediate(int);

extern unsigned char get_opcode_alu64_imm(unsigned long long);

extern unsigned char get_opcode_alu64_reg(unsigned long long);

extern unsigned char get_opcode_alu32_imm(unsigned long long);

extern unsigned char get_opcode_alu32_reg(unsigned long long);

extern unsigned char get_opcode_branch_imm(unsigned long long);

extern unsigned char get_opcode_branch_reg(unsigned long long);

extern unsigned char get_opcode_mem_ld_imm(unsigned long long);

extern unsigned char get_opcode_mem_ld_reg(unsigned long long);

extern unsigned char get_opcode_mem_st_imm(unsigned long long);

extern unsigned char get_opcode_mem_st_reg(unsigned long long);

extern unsigned char get_opcode(unsigned long long);

extern unsigned long long get_addl(unsigned long long, unsigned long long);

extern unsigned long long get_subl(unsigned long long, unsigned long long);

extern unsigned long long getMemRegion_block_ptr(struct memory_region *);

extern unsigned long long getMemRegion_start_addr(struct memory_region *);

extern unsigned long long getMemRegion_block_size(struct memory_region *);

extern _Bool is_well_chunk_bool(unsigned int);

extern unsigned long long check_mem_aux(struct memory_region *, unsigned long long, unsigned int);

extern unsigned long long check_mem(unsigned long long *, unsigned long long, unsigned int);

extern void step_opcode_alu64_imm(unsigned long long *);

extern void step_opcode_alu64_reg(unsigned long long *);

extern void step_opcode_alu32_imm(unsigned long long *);

extern void step_opcode_alu32_reg(unsigned long long *);

extern void step_opcode_branch_imm(unsigned long long *);

extern void step_opcode_branch_reg(unsigned long long *);

extern void step_opcode_mem_ld_imm(unsigned long long *, unsigned long long);

extern void step_opcode_mem_ld_reg(unsigned long long *);

extern void step_opcode_mem_st_imm(unsigned long long *);

extern void step_opcode_mem_st_reg(unsigned long long *);

extern void step(unsigned long long *, unsigned long long);

extern void bpf_interpreter_aux(unsigned long long *, unsigned long long, unsigned int);

extern unsigned long long bpf_interpreter(unsigned long long *, unsigned long long, unsigned int);

extern unsigned long long eval_pc(void);

extern void upd_pc(unsigned long long);

extern void upd_pc_incr(void);

extern unsigned long long eval_reg(unsigned int);

extern void upd_reg(unsigned int, unsigned long long);

extern int eval_flag(void);

extern void upd_flag(int);

extern struct memory_regions *eval_mem_regions(void);

extern void upd_mem_regions(struct memory_regions *);

extern unsigned long long load_mem(unsigned int, unsigned long long);

extern void store_mem_imm(unsigned int, unsigned long long, int);

extern void store_mem_reg(unsigned int, unsigned long long, unsigned long long);

unsigned long long list_get(unsigned long long *l, unsigned long long idx0)
{
  return *(l + idx0);
}

unsigned int get_dst(unsigned long long ins1)
{
  return (unsigned int) ((ins1 & 4095LLU) >> 8LLU);
}

unsigned int reg64_to_reg32(unsigned long long d)
{
  return (unsigned int) d;
}

unsigned int get_src(unsigned long long ins2)
{
  return (unsigned int) ((ins2 & 65535LLU) >> 12LLU);
}

unsigned long long get_offset(unsigned long long i)
{
  return i << 32LLU >> 48LLU;
}

unsigned long long eval_offset(unsigned long long i)
{
  return i;
}

int get_immediate(unsigned long long i1)
{
  return (int) (i1 >> 32LLU);
}

unsigned long long eval_immediate(int i)
{
  return (unsigned long long) i;
}

unsigned char get_opcode_alu64_imm(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

unsigned char get_opcode_alu64_reg(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

unsigned char get_opcode_alu32_imm(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

unsigned char get_opcode_alu32_reg(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

unsigned char get_opcode_branch_imm(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

unsigned char get_opcode_branch_reg(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

unsigned char get_opcode_mem_ld_imm(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

unsigned char get_opcode_mem_ld_reg(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

unsigned char get_opcode_mem_st_imm(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

unsigned char get_opcode_mem_st_reg(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

unsigned char get_opcode(unsigned long long ins)
{
  return (unsigned char) (ins & 15LLU);
}

unsigned long long get_addl(unsigned long long x, unsigned long long y)
{
  return x + y;
}

unsigned long long get_subl(unsigned long long x1, unsigned long long y1)
{
  return x1 - y1;
}

unsigned long long getMemRegion_block_ptr(struct memory_region *mr0)
{
  return 1LLU;
}

unsigned long long getMemRegion_start_addr(struct memory_region *mr1)
{
  return (*mr1).start_addr;
}

unsigned long long getMemRegion_block_size(struct memory_region *mr2)
{
  return (*mr2).block_size;
}

_Bool is_well_chunk_bool(unsigned int chunk0)
{
  switch (chunk0) {
    case 1:
      return 1;
    case 2:
      return 1;
    case 4:
      return 1;
    case 8:
      return 1;
    default:
      return 0;
    
  }
}

unsigned long long check_mem_aux(struct memory_region *mr3, unsigned long long addr0, unsigned int chunk1)
{
  _Bool well_chunk;
  unsigned long long ptr;
  unsigned long long start;
  unsigned long long size;
  unsigned long long lo_ofs;
  unsigned long long hi_ofs;
  well_chunk = is_well_chunk_bool(chunk1);
  if (well_chunk) {
    ptr = getMemRegion_block_ptr(mr3);
    start = getMemRegion_start_addr(mr3);
    size = getMemRegion_block_size(mr3);
    lo_ofs = get_subl(addr0, start);
    hi_ofs = get_addl(lo_ofs, (unsigned long long) chunk1);
    if (0LLU <= lo_ofs && hi_ofs < size) {
      if (lo_ofs <= 18446744073709551615LLU - (unsigned long long) chunk1
            && 0LLU == lo_ofs % (unsigned long long) chunk1) {
        return ptr + lo_ofs;
      } else {
        return 0LLU;
      }
    } else {
      return 0LLU;
    }
  } else {
    return 0LLU;
  }
}

unsigned long long check_mem(unsigned long long *l, unsigned long long addr1, unsigned int chunk2)
{
  struct memory_regions *mrs;
  unsigned long long check_mem_ctx;
  unsigned long long check_mem_stk;
  unsigned long long check_mem_content;
  mrs = eval_mem_regions();
  check_mem_ctx = check_mem_aux((*mrs).bpf_ctx, addr1, chunk2);
  if (check_mem_ctx == 0LLU) {
    check_mem_stk = check_mem_aux((*mrs).bpf_stk, addr1, chunk2);
    if (check_mem_stk == 0LLU) {
      check_mem_content = check_mem_aux((*mrs).content, addr1, chunk2);
      if (check_mem_content == 0LLU) {
        return 0LLU;
      } else {
        return check_mem_content;
      }
    } else {
      return check_mem_stk;
    }
  } else {
    return check_mem_ctx;
  }
}

void step_opcode_alu64_imm(unsigned long long *l)
{
  unsigned long long pc;
  unsigned long long ins;
  unsigned int dst;
  unsigned long long dst64;
  int imm;
  unsigned long long imm64;
  unsigned char opcode;
  pc = eval_pc();
  ins = list_get(l, pc);
  dst = get_dst(ins);
  dst64 = eval_reg(dst);
  imm = get_immediate(ins);
  imm64 = eval_immediate(imm);
  opcode = get_opcode_alu64_imm(ins);
  switch (opcode) {
    case 7:
      upd_reg(dst, dst64 + imm64);
      upd_flag(0);
      return;
    case 23:
      upd_reg(dst, dst64 - imm64);
      upd_flag(0);
      return;
    case 39:
      upd_reg(dst, dst64 * imm64);
      upd_flag(0);
      return;
    case 55:
      if (imm64 != 0LLU) {
        upd_reg(dst, dst64 / imm64);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 71:
      upd_reg(dst, dst64 | imm64);
      upd_flag(0);
      return;
    case 87:
      upd_reg(dst, dst64 & imm64);
      upd_flag(0);
      return;
    case 103:
      if (imm64 < 64LLU) {
        upd_reg(dst, dst64 << imm);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 119:
      if (imm64 < 64LLU) {
        upd_reg(dst, dst64 >> imm);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 135:
      upd_reg(dst, -dst64);
      upd_flag(0);
      return;
    case 151:
      if (imm64 != 0LLU) {
        upd_reg(dst, dst64 % imm);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 167:
      upd_reg(dst, dst64 ^ imm64);
      upd_flag(0);
      return;
    case 183:
      upd_reg(dst, imm64);
      upd_flag(0);
      return;
    case 199:
      if (imm64 < 64LLU) {
        upd_reg(dst, (long long) dst64 >> imm);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_alu64_reg(unsigned long long *l)
{
  unsigned long long pc;
  unsigned long long ins;
  unsigned int dst;
  unsigned long long dst64;
  unsigned int src;
  unsigned long long src64;
  unsigned char opcode;
  unsigned int src32;
  unsigned int src32;
  unsigned int src32;
  unsigned int src32;
  pc = eval_pc();
  ins = list_get(l, pc);
  dst = get_dst(ins);
  dst64 = eval_reg(dst);
  src = get_src(ins);
  src64 = eval_reg(src);
  opcode = get_opcode_alu64_reg(ins);
  switch (opcode) {
    case 15:
      upd_reg(dst, dst64 + src64);
      upd_flag(0);
      return;
    case 31:
      upd_reg(dst, dst64 - src64);
      upd_flag(0);
      return;
    case 47:
      upd_reg(dst, dst64 * src64);
      upd_flag(0);
      return;
    case 63:
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 / src64);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 79:
      upd_reg(dst, dst64 | src64);
      upd_flag(0);
      return;
    case 95:
      upd_reg(dst, dst64 & src64);
      upd_flag(0);
      return;
    case 111:
      src32 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 << src32);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 127:
      src32 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 >> src32);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 159:
      src32 = reg64_to_reg32(src64);
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 % src32);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 175:
      upd_reg(dst, dst64 ^ src64);
      upd_flag(0);
      return;
    case 191:
      upd_reg(dst, src64);
      upd_flag(0);
      return;
    case 207:
      src32 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst, (long long) dst64 >> src32);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_alu32_imm(unsigned long long *l)
{
  unsigned long long pc;
  unsigned long long ins;
  unsigned int dst;
  unsigned long long dst64;
  unsigned int dst32;
  int imm;
  unsigned char opcode;
  pc = eval_pc();
  ins = list_get(l, pc);
  dst = get_dst(ins);
  dst64 = eval_reg(dst);
  dst32 = reg64_to_reg32(dst64);
  imm = get_immediate(ins);
  opcode = get_opcode_alu32_imm(ins);
  switch (opcode) {
    case 4:
      upd_reg(dst, (unsigned long long) (dst32 + imm));
      upd_flag(0);
      return;
    case 20:
      upd_reg(dst, (unsigned long long) (dst32 - imm));
      upd_flag(0);
      return;
    case 36:
      upd_reg(dst, (unsigned long long) (dst32 * imm));
      upd_flag(0);
      return;
    case 52:
      if (imm != 0U) {
        upd_reg(dst, (unsigned long long) (dst32 / imm));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 68:
      upd_reg(dst, (unsigned long long) (dst32 | imm));
      upd_flag(0);
      return;
    case 84:
      upd_reg(dst, (unsigned long long) (dst32 & imm));
      upd_flag(0);
      return;
    case 100:
      if (imm < 32U) {
        upd_reg(dst, (unsigned long long) (dst32 << imm));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 116:
      if (imm < 32U) {
        upd_reg(dst, (unsigned long long) (dst32 >> imm));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 132:
      upd_reg(dst, (unsigned long long) -dst32);
      upd_flag(0);
      return;
    case 148:
      if (imm != 0U) {
        upd_reg(dst, (unsigned long long) (dst32 % imm));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 164:
      upd_reg(dst, (unsigned long long) (dst32 ^ imm));
      upd_flag(0);
      return;
    case 180:
      upd_reg(dst, imm);
      upd_flag(0);
      return;
    case 196:
      if (imm < 32U) {
        upd_reg(dst, (unsigned long long) ((int) dst32 >> imm));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_alu32_reg(unsigned long long *l)
{
  unsigned long long pc;
  unsigned long long ins;
  unsigned int dst;
  unsigned long long dst64;
  unsigned int dst32;
  unsigned int src;
  unsigned long long src64;
  unsigned int src32;
  unsigned char opcode;
  pc = eval_pc();
  ins = list_get(l, pc);
  dst = get_dst(ins);
  dst64 = eval_reg(dst);
  dst32 = reg64_to_reg32(dst64);
  src = get_src(ins);
  src64 = eval_reg(src);
  src32 = reg64_to_reg32(src64);
  opcode = get_opcode_alu32_reg(ins);
  switch (opcode) {
    case 12:
      upd_reg(dst, (unsigned long long) (dst32 + src32));
      upd_flag(0);
      return;
    case 28:
      upd_reg(dst, (unsigned long long) (dst32 - src32));
      upd_flag(0);
      return;
    case 44:
      upd_reg(dst, (unsigned long long) (dst32 * src32));
      upd_flag(0);
      return;
    case 60:
      if (src32 != 0U) {
        upd_reg(dst, (unsigned long long) (dst32 / src32));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 76:
      upd_reg(dst, (unsigned long long) (dst32 | src32));
      upd_flag(0);
      return;
    case 92:
      upd_reg(dst, (unsigned long long) (dst32 & src32));
      upd_flag(0);
      return;
    case 108:
      if (src32 < 32U) {
        upd_reg(dst, (unsigned long long) (dst32 << src32));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 124:
      if (src32 < 32U) {
        upd_reg(dst, (unsigned long long) (dst32 >> src32));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 156:
      if (src32 != 0U) {
        upd_reg(dst, (unsigned long long) (dst32 % src32));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 172:
      upd_reg(dst, (unsigned long long) (dst32 ^ src32));
      upd_flag(0);
      return;
    case 188:
      upd_reg(dst, src32);
      upd_flag(0);
      return;
    case 204:
      if (src32 < 32U) {
        upd_reg(dst, (unsigned long long) ((int) dst32 >> src32));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_branch_imm(unsigned long long *l)
{
  unsigned long long pc;
  unsigned long long ins;
  unsigned int dst;
  unsigned long long dst64;
  unsigned long long ofs;
  int imm;
  unsigned char opcode;
  pc = eval_pc();
  ins = list_get(l, pc);
  dst = get_dst(ins);
  dst64 = eval_reg(dst);
  ofs = get_offset(ins);
  imm = get_immediate(ins);
  opcode = get_opcode_branch_imm(ins);
  switch (opcode) {
    case 5:
      upd_pc(pc + ofs);
      upd_flag(0);
      return;
    case 21:
      if (dst64 == (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 37:
      if (dst64 > (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 53:
      if (dst64 >= (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 69:
      if (dst64 < (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 85:
      if (dst64 <= (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 101:
      if ((dst64 & (unsigned long long) imm) != 0LLU) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 117:
      if (dst64 != (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 149:
      if ((long long) dst64 > (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 165:
      if ((long long) dst64 >= (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 181:
      if ((long long) dst64 < (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 197:
      if ((long long) dst64 <= (long long) (unsigned long long) imm) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 213:
      upd_flag(1);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_branch_reg(unsigned long long *l)
{
  unsigned long long pc;
  unsigned long long ins;
  unsigned int dst;
  unsigned long long dst64;
  unsigned int src;
  unsigned long long src64;
  unsigned long long ofs;
  unsigned char opcode;
  pc = eval_pc();
  ins = list_get(l, pc);
  dst = get_dst(ins);
  dst64 = eval_reg(dst);
  src = get_src(ins);
  src64 = eval_reg(src);
  ofs = get_offset(ins);
  opcode = get_opcode_branch_reg(ins);
  switch (opcode) {
    case 29:
      if (dst64 == src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 45:
      if (dst64 > src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 61:
      if (dst64 >= src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 173:
      if (dst64 < src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 189:
      if (dst64 <= src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 77:
      if ((dst64 & src64) != 0LLU) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 93:
      if (dst64 != src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 109:
      if ((long long) dst64 > (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 125:
      if ((long long) dst64 >= (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 205:
      if ((long long) dst64 < (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 221:
      if ((long long) dst64 <= (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_ld_imm(unsigned long long *l, unsigned long long len)
{
  unsigned long long pc;
  unsigned long long ins;
  unsigned int dst;
  int imm;
  unsigned long long imm64;
  unsigned char opcode;
  unsigned long long next_ins;
  int next_imm;
  unsigned long long n_imm64;
  pc = eval_pc();
  ins = list_get(l, pc);
  dst = get_dst(ins);
  eval_reg(dst);
  get_offset(ins);
  imm = get_immediate(ins);
  imm64 = eval_immediate(imm);
  opcode = get_opcode_mem_ld_imm(ins);
  switch (opcode) {
    case 24:
      if (pc + 1LLU < len) {
        next_ins = list_get(l, pc + 1LLU);
        next_imm = get_immediate(next_ins);
        n_imm64 = eval_immediate(next_imm);
        upd_reg(dst, imm64 | n_imm64 << 32U);
        upd_pc_incr();
        upd_flag(0);
        return;
      } else {
        upd_flag(-5);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_ld_reg(unsigned long long *l)
{
  unsigned long long pc;
  unsigned long long ins;
  unsigned int dst;
  unsigned int src;
  unsigned long long src64;
  unsigned long long ofs;
  unsigned long long ofs64;
  unsigned char opcode;
  unsigned long long addr_src;
  unsigned long long check_ldxw;
  unsigned long long v_xw;
  unsigned long long check_ldxh;
  unsigned long long v_xh;
  unsigned long long check_ldxb;
  unsigned long long v_xb;
  unsigned long long check_ldxdw;
  unsigned long long v_xdw;
  pc = eval_pc();
  ins = list_get(l, pc);
  dst = get_dst(ins);
  src = get_src(ins);
  src64 = eval_reg(src);
  ofs = get_offset(ins);
  ofs64 = eval_offset(ofs);
  opcode = get_opcode_mem_ld_reg(ins);
  addr_src = get_addl(src64, ofs64);
  switch (opcode) {
    case 97:
      check_ldxw = check_mem(l, addr_src, 4U);
      if (check_ldxw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xw = load_mem(4U, src64 + ofs64);
        upd_reg(dst, v_xw);
        upd_flag(0);
        return;
      }
    case 105:
      check_ldxh = check_mem(l, addr_src, 2U);
      if (check_ldxh == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xh = load_mem(2U, src64 + ofs64);
        upd_reg(dst, v_xh);
        upd_flag(0);
        return;
      }
    case 113:
      check_ldxb = check_mem(l, addr_src, 1U);
      if (check_ldxb == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xb = load_mem(1U, src64 + ofs64);
        upd_reg(dst, v_xb);
        upd_flag(0);
        return;
      }
    case 121:
      check_ldxdw = check_mem(l, addr_src, 8U);
      if (check_ldxdw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        v_xdw = load_mem(8U, src64 + ofs64);
        upd_reg(dst, v_xdw);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_imm(unsigned long long *l)
{
  unsigned long long pc;
  unsigned long long ins;
  unsigned int dst;
  unsigned long long dst64;
  unsigned long long ofs;
  unsigned long long ofs64;
  int imm;
  unsigned long long addr_dst;
  unsigned char opcode;
  unsigned long long check_stw;
  unsigned long long check_sth;
  unsigned long long check_stb;
  unsigned long long check_stdw;
  pc = eval_pc();
  ins = list_get(l, pc);
  dst = get_dst(ins);
  dst64 = eval_reg(dst);
  ofs = get_offset(ins);
  ofs64 = eval_offset(ofs);
  imm = get_immediate(ins);
  addr_dst = get_addl(dst64, ofs64);
  opcode = get_opcode_mem_st_imm(ins);
  switch (opcode) {
    case 98:
      check_stw = check_mem(l, addr_dst, 4U);
      if (check_stw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, dst64 + ofs64, imm);
        upd_flag(0);
        return;
      }
    case 106:
      check_sth = check_mem(l, addr_dst, 2U);
      if (check_sth == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, dst64 + ofs64, imm);
        upd_flag(0);
        return;
      }
    case 114:
      check_stb = check_mem(l, addr_dst, 1U);
      if (check_stb == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, dst64 + ofs64, imm);
        upd_flag(0);
        return;
      }
    case 122:
      check_stdw = check_mem(l, addr_dst, 8U);
      if (check_stdw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(8U, dst64 + ofs64, imm);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_reg(unsigned long long *l)
{
  unsigned long long pc;
  unsigned long long ins;
  unsigned int dst;
  unsigned long long dst64;
  unsigned int src;
  unsigned long long src64;
  unsigned long long ofs;
  unsigned long long ofs64;
  unsigned long long addr_dst;
  unsigned char opcode;
  unsigned long long check_stxw;
  unsigned long long check_stxh;
  unsigned long long check_stxb;
  unsigned long long check_stxdw;
  pc = eval_pc();
  ins = list_get(l, pc);
  dst = get_dst(ins);
  dst64 = eval_reg(dst);
  src = get_src(ins);
  src64 = eval_reg(src);
  ofs = get_offset(ins);
  ofs64 = eval_offset(ofs);
  addr_dst = get_addl(dst64, ofs64);
  opcode = get_opcode_mem_st_reg(ins);
  switch (opcode) {
    case 99:
      check_stxw = check_mem(l, addr_dst, 4U);
      if (check_stxw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, dst64 + ofs64, src64);
        upd_flag(0);
        return;
      }
    case 107:
      check_stxh = check_mem(l, addr_dst, 2U);
      if (check_stxh == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, dst64 + ofs64, src64);
        upd_flag(0);
        return;
      }
    case 115:
      check_stxb = check_mem(l, addr_dst, 1U);
      if (check_stxb == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, dst64 + ofs64, src64);
        upd_flag(0);
        return;
      }
    case 123:
      check_stxdw = check_mem(l, addr_dst, 8U);
      if (check_stxdw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(8U, dst64 + ofs64, src64);
        upd_flag(0);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(unsigned long long *l, unsigned long long len)
{
  unsigned long long pc;
  unsigned long long ins;
  unsigned char op;
  pc = eval_pc();
  ins = list_get(l, pc);
  op = get_opcode(ins);
  switch (op) {
    case 7:
      step_opcode_alu64_imm(l);
      return;
    case 15:
      step_opcode_alu64_reg(l);
      return;
    case 4:
      step_opcode_alu32_imm(l);
      return;
    case 12:
      step_opcode_alu32_reg(l);
      return;
    case 5:
      step_opcode_branch_imm(l);
      return;
    case 13:
      step_opcode_branch_reg(l);
      return;
    case 8:
      step_opcode_mem_ld_imm(l, len);
      return;
    case 1:
      step_opcode_mem_ld_reg(l);
      return;
    case 9:
      step_opcode_mem_ld_reg(l);
      return;
    case 2:
      step_opcode_mem_st_imm(l);
      return;
    case 10:
      step_opcode_mem_st_imm(l);
      return;
    case 3:
      step_opcode_mem_st_reg(l);
      return;
    case 11:
      step_opcode_mem_st_reg(l);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(unsigned long long *l, unsigned long long len, unsigned int fuel)
{
  unsigned int fuel;
  unsigned long long pc;
  int f;
  if (fuel == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel = fuel - 1U;
    pc = eval_pc();
    if (pc < len) {
      step(l, len);
      upd_pc_incr();
      f = eval_flag();
      if (f == 0) {
        bpf_interpreter_aux(l, len, fuel);
        return;
      } else {
        return;
      }
    } else {
      upd_flag(-5);
      return;
    }
  }
}

unsigned long long bpf_interpreter(unsigned long long *l, unsigned long long len, unsigned int fuel)
{
  struct memory_regions *mrs;
  int f;
  mrs = eval_mem_regions();
  upd_reg(1U, (*(*mrs).bpf_ctx).start_addr);
  bpf_interpreter_aux(l, len, fuel);
  f = eval_flag();
  if (f == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}


