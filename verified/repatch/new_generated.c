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

extern unsigned char get_opcode_ins(unsigned long long);

extern unsigned char get_opcode_alu64(unsigned char);

extern unsigned char get_opcode_alu32(unsigned char);

extern unsigned char get_opcode_branch(unsigned char);

extern unsigned char get_opcode_mem_ld_imm(unsigned char);

extern unsigned char get_opcode_mem_ld_reg(unsigned char);

extern unsigned char get_opcode_mem_st_imm(unsigned char);

extern unsigned char get_opcode_mem_st_reg(unsigned char);

extern unsigned char get_opcode(unsigned char);

extern unsigned long long get_addl(unsigned long long, unsigned long long);

extern unsigned long long get_subl(unsigned long long, unsigned long long);

extern unsigned long long getMemRegion_block_ptr(struct memory_region *);

extern unsigned long long getMemRegion_start_addr(struct memory_region *);

extern unsigned long long getMemRegion_block_size(struct memory_region *);

extern _Bool is_well_chunk_bool(unsigned int);

extern unsigned long long check_mem_aux(struct memory_region *, unsigned long long, unsigned int);

extern unsigned long long check_mem(unsigned long long *, unsigned long long, unsigned int);

extern _Bool comp_and_0x08_byte(unsigned char);

extern void step_opcode_alu64(unsigned long long, unsigned int, unsigned long long, unsigned long long, unsigned char);

extern void step_opcode_alu32(unsigned long long, unsigned int, unsigned int, unsigned int, unsigned char);

extern void step_opcode_branch(unsigned long long, unsigned long long, unsigned long long, unsigned char, unsigned long long);

extern void step_opcode_mem_ld_imm(unsigned long long, unsigned int, unsigned long long, unsigned long long, unsigned char, unsigned long long, unsigned long long *);

extern void step_opcode_mem_ld_reg(unsigned long long, unsigned int, unsigned long long, unsigned long long, unsigned char, unsigned long long, unsigned long long, unsigned long long *);

extern void step_opcode_mem_st_imm(unsigned long long, unsigned int, unsigned long long, int, unsigned char, unsigned long long, unsigned long long, unsigned long long *);

extern void step_opcode_mem_st_reg(unsigned long long, unsigned int, unsigned long long, unsigned long long, unsigned char, unsigned long long, unsigned long long, unsigned long long *);

extern void step(unsigned long long, unsigned long long *);

extern void bpf_interpreter_aux(unsigned long long, unsigned int, unsigned long long *);

extern unsigned long long bpf_interpreter(unsigned long long, unsigned int, unsigned long long *);

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

unsigned long long list_get(unsigned long long *l, unsigned long long idx)
{
  return *(l + idx);
}

unsigned int get_dst(unsigned long long ins)
{
  return (unsigned int) ((ins & 4095LLU) >> 8LLU);
}

unsigned int reg64_to_reg32(unsigned long long d)
{
  return (unsigned int) d;
}

unsigned int get_src(unsigned long long ins)
{
  return (unsigned int) ((ins & 65535LLU) >> 12LLU);
}

unsigned long long get_offset(unsigned long long ins)
{
  return ins << 32LLU >> 48LLU;
}

unsigned long long eval_offset(unsigned long long ins)
{
  return ins;
}

int get_immediate(unsigned long long ins)
{
  return (int) (ins >> 32LLU);
}

unsigned long long eval_immediate(int ins)
{
  return (unsigned long long) ins;
}

unsigned char get_opcode_ins(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

unsigned char get_opcode_alu64(unsigned char op)
{
  return (unsigned char) (op & 240);
}

unsigned char get_opcode_alu32(unsigned char op)
{
  return (unsigned char) (op & 240);
}

unsigned char get_opcode_branch(unsigned char op)
{
  return (unsigned char) (op & 240);
}

unsigned char get_opcode_mem_ld_imm(unsigned char op)
{
  return (unsigned char) (op & 255);
}

unsigned char get_opcode_mem_ld_reg(unsigned char op)
{
  return (unsigned char) (op & 255);
}

unsigned char get_opcode_mem_st_imm(unsigned char op)
{
  return (unsigned char) (op & 255);
}

unsigned char get_opcode_mem_st_reg(unsigned char op)
{
  return (unsigned char) (op & 255);
}

unsigned char get_opcode(unsigned char op)
{
  return (unsigned char) (op & 7);
}

unsigned long long get_addl(unsigned long long x, unsigned long long y)
{
  return x + y;
}

unsigned long long get_subl(unsigned long long x, unsigned long long y)
{
  return x - y;
}

unsigned long long getMemRegion_block_ptr(struct memory_region *mr)
{
  return 1LLU;
}

unsigned long long getMemRegion_start_addr(struct memory_region *mr)
{
  return (*mr).start_addr;
}

unsigned long long getMemRegion_block_size(struct memory_region *mr)
{
  return (*mr).block_size;
}

_Bool is_well_chunk_bool(unsigned int chunk)
{
  switch (chunk) {
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

unsigned long long check_mem_aux(struct memory_region *mr, unsigned long long addr, unsigned int chunk)
{
  _Bool well_chunk;
  unsigned long long ptr;
  unsigned long long start;
  unsigned long long size;
  unsigned long long lo_ofs;
  unsigned long long hi_ofs;
  well_chunk = is_well_chunk_bool(chunk);
  if (well_chunk) {
    ptr = getMemRegion_block_ptr(mr);
    start = getMemRegion_start_addr(mr);
    size = getMemRegion_block_size(mr);
    lo_ofs = get_subl(addr, start);
    hi_ofs = get_addl(lo_ofs, (unsigned long long) chunk);
    if (0LLU <= lo_ofs && hi_ofs < size) {
      if (lo_ofs <= 18446744073709551615LLU - (unsigned long long) chunk
            && 0LLU == lo_ofs % (unsigned long long) chunk) {
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

unsigned long long check_mem(unsigned long long *l, unsigned long long addr, unsigned int chunk)
{
  struct memory_regions *mrs;
  unsigned long long check_mem_ctx;
  unsigned long long check_mem_stk;
  unsigned long long check_mem_content;
  mrs = eval_mem_regions();
  check_mem_ctx = check_mem_aux((*mrs).bpf_ctx, addr, chunk);
  if (check_mem_ctx == 0LLU) {
    check_mem_stk = check_mem_aux((*mrs).bpf_stk, addr, chunk);
    if (check_mem_stk == 0LLU) {
      check_mem_content = check_mem_aux((*mrs).content, addr, chunk);
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

_Bool comp_and_0x08_byte(unsigned char x)
{
  return 0 == (x & 8);
}

void step_opcode_alu64(unsigned long long pc, unsigned int dst, unsigned long long dst64, unsigned long long src64, unsigned char op)
{
  unsigned char opcode_alu64;
  unsigned int src32;
  unsigned int src32;
  unsigned int src32;
  unsigned int src32;
  opcode_alu64 = get_opcode_alu64(op);
  switch (opcode_alu64) {
    case 0:
      upd_reg(dst, dst64 + src64);
      upd_flag(0);
      return;
    case 16:
      upd_reg(dst, dst64 - src64);
      upd_flag(0);
      return;
    case 32:
      upd_reg(dst, dst64 * src64);
      upd_flag(0);
      return;
    case 48:
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 / src64);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst, dst64 | src64);
      upd_flag(0);
      return;
    case 80:
      upd_reg(dst, dst64 & src64);
      upd_flag(0);
      return;
    case 96:
      src32 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 << src32);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      src32 = reg64_to_reg32(src64);
      if (src64 < 64LLU) {
        upd_reg(dst, dst64 >> src32);
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      upd_reg(dst, -dst64);
      upd_flag(0);
      return;
    case 144:
      src32 = reg64_to_reg32(src64);
      if (src64 != 0LLU) {
        upd_reg(dst, dst64 % src32);
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst, dst64 ^ src64);
      upd_flag(0);
      return;
    case 176:
      upd_reg(dst, src64);
      upd_flag(0);
      return;
    case 192:
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

void step_opcode_alu32(unsigned long long pc, unsigned int dst, unsigned int dst32, unsigned int src32, unsigned char op)
{
  unsigned char opcode_alu32;
  opcode_alu32 = get_opcode_alu32(op);
  switch (opcode_alu32) {
    case 0:
      upd_reg(dst, (unsigned long long) (dst32 + src32));
      upd_flag(0);
      return;
    case 16:
      upd_reg(dst, (unsigned long long) (dst32 - src32));
      upd_flag(0);
      return;
    case 32:
      upd_reg(dst, (unsigned long long) (dst32 * src32));
      upd_flag(0);
      return;
    case 48:
      if (src32 != 0U) {
        upd_reg(dst, (unsigned long long) (dst32 / src32));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst, (unsigned long long) (dst32 | src32));
      upd_flag(0);
      return;
    case 80:
      upd_reg(dst, (unsigned long long) (dst32 & src32));
      upd_flag(0);
      return;
    case 96:
      if (src32 < 32U) {
        upd_reg(dst, (unsigned long long) (dst32 << src32));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      if (src32 < 32U) {
        upd_reg(dst, (unsigned long long) (dst32 >> src32));
        upd_flag(0);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      upd_reg(dst, (unsigned long long) -dst32);
      upd_flag(0);
      return;
    case 144:
      if (src32 != 0U) {
        upd_reg(dst, (unsigned long long) (dst32 % src32));
        upd_flag(0);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst, (unsigned long long) (dst32 ^ src32));
      upd_flag(0);
      return;
    case 176:
      upd_reg(dst, src32);
      upd_flag(0);
      return;
    case 192:
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

void step_opcode_branch(unsigned long long pc, unsigned long long dst64, unsigned long long src64, unsigned char op, unsigned long long ofs)
{
  unsigned char opcode_jmp;
  opcode_jmp = get_opcode_branch(op);
  switch (opcode_jmp) {
    case 0:
      upd_pc(pc + ofs);
      upd_flag(0);
      return;
    case 16:
      if (dst64 == src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 32:
      if (dst64 > src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 48:
      if (dst64 >= src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 64:
      if (dst64 < src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 80:
      if (dst64 <= src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 96:
      if ((dst64 & src64) != 0LLU) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 112:
      if (dst64 != src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 144:
      if ((long long) dst64 > (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 160:
      if ((long long) dst64 >= (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 176:
      if ((long long) dst64 < (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 192:
      if ((long long) dst64 <= (long long) src64) {
        upd_pc(pc + ofs);
        upd_flag(0);
        return;
      } else {
        upd_flag(0);
        return;
      }
    case 208:
      upd_flag(1);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_ld_imm(unsigned long long pc, unsigned int dst, unsigned long long dst64, unsigned long long imm64, unsigned char op, unsigned long long len, unsigned long long *l)
{
  unsigned char opcode_ld;
  unsigned long long next_ins;
  int next_imm;
  unsigned long long n_imm64;
  opcode_ld = get_opcode_mem_ld_imm(op);
  switch (opcode_ld) {
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

void step_opcode_mem_ld_reg(unsigned long long pc, unsigned int dst, unsigned long long dst64, unsigned long long src64, unsigned char op, unsigned long long ofs64, unsigned long long addr, unsigned long long *l)
{
  unsigned char opcode_ld;
  unsigned long long check_ldxw;
  unsigned long long v_xw;
  unsigned long long check_ldxh;
  unsigned long long v_xh;
  unsigned long long check_ldxb;
  unsigned long long v_xb;
  unsigned long long check_ldxdw;
  unsigned long long v_xdw;
  opcode_ld = get_opcode_mem_ld_reg(op);
  switch (opcode_ld) {
    case 97:
      check_ldxw = check_mem(l, addr, 4U);
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
      check_ldxh = check_mem(l, addr, 2U);
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
      check_ldxb = check_mem(l, addr, 1U);
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
      check_ldxdw = check_mem(l, addr, 8U);
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

void step_opcode_mem_st_imm(unsigned long long pc, unsigned int dst, unsigned long long dst64, int imm, unsigned char op, unsigned long long ofs64, unsigned long long addr, unsigned long long *l)
{
  unsigned char opcode_st;
  unsigned long long check_stw;
  unsigned long long check_sth;
  unsigned long long check_stb;
  unsigned long long check_stdw;
  opcode_st = get_opcode_mem_st_imm(op);
  switch (opcode_st) {
    case 98:
      check_stw = check_mem(l, addr, 4U);
      if (check_stw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(4U, dst64 + ofs64, imm);
        upd_flag(0);
        return;
      }
    case 106:
      check_sth = check_mem(l, addr, 2U);
      if (check_sth == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(2U, dst64 + ofs64, imm);
        upd_flag(0);
        return;
      }
    case 114:
      check_stb = check_mem(l, addr, 1U);
      if (check_stb == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(1U, dst64 + ofs64, imm);
        upd_flag(0);
        return;
      }
    case 122:
      check_stdw = check_mem(l, addr, 8U);
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

void step_opcode_mem_st_reg(unsigned long long pc, unsigned int dst, unsigned long long dst64, unsigned long long src64, unsigned char op, unsigned long long ofs64, unsigned long long addr, unsigned long long *l)
{
  unsigned char opcode_st;
  unsigned long long check_stxw;
  unsigned long long check_stxh;
  unsigned long long check_stxb;
  unsigned long long check_stxdw;
  opcode_st = get_opcode_mem_st_reg(op);
  switch (opcode_st) {
    case 99:
      check_stxw = check_mem(l, addr, 4U);
      if (check_stxw == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(4U, dst64 + ofs64, src64);
        upd_flag(0);
        return;
      }
    case 107:
      check_stxh = check_mem(l, addr, 2U);
      if (check_stxh == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(2U, dst64 + ofs64, src64);
        upd_flag(0);
        return;
      }
    case 115:
      check_stxb = check_mem(l, addr, 1U);
      if (check_stxb == 0LLU) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(1U, dst64 + ofs64, src64);
        upd_flag(0);
        return;
      }
    case 123:
      check_stxdw = check_mem(l, addr, 8U);
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

void step(unsigned long long len, unsigned long long *l)
{
  unsigned long long pc;
  unsigned long long ins;
  unsigned char op;
  unsigned char opc;
  unsigned int dst;
  unsigned long long dst64;
  _Bool is_imm;
  int imm;
  unsigned long long imm64;
  unsigned int src;
  unsigned long long src64;
  unsigned int dst;
  unsigned long long dst64;
  unsigned int dst32;
  _Bool is_imm;
  int imm;
  unsigned int src;
  unsigned long long src64;
  unsigned int src32;
  unsigned int dst;
  unsigned long long dst64;
  unsigned long long ofs;
  _Bool is_imm;
  int imm;
  unsigned long long imm64;
  unsigned int src;
  unsigned long long src64;
  unsigned int dst;
  unsigned long long dst64;
  int imm;
  unsigned long long imm64;
  unsigned int dst;
  unsigned long long dst64;
  unsigned int src;
  unsigned long long src64;
  unsigned long long ofs;
  unsigned long long ofs64;
  unsigned long long addr;
  unsigned int dst;
  unsigned long long dst64;
  unsigned long long ofs;
  unsigned long long ofs64;
  int imm;
  unsigned long long addr;
  unsigned int dst;
  unsigned long long dst64;
  unsigned int src;
  unsigned long long src64;
  unsigned long long ofs;
  unsigned long long ofs64;
  unsigned long long addr;
  pc = eval_pc();
  ins = list_get(l, pc);
  op = get_opcode_ins(ins);
  opc = get_opcode(op);
  switch (opc) {
    case 7:
      dst = get_dst(ins);
      dst64 = eval_reg(dst);
      is_imm = comp_and_0x08_byte(op);
      if (is_imm) {
        imm = get_immediate(ins);
        imm64 = eval_immediate(imm);
        step_opcode_alu64(pc, dst, dst64, imm64, op);
        return;
      } else {
        src = get_src(ins);
        src64 = eval_reg(src);
        step_opcode_alu64(pc, dst, dst64, src64, op);
        return;
      }
    case 4:
      dst = get_dst(ins);
      dst64 = eval_reg(dst);
      dst32 = reg64_to_reg32(dst64);
      is_imm = comp_and_0x08_byte(op);
      if (is_imm) {
        imm = get_immediate(ins);
        step_opcode_alu32(pc, dst, dst32, imm, op);
        return;
      } else {
        src = get_src(ins);
        src64 = eval_reg(src);
        src32 = reg64_to_reg32(src64);
        step_opcode_alu32(pc, dst, dst32, src32, op);
        return;
      }
    case 5:
      dst = get_dst(ins);
      dst64 = eval_reg(dst);
      ofs = get_offset(ins);
      is_imm = comp_and_0x08_byte(op);
      if (is_imm) {
        imm = get_immediate(ins);
        imm64 = eval_immediate(imm);
        step_opcode_branch(pc, dst64, imm64, op, ofs);
        return;
      } else {
        src = get_src(ins);
        src64 = eval_reg(src);
        step_opcode_branch(pc, dst64, src64, op, ofs);
        return;
      }
    case 0:
      dst = get_dst(ins);
      dst64 = eval_reg(dst);
      imm = get_immediate(ins);
      imm64 = eval_immediate(imm);
      step_opcode_mem_ld_imm(pc, dst, dst64, imm64, op,
                             len, l);
      return;
    case 1:
      dst = get_dst(ins);
      dst64 = eval_reg(dst);
      src = get_src(ins);
      src64 = eval_reg(src);
      ofs = get_offset(ins);
      ofs64 = eval_offset(ofs);
      addr = get_addl(src64, ofs64);
      step_opcode_mem_ld_reg(pc, dst, dst64, src64, op,
                             ofs64, addr, l);
      return;
    case 2:
      dst = get_dst(ins);
      dst64 = eval_reg(dst);
      ofs = get_offset(ins);
      ofs64 = eval_offset(ofs);
      imm = get_immediate(ins);
      addr = get_addl(dst64, ofs64);
      step_opcode_mem_st_imm(pc, dst, dst64, imm, op,
                             ofs64, addr, l);
      return;
    case 3:
      dst = get_dst(ins);
      dst64 = eval_reg(dst);
      src = get_src(ins);
      src64 = eval_reg(src);
      ofs = get_offset(ins);
      ofs64 = eval_offset(ofs);
      addr = get_addl(dst64, ofs64);
      step_opcode_mem_st_reg(pc, dst, dst64, src64, op,
                             ofs64, addr, l);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(unsigned long long len, unsigned int fuel, unsigned long long *l)
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
      step(len, l);
      upd_pc_incr();
      f = eval_flag();
      if (f == 0) {
        bpf_interpreter_aux(len, fuel, l);
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

unsigned long long bpf_interpreter(unsigned long long len, unsigned int fuel, unsigned long long *l)
{
  struct memory_regions *mrs;
  int f;
  mrs = eval_mem_regions();
  upd_reg(1U, (*(*mrs).bpf_ctx).start_addr);
  bpf_interpreter_aux(len, fuel, l);
  f = eval_flag();
  if (f == 1) {
    return eval_reg(0U);
  } else {
    return 0LLU;
  }
}


