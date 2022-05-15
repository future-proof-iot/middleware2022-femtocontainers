struct memory_region;
struct bpf_state;
struct memory_region {
  unsigned int start_addr;
  unsigned int block_size;
  unsigned int block_perm;
  unsigned char *block_ptr;
};

struct bpf_state {
  unsigned int state_pc;
  int bpf_flag;
  unsigned long long regsmap[11];
  unsigned int mrs_num;
  struct memory_region *mrs$757165;
  unsigned int ins_len;
  unsigned long long *ins$756645;
};

extern unsigned int reg64_to_reg32(unsigned long long);

extern int get_offset(unsigned long long);

extern int get_immediate(unsigned long long);

extern long long eval_immediate(int);

extern unsigned long long get_src64(unsigned char, unsigned long long);

extern unsigned int get_src32(unsigned char, unsigned long long);

extern unsigned char get_opcode_ins(unsigned long long);

extern unsigned char get_opcode_alu64(unsigned char);

extern unsigned char get_opcode_alu32(unsigned char);

extern unsigned char get_opcode_branch(unsigned char);

extern unsigned char get_opcode_mem_ld_imm(unsigned char);

extern unsigned char get_opcode_mem_ld_reg(unsigned char);

extern unsigned char get_opcode_mem_st_imm(unsigned char);

extern unsigned char get_opcode_mem_st_reg(unsigned char);

extern unsigned char get_opcode(unsigned char);

extern unsigned int get_add(unsigned int, unsigned int);

extern unsigned int get_sub(unsigned int, unsigned int);

extern unsigned int get_addr_ofs(unsigned long long, int);

extern unsigned int get_start_addr(struct memory_region *);

extern unsigned int get_block_size(struct memory_region *);

extern unsigned int get_block_perm(struct memory_region *);

extern _Bool is_well_chunk_bool(unsigned int);

extern unsigned char *check_mem_aux2(struct memory_region *, unsigned int, unsigned int, unsigned int);

extern unsigned char *check_mem_aux(unsigned int, unsigned int, unsigned int, unsigned int, struct memory_region *);

extern unsigned char *check_mem(unsigned int, unsigned int, unsigned int);

extern void step_opcode_alu64(unsigned long long, unsigned long long, unsigned int, unsigned char);

extern void step_opcode_alu32(unsigned int, unsigned int, unsigned int, unsigned char);

extern void step_opcode_branch(unsigned long long, unsigned long long, unsigned int, unsigned int, unsigned char);

extern void step_opcode_mem_ld_imm(int, unsigned long long, unsigned int, unsigned char);

extern void step_opcode_mem_ld_reg(unsigned int, unsigned int, unsigned char);

extern void step_opcode_mem_st_imm(int, unsigned int, unsigned int, unsigned char);

extern void step_opcode_mem_st_reg(unsigned long long, unsigned int, unsigned int, unsigned char);

extern void step(void);

extern void bpf_interpreter_aux(unsigned int);

extern unsigned long long bpf_interpreter(unsigned int);

extern unsigned int eval_pc(void);

extern void upd_pc(unsigned int);

extern void upd_pc_incr(void);

extern int eval_flag(void);

extern void upd_flag(int);

extern unsigned int eval_mrs_num(void);

extern unsigned long long eval_reg(unsigned int);

extern void upd_reg(unsigned int, unsigned long long);

extern struct memory_region *eval_mrs_regions(void);

extern unsigned long long load_mem(unsigned int, unsigned int);

extern void store_mem_imm(unsigned char *, unsigned int, int);

extern void store_mem_reg(unsigned char *, unsigned int, unsigned long long);

extern unsigned int eval_ins_len(void);

extern unsigned long long eval_ins(unsigned int);

extern _Bool cmp_ptr32_nullM(unsigned char *);

extern unsigned int get_dst(unsigned long long);

extern unsigned int get_src(unsigned long long);

extern struct memory_region *get_mem_region(unsigned int, struct memory_region *);

extern unsigned char *_bpf_get_call(int);

extern unsigned int exec_function(unsigned char *);

unsigned int reg64_to_reg32(unsigned long long d)
{
  return (unsigned int) d;
}

int get_offset(unsigned long long ins)
{
  return (int) (short) (ins << 32LLU >> 48LLU);
}

int get_immediate(unsigned long long ins$116)
{
  return (int) (ins$116 >> 32LLU);
}

long long eval_immediate(int ins$118)
{
  return (long long) ins$118;
}

unsigned long long get_src64(unsigned char x, unsigned long long ins$122)
{
  int imm;
  long long imm64;
  unsigned int src;
  unsigned long long src64;
  if (0U == (x & 8U)) {
    imm = get_immediate(ins$122);
    imm64 = eval_immediate(imm);
    return (unsigned long long) imm64;
  } else {
    src = get_src(ins$122);
    src64 = eval_reg(src);
    return src64;
  }
}

unsigned int get_src32(unsigned char x$132, unsigned long long ins$134)
{
  int imm$136;
  unsigned int src$138;
  unsigned long long src64$140;
  unsigned int src32;
  if (0U == (x$132 & 8U)) {
    imm$136 = get_immediate(ins$134);
    return imm$136;
  } else {
    src$138 = get_src(ins$134);
    src64$140 = eval_reg(src$138);
    src32 = reg64_to_reg32(src64$140);
    return src32;
  }
}

unsigned char get_opcode_ins(unsigned long long ins$144)
{
  return (unsigned char) (ins$144 & 255LLU);
}

unsigned char get_opcode_alu64(unsigned char op)
{
  return (unsigned char) (op & 240);
}

unsigned char get_opcode_alu32(unsigned char op$148)
{
  return (unsigned char) (op$148 & 240);
}

unsigned char get_opcode_branch(unsigned char op$150)
{
  return (unsigned char) (op$150 & 240);
}

unsigned char get_opcode_mem_ld_imm(unsigned char op$152)
{
  return (unsigned char) (op$152 & 255);
}

unsigned char get_opcode_mem_ld_reg(unsigned char op$154)
{
  return (unsigned char) (op$154 & 255);
}

unsigned char get_opcode_mem_st_imm(unsigned char op$156)
{
  return (unsigned char) (op$156 & 255);
}

unsigned char get_opcode_mem_st_reg(unsigned char op$158)
{
  return (unsigned char) (op$158 & 255);
}

unsigned char get_opcode(unsigned char op$160)
{
  return (unsigned char) (op$160 & 7);
}

unsigned int get_add(unsigned int x$162, unsigned int y)
{
  return x$162 + y;
}

unsigned int get_sub(unsigned int x$166, unsigned int y$168)
{
  return x$166 - y$168;
}

unsigned int get_addr_ofs(unsigned long long x$170, int ofs)
{
  return (unsigned int) (x$170 + (unsigned long long) ofs);
}

unsigned int get_start_addr(struct memory_region *mr)
{
  return (*mr).start_addr;
}

unsigned int get_block_size(struct memory_region *mr$176)
{
  return (*mr$176).block_size;
}

unsigned int get_block_perm(struct memory_region *mr$178)
{
  return (*mr$178).block_perm;
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

unsigned char *check_mem_aux2(struct memory_region *mr$182, unsigned int perm, unsigned int addr, unsigned int chunk$188)
{
  unsigned int start;
  unsigned int size;
  unsigned int mr_perm;
  unsigned int lo_ofs;
  unsigned int hi_ofs;
  start = get_start_addr(mr$182);
  size = get_block_size(mr$182);
  mr_perm = get_block_perm(mr$182);
  lo_ofs = get_sub(addr, start);
  hi_ofs = get_add(lo_ofs, chunk$188);
  if (hi_ofs < size
        && (lo_ofs <= 4294967295U - chunk$188 && 0U == lo_ofs % chunk$188)
        && mr_perm >= perm) {
    return (*mr$182).block_ptr + lo_ofs;
  } else {
    return 0;
  }
}

unsigned char *check_mem_aux(unsigned int num, unsigned int perm$202, unsigned int chunk$204, unsigned int addr$206, struct memory_region *mrs)
{
  unsigned int n;
  struct memory_region *cur_mr;
  unsigned char *check_mem$214;
  _Bool is_null;
  if (num == 0U) {
    return 0;
  } else {
    n = num - 1U;
    cur_mr = get_mem_region(n, mrs);
    check_mem$214 = check_mem_aux2(cur_mr, perm$202, addr$206, chunk$204);
    is_null = cmp_ptr32_nullM(check_mem$214);
    if (is_null) {
      return check_mem_aux(n, perm$202, chunk$204, addr$206, mrs);
    } else {
      return check_mem$214;
    }
  }
}

unsigned char *check_mem(unsigned int perm$218, unsigned int chunk$220, unsigned int addr$222)
{
  _Bool well_chunk;
  unsigned int mem_reg_num;
  struct memory_region *mrs$228;
  unsigned char *check_mem$230;
  _Bool is_null$232;
  well_chunk = is_well_chunk_bool(chunk$220);
  if (well_chunk) {
    mem_reg_num = eval_mrs_num();
    mrs$228 = eval_mrs_regions();
    check_mem$230 =
      check_mem_aux(mem_reg_num, perm$218, chunk$220, addr$222, mrs$228);
    is_null$232 = cmp_ptr32_nullM(check_mem$230);
    if (is_null$232) {
      return 0;
    } else {
      return check_mem$230;
    }
  } else {
    return 0;
  }
}

void step_opcode_alu64(unsigned long long dst64, unsigned long long src64$236, unsigned int dst, unsigned char op$240)
{
  unsigned char opcode_alu64;
  unsigned int src32$244;
  unsigned int src32$246;
  unsigned int src32$248;
  opcode_alu64 = get_opcode_alu64(op$240);
  switch (opcode_alu64) {
    case 0:
      upd_reg(dst, dst64 + src64$236);
      return;
    case 16:
      upd_reg(dst, dst64 - src64$236);
      return;
    case 32:
      upd_reg(dst, dst64 * src64$236);
      return;
    case 48:
      if (src64$236 != 0LLU) {
        upd_reg(dst, dst64 / src64$236);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst, dst64 | src64$236);
      return;
    case 80:
      upd_reg(dst, dst64 & src64$236);
      return;
    case 96:
      src32$244 = reg64_to_reg32(src64$236);
      if (src32$244 < 64U) {
        upd_reg(dst, dst64 << src32$244);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      src32$246 = reg64_to_reg32(src64$236);
      if (src32$246 < 64U) {
        upd_reg(dst, dst64 >> src32$246);
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      if (op$240 == 135) {
        upd_reg(dst, -dst64);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (src64$236 != 0LLU) {
        upd_reg(dst, dst64 % src64$236);
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst, dst64 ^ src64$236);
      return;
    case 176:
      upd_reg(dst, src64$236);
      return;
    case 192:
      src32$248 = reg64_to_reg32(src64$236);
      if (src32$248 < 64U) {
        upd_reg(dst, (unsigned long long) ((long long) dst64 >> src32$248));
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

void step_opcode_alu32(unsigned int dst32, unsigned int src32$252, unsigned int dst$254, unsigned char op$256)
{
  unsigned char opcode_alu32;
  opcode_alu32 = get_opcode_alu32(op$256);
  switch (opcode_alu32) {
    case 0:
      upd_reg(dst$254, (unsigned long long) (dst32 + src32$252));
      return;
    case 16:
      upd_reg(dst$254, (unsigned long long) (dst32 - src32$252));
      return;
    case 32:
      upd_reg(dst$254, (unsigned long long) (dst32 * src32$252));
      return;
    case 48:
      if (src32$252 != 0U) {
        upd_reg(dst$254, (unsigned long long) (dst32 / src32$252));
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 64:
      upd_reg(dst$254, (unsigned long long) (dst32 | src32$252));
      return;
    case 80:
      upd_reg(dst$254, (unsigned long long) (dst32 & src32$252));
      return;
    case 96:
      if (src32$252 < 32U) {
        upd_reg(dst$254, (unsigned long long) (dst32 << src32$252));
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 112:
      if (src32$252 < 32U) {
        upd_reg(dst$254, (unsigned long long) (dst32 >> src32$252));
        return;
      } else {
        upd_flag(-10);
        return;
      }
    case 128:
      if (op$256 == 132) {
        upd_reg(dst$254, (unsigned long long) -dst32);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (src32$252 != 0U) {
        upd_reg(dst$254, (unsigned long long) (dst32 % src32$252));
        return;
      } else {
        upd_flag(-9);
        return;
      }
    case 160:
      upd_reg(dst$254, (unsigned long long) (dst32 ^ src32$252));
      return;
    case 176:
      upd_reg(dst$254, (unsigned long long) src32$252);
      return;
    case 192:
      if (src32$252 < 32U) {
        upd_reg(dst$254, (unsigned long long) ((int) dst32 >> src32$252));
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

void step_opcode_branch(unsigned long long dst64$260, unsigned long long src64$262, unsigned int pc, unsigned int ofs$266, unsigned char op$268)
{
  unsigned char opcode_jmp;
  unsigned char *f_ptr;
  _Bool is_null$274;
  unsigned int res;
  opcode_jmp = get_opcode_branch(op$268);
  switch (opcode_jmp) {
    case 0:
      if (op$268 == 5) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    case 16:
      if (dst64$260 == src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 32:
      if (dst64$260 > src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 48:
      if (dst64$260 >= src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 160:
      if (dst64$260 < src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 176:
      if (dst64$260 <= src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 64:
      if ((dst64$260 & src64$262) != 0LLU) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 80:
      if (dst64$260 != src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 96:
      if ((long long) dst64$260 > (long long) src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 112:
      if ((long long) dst64$260 >= (long long) src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 192:
      if ((long long) dst64$260 < (long long) src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 208:
      if ((long long) dst64$260 <= (long long) src64$262) {
        upd_pc(pc + ofs$266);
        return;
      } else {
        return;
      }
    case 128:
      if (op$268 == 133) {
        f_ptr = _bpf_get_call((int) src64$262);
        is_null$274 = cmp_ptr32_nullM(f_ptr);
        if (is_null$274) {
          upd_flag(-4);
          return;
        } else {
          res = exec_function(f_ptr);
          upd_reg(0U, (unsigned long long) res);
          return;
        }
      } else {
        upd_flag(-1);
        return;
      }
    case 144:
      if (op$268 == 149) {
        upd_flag(1);
        return;
      } else {
        upd_flag(-1);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_ld_imm(int imm$278, unsigned long long dst64$280, unsigned int dst$282, unsigned char op$284)
{
  unsigned char opcode_ld;
  opcode_ld = get_opcode_mem_ld_imm(op$284);
  switch (opcode_ld) {
    case 24:
      upd_reg(dst$282, (unsigned long long) (unsigned int) imm$278);
      return;
    case 16:
      upd_reg(dst$282,
              dst64$280 | (unsigned long long) (unsigned int) imm$278 << 32U);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_ld_reg(unsigned int addr$288, unsigned int dst$290, unsigned char op$292)
{
  unsigned char opcode_ld$294;
  unsigned char *addr_ptr;
  _Bool is_null$298;
  unsigned long long v;
  unsigned char *addr_ptr$302;
  _Bool is_null$304;
  unsigned long long v$306;
  unsigned char *addr_ptr$308;
  _Bool is_null$310;
  unsigned long long v$312;
  unsigned char *addr_ptr$314;
  _Bool is_null$316;
  unsigned long long v$318;
  opcode_ld$294 = get_opcode_mem_ld_reg(op$292);
  switch (opcode_ld$294) {
    case 97:
      addr_ptr = check_mem(1U, 4U, addr$288);
      is_null$298 = cmp_ptr32_nullM(addr_ptr);
      if (is_null$298) {
        upd_flag(-2);
        return;
      } else {
        v = load_mem(4U, addr_ptr);
        upd_reg(dst$290, v);
        return;
      }
    case 105:
      addr_ptr$302 = check_mem(1U, 2U, addr$288);
      is_null$304 = cmp_ptr32_nullM(addr_ptr$302);
      if (is_null$304) {
        upd_flag(-2);
        return;
      } else {
        v$306 = load_mem(2U, addr_ptr$302);
        upd_reg(dst$290, v$306);
        return;
      }
    case 113:
      addr_ptr$308 = check_mem(1U, 1U, addr$288);
      is_null$310 = cmp_ptr32_nullM(addr_ptr$308);
      if (is_null$310) {
        upd_flag(-2);
        return;
      } else {
        v$312 = load_mem(1U, addr_ptr$308);
        upd_reg(dst$290, v$312);
        return;
      }
    case 121:
      addr_ptr$314 = check_mem(1U, 8U, addr$288);
      is_null$316 = cmp_ptr32_nullM(addr_ptr$314);
      if (is_null$316) {
        upd_flag(-2);
        return;
      } else {
        v$318 = load_mem(8U, addr_ptr$314);
        upd_reg(dst$290, v$318);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_imm(int imm$320, unsigned int addr$322, unsigned int dst$324, unsigned char op$326)
{
  unsigned char opcode_st;
  unsigned char *addr_ptr$330;
  _Bool is_null$332;
  unsigned char *addr_ptr$334;
  _Bool is_null$336;
  unsigned char *addr_ptr$338;
  _Bool is_null$340;
  unsigned char *addr_ptr$342;
  _Bool is_null$344;
  opcode_st = get_opcode_mem_st_imm(op$326);
  switch (opcode_st) {
    case 98:
      addr_ptr$330 = check_mem(2U, 4U, addr$322);
      is_null$332 = cmp_ptr32_nullM(addr_ptr$330);
      if (is_null$332) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(addr_ptr$330, 4U, imm$320);
        return;
      }
    case 106:
      addr_ptr$334 = check_mem(2U, 2U, addr$322);
      is_null$336 = cmp_ptr32_nullM(addr_ptr$334);
      if (is_null$336) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(addr_ptr$334, 2U, imm$320);
        return;
      }
    case 114:
      addr_ptr$338 = check_mem(2U, 1U, addr$322);
      is_null$340 = cmp_ptr32_nullM(addr_ptr$338);
      if (is_null$340) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(addr_ptr$338, 1U, imm$320);
        return;
      }
    case 122:
      addr_ptr$342 = check_mem(2U, 8U, addr$322);
      is_null$344 = cmp_ptr32_nullM(addr_ptr$342);
      if (is_null$344) {
        upd_flag(-2);
        return;
      } else {
        store_mem_imm(addr_ptr$342, 8U, imm$320);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step_opcode_mem_st_reg(unsigned long long src64$346, unsigned int addr$348, unsigned int dst$350, unsigned char op$352)
{
  unsigned char opcode_st$354;
  unsigned char *addr_ptr$356;
  _Bool is_null$358;
  unsigned char *addr_ptr$360;
  _Bool is_null$362;
  unsigned char *addr_ptr$364;
  _Bool is_null$366;
  unsigned char *addr_ptr$368;
  _Bool is_null$370;
  opcode_st$354 = get_opcode_mem_st_reg(op$352);
  switch (opcode_st$354) {
    case 99:
      addr_ptr$356 = check_mem(2U, 4U, addr$348);
      is_null$358 = cmp_ptr32_nullM(addr_ptr$356);
      if (is_null$358) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(addr_ptr$356, 4U, src64$346);
        return;
      }
    case 107:
      addr_ptr$360 = check_mem(2U, 2U, addr$348);
      is_null$362 = cmp_ptr32_nullM(addr_ptr$360);
      if (is_null$362) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(addr_ptr$360, 2U, src64$346);
        return;
      }
    case 115:
      addr_ptr$364 = check_mem(2U, 1U, addr$348);
      is_null$366 = cmp_ptr32_nullM(addr_ptr$364);
      if (is_null$366) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(addr_ptr$364, 1U, src64$346);
        return;
      }
    case 123:
      addr_ptr$368 = check_mem(2U, 8U, addr$348);
      is_null$370 = cmp_ptr32_nullM(addr_ptr$368);
      if (is_null$370) {
        upd_flag(-2);
        return;
      } else {
        store_mem_reg(addr_ptr$368, 8U, src64$346);
        return;
      }
    default:
      upd_flag(-1);
      return;
    
  }
}

void step(void)
{
  unsigned int pc$372;
  unsigned long long ins$374;
  unsigned char op$376;
  unsigned char opc;
  unsigned int dst$380;
  unsigned long long dst64$382;
  unsigned long long src64$384;
  unsigned long long dst64$386;
  unsigned int dst32$388;
  unsigned int src32$390;
  unsigned long long dst64$392;
  int ofs$394;
  unsigned long long src64$396;
  unsigned long long dst64$398;
  int imm$400;
  unsigned int src$402;
  unsigned long long src64$404;
  int ofs$406;
  unsigned int addr$408;
  unsigned long long dst64$410;
  int ofs$412;
  int imm$414;
  unsigned int addr$416;
  unsigned long long dst64$418;
  unsigned int src$420;
  unsigned long long src64$422;
  int ofs$424;
  unsigned int addr$426;
  pc$372 = eval_pc();
  ins$374 = eval_ins(pc$372);
  op$376 = get_opcode_ins(ins$374);
  opc = get_opcode(op$376);
  dst$380 = get_dst(ins$374);
  switch (opc) {
    case 7:
      dst64$382 = eval_reg(dst$380);
      src64$384 = get_src64(op$376, ins$374);
      step_opcode_alu64(dst64$382, src64$384, dst$380, op$376);
      return;
    case 4:
      dst64$386 = eval_reg(dst$380);
      dst32$388 = reg64_to_reg32(dst64$386);
      src32$390 = get_src32(op$376, ins$374);
      step_opcode_alu32(dst32$388, src32$390, dst$380, op$376);
      return;
    case 5:
      dst64$392 = eval_reg(dst$380);
      ofs$394 = get_offset(ins$374);
      src64$396 = get_src64(op$376, ins$374);
      step_opcode_branch(dst64$392, src64$396, pc$372,
                         (unsigned int) ofs$394, op$376);
      return;
    case 0:
      dst64$398 = eval_reg(dst$380);
      imm$400 = get_immediate(ins$374);
      step_opcode_mem_ld_imm(imm$400, dst64$398, dst$380, op$376);
      return;
    case 1:
      src$402 = get_src(ins$374);
      src64$404 = eval_reg(src$402);
      ofs$406 = get_offset(ins$374);
      addr$408 = get_addr_ofs(src64$404, ofs$406);
      step_opcode_mem_ld_reg(addr$408, dst$380, op$376);
      return;
    case 2:
      dst64$410 = eval_reg(dst$380);
      ofs$412 = get_offset(ins$374);
      imm$414 = get_immediate(ins$374);
      addr$416 = get_addr_ofs(dst64$410, ofs$412);
      step_opcode_mem_st_imm(imm$414, addr$416, dst$380, op$376);
      return;
    case 3:
      dst64$418 = eval_reg(dst$380);
      src$420 = get_src(ins$374);
      src64$422 = eval_reg(src$420);
      ofs$424 = get_offset(ins$374);
      addr$426 = get_addr_ofs(dst64$418, ofs$424);
      step_opcode_mem_st_reg(src64$422, addr$426, dst$380, op$376);
      return;
    default:
      upd_flag(-1);
      return;
    
  }
}

void bpf_interpreter_aux(unsigned int fuel)
{
  unsigned int fuel0;
  unsigned int len;
  unsigned int pc$434;
  int f;
  unsigned int len0;
  unsigned int pc0;
  if (fuel == 0U) {
    upd_flag(-5);
    return;
  } else {
    fuel0 = fuel - 1U;
    len = eval_ins_len();
    pc$434 = eval_pc();
    if (pc$434 < len) {
      step();
      f = eval_flag();
      if (f == 0) {
        len0 = eval_ins_len();
        pc0 = eval_pc();
        if (pc0 + 1U < len0) {
          upd_pc_incr();
          bpf_interpreter_aux(fuel0);
          return;
        } else {
          upd_flag(-5);
          return;
        }
      } else {
        return;
      }
    } else {
      upd_flag(-5);
      return;
    }
  }
}

unsigned long long bpf_interpreter(unsigned int fuel$442)
{
  struct memory_region *mrs$444;
  struct memory_region *bpf_ctx;
  unsigned int start$448;
  int f$450;
  unsigned long long res$452;
  mrs$444 = eval_mrs_regions();
  bpf_ctx = get_mem_region(0U, mrs$444);
  start$448 = get_start_addr(bpf_ctx);
  upd_reg(1U, (unsigned long long) start$448);
  bpf_interpreter_aux(fuel$442);
  f$450 = eval_flag();
  if (f$450 == 1) {
    res$452 = eval_reg(0U);
    return res$452;
  } else {
    return 0LLU;
  }
}


