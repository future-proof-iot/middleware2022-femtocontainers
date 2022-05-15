/**************************************************************************/
/*  This file is part of CertrBPF,                                        */
/*  a formally verified rBPF verifier + interpreter + JIT in Coq.         */
/*                                                                        */
/*  Copyright (C) 2022 Inria                                              */
/*                                                                        */
/*  This program is free software; you can redistribute it and/or modify  */
/*  it under the terms of the GNU General Public License as published by  */
/*  the Free Software Foundation; either version 2 of the License, or     */
/*  (at your option) any later version.                                   */
/*                                                                        */
/*  This program is distributed in the hope that it will be useful,       */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU General Public License for more details.                          */
/*                                                                        */
/**************************************************************************/

/**
 * 1. deleting all lines before `struct memory_region *get_mem_region`
 * 2. deleting `\n\n`.
 * 2. deleting all `extern` lines
 * 3. adding `st` to all possible places
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BUFFER_SIZE 1000
#define CNT 1000

/* Function declaration */
void replaceAll(char *str, const char *oldWord, const char *newWord);


const char start_point[] = "unsigned long long eval_ins(unsigned int)";


const char old_words[][200] = {
	"_Bool is_dst_R0",
	"_Bool is_well_dst",
	"_Bool is_well_src",
	"_Bool is_well_jump",
	"_Bool is_not_div_by_zero(",
	"_Bool is_not_div_by_zero64",
	"_Bool is_shift_range(",
	"_Bool is_shift_range64",
	"unsigned int get_opcode",
	"int get_offset",
	"_Bool bpf_verifier_opcode_alu32_imm",
	"_Bool bpf_verifier_opcode_alu32_reg",
	"_Bool bpf_verifier_opcode_alu64_imm",
	"_Bool bpf_verifier_opcode_alu64_reg",
	"_Bool bpf_verifier_opcode_branch_imm",
	"_Bool bpf_verifier_opcode_branch_reg",
	"_Bool bpf_verifier_opcode_load_imm",
	"_Bool bpf_verifier_opcode_load_reg",
	"_Bool bpf_verifier_opcode_store_imm",
	"_Bool bpf_verifier_opcode_store_reg",
	"_Bool bpf_verifier_aux2(",
	"eval_ins_len()",
	"eval_ins(",
	"_Bool bpf_verifier_aux(",
	"_Bool bpf_verifier(void)",
	"return bpf_verifier_aux(",
	"= bpf_verifier_aux("
	
	};

const char new_words[][200] = {
	"static __attribute__((always_inline)) inline _Bool is_dst_R0",
	"static __attribute__((always_inline)) inline _Bool is_well_dst",
	"static __attribute__((always_inline)) inline _Bool is_well_src",
	"static __attribute__((always_inline)) inline _Bool is_well_jump",
	"static __attribute__((always_inline)) inline _Bool is_not_div_by_zero(",
	"static __attribute__((always_inline)) inline _Bool is_not_div_by_zero64",
	"static __attribute__((always_inline)) inline _Bool is_shift_range(",
	"static __attribute__((always_inline)) inline _Bool is_shift_range64",
	"static __attribute__((always_inline)) inline unsigned int get_opcode",
	"static __attribute__((always_inline)) inline int get_offset",
	"static __attribute__((always_inline)) inline _Bool bpf_verifier_opcode_alu32_imm",
	"static __attribute__((always_inline)) inline _Bool bpf_verifier_opcode_alu32_reg",
	"static __attribute__((always_inline)) inline _Bool bpf_verifier_opcode_alu64_imm",
	"static __attribute__((always_inline)) inline _Bool bpf_verifier_opcode_alu64_reg",
	"static __attribute__((always_inline)) inline _Bool bpf_verifier_opcode_branch_imm",
	"static __attribute__((always_inline)) inline _Bool bpf_verifier_opcode_branch_reg",
	"static __attribute__((always_inline)) inline _Bool bpf_verifier_opcode_load_imm",
	"static __attribute__((always_inline)) inline _Bool bpf_verifier_opcode_load_reg",
	"static __attribute__((always_inline)) inline _Bool bpf_verifier_opcode_store_imm",
	"static __attribute__((always_inline)) inline _Bool bpf_verifier_opcode_store_reg",
	"static __attribute__((always_inline)) inline _Bool bpf_verifier_aux2(",
	"eval_ins_len(st)",
	"eval_ins(st, ",
	"_Bool bpf_verifier_aux(struct verifier_state * st, ",
	"_Bool bpf_verifier(struct verifier_state * st)",
	"return bpf_verifier_aux(st, ",
	"= bpf_verifier_aux(st, "
	
	};
	


const char delete_lines[] ="extern ";

int main()
{
    /* File pointer to hold reference of input file */
    FILE * ptr_r;
    FILE * ptr_w;
    int counter = CNT;
    int index;
    int before_start_point;
    int two_blanks;
    
    char buffer[BUFFER_SIZE];



    /*  Open all required files */
    ptr_r  = fopen("repatch1_generated.c", "r");
    ptr_w = fopen("repatch2_generated.c", "w+"); 

    /* fopen() return NULL if unable to open file in given mode. */
    if (ptr_r == NULL || ptr_w == NULL)
    {
        /* Unable to open file hence exit */
        printf("\nUnable to open file.\n");
        printf("Please check whether file exists and you have read/write privilege.\n");
        exit(EXIT_SUCCESS);
    }

    before_start_point = 0;
    two_blanks = 0;
    while ((fgets(buffer, BUFFER_SIZE, ptr_r)) != NULL)
    {  //printf("%d\n", CNT-counter);
    	//if ((counter --) == 0) { break; }
    	/* deleting all lines before `struct memory_region *get_mem_region` */
    	if (before_start_point == 0 && strstr(buffer, start_point) == NULL){
    	  /* we just skip this line and don't write it */
    	  continue;
    	}
    	else {
    	  before_start_point = 1;
    	}
    	
    	if (strcmp(buffer, "\n") == 0){
    	  if(two_blanks == 0){
    	    two_blanks = 1;
    	  }
    	  else {//two_blanks == 1
    	    //printf("skip\n");
    	    continue;
    	  }
    	}
    	else if(strcmp(buffer, "}\n") == 0) {
    	  /* we just skip this line and don't write it */
    	  two_blanks = 0;
    	}
    	
    	/* Delete all lines starting by `extern  ` */
    	if (strstr(buffer, delete_lines) != NULL){
    	  /* we just skip this line and don't write it */
    	  continue;
    	}
    	
    	if(strcmp(buffer,"\n") == 0) { fputs(buffer, ptr_w); continue; }
    
    	//printf("readline: %s\n", buffer);
        // Replace all occurrence of word from current line
        for (index = 0; index < sizeof(old_words)/200; index ++){
          replaceAll(buffer, old_words[index], new_words[index]);
        }

        // After replacing write it to temp file.
        fputs(buffer, ptr_w);
    }

    //printf("repatch2 done!\n");
    /* Close all files to release resource */
    fclose(ptr_r);
    fclose(ptr_w);

    return 0;
}



/**
 * Replace all occurrences of a given a word in string.
 */
void replaceAll(char *str, const char *oldWord, const char *newWord)
{
    char *pos, temp[BUFFER_SIZE];
    int index = 0;
    int owlen;

    owlen = strlen(oldWord);

    // Fix: If oldWord and newWord are same it goes to infinite loop
    if (!strcmp(oldWord, newWord)) {
        return;
    }

    if ((pos = strstr(str, oldWord)) == NULL) {return ;}
    /*
     * Repeat till all occurrences are replaced. 
     */
    //while ((pos = strstr(str, oldWord)) != NULL)
    //{
        // Backup current line
        strcpy(temp, str);

        // Index of current found word
        index = pos - str;

        // Terminate str after word found index
        str[index] = '\0';

        // Concatenate str with new word 
        strcat(str, newWord);
        
        // Concatenate str with remaining words after 
        // oldword found index.
        strcat(str, temp + index + owlen);
    //}
}
