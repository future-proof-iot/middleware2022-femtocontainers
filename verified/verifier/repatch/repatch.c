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

#include<stdio.h>
#include<stdint.h>
#include <inttypes.h>

int main(){
  char buffer[500];
  char newbuffer[500];
  FILE *ptr_r, *ptr_w;
  int i,f;

  ptr_r = fopen("generated.c", "r");
  ptr_w = fopen("new_generated.c", "w+");
  f = 0;
  while (1){
    char c = fgetc(ptr_r);
    if (feof(ptr_r)){
      break;
    }
    if (c == '$'){
      f = 1;
      continue;
    }
    if (f == 1 && '0' <= c && c <= '9'){
      continue;
    }
    else{
      f = 0;
    }
    fputc(c, ptr_w);
  }
  
  if (feof(ptr_r))
  {
    printf ("\n!Completing the repatch process!\n");
    fclose(ptr_r);
    fclose(ptr_w);
  }
  return 0;
}
