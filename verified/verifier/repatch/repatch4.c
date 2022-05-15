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
 * 1. concat two .c files
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BUFFER_SIZE 10000
#define CNT 1000

int main()
{
    /* File pointer to hold reference of input file */
    FILE * ptr_r0;
    FILE * ptr_r1;
    FILE * ptr_w;
    int counter = CNT;
    int index;
    
    char buffer[BUFFER_SIZE];



    /*  Open all required files */
    ptr_r0  = fopen("verifier_pre.c", "r");
    ptr_r1  = fopen("repatch3_generated.c", "r");
    ptr_w = fopen("verifier.c", "w+"); 

    /* fopen() return NULL if unable to open file in given mode. */
    if (ptr_r0 == NULL || ptr_r1 == NULL || ptr_w == NULL)
    {
        /* Unable to open file hence exit */
        printf("\nUnable to open file.\n");
        printf("Please check whether file exists and you have read/write privilege.\n");
        exit(EXIT_SUCCESS);
    }
    while ((fgets(buffer, BUFFER_SIZE, ptr_r0)) != NULL)
    {  
        fputs(buffer, ptr_w);
    }
    
    while ((fgets(buffer, BUFFER_SIZE, ptr_r1)) != NULL)
    {  
        fputs(buffer, ptr_w);
    }
    /* Close all files to release resource */
    fclose(ptr_r0);
    fclose(ptr_r1);
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
    printf("0");

    owlen = strlen(oldWord);
    printf("1");
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
    printf("2");
        // Backup current line
        strcpy(temp, str);

        // Index of current found word
        index = pos - str;

    printf("3");
        // Terminate str after word found index
        str[index] = '\0';

        // Concatenate str with new word 
        strcat(str, newWord);
      
    printf("4");  
        // Concatenate str with remaining words after 
        // oldword found index.
        strcat(str, temp + index + owlen);
    printf("5");
    //}
}
