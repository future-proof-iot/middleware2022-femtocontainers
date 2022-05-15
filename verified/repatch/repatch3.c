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
 * 1. deleting all repeated declaration of variables
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define TRUE 1
#define FALSE 0
#define FULL 100
#define BUFFER_SIZE 1000
#define CNT 10000

const char variable_types[][20] = {
	"unsigned long long",
	"long long",
	"unsigned int",
	"int",
	"unsigned char",
	"char",
	"_Bool"
	};

	
int is_include_types (char* s){
    for (int i = 0; i< sizeof(variable_types)/20; i++){
        if (strstr(s, variable_types[i]) != NULL){
             return 1;
        }
    }
    return 0;
};

struct node
{
    char data[BUFFER_SIZE];
    struct node *next;
};

typedef struct node node;

struct queue
{
    int count;
    node *front;
    node *rear;
};
typedef struct queue queue;

void initialize(queue *q)
{
    q->count = 0;
    q->front = NULL;
    q->rear = NULL;
}

int isempty(queue *q)
{
    return (q->rear == NULL);
}

void enqueue(queue *q, char *value)
{
    if (q->count < FULL)
    {
        node *tmp;
        tmp = malloc(sizeof(node));
        strcpy(tmp->data, value);
        tmp->next = NULL;
        if(!isempty(q))
        {
            q->rear->next = tmp;
            q->rear = tmp;
        }
        else
        {
            q->front = q->rear = tmp;
        }
        q->count++;
    }
    else
    {
        printf("List is full\n");
    }
}

void dequeue(char* n, queue *q)
{
    node *tmp;
    strcpy (n, q->front->data);
    tmp = q->front;
    q->front = q->front->next;
    q->count--;
    free(tmp);
}

void display(node *head)
{
    if(head == NULL)
    {
        printf("NULL\n");
    }
    else
    {
        printf("%s\n", head -> data);
        display(head->next);
    }
}

int check_same(char *s, node *head){
    if (head == NULL) {
        return 0;
    }
    else {
        if (strcmp(s, head->data) == 0) {
            //printf("src:%s\n", s);
            //printf("dst:%s\n", head->data);
            return 1;
        }
        else {
            check_same(s, head->next);
        }
    }
}

int main(void)
{
    /* File pointer to hold reference of input file */
    FILE * ptr_r;
    FILE * ptr_w;
    int counter = CNT;
    int index;
    
    char buffer[BUFFER_SIZE];
    char queueArray[FULL][BUFFER_SIZE];
    char readbuffer[BUFFER_SIZE];
    char writebuffer[BUFFER_SIZE];
    
    
    queue *q;
    q = malloc(sizeof(queue));
    initialize(q);


    /*  Open all required files */
    ptr_r  = fopen("repatch2_generated.c", "r");
    ptr_w = fopen("repatch3_generated.c", "w+"); 

    /* fopen() return NULL if unable to open file in given mode. */
    if (ptr_r == NULL || ptr_w == NULL)
    {
        /* Unable to open file hence exit */
        printf("\nUnable to open file.\n");
        printf("Please check whether file exists and you have read/write privilege.\n");
        exit(EXIT_SUCCESS);
    }

    while ((fgets(buffer, BUFFER_SIZE, ptr_r)) != NULL)
    {  
       strcpy(readbuffer, buffer);
        //printf("%03d:%s", CNT-counter, buffer);
    	//if ((counter --) == 0) { break; }
    	
    	// if the cur_line includes `declaration info`
        if (is_include_types(readbuffer) == 1){
            // if the cur_line is same with someone in the queue, skip this line
            if (check_same (readbuffer, q->front) == 1){
                /*printf("find same1\n");
                display(q->front);
                printf("find same2\n");*/
                continue;
            }
            // else if the queue is full, dequeue info, (i.e. writing into file) and enqueue the cur_line
            else if (q->count >= FULL) {
            	 printf("warning: is full!!!\n");
            	 
                dequeue(writebuffer, q);
                fputs(writebuffer, ptr_w);
                enqueue(q, readbuffer);
            }
            // else insert the cur_line to the queue
            else {
                enqueue(q, readbuffer);
                /*printf("enqueue! queue size=%d\n", q->count);
                printf("find enqueue1\n");
                display(q->front);
                printf("find enqueue2\n");*/
            }
        }
        // else if the queue is not empty, peek all, i.e. writing all into file
        else if (q->count != 0) {
          while (q->count != 0) {
              //printf("queue size=%d\n", q->count);
              dequeue(writebuffer, q);
              //printf("writebuffer:%s\n", writebuffer);
              fputs(writebuffer, ptr_w);
          }
          initialize(q);
          fputs(buffer, ptr_w);
          //printf("end\n");
        }
        else{ 
            fputs(buffer, ptr_w);      
            //printf("bad queue size=%d\n", q->count);
        }
        
        // else donothing
    }
    /* Close all files to release resource */
    fclose(ptr_r);
    fclose(ptr_w);

    return 0;
}
