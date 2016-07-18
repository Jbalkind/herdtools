/*********************************************************************/
/*                        DIY                                        */
/*                                                                   */
/*               Luc Maranget, INRIA Paris-Rocquencourt, France.     */
/*                                                                   */
/*  Copyright 2014 Institut National de Recherche en Informatique et */
/*  en Automatique and the authors. All rights reserved.             */
/*  This file is distributed  under the terms of the Lesser GNU      */
/*  General Public License.                                          */
/*********************************************************************/

%{
open SPARCBase
%}

%token EOF
%token <SPARCBase.reg> ARCH_REG
%token <string> SYMB_REG
%token <int> NUM
%token <string> NAME
%token <int> PROC
%token <string> STORELOAD
%token <SPARCBase.condreg> COND_REG

%token SEMI COMMA PIPE COLON LPAR RPAR LBRK RBRK PLUS

/* Instruction tokens */
%token LD ST MEMBAR
/*%token LDX STX*/
%token ADD ADDC XOR XNOR
%token SUB SUBC OR ORN
%token SLLX SRAX SRLX
%token BA BN BE BNE BL BLE BG BGE
%token BLU BLEU BGU BGEU
%token BPOS BNEG BCS BCC BVS BVC
%token BRZ BRLEZ BRLZ BRNZ BRGZ BRGEZ

%type <int list * (SPARCBase.pseudo) list list * MiscParser.gpu_data option> main 
%start  main

%nonassoc SEMI
%%
 
main:
| semi_opt proc_list iol_list EOF { $2,$3,None }

semi_opt:
| { () }
| SEMI { () }

proc_list:
| PROC SEMI
    {[$1]}

| PROC PIPE proc_list  { $1::$3 }

iol_list :
|  instr_option_list SEMI
    {[$1]}
|  instr_option_list SEMI iol_list {$1::$3}

instr_option_list :
  | instr_option
      {[$1]}
  | instr_option PIPE instr_option_list 
      {$1::$3}

instr_option :
|            { Nop }
| NAME COLON instr_option { Label ($1,$3) }
| instr      { Instruction $1}

reg:
| SYMB_REG { Symbolic_reg $1 }
| ARCH_REG { $1 }

k:
| NUM { $1 }

kr:
| k { K $1 }
| reg { RV $1 }

instr:
/* Branch */
| BA   COND_REG COMMA NAME { BCOND (A  ,$2,$4) }
| BN   COND_REG COMMA NAME { BCOND (N  ,$2,$4) }
| BE   COND_REG COMMA NAME { BCOND (E  ,$2,$4) }
| BNE  COND_REG COMMA NAME { BCOND (NE ,$2,$4) }
| BL   COND_REG COMMA NAME { BCOND (L  ,$2,$4) }
| BLE  COND_REG COMMA NAME { BCOND (LE ,$2,$4) }
| BG   COND_REG COMMA NAME { BCOND (G  ,$2,$4) }
| BGE  COND_REG COMMA NAME { BCOND (GE ,$2,$4) }
| BLU  COND_REG COMMA NAME { BCOND (LU ,$2,$4) }
| BLEU COND_REG COMMA NAME { BCOND (LEU,$2,$4) }
| BGU  COND_REG COMMA NAME { BCOND (GU ,$2,$4) }
| BGEU COND_REG COMMA NAME { BCOND (GEU,$2,$4) }
| BPOS COND_REG COMMA NAME { BCOND (POS,$2,$4) }
| BNEG COND_REG COMMA NAME { BCOND (NEG,$2,$4) }
| BCS  COND_REG COMMA NAME { BCOND (CS ,$2,$4) }
| BCC  COND_REG COMMA NAME { BCOND (CC ,$2,$4) }
| BVS  COND_REG COMMA NAME { BCOND (VS ,$2,$4) }
| BVC  COND_REG COMMA NAME { BCOND (VC ,$2,$4) }
/* Branch Reg */
| BRZ   reg COMMA NAME { BRCOND (RZ  ,$2,$4) }
| BRLEZ reg COMMA NAME { BRCOND (RLEZ,$2,$4) }
| BRLZ  reg COMMA NAME { BRCOND (RLZ ,$2,$4) }
| BRNZ  reg COMMA NAME { BRCOND (RNZ ,$2,$4) }
| BRGZ  reg COMMA NAME { BRCOND (RGZ ,$2,$4) }
| BRGEZ reg COMMA NAME { BRCOND (RGEZ,$2,$4) }
/* Memory */
| LD LBRK reg PLUS kr RBRK COMMA reg
  { LD ($3,$5,$8) }
| LD LBRK reg RBRK COMMA reg
  { LD ($3,(K 0),$6) }
| ST reg COMMA LBRK reg PLUS kr RBRK
  { ST ($2,$5,$7) }
| ST reg COMMA LBRK reg RBRK
  { ST ($2,$5,(K 0)) }
/*| LDX LBRK reg PLUS kr RBRK COMMA reg
  { LDX ($3,$5,$8) }
| LDX LBRK reg RBRK COMMA reg
  { LDX ($3,(K 0),$6) }
| STX reg COMMA LBRK reg PLUS kr RBRK
  { STX ($2,$5,$7) }
| STX reg COMMA LBRK reg RBRK
  { STX ($2,$5,(K 0)) }*/
/* Operations */
| ADD   reg COMMA kr COMMA reg
  { OP3 (None,ADD,$2,$4,$6) }
| ADDC  reg COMMA kr COMMA reg
  { OP3 (None,ADDC,$2,$4,$6) }
| XOR   reg COMMA kr COMMA reg
  { OP3 (None,XOR,$2,$4,$6) }
| XNOR  reg COMMA kr COMMA reg
  { OP3 (None,XNOR,$2,$4,$6) }
| SUB   reg COMMA kr COMMA reg
  { OP3 (None,SUB,$2,$4,$6) }
| SUBC  reg COMMA kr COMMA reg
  { OP3 (None,SUBC,$2,$4,$6) }
| OR    reg COMMA kr COMMA reg
  { OP3 (None,OR,$2,$4,$6) }
| ORN   reg COMMA kr COMMA reg
  { OP3 (None,ORN,$2,$4,$6) }
| SLLX  reg COMMA kr COMMA reg
  { OP3 (None,SLLX,$2,$4,$6) }
| SRAX  reg COMMA kr COMMA reg
  { OP3 (None,SRAX,$2,$4,$6) }
| SRLX  reg COMMA kr COMMA reg
  { OP3 (None,SRLX,$2,$4,$6) }
/* Barrier */
| MEMBAR barriertype
  { MEMBAR $2 }

barriertype:
| STORELOAD { StoreLoad }
