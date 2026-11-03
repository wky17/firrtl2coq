%{
    open Ast

%}

%token<string> COMMENT
%token<string> BINARY HEX_DECIMAL OCTAL DECIMAL NUMERAL STRING SYMBOL S_HEX_DECIMAL S_BINARY S_NUMERAL S_OCTAL
%token PAR_OPEN PAR_CLOSE ANG_OPEN ANG_CLOSE SQR_OPEN SQR_CLOSE UNDERSCORE QUOT SPRT KEYWORD
%token CIRCUIT STM_MODULE STM_PUBMODULE STM_EXTMODULE STM_SKIP STM_INPUT STM_OUTPUT STM_WHEN STM_ELSE  STM_CONNECT STM_PCONNECT
%token STM_NODE STM_NASS STM_INST KEYWORD_OF STM_DEFNAME STM_INVALID STM_PARAM /*STM_DATATYPE STM_DEPTH STM_READ STM_READ_L STM_WRITE STM_WRITE_L STM_READWRITE*/ STM_PREFIX STM_FORMAT STM_DEFAULT STM_WIDTH
%token STM_WIRE STM_REG REG_WITH REG_RST REG_RSTARR STM_MEM SUB_FIELD UINT SINT INT CLOCK 
%token EXPR_VALIDIF EXPR_ADD EXPR_AND EXPR_ANDR EXPR_ASCLOCK EXPR_ASFIXED EXPR_ASSINT EXPR_ASUINT EXPR_CAT EXPR_CVT EXPR_DIV EXPR_DSHL EXPR_DSHR EXPR_EQ EXPR_GEQ EXPR_GT EXPR_HEAD EXPR_LEQ EXPR_LT EXPR_MUL EXPR_MUX EXPR_NEG EXPR_NEQ EXPR_NOT EXPR_OR EXPR_ORR EXPR_PAD EXPR_REM EXPR_SHL EXPR_SHR EXPR_SUB EXPR_TAIL EXPR_XOR EXPR_XORR EXPR_BITS
%token EOF
%token /*M_OLD M_NEW*/ M_UNDEFINED ASYNC RESET BRA_OPEN BRA_CLOSE FLIP EXPR_ASASYNC FULL STM_CONNECT0 STM_INVALID0 STM_REGRESET0 STM_MEM_INFER STM_MEM_READ STM_MEM_WRITE STM_SMEM

%start file
%type <Ast.file> file

%%

file
  : circuit EOF                          { $1 }
;

circuit
  : cct fmodules                         { Fcircuit ($1, $2)}
  ;

cct
  : CIRCUIT symbol KEYWORD               { $2 }
  ;
    
fmodules
  :                                      { [] }
  | fmodule fmodules                     { $1::$2}
  ;
    
fmodule
  : mdl ports statements                 { FInmod ($1, $2, $3) }
  | pubmdl ports statements              { FInmod ($1, $2, $3) }
  | extmdl ports statements              { FExmod ($1, $2, $3) }
  ;

mdl 
  : STM_MODULE symbol KEYWORD            { $2 }
  ;

pubmdl 
  : STM_PUBMODULE symbol KEYWORD         { $2 }
  ;

extmdl 
  : STM_EXTMODULE symbol KEYWORD         { $2 }
  ;

ports
  :                                      { [] }
  | port ports                           { $1::$2 }
  ;    

port
  : STM_INPUT symbol KEYWORD typ_def
                                         { Finput ($2, $4) }
  | STM_OUTPUT symbol KEYWORD typ_def
                                         { Foutput ($2, $4) }
;

btyp_def
  :                                      { Fnil }
  | FLIP symbol KEYWORD typ_def          { Fflips ($2, Flipped, $4, Fnil) }
  | symbol KEYWORD typ_def               { Fflips ($1, Nflip, $3, Fnil) }
  | FLIP symbol KEYWORD typ_def SPRT btyp_def 
                                         { Fflips ($2, Flipped, $4, $6) }
  | symbol KEYWORD typ_def SPRT btyp_def      
                                         { Fflips ($1, Nflip, $3, $5) }
;

typ_def
  : UINT ANG_OPEN numeral ANG_CLOSE      { Gtyp (Fuint $3) }
  | SINT ANG_OPEN numeral ANG_CLOSE      { Gtyp (Fsint $3) }
  | CLOCK                                { Gtyp Fclock }
  | RESET                                { Gtyp Freset}
  | ASYNC                                { Gtyp Fasyncreset}
  | UINT                                 { Gtyp (Fuint_implicit 0) }
  | SINT                                 { Gtyp (Fsint_implicit 0) }
  | typ_def SQR_OPEN numeral SQR_CLOSE   { Atyp ($1, $3) }
  | BRA_OPEN btyp_def BRA_CLOSE          { Btyp ($2) }
;

/*ruw
  : M_OLD                                { Coq_old }
  | M_NEW                                { Coq_new }
  | M_UNDEFINED                          { Coq_undefined }
;*/
/* statement */

statements
  :                                      { Qnil }
  | statement statements                 { Qcons ($1, $2) }
  ;    

statement
  : STM_SKIP                             { Sskip }
  | ref STM_CONNECT expr                 { Sfcnct ($1, $3) }
  | ref STM_PCONNECT expr                { Sskip }
  | STM_CONNECT0 ref SPRT expr           { Sfcnct ($2, $4) }
  | STM_WIRE symbol KEYWORD typ_def      { Swire ($2, $4) }
  | STM_NODE symbol STM_NASS expr        { Snode ($2, $4) }
  | STM_REG symbol KEYWORD typ_def SPRT expr  
                                         { Sreg ($2, mk_freg_non $4 $6)}
  | STM_REG symbol KEYWORD typ_def SPRT expr REG_WITH KEYWORD REG_RST REG_RSTARR PAR_OPEN expr SPRT expr PAR_CLOSE
                                         { Sreg ($2, mk_freg $4 $6 $12 $14) }
  | STM_REG symbol KEYWORD typ_def SPRT expr REG_WITH KEYWORD PAR_OPEN REG_RST REG_RSTARR PAR_OPEN expr SPRT expr PAR_CLOSE PAR_CLOSE
                                         { Sreg ($2, mk_freg $4 $6 $13 $15) }
  | STM_REGRESET0 symbol KEYWORD typ_def SPRT expr SPRT expr SPRT expr
                                         { Sreg ($2, mk_freg $4 $6 $8 $10) }
  | ref STM_INVALID                      { Sinvalid ($1) }
  | STM_INVALID0 ref                     { Sinvalid ($2) }
  /*| STM_MEM symbol KEYWORD STM_DATATYPE REG_RSTARR typ_def STM_DEPTH REG_RSTARR numeral STM_READ_L REG_RSTARR numeral STM_WRITE_L REG_RSTARR numeral memrdports memwrports STM_READWRITE REG_RSTARR ruw
                                         { Smem ($2, mk_fmem $6 $9 $12 $15 $16 $17 $20)}
  | STM_MEM symbol KEYWORD STM_DATATYPE REG_RSTARR typ_def STM_DEPTH REG_RSTARR numeral STM_READ_L REG_RSTARR numeral STM_WRITE_L REG_RSTARR numeral STM_READ REG_RSTARR symbols STM_WRITE REG_RSTARR symbols STM_READWRITE REG_RSTARR ruw
                                           { Smem (mk_fmem $2 $6 $9 $12 $15 $18 $21 $24)}*/

  | STM_MEM symbol KEYWORD typ_def       { Swire ($2, $4) }
  | STM_SMEM symbol KEYWORD typ_def      { Swire ($2, $4) }
  | STM_SMEM symbol KEYWORD typ_def SPRT M_UNDEFINED      { Swire ($2, $4) }
  | STM_MEM_INFER symbol STM_NASS expr SPRT expr
                                         { Snode ($2, $4) }
  | STM_MEM_READ symbol STM_NASS expr SPRT ref
                                         { Snode ($2, $4) }
  | STM_MEM_WRITE symbol STM_NASS expr SPRT ref
                                         { Snode ($2, $4) }

  | STM_INST symbol KEYWORD_OF symbol    { Sinst ($2, $4) }
  | STM_WHEN expr KEYWORD BRA_OPEN statements BRA_CLOSE STM_ELSE KEYWORD BRA_OPEN statements BRA_CLOSE
                                         {Swhen ($2, $5, $10)}
  | STM_WHEN expr KEYWORD BRA_OPEN statements BRA_CLOSE {Swhen ($2, $5, Qnil)}
  | STM_DEFNAME STM_NASS symbol          {Sskip}
;
  
/* expression */
  
expr
:   ref                                     { Eref $1 }
    | UINT ANG_OPEN numeral ANG_CLOSE PAR_OPEN QUOT hexadecimal QUOT PAR_CLOSE
                                            { Econst (Fuint($3), $7)}
    | UINT ANG_OPEN numeral ANG_CLOSE PAR_OPEN QUOT binary QUOT PAR_CLOSE
                                            { Econst (Fuint($3), $7)}
    | UINT ANG_OPEN numeral ANG_CLOSE PAR_OPEN QUOT octal QUOT PAR_CLOSE
                                            { Econst (Fuint($3), $7)}
    | UINT ANG_OPEN numeral ANG_CLOSE PAR_OPEN u_numeral PAR_CLOSE
                                            { Econst (Fuint($3), $6)}

    | UINT PAR_OPEN QUOT hexadecimal QUOT PAR_CLOSE
                                            { Econst (Fuint_implicit(0), $4)}
    | UINT PAR_OPEN QUOT binary QUOT PAR_CLOSE
                                            { Econst (Fuint_implicit(0), $4)}
    | UINT PAR_OPEN QUOT octal QUOT PAR_CLOSE
                                            { Econst (Fuint_implicit(0), $4)}
    | UINT PAR_OPEN u_numeral PAR_CLOSE
                                            { Econst (Fuint_implicit(0), $3)}
                  

    | SINT ANG_OPEN numeral ANG_CLOSE PAR_OPEN QUOT s_hexadecimal QUOT PAR_CLOSE
                                            { Econst (Fsint($3), $7)}
    | SINT ANG_OPEN numeral ANG_CLOSE PAR_OPEN QUOT s_binary QUOT PAR_CLOSE
                                            { Econst (Fsint($3), $7)}
    | SINT ANG_OPEN numeral ANG_CLOSE PAR_OPEN QUOT s_octal QUOT PAR_CLOSE
                                            { Econst (Fsint($3), $7)}
    | SINT ANG_OPEN numeral ANG_CLOSE PAR_OPEN s_numeral PAR_CLOSE
                                            { Econst (Fsint($3), $6)}

    | SINT PAR_OPEN QUOT s_hexadecimal QUOT PAR_CLOSE
                                            { Econst (Fsint_implicit(0), $4)}
    | SINT PAR_OPEN QUOT s_binary QUOT PAR_CLOSE
                                            { Econst (Fsint_implicit(0), $4)}
    | SINT PAR_OPEN QUOT s_octal QUOT PAR_CLOSE
                                            { Econst (Fsint_implicit(0), $4)}
    | SINT PAR_OPEN s_numeral PAR_CLOSE
                                            { Econst (Fsint_implicit(0), $3)}
     

    | SINT ANG_OPEN numeral ANG_CLOSE PAR_OPEN QUOT hexadecimal QUOT PAR_CLOSE
                                            { Econst (Fsint($3), $7)}
    | SINT ANG_OPEN numeral ANG_CLOSE PAR_OPEN QUOT binary QUOT PAR_CLOSE
                                            { Econst (Fsint($3), $7)}
    | SINT ANG_OPEN numeral ANG_CLOSE PAR_OPEN QUOT octal QUOT PAR_CLOSE
                                            { Econst (Fsint($3), $7)}
    | SINT ANG_OPEN numeral ANG_CLOSE PAR_OPEN u_numeral PAR_CLOSE
                                            { Econst (Fsint($3), $6)}

    | SINT PAR_OPEN QUOT hexadecimal QUOT PAR_CLOSE
                                            { Econst (Fsint_implicit(0), $4)}
    | SINT PAR_OPEN QUOT binary QUOT PAR_CLOSE
                                            { Econst (Fsint_implicit(0), $4)}
    | SINT PAR_OPEN QUOT octal QUOT PAR_CLOSE
                                            { Econst (Fsint_implicit(0), $4)}
    | SINT PAR_OPEN u_numeral PAR_CLOSE
                                            { Econst (Fsint_implicit(0), $3)}

    | EXPR_ADD PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Badd, $3, $5)}
    | EXPR_SUB PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Bsub, $3 , $5)}
    | EXPR_MUL PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Bmul, $3 , $5)}
    | EXPR_DIV PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Bdiv, $3 , $5)}
    | EXPR_REM PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Brem, $3 , $5)}
    | EXPR_DSHL PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Bdshl, $3, $5)}
    | EXPR_DSHR PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Bdshr, $3, $5)}
    | EXPR_AND PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Band, $3, $5)}
    | EXPR_OR PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Bor, $3, $5)}
    | EXPR_XOR PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Bxor, $3, $5)}
    | EXPR_CAT PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Bcat, $3, $5)}
                                            
    | EXPR_CVT PAR_OPEN expr PAR_CLOSE
                                            { Eprim_unop (Ucvt, $3)}
    | EXPR_NEG PAR_OPEN expr PAR_CLOSE
                                            { Eprim_unop (Uneg, $3)}
    | EXPR_NOT PAR_OPEN expr PAR_CLOSE
                                            { Eprim_unop (Unot, $3)}
    | EXPR_ANDR PAR_OPEN expr PAR_CLOSE
                                            { Eprim_unop (Uandr, $3)}
    | EXPR_ORR PAR_OPEN expr PAR_CLOSE
                                            { Eprim_unop (Uorr, $3)}
    | EXPR_XORR PAR_OPEN expr PAR_CLOSE
                                            { Eprim_unop (Uxorr, $3)}
    | EXPR_TAIL PAR_OPEN expr SPRT numeral PAR_CLOSE
                                            { Eprim_unop (Utail ($5), $3)}
    | EXPR_HEAD PAR_OPEN expr SPRT numeral PAR_CLOSE
                                            { Eprim_unop (Uhead ($5), $3)}
    | EXPR_PAD PAR_OPEN expr SPRT numeral PAR_CLOSE
                                            { Eprim_unop ( Upad ($5), $3)}
    | EXPR_SHL PAR_OPEN expr SPRT numeral PAR_CLOSE
                                            { Eprim_unop ( Ushl ($5), $3)}
    | EXPR_SHR PAR_OPEN expr SPRT numeral PAR_CLOSE
                                            { Eprim_unop ( Ushr ($5), $3)}
    | EXPR_BITS PAR_OPEN expr SPRT numeral SPRT numeral PAR_CLOSE
                                            { Eprim_unop ( Uextr ($5, $7), $3)}

    | EXPR_ASUINT PAR_OPEN expr PAR_CLOSE
                                            { Ecast (AsUInt, $3)}
    | EXPR_ASSINT PAR_OPEN expr PAR_CLOSE
                                            { Ecast (AsSInt, $3)}
    /*| EXPR_ASFIXED PAR_OPEN expr PAR_CLOSE
                                            { Eprim_unop (Ucast (AsFixed), $3)}*/
    | EXPR_ASCLOCK PAR_OPEN expr PAR_CLOSE
                                            { Ecast (AsClock, $3)}
    | EXPR_ASASYNC PAR_OPEN expr PAR_CLOSE
                                            { Ecast (AsAsync, $3)}

    | EXPR_GT PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Bcomp (Bgt), $3, $5)}
    | EXPR_LT PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Bcomp (Blt), $3, $5)}
    | EXPR_LEQ PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Bcomp (Bleq), $3, $5)}
    | EXPR_GEQ PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Bcomp (Bgeq), $3, $5)}
    | EXPR_EQ PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Bcomp (Beq), $3, $5)}
    | EXPR_NEQ PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Eprim_binop (Bcomp (Bneq), $3, $5)}

    | EXPR_MUX PAR_OPEN expr SPRT expr SPRT expr PAR_CLOSE
                                            { Emux ($3, $5, $7)}
    /*| EXPR_VALIDIF PAR_OPEN expr SPRT expr PAR_CLOSE
                                            { Evalidif ($3, $5)}*/
;  


/* Symbols */

symbol
  : SYMBOL                              { $1 }
  
ref
  : SYMBOL                              { Eid ($1) }
  | ref FULL SYMBOL                     { Esubfield ($1, $3) }
  | ref SQR_OPEN numeral SQR_CLOSE      { Esubindex ($1, $3) }
  /*| ref SQR_OPEN expr SQR_CLOSE          { Esubindex ($1, 0) }*/
  | ref SQR_OPEN expr SQR_CLOSE         { Esubaccess ($1, $3) }
;

symbols
  :                                      { [] }
  | symbol symbols                       { $1::$2 }
;
/* memports 

memrdport 
  : STM_READ REG_RSTARR symbol            { $3 }
;

memrdports
  :                                       { [] }
  | memrdport memrdports               { $1::$2 }
;

memwrport 
  : STM_WRITE REG_RSTARR symbol            { $3 }
;

memwrports
  :                                       { [] }
  | memwrport memwrports                { $1::$2 }
;
*/

/* spec_constant */

numeral
  : NUMERAL                             { Stdlib.int_of_string $1 }
;

u_numeral
  : NUMERAL                             { Z.of_string $1 }
;

s_numeral
  : S_NUMERAL                             { Z.of_string $1 }
;

decimal
  : DECIMAL                             { $1 }
;

hexadecimal
  : HEX_DECIMAL                         { Z.of_string_base 16 $1 }
;

s_hexadecimal
  : S_HEX_DECIMAL                         { Z.of_string_base 16 $1 }
;

binary
  : BINARY                              { Z.of_string_base 2 $1 }
;

s_binary
  : S_BINARY                              { Z.of_string_base 2 $1 }
;

octal 
  : OCTAL                                { Z.of_string_base 10 $1 }
;

s_octal
  : S_OCTAL                              { Z.of_string_base 10 $1 }
;

string
  : STRING                              { Z.of_string $1 }
;
