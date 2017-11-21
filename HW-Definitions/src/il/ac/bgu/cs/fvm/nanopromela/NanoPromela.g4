grammar NanoPromela;


// For Parser based interleaving action definition
hsreadstmt  : ZEROCAPACITYCHANNAME '?' (VARNAME)? ;
hswritestmt : ZEROCAPACITYCHANNAME '!' (intexpr)? ;

joined: ((hsreadstmt '|' hswritestmt) | (hswritestmt '|' hsreadstmt)) EOF;
onesided: (hsreadstmt | hswritestmt) EOF;  
//---------------------------------------------------------------------------


spec : stmt EOF ;



stmt: ifstmt | dostmt | assstmt | chanreadstmt | chanwritestmt | atomicstmt | skipstmt | stmt ';' stmt ;
      
ifstmt        : 'if' option+ 'fi' ;
dostmt  	  : 'do' option+ 'od' ;
assstmt       : VARNAME ':=' intexpr ;
chanreadstmt  : CHANNAME '?' VARNAME ;
chanwritestmt : CHANNAME '!' intexpr ;
atomicstmt    : 'atomic' '{' (VARNAME ':=' intexpr  ';')* VARNAME ':=' intexpr '}' ;
skipstmt      : 'skip' ;

option: '::' boolexpr '->' stmt ; 



intexpr
 : intexpr POW int expr           				
 | MINUS intexpr                                                       
 | intexpr op=(MULT | DIV | MOD) intexpr      
 | intexpr op=(PLUS | MINUS) intexpr          
 | INT 
 | 'size(' CHANNAME ')'
 | VARNAME                               
 | OPAR intexpr CPAR 
 ;

boolexpr
 : NOT boolexpr
 | boolexpr AND boolexpr
 | boolexpr OR boolexpr                                           
 | intexpr op=(LTEQ | GTEQ | LT | GT) intexpr 
 | intexpr op=(EQ | NEQ) intexpr
 | TRUE
 | FALSE 
 | OPAR boolexpr CPAR  
 ;



OR : '||';
AND : '&&';
EQ : '==';
NEQ : '!=';
GT : '>';
LT : '<';
GTEQ : '>=';
LTEQ : '<=';
PLUS : '+';
MINUS : '-';
MULT : '*';
DIV : '/';
MOD : '%';
POW : '^';
NOT : '!';

SCOL : ';';
ASSIGN : '=';
OPAR : '(';
CPAR : ')';
OBRACE : '{';
CBRACE : '}';

TRUE : 'true';
FALSE : 'false';

INT
 : [0-9]+
 ;

VARNAME 
: [a-z] [a-zA-Z_0-9]*
 ;
 

CHANNAME 
  : 
  [A-Z] [a-zA-Z_0-9]*
  ;

ZEROCAPACITYCHANNAME 
  : 
  '_' [a-zA-Z_0-9]*
  ;

  
COMMENT
 : '#' ~[\r\n]* -> skip
 ;

SPACE
 : [ \t\r\n] -> skip
 ;

OTHER
 : . 
 ;
 
