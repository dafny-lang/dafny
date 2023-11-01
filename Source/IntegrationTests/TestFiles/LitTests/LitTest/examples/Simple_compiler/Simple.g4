grammar Simple;
options { language=CSharp; }

prog : (s+=stmt ';')*;

stmt : 'print' '(' e=expr ')' # Print
     | 'set' v=VAR ':=' e=expr # Assign;

expr : c=INT # Const
     | v=VAR # Var
     | l=expr '+' r=expr # Add
     | l=expr '-' r=expr # Sub;

VAR  : [a-z]+;
INT  : [0-9]+;
WS   : [ \t\n\r]+ -> skip;


