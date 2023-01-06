
<!--PDF NEWPAGE-->
# 29. Testing syntax rendering

Sample math B: $a \to b$ or
<p style="text-align: center;">$$ a \to \pi $$</p>
 or \( a \top \) or \[ a \to \pi \]

Colors
<!-- %no-check -->
```dafny
integer literal:  10
hex literal:      0xDEAD
real literal:     1.1
boolean literal:  true false
char literal:     'c'
string literal:   "abc"
verbatim string:  @"abc"
ident:            ijk
type:             int
generic type:     map<int,T>
operator:         <=
punctuation:      { }
keyword:          while
spec:             requires
comment:          // comment
attribute         {: name }
error:            $
```

Syntax color tests:

<!-- %no-check -->
```dafny
integer: 0 00 20 01 0_1
float:   .0 1.0 1. 0_1.1_0
bad:    0_
hex:    0x10_abcdefABCDEF
string:   "string \n \t \r \0" "a\"b" "'" "\'" ""
string:   "!@#$%^&*()_-+={}[]|:;\\<>,.?/~`"
string:   "\u1234 "
string:   "     " : "\0\n\r\t\'\"\\"
notstring: "abcde
notstring: "\u123 " : "x\Zz" : "x\ux"
vstring:  @"" @"a" @"""" @"'\" @"\u"
vstring:  @"xx""y y""zz "
vstring:  @" " @"       "
vstring:  @"x
x"
bad:      @!
char:    'a' '\n' '\'' '"' '\"' ' ' '\\'
char:    '\0' '\r' '\t'  '\u1234'
badchar:  $ `
ids:  '\u123'   '\Z'  '\u'  '\u2222Z'
ids:  '\u123ZZZ'     '\u2222Z'
ids: 'a : a' : 'ab' :  'a'b' : 'a''b'
ids:  a_b _ab ab? _0
id-label:  a@label
literal:  true false null
op:      - ! ~ x  -!~x
op:      a + b - c * d / e % f a+b-c*d/e%f
op:      <= >= < > == != b&&c || ==> <==> <==
op:      !=# !! in !in
op:      !in∆  !iné
not op:  !inx
punc:    . , :: | :| := ( ) [ ] { }
types:   int real string char bool nat ORDINAL
types:   object object?
types:   bv1 bv10 bv0
types:   array array2 array20 array10
types:   array? array2? array20? array10?
ids:     array1 array0 array02 bv02 bv_1
ids:     intx natx int0 int_ int? bv1_ bv1x array2x
types:   seq<int>  set < bool >
types:   map<bool,bool>  imap < bool , bool >
types:   seq<Node> seq< Node >
types:   seq<set< real> >
types:   map<set<int>,seq<bool>>
types:   G<A,int> G<G<A>,G<bool>>
types:   seq map imap set iset multiset
ids:     seqx mapx
no arg:  seq < >  seq < , >  seq <bool , , bool >  seq<bool,>
keywords: if while assert assume
spec:    requires  reads modifies
attribute:  {: MyAttribute "asd", 34 }
attribute:  {: MyAttribute }
comment:  // comment
comment:  /* comment */ after
comment:  // comment /* asd */ dfg
comment:  /* comment /* embedded */ tail */ after
comment:  /* comment // embedded */ after
comment: /* comment
   /* inner comment
   */
   outer comment
   */ after
   more after
```

