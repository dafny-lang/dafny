<link rel="stylesheet" href="../assets/main.css">
<script src="https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML" type="text/javascript"></script>

<font size="+4"><p style="text-align: center;">Dafny Reference Manual</p></font> <!-- PDFOMIT -->
<p style="text-align: center;">K. Rustan M. Leino, Richard L. Ford, David R. Cok</p> <!-- PDFOMIT -->
<p style="text-align: center;"><script> document.write(new Date(document.lastModified)); </script></p> <!-- PDFOMIT -->

<!--PDF NEWPAGE-->

**Abstract:** 
This is the Dafny reference manual which describes the Dafny programming
language and how to use the Dafny verification system.
Parts of this manual are more tutorial in nature in order to help the
user understand how to do proofs with Dafny.

[Link to current document as pdf](https://dafny-lang.github.io/dafny/DafnyReferenceManual/DafnyRef.pdf)<br/>
[Link to current document as html](https://dafny-lang.github.io/dafny/DafnyReferenceManual/DafnyRef)

```dafny
Syntax color tests:
integer: 0 00 20 01 0_1
float:   .0 1.0 1. 0_1.1_0
bad:    0_  
hex:    0x10_abcdefABCDEF
string:   "string \n \t \r \0" "a\"b" "'" "\'" ""
string:   "!@#$%^&*()_-+={}[]|:;\\<>,.?/~`"
string:   "\u1234 "
string:   "	" : "\0\n\r\t\'\"\\"
notstring: "abcde
notstring: "\u123 " : "x\Zz" : "x\ux"
vstring:  @"" @"a" @"""" @"'\" @"\u"
vstring:  @"xx""y y""zz " 
vstring:  @" " @"	"
vstring:  @"x
x"
bad:      @x
char:    'a' '\n' '\'' '"' '\"' ' ' '\\'
char:    '\0' '\r' '\t'  '\u1234'
badchar:  $ `
ids:  '\u123'   '\Z'  '\u'  '\u2222Z'
ids:  '\u123ZZZ'     '\u2222Z'
ids: 'a : a' : 'ab' :  'a'b' : 'a''b'
ids:  a_b _ab ab? _0
literal:  true false null
op:      - ! ~ x  -!~x
op:      a + b - c * d / e % f a+b-c*d/e%f
op:      <= >= < > == != b&&c || ==> <==> <==
op:      .. ==# !=# !! in !in
punc:    . , :: | :| := ( ) [ ] { } 
types:   int real string char bool nat ORDINAL
types:   object object?
types:   bv1 bv10 bv0 
types:   array array2 array20 array10
types:   array? array2? array20? array10?
ids:     array1 array0 array02 bv02
ids:     intx natx int0 int_ int? bv1_ bv1x array2x
types:   seq<int>  set < bool >
types:   map<bool,bool>  imap < bool , bool >
types:   seq<Node> seq< Node >
types:   seq<set< real> >
types:   map<set<int>,seq<bool>> 
types:   G<A,int> G<G<A>,G<bool>>
ids:     seqx mapx
no <:   seq map imap set iset multiset .
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

<!--
Sample math B: $a \to b$ or 
<p style="text-align: center;">$$ a \to \pi $$</p>
 or \\( a \top \\) or \\[ a \to \pi \\] 
-->

1. numbered toc 
{:toc}

{% include Introduction.md %}

{% include Grammar.md %}

{% include Programs.md %}

{% include Modules.md %}

{% include Specifications.md %}

{% include Types.md %}

{% include Statements.md %}

{% include Expressions.md %}

{% include Grammar.md %}


# Module Refinement
TODO: Write this section.

{% include Attributes.md %}

{% include UserGuide.md %}

# References
[BIB]

