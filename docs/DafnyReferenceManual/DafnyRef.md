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
bad:    _0 0_  _.0 _1.1 1_.1 1._ 1._1 1.1_
hex:    0x10_abcdefABCDEF
string:   "string \n \t \r \0" "a\"b" "'" "\'" ""
string:   "!@#$%^&*()_-+={}[]|:;\\<>,.?/~`"
string:   "\u1234 "
string:   "	"
notstring: "\u123 "
vstring:  @"" @"a" @"""" @"'\"
vstring:  @"xx""y y""zz " 
vstring:  @" " @"	"
vstring:  @"x
x"
char:    'a' '\n' '\'' '"' '\"' ' ' '\\'
char:    '\0' '\r' '\t'  '\u1234'
notchar:  '\u123'   '\Z'  '\u'  '\u2222Z'
notchar:  '\u123ZZZ'     '\u2222Z'
ids: 'a : a' : 'ab' :  'a'b' : 'a''b'
ids:  a_b _ab ab?
boolean:  true false
types:   int real string char bool 
types:   bv1 bv10 bv02 
types:   array array2 array20 array10
bad:     array1 array0 array02
types:   seq map imap set iset multiset
types:   seq<int> map<bool,bool> seq<set<real>> 
types:   map<set<int>,seq<bool>> seq<Node> seq< Node >
keywords: if while assert assume
spec:    requires  reads modifies
comment:  // comment
comment:  /* comment */ after
comment:  // comment /* asd */ dfg
comment:  /* comment /* embedded */ after
comment:  /* comment // embedded */ after
comment: /* comment
   /* inner comment
   */
   outer comment
   */ after
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

