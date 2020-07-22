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

<!--
```dafny
Syntax color tests:
integer: 0 00 20 01 0_1
float:   .0 1.0 1.
hex:    0x10_abcdefABCDEF
string:   "string \n" "a\"b"
char:    'a' '\n' '\'' '"'
boolean:  true false
types:   int real string char bool 
types:   bv1 bv10 bv02 
types:   array array1 array2 array20 array10
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
```
-->
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

