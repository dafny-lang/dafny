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

[Link to current document as pdf](https://github.com/dafny-lang/dafny/blob/master/docs/DafnyRef/out/DafnyRef.pdf)<br/>
[Link to current document as html](https://dafny-lang.github.io/dafny/DafnyReferenceManual/DafnyRef)

1. numbered toc
{:toc}

{% include Introduction.md %}

{% include Grammar.md %}

{% include Programs.md %}

{% include Modules.md %}

{% include Specifications.md %}

{% include Types.md %}

# Type Inference

TO BE WRITTEN

{% include Statements.md %}

{% include Expressions.md %}

# Variable Initialization and Definite Assignment

TO BE WRITTEN -- rules for default initialization; resulting rules for constructors; definite assignment rules

# Well-founded Orders {#sec-well-founded-orders}

TODO: Write this section

# Module Refinement {#sec-module-refinement}

TODO: Write this section.

{% include Attributes.md %}

{% include UserGuide.md %}

# TODO

-- const, static const

-- declarations

-- inference of array sizes

-- witness, ghost witness clauses

-- customizable error messages

-- opaque types

-- the !new type parameter characteristic

-- traits, object

-- non-null types

-- abstemious functions

-- labels (for program locations)

-- updates to shared destructors

-- labelled assertion statements, labelled preconditions

# References
[BIB]

{% include SyntaxTests.md %}
