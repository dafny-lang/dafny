---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

layout: page
---
<script src="https://polyfill.io/v3/polyfill.min.js?features=es6"></script>
<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
<script type="text/x-mathjax-config">
        MathJax.Hub.Config({tex2jax: {inlineMath: [['$','$'], ["\\(","\\)"]], displayMath: [ ["$$","$$"], ["\\[","\\]"] ]
        }});
</script>

<link rel="stylesheet" href="assets/main.css">

<font size="+4"><p style="text-align: center;">The Dafny Language and Software Verification System</p></font>

**Quick Links:**
- [Dafny Reference Manual and User Guide](DafnyRef/DafnyRef)
- [Tips and Tricks and FAQs](HowToFAQ)
- [Index to Dafny Resources for Users](toc)
- [Dafny GitHub project (for developers of the Dafny tools themselves)](https://github.com/dafny-lang/dafny)

![Dafny Banner](./banner.png "Dafny")

Dafny is a <strong>verification-ready programming language</strong>.
As you type in your program, Dafny's verifier constantly looks over your shoulder, flags any errors, shows you counterexamples, and congratulates you when your code matches your specifications.
When you're done, Dafny can <strong>compile your code to C#, Java, JavaScript, Python, C++ or Go</strong> (more to come!), so it can integrate with your existing workflow.

Dafny will give you <strong>assurance that your code meets the specifications you write</strong>, while letting you write both code and specifications in the Dafny programming language itself.
Since verification is an integral part of development, it will thus <strong>reduce the risk of costly late-stage bugs</strong> that are typically missed by testing.

Dafny has support for common programming concepts such as 
- mathematical iand bounded integers and reals, bit-vectors, classes, iterators, arrays, tuples, generic types, refinement and inheritance
- [inductive datatypes](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-inductive-datatypes) that can have methods and are suitable for pattern matching,
- [lazily unbounded datatypes](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-co-inductive-datatypes),
- [subset types](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-subset-types), such as for bounded integers,
- [lambda expressions](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-lambda-expressions) and functional programming idioms,
- and [immutable and mutable data structures](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-collection-types).

Dafny also offers an extensive toolbox for mathematical proofs about software, including
- [bounded and unbounded quantifiers](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-forall-statement"),
- [calculational proofs](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-calc-statement) and ability to use and prove lemmas,
- [pre- and post-conditions, termination conditions, loop invariants, and read/write specifications](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-specification-clauses)

