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
- [Compendium of Dafny Resources for Users](#resources)
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

# Compendium of Dafny resources {#resources}

* Quick start material:
   * [Installation](https://github.com/dafny-lang/dafny/wiki/INSTALL) and [Releases](https://github.com/dafny-lang/dafny/releases)
   * [Cheatsheet](https://docs.google.com/document/d/1kz5_yqzhrEyXII96eCF1YoHZhnb_6dzv-K3u79bMMis/edit?pref=2&pli=1): basic Dafny syntax on two pages
   * Dafny [Quick Reference](./QuickReference)
   * [Getting started tutorial](./OnlineTutorial/guide), focusing mostly on simple imperative programs
* Detailed documents for programmers
   * [**Dafny Reference Manual**](DafnyRef/DafnyRef)
   * [**Style Guide for Dafny programs**](StyleGuide/Style-Guide)
   * [**Tips and Tricks and FAQs**](HowToFAQ)
   * Language reference for the [Dafny type system](http://leino.science/papers/krml243.html), which also describes available expressions for each type
* Dafny Tutorials
   * [Introduction to Dafny](OnlineTutorial/guide)
   * [A Tutorial on Using Dafny to Construct Verified Software](https://arxiv.org/pdf/1701.04481.pdf), Paqui Lucio, 2017
   * [Value Types](OnlineTutorial/ValueTypes)
   * [Sets](OnlineTutorial/Sets)
   * [Sequences](OnlineTutorial/Sequences)
   * [Lemmas and Induction](OnlineTutorial/Lemmas)
   * [Modules](OnlineTutorial/Modules)
   * [Termination](OnlineTutorial/Termination)

* Forums for Q&amp;A
   * Problem reports on [GitHub](https://gitnub.com/dafny-lang/dafny/Issues)
   * Dafny-tagged queries on [Stackoverflow](https://stackoverflow.com/questions/tagged/dafny)
   * (Internal to Amazon only) The Dafny channel in the AWS workspace on Slack.
   * (Internal to Amazon only) Dafny Coding Clinic

There are also publications and lecture notes:

* 4-part course on the _Basics of specification and verification of code_:
  - Lecture 0: [Pre- and postconditions](https://youtu.be/oLS_y842fMc) (19:08)
  - Lecture 1: [Invariants](https://youtu.be/J0FGb6PyO_k) (20:56)
  - Lecture 2: [Binary search](https://youtu.be/-_tx3lk7yn4) (21:14)
  - Lecture 3: [Dutch National Flag algorithm](https://youtu.be/dQC5m-GZYbk) (20:33)
* Overview article: [Accessible Software Verification with Dafny](https://www.computer.org/csdl/mags/so/2017/06/mso2017060094-abs.html), IEEE Software, Nov/Dec 2017
* [3-page tutorial notes](http://leino.science/papers/krml233.pdf) with examples (ICSE 2013)
* [Dafny Power User](http://leino.science/dafny-power-user)
* Videos at [Verification Corner](https://www.youtube.com/channel/UCP2eLEql4tROYmIYm5mA27A)

And some books:
* K. Rustan M. Leino and Kaleb Leino, 2022, [_Program Proofs_](https://www.lulu.com/shop/k-rustan-m-leino-and-kaleb-leino/program-proofs/paperback/product-wqy8w5.html). to be available from MIT Press in 2023.
* Boro Sitnovski, 2022, [_Introducing Software Verification with Dafny Language_](https://link.springer.com/book/10.1007/978-1-4842-7978-6_)
* Jason Koenig, K. Rustan M. Leino, 2016, [_Getting Started with Dafny: A Guide_](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml220.pdf)

Preliminary notes about Dafny integration with code in other programming languages:
   * [Go](Compilation/Go)
   * [C++](Compilation/Cpp)
   * [Reference values](Compilation/ReferenceTypes)
   * [Automatic Initialization of Variables](Compilation/AutoInitialization.md)

