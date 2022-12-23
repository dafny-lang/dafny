---
title: Dafny Resources for Users
layout: default
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults
---

<link rel="stylesheet" href="assets/main.css">
<script src="https://polyfill.io/v3/polyfill.min.js?features=es6"></script>
<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
<script type="text/x-mathjax-config">
        MathJax.Hub.Config({tex2jax: {inlineMath: [['$','$'], ["\\(","\\)"]], displayMath: [ ["$$","$$"], ["\\[","\\]"] ]
        }});
</script>

<font size="+4"><p style="text-align: center;">Dafny Documentation</p></font>

<p style="text-align: center;">
{% include_relative DafnyRef/version.txt %}
</p>

This page contains links to Dafny documentation.

[Project site for releases, issues, installation instructions, and source code](https://github.com/dafny-lang/dafny)

* Quick start material:
   * [Installation](https://github.com/dafny-lang/dafny/wiki/INSTALL) and [Releases](https://github.com/dafny-lang/dafny/releases)
   * [Cheatsheet](DafnyCheatsheet.pdf)
   * Dafny [Quick Reference](./QuickReference)
   * [Getting started tutorial](./OnlineTutorial/guide), focusing mostly on simple imperative programs
   * [FAQs and explanations of error messages](HowToFAQ/index)
* Detailed documents for programmers
   * [**Dafny Reference Manual**](DafnyRef/DafnyRef)
   * [**Style Guide for Dafny programs**](StyleGuide/Style-Guide)
   * Language reference for the [Dafny type system](http://leino.science/papers/krml243.html), which also describes available expressions for each type
   * [Miscellaneous Examples of Dafny programs](examples/README)
* Dafny Tutorials
   * [Introduction to Dafny](OnlineTutorial/guide)
   * [Value Types](OnlineTutorial/ValueTypes)
   * [Sets](OnlineTutorial/Sets)
   * [Sequences](OnlineTutorial/Sequences)
   * [Lemmas and Induction](OnlineTutorial/Lemmas)
   * [Modules](OnlineTutorial/Modules)
   * [Termination](OnlineTutorial/Termination)
   * [A Tutorial on Using Dafny to Construct Verified Software](https://arxiv.org/pdf/1701.04481.pdf), Paqui Lucio, 2017
* Forums for Q&amp;A (#discussion)
   * [Problem reports](https://github.com/dafny-lang/dafny/issues) and [discussions](https://github.com/dafny-lang/dafny/discussions) on GitHub
   * Dafny-tagged queries on [Stackoverflow](https://stackoverflow.com/questions/tagged/dafny)

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
* K. Rustan M. Leino, 2023, [_Program Proofs_](https://mitpress.mit.edu/9780262546232/program-proofs/), to be available in 2023.
* K. Rustan M. Leino and Kaleb Leino, 2020, [_Program Proofs_](https://www.lulu.com/shop/k-rustan-m-leino-and-kaleb-leino/program-proofs/paperback/product-wqy8w5.html). Draft version of the book being published by MIT Press in 2023 (see previous item).
* Boro Sitnovski, 2022, [_Introducing Software Verification with Dafny Language_](https://link.springer.com/book/10.1007/978-1-4842-7978-6_)
* Jason Koenig, K. Rustan M. Leino, 2016, [_Getting Started with Dafny: A Guide_](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml220.pdf)

Miscellaneous notes about compiling Dafny code
   * [Go](Compilation/Go)
   * [Strings and Characters](StringsAndChars)
   * [Reference values](Compilation/ReferenceTypes)
   * [Automatic Initialization of Variables](Compilation/AutoInitialization)
   * [Boogie](Compilation/Boogie)
