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

<font size="+4"><p style="text-align: center;">Dafny Documentation</p></font>

This site contains links to Dafny documentation.

[Project site for releases, issues, installation instructions, and source code](https://github.com/dafny-lang/dafny)

* Quick start material:
   * Dafny [Quick Reference](./QuickReference)
   * [Getting started tutorial](./OnlineTutorial/guide), focusing mostly on simple imperative programs
   * [Cheatsheet](https://docs.google.com/document/d/1kz5_yqzhrEyXII96eCF1YoHZhnb_6dzv-K3u79bMMis/edit?pref=2&pli=1): basic Dafny syntax on two pages
* Detailed documents for programmers
   * [Dafny Reference Manual](DafnyRef/DafnyRef)
   * Language reference for the [Dafny type system](http://leino.science/papers/krml243.html), which also describes available expressions for each type
   * [Style Guide for Dafny programs](StyleGuide/Style-Guide)
* Dafny Tutorials
   * [Introduction to Dafny](OnlineTutorial/guide)
   * [Value Types](OnlineTutorial/ValueTypes)
   * [Sets](OnlineTutorial/Sets)
   * [Sequences](OnlineTutorial/Sequences)
   * [Lemmas and Induction](OnlineTutorial/Lemmas)
   * [Modules](OnlineTutorial/Modules)
   * [Termination](OnlineTutorial/Termination)

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

Notes for Dafny contributors:
* Notes on Compilation
   * [Go](Compilation/Go)
   * [C++](Compilation/Cpp)
   * [Reference values](Compilation/ReferenceTypes)
   * [Automatic Initialization of Variables](Compilation/AutoInitialization.md)
