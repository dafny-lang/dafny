---
layout: default
---
<link rel="stylesheet" href="../assets/main.css">
<link rel="icon" href="../images/dafny-favicon.png" type="image/png">
<link rel="icon" href="../images/dafny-favicon.svg" type="image/svg+xml">

<script src="https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML" type="text/javascript"></script>

<font size="+4"><p style="text-align: center;">Dafny Reference Manual</p></font> <!-- PDFOMIT -->
<p style="text-align: center;">The dafny-lang community</p> <!-- PDFOMIT -->
<p style="text-align: center;"><script> document.write(new Date(document.lastModified)); </script></p> <!-- PDFOMIT -->
<p style="text-align: center;">
{% include_relative version.txt %}
</p>
<!--PDF NEWPAGE-->

**Abstract:**
This is the Dafny reference manual; it describes the Dafny programming
language and how to use the Dafny verification system.
Parts of this manual are more tutorial in nature in order to help the
user understand how to do proofs with Dafny.

[(Link to current document as html)](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef)

- numbered toc
{:toc}

{% include_relative Introduction.md %}

<!--PDF NEWPAGE-->
{% include_relative Grammar.md %}

<!--PDF NEWPAGE-->
{% include_relative Programs.md %}

<!--PDF NEWPAGE-->
{% include_relative Modules.md %}

<!--PDF NEWPAGE-->
{% include_relative Specifications.md %}

<!--PDF NEWPAGE-->
{% include_relative Types.md %}

<!--PDF NEWPAGE-->
{% include_relative Statements.md %}

<!--PDF NEWPAGE-->
{% include_relative Expressions.md %}

<!--PDF NEWPAGE-->
{% include_relative Refinement.md %}

<!--PDF NEWPAGE-->
{% include_relative Attributes.md %}

<!--PDF NEWPAGE-->
{% include_relative Topics.md %}

<!--PDF NEWPAGE-->
{% include_relative UserGuide.md %}

<!--PDF NEWPAGE-->
{% include_relative VSCodeIDE.md %}

<!--PDF NEWPAGE-->
{% include_relative Plugins.md %}

<!--PDF NEWPAGE-->
{% include_relative CommandLineOptions.md %}

# 29. References

{% include_relative SyntaxTests.md %}

