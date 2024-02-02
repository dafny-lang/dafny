---
layout: default
---
<font size="+4"><p style="text-align: center;">Dafny Errors and Warnings</p></font> <!-- PDFOMIT -->


<link rel="stylesheet" href="../assets/main.css">
<link rel="icon" href="../images/dafny-favicon.png" type="image/png">
<link rel="icon" href="../images/dafny-favicon.svg" type="image/svg+xml">

<script src="https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML" type="text/javascript"></script>

This page contains a catalog of the dafny tool's Error and Warning messages,
all in one long page to facilitate searching.

The title of each section is an error message.
Each section contains example code that produces the error,
which is then followed by explanation and references.

Italicized words in the given messages indicate variable content.

# **Command-line Errors and Warnings**

{% include_relative Errors-CommandLine.md %} 

# **Compilation Errors**

{% include_relative Errors-Compiler.md %}

# **Parser Errors and Warnings**

{% include_relative Errors-Parser.md %}

# **Miscellaneous Errors and Warnings**

{% include_relative Errors-Generic.md %}

# **Name and Type Resolution Errors and Warnings**

{% include_relative Errors-Resolution.md %}
{% include_relative Errors-Resolver2.md %}
{% include_relative Errors-Resolver3.md %}
{% include_relative Errors-Rewriter.md %}

# **Verification Errors**

_This section is a work in progress_

