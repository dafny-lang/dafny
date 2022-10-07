
This document describes information needed to maintain the Dafny Reference
Manual, including information about syntax coloring.

Note that the reference manual is written in github markdown,
which is rendered by github servers for web browsing
and by pandoc to create a Latex-style pdf.

# The Dafny Reference Manual sources

This folder holds the source for the Dafny Reference Manual. This is the second iteration of the DRM -- the first was based on madoko.
Instead this source is GitHub markdown augmented by MathJax LaTeX math notation.The markdown source is rendered by github pages and can be transformed by
pandoc into pdf, via LaTeX (see the Makefile in this folder).

Some care must be taken to enable both modes of rendering.
* Inline math is bracketed by $...$.
* Displayed (centered) math is enclosed in <p style="text-align: center;">$$...$$</p> and similarly for centered non-math text.
* The abstract is duplicated, to permit it to be part of the pdf title page.
* The title page itself is written in header.tex, in LaTeX.

In addition, some textual search and replace operations are implemented
(see the Makefile) to perform section numbering uniformly and to adjust a few
other aspects that are dissimilar between the pdf and online versions.

GitHub pages are rendered (converted from markdown to html) using Jekyll.
The result is a single, long html page.
There are a number of configuration files for Jekyll in the `docs` folder and
subfolders. In order to render files locally you must
* have `ruby`, `bundler` and `jekyll` installed on your machine
* set the working directly (`cd`) to the `docs` folder (Windows or Ruby 3.0 users, see below for some tweaks)
* run the jekyll server: `bundle exec jekyll server`
* open a browser on the page http://localhost:4000 or directly to http://localhost:4000/DafnyRef/DafnyRef
* the server rerenders when files are changed -- but not always quite completely. Sometimes one must kill the server process, delete all the files in the _saite folder, and restart the server.

In order to convert markdown to pdf, you must be able to execute the Makefile, which requires installing pandoc and LaTeX, and being on a Linux-like platform.

The Makefile does some preprocessing of the markdown files: it removes some
markdown lines that are not interpreted by pandoc and adds some additional
directives, such as page breaks.

To re-generate `Options.txt`, run `make options` in the `DafnyRef` folder.

## Windows users or Ruby 3.0 users

You might want to apply this diff to the file `../GemFile`
```diff
gem "kramdown", ">= 2.3.1"
+gem "webrick"
```

and then run `bundle install`

# Syntax Coloring

Tools providing syntax coloring for programming language source typically
require a PL-specific regular-expression based definition of the language
syntax. Unfortunately there are many such tools.

In the RM markdown sources, text bracketed by ` ```dafny ` and ` ``` ` will have
syntax coloring for dafny applied. Text bracketed by
` ```grammar ` and ` ``` ` has syntax coloring applied per the grammar
definition file.

## On-line RM through github
Github uses rouge, via Jekyll. The syntax definition is a ruby-based file
maintained in the rouge github repo.
To modify the definition, follow the directions in
[https://rouge-ruby.github.io/docs/file.LexerDevelopment.html]
(https://rouge-ruby.github.io/docs/file.LexerDevelopment.html)
after setting up a development environment according to
[https://rouge-ruby.github.io/docs/file.DevEnvironment.html]
(https://rouge-ruby.github.io/docs/file.DevEnvironment.html).
The file itself, `dafny.rb` is in Ruby. Details of the Ruby Regular
Expression language can be found many places online, such as
[here](https://www.princeton.edu/~mlovett/reference/Regular-Expressions.pdf).

Within the github repo for rouge, the syntax definition file is
`rouge/lib/rouge/lexers/dafny.rb`. You also need to maintain a
test file, in `rouge/lib/rouge/demos/dafny` and a demonstration and
development file in `rouge/spec/visual/samples/dafny`.
The development instructions tell how to view this latter file as you
debug or extend the definition file.

Once you create a PR that is merged, github automatically (after a bit of a
time lag) uses the file to render code snippets.
[The rouge maintenance team must accept the PR -- it seems they are not
very active.]

The mapping from tokens to actual colors is specified separately from the
syntax definition. The on-line rendering uses the Github default
(which, at last investigation, was not changeable).

Although the RM sources also contain grammar blocks, there is at present no
rouge definition for these blocks.

## Latex pdf

The pdf version of the RM is created by `pandoc`, which uses the
[KDE tool](https://docs.kde.org). pandoc references (via the command-line
in the Makefile) local definition files that are in the Dafny github
repository, at `dafny/docs/KDESyntaxDefinition/`. Though these definition
files could be submitted to the KDE repo for public use, at present they
are only local.

One can test the syntax definition file by running the Makefile to create the
pdf. One of the last pages of the RM is a test page for syntax coloring.

The coloring style (mapping of tokens to colors) is set in the `dafny.theme` file.
Note that there is a definition and theme for the grammar blocks in the pdf
file as well.


## LSP

Many IDEs interact with Language Servers (via LSP). Possibly an LSP protocol
will be generated in the future.