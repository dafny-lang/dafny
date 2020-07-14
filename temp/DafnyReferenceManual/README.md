This folder holds the source for the Dafny Reference Manual. This is the second iteration of the DRM -- the first was based on madoko.
Instead this source is GitHub markdown augmented by MathJax LaTeX math notation.The markdown source is rendered by github pages and can be transformed by
pandoc into pdf, via LaTeX (see the Makefile in this folder).

Some care must be taken to enable both modes of rendering. 
* Inline math is bracketed by $...$. 
* Displayed (centered) math is enclosed in <p style="text-align: center;">$$...$$</p> and similarly for centered non-math text.
* The abstract is duplicated, to permit it to be part of the pdf title page.
* The title page itself is written in header.tex, in LaTeX.

GitHub pages are rendered (converted from markdown to html) using Jekyll. 
There are a number of configuration files for Jekyll in the docs folder and
subfolders. In order to render files locally you must 
* have ruby, bundler and jekyll installed on your machine
* set the working directly (cd) to the docs folder
* run the jekyll server: bundle exec jekyll server
* open a browser on the page http://localhost:4000 or directly to http://localhost:4000/DafnyReferenceManual/DafnyRef
* the server rerenders when files are changed -- but not always quite completely. Sometimes one must kill the saerver process, delete all the files in the _saite folder, and restart the server.

In order to convert markdown to pdf, you must be able to execute the Makefile, which requires installing pandoc and LaTeX, and being on a Linux-like platform.
