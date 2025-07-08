---
title: Summary of Dafny Documentation
---

Author: David R. Cok (david.r.cok@gmail.com) - 31 May 2023

## dafny.org

The user portal to Dafny documentation is the dafny.org website.
This is a GitHub Pages site, served by GitHub, from the dafny-lang/dafny.github.io repository.
However the material in this repository is a series of snapshots of the development version of the documentation. 
That development version is maintained in the docs folder of the dafny-lang/dafny GitHub project.

It is not intended that the dafny-lang/dafny.github.io (the GitHub pages) site be edited directly.
Instead, the process for creating a new Dafny release includes creating a snapshot of the current Dafny documentation (by running the script docs/make-snapshot)
dafny.org points by default to the documentation at the time of the latest release (at dafny.org/latest), with earlier release snapshots also available, 
The bleeding-edge current development state is available at dafny.org/dafny.

This documentation consists of a variety of large and small documents and links to other resources, such as books.

Some issues to watch:
- Having the current version of documentation in dafny-lang/dafny keeps changes in documentation as part of the same commits as changes in code.
- However, maintaining the github pages site as a collecction of snapshots also has a maintenance cost.
- It is not known how much use users make of which material on these websites. Some analytics would inform future work.
- It is not known how frequently users access old material, to justify maintaining it. (One could always resurrect old version from GitHub directly.)

## The GitHub project

The Dafny project uses GitHub repositories to store all of its artifacts. There are a number of repositories, all under github.com/dafny-lang.

The principal repository is github.com/dafny-lang/dafny, which contains the project source code and the project documentation. The latter is primarily in dafny/docs.

## Dafny Reference Manual and User Guide

This large document is the definition of the Dafny language and a guide to its use.
   * It is a (GitHub) markdown document that is served by GitHub pages at dafny.org/latest/DafnyRef/DafnyRef (with snapshots at each release); the current development version is https://dafny.org/dafny/DafnyRef/DafnyRef
   * The source material is in dafny/docs/DafnyRef
   * The document is also rendered to pdf using pandoc; that pdf document is created and shipped with each release build. The Makefile to do the building is dafny/docs/DafnyRef/Makefile. The release build happens using GitHub actions on GitHub VMs.
   * Section numbering is not built-in (because markdown does not support it). Run `make numbers` when sections need renumbering, which includes updating internal document hyperlinks. 
     Run `make options` when the command-line options documentation needs updating (this material is included by running the dafny tool to print out the in-app help information.
     The CI build will fail if section numbering and options are not up-to-date in the manual.

Maintenance of the reference manual.
   * Team members are expected to add documentation when they add features. Such documentation should be reviewed for understandability and completeness. Also, periodically the whole document needs review for consistency.
   * Particularly before each release, a check should be made that new functionality is described thoroughly in the release.
   * The manual is large and has grown to include reference manual material (the definition of the Dafny language), user guide material (how to use the dafny tools) and tutorial material (detailed explanations and examples). It might be reasonable to separate these into different documents.
   * Various touchup tasks are listed in the github issues list with the ‘documentation’ tag

## FAQs

The folder docs/HowToFAQ contains a large number of files named FAQ*.md. These along with index.md and one-page.md are a collection of FAQs and answers. 
Each FAQ has a title and link in `index.md`, which points to a markdown file for that FAQ.
To aid searching, a (long) one page version is generated with the script `make-onepage`, which generates the `one-page.md` file (so that file should not be edited directly.

Task for the future:
- add to FAQs based on more recent questions
- consider whether to have just the index.md and one-page.md and avoid the intermediate small files
- determine how much use is made of these files

## Small documents

- Installation instructions (these should be validated on clean systems every now and then, particularly when new versions of OSes are released)
- Landing page for dafny.org
- The Style Guide to writing Dafny programs.

## Error message catalog

The files `docs/HowToFAQ/Errors-*.md` contain a catalog of (ideally) every error message that Dafny tools can produce, along with (a) a small code example that elicits that error and (b) an extended explanation of the error, sufficient to aid the user in fixing the error.
This is a sizable body of work and needs continual updating as the Dafny tools evolve.
The code examples are written in such a way that running the `check-examples` script on each of these .md files checks that the code does indeed produce to reported error. This check is done as part of CI to ensure the error messages stay correct as the code evolves.

TODO - add material about tools to check that the information is consistent.

## Checking of examples

Nearly all the examples in the reference manual, error catalog, FAQs and tutorials are written in a way such that scripts (`check-examples`) check that the examples work correctly (as dafny evolves). These checks are done as part of CI.

## Material for developers of the dafny tools

The folder ‘docs/dev’ contains material relevant to developers and not to users. This includes information like release instructions and measuring test coverage.

## The Dafny Library

The Dafny library is a set of (mostly) Dafny code that implements core modules and algorithms that many users might commonly use and should not have to reimplement.
Anything in the library should be documented, with examples. The examples should be checked during the regular CI of the library.
Making sure the documentation is accurate and complete as material is added to the library requires ongoing vigilance.

The library is in the dafny-lang/libraries repository.

## Dafny doc

`dafny doc` is a dafny tool particularly relevant to documentation: it generates html pages from the docsstring content within Dafny programs.
It is meant both for user use and as a way to generate web-based documentation of the library.

Task for the future: As of 31 May 2023, the library and the dafny doc tool are not yet released in a manner that there are published library documentation pages on the dafny web site.

## Other material

- Rustan Leino authors a number of ‘Dafny Power User’ notes and other Dafny technical references. These are typically hosted on his own professional web site at https://leino.science/dafny-power-user/. 
They have typically not been reviewed directly by any Dafny technical documentation team.

- John Tristan teaches courses and workshops on Dafny and authors course materials for that purpose.

- Some tutorial material is written by developers separately and typically needs to be coralled into the docs arena, reviewed and edited, and with CI checks to make sure examples stay operational.

- Blog posts as yet do not have mechanisms to check that code snippets are valid Dafny.


