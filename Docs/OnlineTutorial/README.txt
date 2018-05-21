
Dafny Documentation Source Files
--------------------------------

The Dafny documentation is automatically generated
from .source files using the DocumentationTransducer
program. This program 

 1) synatx highlights Dafny source code in the text
 2) generates the .dfy files and links them appropriately.

The program reads in the given .source file and generates
the .htm and .dfy files in the working directory. It 
ignores all text except for three tags (case sensitive):

<listing>: This specifies a piece of code which will be
   linked in the embedded editor. If there is an <editor/>
   tag before the closing </listing>, then the program text
   after the tag will appear in the editor, and the text
   before the tag will appear in the documentation, syntax
   highlighted. The program will escape all html special
   entities, so source code can be given literally. Example:

   <listing>
   function f(a: object, s: set<object>): bool
   {
      a in s && s != {}
   }
   <editor/>
   function f(a: object, s: set<object>): bool
   {
      a in s // different than above
   }
   </listing>

   Note that <editor/> and </listing> cannot appear in the
   program text at all, and there is no work around for this.
   If the <editor/> tag is missing, then the source code is
   considered the same for both the listing and the editor.
   In either case, the code is set appart from the embedding
   text.

<snippet>: This is like the above, except no link to the editor
   is made. There is still syntax highlighting. This is useful
   for giving snippets of code for which an editor expansion is
   not useful. The closing tag is </snippet>, and it cannot
   appear in the source text as well.

<c>: This tag specifies an inline code segment. No link to the
   editor is generated, but the program fragment is syntax
   highlighted. The closing tag is </c> with the usual restriction.

Build and run instructions
--------------------------

$ msbuild DocumentationTransducer.sln
$ cd manuscripts
$ mono ../DocumentationTransducer/DocumentationTransducer.exe Guide.source
$ mono ../DocumentationTransducer/DocumentationTransducer.exe Lemmas.source
$ mono ../DocumentationTransducer/DocumentationTransducer.exe Termination.source
$ mono ../DocumentationTransducer/DocumentationTransducer.exe ValueTypes.source
$ mono ../DocumentationTransducer/DocumentationTransducer.exe Modules.source
