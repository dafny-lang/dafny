using System;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny;

// To use it in CLI or Dafny language server, use the option
// --javadoclike-docstring-plugin
// You can also create your own 
public class JavadocLikeDocstringRewriter : Plugins.DocstringRewriter {
  private const string DocTableStart = "\n|  |  |\n| --- | --- |";

  public override string RewriteDocstring(string extractedDocString) {
    var detectJavadoc = new Regex(@"(\r?\n|^)\s*(@param|@return)");
    if (!detectJavadoc.Match(extractedDocString).Success) {
      return null;
    }
    var documentation = "";

    var initialText = new Regex(@"^(?:(?!\r?\n\s*@)[\s\S])*").Match(extractedDocString).Value.Trim();
    documentation += initialText;

    var paramsRanges = new Regex(@"@param\s+(?<Name>\w+)\s+(?<Description>(?:(?!\n\s*@)[\s\S])*)");

    var matches = paramsRanges.Matches(extractedDocString);
    var tableRows = 0;
    for (var i = 0; i < matches.Count; i++) {
      var match = matches[i];
      var name = match.Groups["Name"].Value;
      var description = EscapeNewlines(match.Groups["Description"].Value);
      if (i == 0) {
        if (tableRows++ == 0) {
          documentation += DocTableStart;
        }
        documentation += "\n| **Params** | ";
      } else {
        documentation += "\n| | ";
      }
      documentation += $"**{name}** - {description} |";
    }
    var returnsDoc = new Regex(@"@returns?\s+(?<Description>(?:(?!\n\s*@)[\s\S])*)");
    if (returnsDoc.Match(extractedDocString) is { Success: true } matched) {
      var description = EscapeNewlines(matched.Groups["Description"].Value);
      if (tableRows == 0) {
        documentation += DocTableStart;
      }
      documentation += $"\n| **Returns** | {description} |";
    }

    return documentation;
  }

  private static string EscapeNewlines(string content) {
    var newlines = new Regex(@"\r?\n");
    return newlines.Replace(content, "<br>");
  }
}