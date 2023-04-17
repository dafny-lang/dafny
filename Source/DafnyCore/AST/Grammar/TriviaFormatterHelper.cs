using System.Text.RegularExpressions;

namespace Microsoft.Dafny;

public static class TriviaFormatterHelper {
  // A regex that checks if a particular string ends with a newline and some spaces.
  private static readonly Regex EndsWithNewlineRegex =
    new(@"(\r?\n|\r)[ \t]*$");

  // This is used by Formatter.dfy
  public static bool EndsWithNewline(string s) {
    return EndsWithNewlineRegex.IsMatch(s);
  }

  public static readonly string AnyNewline = @"\r?\n|\r(?!\n)";

  private static readonly string NoCommentDelimiter = @"(?:(?!/\*|\*/)[\s\S])*";

  public static readonly string MultilineCommentContent =
    $@"(?:{NoCommentDelimiter}(?:(?'Open'/\*)|(?'-Open'\*/)))*{NoCommentDelimiter}";

  public static readonly Regex NewlineRegex =
    new($@"(?<=(?<previousChar>{AnyNewline}|^))" // Always start after the beginning of the string or after a newline
        + @"(?<currentIndent>[ \t]*)"                  // Captures the current indent on the line
                                                       // Now, either capture a comment or a trailing whitespace.
        + ($@"(?<capturedComment>/\*{MultilineCommentContent}\*/" // Captures a nested multiline comment
           + $@"|///?/? ?(?<caseCommented>(?:\||case))?"           // Captures a single-line comment, with a possibly commented out case.
           + $@"|{AnyNewline}"                                     // Captures a newline
           + $@"|$)")                                              // Captures the end of the string
        + $@"|(?<=\S|^)(?<trailingWhitespace>[ \t]+)(?={AnyNewline})" // Captures a trailing whitespace
    );
}