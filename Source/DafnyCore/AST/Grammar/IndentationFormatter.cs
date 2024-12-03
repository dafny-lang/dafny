using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Formatting;

namespace Microsoft.Dafny;

public class IndentationFormatter : IIndentationFormatter {
  // If we ever decide that blank lines should keep spaces, we can set this to false. 
  public static readonly bool BlankNewlinesWithoutSpaces = true;

  // If we remove whitespace (tabs or space) at the end of lines. 
  public static readonly bool RemoveTrailingWhitespace = true;

  private TokenNewIndentCollector formatter;
  public IndentationFormatter(TokenNewIndentCollector formatter) {
    this.formatter = formatter;
  }

  /// <summary>
  /// Creates an IndentationFormatter for the given program,
  /// by immediately processing all nodes and assigning indentations to most structural tokens 
  /// </summary>
  public static IndentationFormatter ForProgram(Program program, Uri fileToFormat, bool reduceBlockiness = true) {
    var tokenNewIndentCollector = new TokenNewIndentCollector(program, fileToFormat) {
      ReduceBlockiness = reduceBlockiness
    };
    foreach (var child in program.DefaultModuleDef.PreResolveChildren) {
      var isPhysicalToken = child.Tok.line != 0;
      if (isPhysicalToken && child.Tok.Uri != fileToFormat) {
        continue;
      }
      if (child is TopLevelDecl topLevelDecl) {
        tokenNewIndentCollector.SetDeclIndentation(topLevelDecl, 0);
      } else if (child is Include include) {
        if (include.OwnedTokens.Any()) {
          tokenNewIndentCollector.SetOpeningIndentedRegion(include.OwnedTokens.First(), 0);
        }
      }
    }

    return new IndentationFormatter(tokenNewIndentCollector);
  }


  #region Override for implementing IIndentationFormatter

  public string GetNewLeadingTrivia(Token token) {
    return GetNewTrivia(token, false);
  }

  public string GetNewTrailingTrivia(Token token) {
    return GetNewTrivia(token, true);
  }

  /// This method implements IIndentationFormatter.Reindent and is called by Formatter.dfy
  /// It considers the space (trivia) before a token (if trailingTrivia == false)
  /// or the space after a token (if trailingTrivia == true)
  /// and add or remove spaces after every newline to adjust the indentation.
  ///
  /// It uses indentationBefore to fix the indentation everywhere, except if
  /// the space is a leading trivia (trailingTrivia == false)
  /// and it's the last consecutive space without newlines before the token,
  /// in which case it uses indentationInline
  ///
  /// Options:
  /// * If precededByNewline == true, it means that it's possible
  /// to add/remove spaces at the beginning of the string. Used only for leading trivia.
  /// * if trailingTrivia == true, then no indentation is added after
  ///   the eventual last newline  `\n`. Instead, when formatting the leading trivia.
  ///   of the next token, precededByNewline will be set to true.
  ///
  /// # Example
  /// 
  /// For example, consider the consecutive tokens ')' and 'const' in the following unformatted code,
  /// as well as the token 'b' and the final token '}' 
  ///
  /// ```
  /// module X {
  /// datatype A =
  ///     C()
  ///   // Comment
  ///         // continued
  ///
  ///       // Comment here
  ///  const b := 1
  ///
  /// // One last word
  ///   }
  /// ```
  ///
  /// 1. The trailing trivia of the token `)` is
  /// "\n  // Comment\n        // continued\n\n"
  ///
  /// That trivia will be processed with the options
  /// * trailingTrivia == true
  /// * precededByNewline == false (irrelevant, a trailing trivia is preceded by a token)
  /// * indentationBefore == "    " (4 spaces)
  /// * indentationInline == "    " (irrelevant)
  /// The method will return:
  /// "\n    // Comment\n    // continued\n\n"
  ///
  /// 2. The leading trivia of the token `const` is
  /// "      // Comment here\n "
  /// That trivia will be processed with the options
  /// * trailingTrivia == false
  /// * precededByNewline == true
  /// * indentationBefore == "  " (2 spaces, it's indentation for any comment before the constant)
  /// * indentationInline == "  " (2 spaces, it's the indentation in front of the "const" token if it's on its own line)
  /// The method will return:
  /// "  // Comment here\n  "
  ///
  /// 3. The leading trivia of the token `b``is
  /// " "
  /// That trivia will be processed with the options
  /// * trailingTrivia == false
  /// * precededByNewline == false
  /// * indentationBefore == "    "
  /// * indentationInline == "    "
  /// However, because there are no newlines and it's not preceded
  /// by a newline, the method will return the same:
  /// " "
  /// 
  /// 4. The leading trivia of the token `}` is
  /// "// One last word\n"
  /// That trivia will be processed with the options
  /// * trailingTrivia == false
  /// * precededByNewline == true
  /// * indentationBefore == "  "
  /// * indentationInline == ""
  /// This is an example where a comment before this token should not
  /// be aligned with that token, the method will return:
  /// "  // One last word\n"
  ///
  /// After all these formattings, the final result will be the expected one
  /// ```
  /// module X {
  ///   datatype A =
  ///     C()
  ///     // Comment
  ///     // continued
  ///
  ///   // Comment here
  ///   const b := 1
  ///
  ///   // One last word
  /// }
  /// ```
  public string GetNewTrivia(Token token, bool trailingTrivia) {
    var precededByNewline = token.Prev != null && !trailingTrivia && TriviaFormatterHelper.EndsWithNewline(token.Prev.TrailingTrivia);
    if (token.val == "") {
      return trailingTrivia ? token.TrailingTrivia : token.LeadingTrivia;
    }
    var indentationBefore = Whitespace(
      trailingTrivia ?
        formatter.GetIndentBelowOrInlineOrAbove(token) :
        formatter.GetIndentAbove(token));
    var indentationInline = trailingTrivia ?
      Whitespace(formatter.GetIndentBelowOrInlineOrAbove(token)) :
      Whitespace(formatter.GetIndentInlineOrAbove(token));
    //indentationBefore = GetIndentInlineOrAbove(token);
    var input = trailingTrivia ? token.TrailingTrivia : token.LeadingTrivia;
    // Invariant: Relative indentation inside a multi-line comment should be unchanged
    var originalCommentIndent = 0;
    var newCommentIndent = 0;
    var previousMatchWasSingleLineCommentToAlign = false;


    return TriviaFormatterHelper.NewlineRegex.Replace(input, match => {
      // Apply the given rules on a match of a (newline|beginning) + space + optional comment
      if (match.Groups["trailingWhitespace"].Success) {
        return RemoveTrailingWhitespace ? "" : match.Groups["trailingWhitespace"].Value;
      }

      var startOfString = match.Groups["previousChar"].Value == "";
      var capturedComment = match.Groups["capturedComment"].Value;
      var currentIndent = match.Groups["currentIndent"].Value.Length;
      var entireMatch = match.Groups[0].Value;
      var caseCommented = match.Groups["caseCommented"];
      if (startOfString && !precededByNewline) {
        if (capturedComment.StartsWith("//") && originalCommentIndent == 0) {
          // Possibly align consecutive // trailing comments
          originalCommentIndent = token.col - 1 + token.val.Length + currentIndent;
          newCommentIndent = formatter.GetNewTokenVisualIndent(token, 0) + token.val.Length + currentIndent;
          previousMatchWasSingleLineCommentToAlign = true;
        }

        var isTrailingWhitespace = capturedComment.StartsWith("\r") || capturedComment.StartsWith("\n");
        if (RemoveTrailingWhitespace &&
            isTrailingWhitespace) {
          precededByNewline = true;
          return capturedComment;
        }

        if (!capturedComment.StartsWith("/*")) {
          return entireMatch;
        }
      }

      var noMoreComment = capturedComment.Length == 0;
      if (noMoreComment) {
        //If no comment was captured, it means we reached the end of the trivia. Do we indent or not?
        return trailingTrivia ? "" : (precededByNewline ? indentationInline : entireMatch);
      }

      if (!startOfString) {
        precededByNewline = true;
      }

      if (capturedComment.StartsWith("/*")) {
        return ReIndentMultilineComment(token, capturedComment, currentIndent, indentationBefore, precededByNewline, out previousMatchWasSingleLineCommentToAlign);
      }

      if (capturedComment.StartsWith("//")) {
        return ReIndentSingleLineComment(token, capturedComment, originalCommentIndent, currentIndent, newCommentIndent, caseCommented, ref previousMatchWasSingleLineCommentToAlign, ref indentationBefore);
      }

      if (capturedComment.StartsWith("\r") || capturedComment.StartsWith("\n")) {
        previousMatchWasSingleLineCommentToAlign = false;
        return (BlankNewlinesWithoutSpaces ? "" : indentationBefore) + capturedComment;
      }

      previousMatchWasSingleLineCommentToAlign = false;

      // Last line
      return indentationInline;
    });
  }

  private string ReIndentMultilineComment(IOrigin token, string capturedComment, int currentIndent,
    string indentationBefore, bool precededByNewline, out bool previousMatchWasSingleLineCommentToAlign) {
    var doubleStar = capturedComment.StartsWith("/**") && !capturedComment.StartsWith("/***");

    var absoluteOriginalIndent = currentIndent;
    var newAbsoluteIndent = indentationBefore.Length;
    if (!precededByNewline) {
      // It has to be the trailing trivia of that token.
      absoluteOriginalIndent = token.col - 1 + token.val.Length + absoluteOriginalIndent;
      newAbsoluteIndent = formatter.GetNewTokenVisualIndent(token, indentationBefore.Length) + token.val.Length + currentIndent;
    }

    var relativeIndent = newAbsoluteIndent - absoluteOriginalIndent;
    var initialRelativeIndent = relativeIndent;
    var tryAgain = true;
    var result = "";
    // This loop executes at most two times. The second time is necessary only if the indentation before the first /* decreases
    // and there were items that would have been moved into a negative column.
    // e.g.
    //
    // const x := 2;
    //     /* Start of comment
    //   end of comment */
    //
    // would be, after the first iteration
    //
    // const x := 2;
    // /* Start of comment
    // end of comment */
    //
    // which breaks the alignment. So with `tryAgain`, it  corrects the offset so that the comment becomes:
    //
    // const x := 2;
    //   /* Start of comment
    // end of comment */
    //
    while (tryAgain)
    // decreases newAbsoluteIndent - relativeIndent
    {
      var canIndentLinesStartingWithStar = true;
      tryAgain = false;
      result = new Regex($@"(?<=\r?\n|\r(?!\n))(?<existingIndent>[ \t]*)(?<star>\*)?").Replace(capturedComment,
        match1 => {
          if (canIndentLinesStartingWithStar && match1.Groups["star"].Success) {
            return indentationBefore + (doubleStar ? "  *" : " *");
          }

          canIndentLinesStartingWithStar = false;
          // Reindent in block:
          var newIndent = match1.Groups["existingIndent"].Value.Length + relativeIndent;
          if (newIndent < 0) {
            relativeIndent -= newIndent;
            tryAgain = true;
            newIndent = 0;
          }

          return Whitespace(newIndent) + (match1.Groups["star"].Success ? match1.Groups["star"].Value : "");
        });
    }

    previousMatchWasSingleLineCommentToAlign = false;
    if (precededByNewline) {
      return Whitespace(absoluteOriginalIndent + relativeIndent) + result;
    }

    return Whitespace(currentIndent + relativeIndent - initialRelativeIndent) + result;
  }

  private string ReIndentSingleLineComment(Token token, string capturedComment, int originalCommentIndent,
    int currentIndent, int newCommentIndent, Group caseCommented, ref bool previousMatchWasSingleLineCommentToAlign,
    ref string indentationBefore) {
    if (capturedComment.StartsWith("///") && !capturedComment.StartsWith("////")) {
      // No indentation
      return capturedComment;
    }

    if (previousMatchWasSingleLineCommentToAlign && originalCommentIndent == currentIndent) {
      return Whitespace(newCommentIndent) + capturedComment;
    }

    var referenceToken = token.Next;
    var isCommentedCaseFollowedByCase =
      caseCommented.Success && token.Next != null &&
      (token.Next.val == caseCommented.Value || TokenNewIndentCollector.FirstTokenOnLineIs(
        token, t => {
          referenceToken = t;
          return t.val == caseCommented.Value;
        }));
    if (isCommentedCaseFollowedByCase) {
      indentationBefore = Whitespace(formatter.GetNewTokenVisualIndent(referenceToken, indentationBefore.Length));
    }

    previousMatchWasSingleLineCommentToAlign = false;

    return indentationBefore + capturedComment;
  }

  private static readonly ConcurrentDictionary<int, string> WhitespaceCache = new();

  public static string Whitespace(int characters) {
    return WhitespaceCache.GetOrAdd(characters, _ => new string(' ', characters));
  }

  #endregion
}
