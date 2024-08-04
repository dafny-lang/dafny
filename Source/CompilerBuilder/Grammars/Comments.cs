// See https://aka.ms/new-console-template for more information

using System.Linq.Expressions;
using Microsoft.Dafny;

namespace CompilerBuilder;

interface ITriviaContainer {
  List<string> Trivia { get; set; }
}

public static class Comments {
  /*
   * Identify all SequenceG. If both sides are non-empty, then insert trivia in between
   * by replacing the left with another SequenceG that has trivia on its right,
   * If the type of the left side can carry trivia, insert them there
   */
  public static void AddJavaComments(Grammar root, Grammar<IEnumerable<string>> triviaGrammar) {
    var grammars = new GrammarPathRoot(root).SelfAndDescendants;
    var voidTrivia = new ParseOnly<IEnumerable<string>>(triviaGrammar);
    foreach (var grammarPath in grammars) {
      var grammar = grammarPath.Current;
      if (grammar is SequenceG<ITriviaContainer, dynamic, ITriviaContainer> sequence) {
        sequence.Left = new SequenceG<ITriviaContainer, IEnumerable<string>, ITriviaContainer>(sequence.Left, triviaGrammar,
          sequence.Mode,
          (c, trivia) => {
            c.Trivia = trivia.ToList();
            return c;
          },
          c => (c, c.Trivia)
        );
      } else if (grammar is SequenceG<dynamic, dynamic, dynamic> nonContainerSequence) {
        nonContainerSequence.Left = nonContainerSequence.Left.Then(voidTrivia);
      }
    }
  }
}