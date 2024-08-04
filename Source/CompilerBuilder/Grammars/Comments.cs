// See https://aka.ms/new-console-template for more information

namespace CompilerBuilder.Grammars;

interface ITriviaContainer {
  List<string> Trivia { get; set; }
}

public static class Comments {

  public static Grammar<List<string>> JavaTrivia() {
    return GrammarBuilder.Whitespace.Or(SlashSlashLineComment()).Many();
  }
  
  public static Grammar<string> SlashSlashLineComment() {
    // TODO I think the printer has to reinsert the line break
    return new ExplicitGrammar<string>(ParserBuilder.SlashSlashLineComment, Verbatim.Instance);
  }
  
  /*
   * Identify all SequenceG. If both sides are non-empty, then insert trivia in between
   * by replacing the left with another SequenceG that has trivia on its right,
   * If the type of the left side can carry trivia, insert them there
   */
  public static Grammar<T> AddTrivia<T>(Grammar<T> root, Grammar<List<string>> triviaGrammar) {
    var grammars = root.SelfAndDescendants;
    var voidTrivia = new ParseOnly<List<string>>(triviaGrammar);
    foreach (var grammar in grammars) {
      if (grammar is not ISequenceLikeG sequence) {
        continue;
      }

      if (sequence.FirstType == typeof(ITriviaContainer)) {
        sequence.First = new SequenceG<ITriviaContainer, List<string>, ITriviaContainer>(
          (Grammar<ITriviaContainer>)sequence.First,
          triviaGrammar,
          sequence.Mode,
          (c, trivia) => {
            c.Trivia = trivia.ToList();
            return c;
          },
          c => (c, c.Trivia)
        );
      } else {
        if (sequence.FirstType == typeof(Unit)) {
          sequence.Second = GrammarExtensions.Then(voidTrivia, (dynamic)sequence.Second);
        } else {
          sequence.First = GrammarExtensions.Then((dynamic)sequence.First, voidTrivia);
        }
      }
    }

    return voidTrivia.Then(root).Then(voidTrivia);
  }
}