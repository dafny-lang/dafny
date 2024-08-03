// See https://aka.ms/new-console-template for more information

using System.Linq.Expressions;
using Microsoft.Dafny;

namespace CompilerBuilder;

public static class Comments {
  /*
   * Identify all SequenceG. If both sides are non-empty, then insert trivia in between
   * by replacing the left with another SequenceG that has trivia on its right,
   * If the type of the left side can carry trivia, insert them there
   */
  public static Grammar<T> AddJavaComments<T>(Grammar<T> grammar) {
    var grammars = new GrammarPathRoot(grammar).SelfAndDescendants;
    //foreach(var sequence in grammars.OfType<SequenceG<>>())
    throw new NotImplementedException();
  }
}