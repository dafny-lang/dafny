using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  public class CounterExampleItem {
    // TODO use LSP's position.
    public int Line { get; }
    public int Col { get; }
    public IDictionary<string, string> Variables = new Dictionary<string, string>();

    public CounterExampleItem(Position position, IDictionary<string, string> variables) {
      Line = position.Line;
      Col = position.Character;
      Variables = variables;
    }
  }
}
