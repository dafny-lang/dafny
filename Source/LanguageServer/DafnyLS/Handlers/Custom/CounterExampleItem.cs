using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  public class CounterExampleItem {
    public Position Position { get; }
    public IDictionary<string, string> Variables { get; }

    public CounterExampleItem(Position position, IDictionary<string, string> variables) {
      Position = position;
      Variables = variables;
    }
  }
}
