using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  public class CounterExampleItem {
    public Position Position { get; }

    public string Assumption { get; }

    public CounterExampleItem(Position position, string assumption) {
      Position = position;
      Assumption = assumption;
    }
  }
}
