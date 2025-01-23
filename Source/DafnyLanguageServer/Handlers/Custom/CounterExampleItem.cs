using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  public class CounterExampleItem(Position position, string assumption) {
    public Position Position { get; } = position;

    public string Assumption { get; } = assumption;
  }
}
