using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  public record CounterExampleItem(Position Position, IDictionary<string, string> Variables);
}
