using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  public class CounterExampleList : Container<CounterExampleItem> {
    public CounterExampleList() {
    }

    public CounterExampleList(IEnumerable<CounterExampleItem> items) : base(items) {
    }

    public CounterExampleList(params CounterExampleItem[] items) : base(items) {
    }
  }
}
