using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Plugins;
using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace PluginsDafnyCodeActionTest {
  /// <summary>
  ///  Small plugin that provides a code action to add a dummy comment in front of the first token of the program
  /// </summary>
  public class TestConfiguration : Microsoft.Dafny.LanguageServer.Plugins.PluginConfiguration {
    public override DafnyCodeActionProvider[] GetDafnyCodeActionProviders() {
      return new DafnyCodeActionProvider[] { new DummyDafnyCodeActionProvider() };
    }
  }

  public class DummyDafnyCodeActionProvider : DafnyCodeActionProvider {
    public override IEnumerable<DafnyCodeAction> GetDafnyCodeActions(IDafnyCodeActionInput input, Range selection) {
      var token = ((Program)input.Program).GetStartOfFirstFileToken();
      return new DafnyCodeAction[] {
        new InstantDafnyCodeAction("Insert file header", new DafnyCodeActionEdit[] {
          new DafnyCodeActionEdit(new TokenRange(token, token).ToDafnyRange(), "/*First comment*/")
        })
      };
    }
  }
}
