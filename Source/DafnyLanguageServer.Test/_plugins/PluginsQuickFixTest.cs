using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Plugins;
using System.Collections;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace PluginsQuickFixTest {
  /// <summary>
  ///  Small plugin that detects all extern methods and verifies that there are test methods that actually invoke them.
  /// </summary>
  public class TestConfiguration : Microsoft.Dafny.LanguageServer.Plugins.PluginConfiguration {
    public override QuickFixer[] GetQuickFixers() {
      return new QuickFixer[] { new DummyQuickFixer() };
    }
  }

  public class DummyQuickFixer : QuickFixer {
    public override QuickFix[] GetQuickFixes(IQuickFixInput input, Range selection) {
      var firstToken = input.Program.GetFirstTopLevelToken();
      var firstRange = firstToken.GetLspRange();
      var range = firstRange.EndRange();
      return new QuickFix[] {
        new InstantQuickFix("Insert file header", new QuickFixEdit[] {
          new QuickFixEdit(range, "/*First comment*/")
        })
      };
    }
  }

}