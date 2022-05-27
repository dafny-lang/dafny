using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Plugins;
using System.Collections;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace PluginsQuickFixTest {
  /// <summary>
  ///  Small plugin that provides a code action to add a dummy comment in front of the first token of the program
  /// </summary>
  public class TestConfiguration : Microsoft.Dafny.LanguageServer.Plugins.PluginConfiguration {
    public override QuickFixer[] GetQuickFixers() {
      return new QuickFixer[] { new DummyQuickFixer() };
    }
  }

  public class DummyQuickFixer : QuickFixer {
    public override QuickFix[] GetQuickFixes(IQuickFixInput input, Range selection) {
      return new QuickFix[] {
        new InstantQuickFix("Insert file header", new QuickFixEdit[] {
          new QuickFixEdit(input.Program.GetFirstTopLevelToken().GetLspRange().GetEndRange(), "/*First comment*/")
        })
      };
    }
  }
}
