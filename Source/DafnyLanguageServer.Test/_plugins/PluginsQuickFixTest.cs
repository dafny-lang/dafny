using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;
using System.Collections;
using Microsoft.Boogie;

namespace PluginsQuickFixTest {

  /// <summary>
  ///  Small plugin that detects all extern methods and verifies that there are test methods that actually invoke them.
  /// </summary>
  public class TestConfiguration : PluginConfiguration {
    public override QuickFixer[] GetQuickFixers() {
      return new QuickFixer[] { new DummyQuickFixer() };
    }
  }

  public class DummyQuickFixer : QuickFixer {
    public override QuickFix[] GetQuickFixes(IQuickFixInput input, IToken selection) {
      return new QuickFix[] {
        new InstantQuickFix("Insert file header", new QuickFixEdit[] {
          new QuickFixEdit(input.Program.GetFirstTopLevelToken().Start(), "/*First comment*/")
        })
      };
    }
  }

}