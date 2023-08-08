using System;
using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;

namespace PluginsTestTranslationError {

  public class TestConfiguration : PluginConfiguration {
    public override Rewriter[] GetRewriters(ErrorReporter errorReporter) {
      return new Rewriter[] { new TranslationErrorRewriter(errorReporter) };
    }
  }

  public class TranslationErrorRewriter : Rewriter {
    public TranslationErrorRewriter(ErrorReporter reporter) : base(reporter) {
    }

    public override void PreTranslate(Program program) {
      Reporter.Error(MessageSource.Translator, program.GetFirstTopLevelToken(),
        "Translation error that should appear in the code");
    }
  }

}