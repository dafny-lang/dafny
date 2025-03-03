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

    public override void PreVerify(ModuleDefinition module) {
      Reporter.Error(MessageSource.Translator, module.Origin, "Translation error that should appear in the code");
    }
  }

}