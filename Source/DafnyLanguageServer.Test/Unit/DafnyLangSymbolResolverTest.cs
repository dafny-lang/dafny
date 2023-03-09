using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Extensions.Logging;
using Moq;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit; 

public class DafnyLangSymbolResolverTest {
  private DafnyLangSymbolResolver dafnyLangSymbolResolver;

  public DafnyLangSymbolResolverTest() {
    var loggerFactory = new Mock<ILoggerFactory>();
    dafnyLangSymbolResolver = new DafnyLangSymbolResolver(
      loggerFactory.Object.CreateLogger<DafnyLangSymbolResolver>()
    );
  }

  class CollectingErrorReporter : BatchErrorReporter {
    public Dictionary<ErrorLevel, List<ErrorMessage>> GetErrors() {
      return this.AllMessages;
    }

    public CollectingErrorReporter(DafnyOptions options) : base(options) {
    }
  }

  class DummyModuleDecl : LiteralModuleDecl {
    public DummyModuleDecl() : base(
      new DefaultModuleDefinition(), null) {
    }
    public override object Dereference() {
      return this;
    }
  }
}
