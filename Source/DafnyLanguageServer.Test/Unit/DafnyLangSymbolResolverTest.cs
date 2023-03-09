using System.Collections.Generic;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Moq;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit; 

[TestClass]
public class DafnyLangSymbolResolverTest {
  private DafnyLangSymbolResolver dafnyLangSymbolResolver;

  [TestInitialize]
  public void SetUp() {
    var loggerFactory = new Mock<ILoggerFactory>();
    dafnyLangSymbolResolver = new DafnyLangSymbolResolver(
      loggerFactory.Object.CreateLogger<DafnyLangSymbolResolver>()
    );
  }

  class CollectingErrorReporter : BatchErrorReporter {
    public Dictionary<ErrorLevel, List<DafnyDiagnostic>> GetErrors() {
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