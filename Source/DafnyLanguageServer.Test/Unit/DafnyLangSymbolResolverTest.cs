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
    public Dictionary<ErrorLevel, List<ErrorMessage>> GetErrors() {
      return this.AllMessages;
    }
  }

  class DummyModuleDecl : LiteralModuleDecl {
    public DummyModuleDecl() : base(
      new DefaultModuleDecl(), null) {
    }
    public override object Dereference() {
      return this;
    }
  }

  [TestMethod]
  public void EnsureResilienceAgainstErrors() {
    // Builtins is null to trigger an error.
    var reporter = new CollectingErrorReporter();
    var program = new Dafny.Program("dummy", new DummyModuleDecl(), null, reporter);
    dafnyLangSymbolResolver.ResolveSymbols(null!, program, CancellationToken.None);
    Assert.AreEqual(1, reporter.ErrorCount);
    Assert.AreEqual(1, reporter.GetErrors()[ErrorLevel.Error].Count);
    var expected = "Dafny encountered an error.  Please report it at ";
    Assert.AreEqual(expected, reporter.GetErrors()[ErrorLevel.Error][0].message.Substring(0, expected.Length));
  }
}