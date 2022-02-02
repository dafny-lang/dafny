using System.Linq;
using System.Threading.Tasks;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.Threading;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Extensions.DependencyModel;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

[TestClass]
public class PluginsAdvancedTest : PluginsTestBase {
  [TestInitialize]
  public async Task SetUp() {
    await SetUpPlugin();
  }

  protected override string GetLibraryCode() {
    return @"
using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;
using System.Collections;

namespace PluginsAdvancedTest {

/// <summary>
///  Small plugin that detects all extern methods and verifies that there are test methods that actually invoke them.
/// </summary>
public class TestConfiguration: Configuration {
  public string PluginUser = """";
  public bool ForceName = false;
  public override void ParseArguments(string[] args) {
    ForceName = args.Length > 0 && args[0] == ""force"";
    PluginUser = args.Length > 1 ? "", "" + args[1] : """";
  }
  public override Rewriter[] GetRewriters(ErrorReporter errorReporter) {
    return new Rewriter[]{new ExternCheckRewriter(errorReporter, this)};
  }
}

public class ExternCheckRewriter: Rewriter {
  private readonly TestConfiguration configuration;

  public ExternCheckRewriter(ErrorReporter reporter, TestConfiguration configuration): base(reporter) {
    this.configuration = configuration;
  }

  public override void PostResolve(Program program) {
    foreach (var moduleDefinition in program.Modules()) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
        if (topLevelDecl is ClassDecl cd) {
          foreach (var member in cd.Members) {
            if (member is Method methodExtern) {
              if (Attributes.Contains(member.Attributes, ""extern"")) {
                // Verify that there exists a test method which references this extern method.
                var tested = false;
                Method candidate = null;
                foreach (var member2 in cd.Members) {
                  if (member2 == member || !(member2 is Method methodTest)) {
                    continue;
                  }
                  if (!Attributes.Contains(methodTest.Attributes, ""test"")) {
                    continue;
                  }
                  if (!moduleDefinition.CallGraph.Reaches(methodTest, methodExtern)) {
                    continue;
                  }
                  candidate = methodTest;

                  if (configuration.ForceName && candidate.Name != methodExtern.Name + ""_test"") {
                    continue;
                  }
                  tested = true;
                  break;
                }

                if (!tested) {
                  var forceMessage = configuration.ForceName ? $"" named {methodExtern.Name}_test"" : """";
                  var token = configuration.ForceName && candidate != null
                    ? new NestedToken(methodExtern.tok, candidate.tok, ""You might want to just rename this method"")
                    : methodExtern.tok;
                  Reporter.Error(MessageSource.Resolver, token,
                    $""Please declare a method {{:test}}{forceMessage} that will call {methodExtern.Name}{configuration.PluginUser}"");
                }
              }
            }
          }
        }
      }
    }
  }
}

}";
  }

  protected override string GetLibraryName() {
    return "PluginsAdvancedTest";
  }

  protected override string[] GetCommandLineArgument() {
    return new[] { $@"--dafny:plugins:0=""{LibraryPath},force you""" };
  }

  [TestMethod]
  public async Task EnsureErrorMessageCanBeComplexAndTakeIntoAccountConfiguration() {
    var documentItem = CreateTestDocument(@"
method {:extern} myMethod(i: int) returns (j: int)

method {:test} myMethodWrongName() {
  var result := myMethod(0);
  expect result == 1;
}
");
    await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionReport = await DiagnosticReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.AreEqual(documentItem.Uri, resolutionReport.Uri);
    var diagnostics = resolutionReport.Diagnostics.ToArray();
    Assert.AreEqual(1, DafnyOptions.O.Plugins.Count, "Too many plugins loaded");
    Assert.AreEqual(1, diagnostics.Length, LibraryPath + " did not raise an error.");
    Assert.AreEqual("Please declare a method {:test} named myMethod_test that will call myMethod, you", diagnostics[0].Message);
    Assert.AreEqual(new Range((1, 17), (1, 25)), diagnostics[0].Range);
    var related = diagnostics[0].RelatedInformation?.GetEnumerator();
    Assert.IsTrue(related != null && related.MoveNext());
    Assert.AreEqual("You might want to just rename this method", related.Current.Message);
    Assert.AreEqual(new Range((3, 15), (3, 32)), related.Current.Location.Range);
    related.Dispose();
  }

  [TestCleanup]
  public void DoCleanup() {
    CleanupPlugin();
  }
}
