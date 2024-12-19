using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;
using System.Collections;

namespace PluginsAdvancedTest {

  /// <summary>
  ///  Small plugin that detects all extern methods and verifies that there are test methods that actually invoke them.
  /// </summary>
  public class TestConfiguration : PluginConfiguration {
    public string PluginUser = "";
    public bool ForceName = false;
    public override void ParseArguments(string[] args) {
      ForceName = args.Length > 0 && args[0] == "force";
      PluginUser = args.Length > 1 ? ", " + args[1] : "";
    }
    public override Rewriter[] GetRewriters(ErrorReporter errorReporter) {
      return new Rewriter[] { new ExternCheckRewriter(errorReporter, this) };
    }
  }

  public class ExternCheckRewriter : Rewriter {
    private readonly TestConfiguration configuration;

    public ExternCheckRewriter(ErrorReporter reporter, TestConfiguration configuration) : base(reporter) {
      this.configuration = configuration;
    }

    public override void PostResolve(Program program) {
      foreach (var moduleDefinition in program.Modules()) {
        foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
          if (topLevelDecl is TopLevelDeclWithMembers cd) {
            foreach (var member in cd.Members) {
              if (member is Method methodExtern) {
                if (Attributes.Contains(member.Attributes, "extern")) {
                  // Verify that there exists a test method which references this extern method.
                  var tested = false;
                  Method candidate = null;
                  foreach (var member2 in cd.Members) {
                    if (member2 == member || !(member2 is Method methodTest)) {
                      continue;
                    }
                    if (!Attributes.Contains(methodTest.Attributes, "test")) {
                      continue;
                    }
                    if (!moduleDefinition.CallGraph.Reaches(methodTest, methodExtern)) {
                      continue;
                    }
                    candidate = methodTest;

                    if (configuration.ForceName && candidate.Name != methodExtern.Name + "_test") {
                      continue;
                    }
                    tested = true;
                    break;
                  }

                  if (!tested) {
                    var forceMessage = configuration.ForceName ? $" named {methodExtern.Name}_test" : "";
                    var token = configuration.ForceName && candidate != null
                      ? new NestedOrigin(methodExtern.Tok, candidate.Tok, "You might want to just rename this method")
                      : methodExtern.Tok;
                    Reporter.Error(MessageSource.Resolver, token,
                      $"Please declare a method {{:test}}{forceMessage} that will call {methodExtern.Name}{configuration.PluginUser}");
                  }
                }
              }
            }
          }
        }
      }
    }
  }

}