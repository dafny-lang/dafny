using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using JetBrains.Annotations;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language;

/// <summary>
/// A verification quick fixers provides quick "fixes" for verification errors.
/// For now, it offers to inline a failing postcondition if its failure is
/// indicated on the '{' -- meaning there is no explicit return.
/// </summary>
class AllOpaqueCodeActionProvider : DafnyCodeActionProvider {
  private DafnyOptions options;

  private static readonly Regex LineRegexReplacer = new Regex(@";\s*");
  public AllOpaqueCodeActionProvider(DafnyOptions options) {
    this.options = options;
  }
  
  
  class InsertAllOpaqueAndRevealStatements : DafnyCodeAction {
    private readonly Declaration target;
    private readonly string originalRevealStatements;

    public InsertAllOpaqueAndRevealStatements(
      Declaration target,
      int count,
      string originalRevealStatements
      ) : base($@"Insert `{{:allOpaque}}` and {count} reveal statement{(count > 1 ? "s" : "")}") {
      this.target = target;
      this.originalRevealStatements = originalRevealStatements;
    }

    public override IEnumerable<DafnyCodeActionEdit> GetEdits() {
      var funIndent = new string(' ', target.StartToken.col - 1);
      var indent = funIndent + "  ";
      var revealStatements =
        "\n" + indent +
        LineRegexReplacer.Replace(originalRevealStatements, ";\n" + indent).Trim();
      var bodyStartTok = target is Method m ? m.BodyStartTok :
        target is Function f ? f.Body.StartToken.Prev : null;
      var edits = new List<DafnyCodeActionEdit>() {
        DafnyCodeActionEdit.InsertBefore("{:allOpaque} ", target.tok)
        };
      if(bodyStartTok != null) {
        DafnyCodeActionEdit.InsertAfter(bodyStartTok, revealStatements);
      };
      IToken? requiresRevealToken = null;
      if (target is Method method &&
          (method.OwnedTokens.Any(tok => tok.val == "returns")
          || method.Req.Any()
          || method.Ens.Any()
          || method.Decreases.OwnedTokens.Any()
          || method.Mod.OwnedTokens.Any())) {
        requiresRevealToken =
          target.OwnedTokens.LastOrDefault(tok => tok.val == ")");
      }
      if (target is Function function) {
        requiresRevealToken = function.ResultType.EndToken;
        if (requiresRevealToken.Next.val == ")") {
          requiresRevealToken =
            requiresRevealToken.Next;
        }
      }
      // Ensures that `function T(): int {` gets a newline before the `{`
      if(requiresRevealToken is Token { line: > 0}) {
        var revealStatementsRequires =
          $"\n{indent}requires\n  {indent}{LineRegexReplacer.Replace(originalRevealStatements, ";\n  " + indent)}true";
        if (requiresRevealToken.Next.val == "{" && requiresRevealToken.line == requiresRevealToken.Next.line) {
          revealStatementsRequires += "\n" + funIndent;
        }
        edits.Add(DafnyCodeActionEdit.InsertAfter(requiresRevealToken, revealStatementsRequires));
      }
      // TODO: Subset type decls and witnesses
      // TODO: Constant definitions

      return edits;
    }
  }

  public override IEnumerable<DafnyCodeAction> GetDafnyCodeActions(IDafnyCodeActionInput input, Range selection) {
    if (!options.Get(CommonOptionBag.AllOpaque)) {
      return Enumerable.Empty<DafnyCodeAction>();
    }
    if (input.Program != null) {
      var finished = false;
      var result = new List<DafnyCodeAction>();
      input.Program.Visit((Node n) => {
        if (n.StartToken.line > 0 && !n.RangeToken.ToLspRange().Contains(selection)) {
          return false;
        }

        if (finished) {
          return false;
        }

        if (n is Declaration decl && n is Method or Function) {
          finished = true;
          if (!Attributes.Contains(decl.Attributes, "allOpaque")) {
            if (selection.Start.Line != decl.RangeToken.ToLspRange().Start.Line) {
              return false;
            }

            // Let's look at whether there were reveal statements added.

            foreach (var diagnostic in input.Diagnostics) {
              if (diagnostic.Level == ErrorLevel.Info && diagnostic.Token.pos == decl.tok.pos
                                                      && diagnostic.Message.StartsWith("reveal")) {
                var originalRevealStatements = diagnostic.Message;
                var count = LineRegexReplacer.Matches(originalRevealStatements).Count;
                result.Add(new InsertAllOpaqueAndRevealStatements(decl, count, originalRevealStatements));
                break;
              }
            }
          }
          return false;
        }

        return true;
      });
      return result;
    } else {
      return Enumerable.Empty<DafnyCodeAction>();
    }
  }
}