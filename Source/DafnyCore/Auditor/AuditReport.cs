using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Policy;
using System.Text;

namespace Microsoft.Dafny.Auditor;

/// <summary>
/// Represents an audit report of a Dafny program, ultimately intended to give an overview of
/// the final assurance argument for the verification of that program. For the moment, it consists
/// of a set of assumptions that can be rendered in several formats.
/// </summary>
public class AuditReport {
  private DafnyOptions options;
  private Dictionary<Declaration, IEnumerable<Assumption>> allAssumptionsByDecl = new();

  // All three fields below are filtered by AddAssumptions()
  private HashSet<Declaration> declsWithEntries = [];
  private HashSet<ModuleDefinition> modulesWithEntries = [];
  private Dictionary<Declaration, IEnumerable<Assumption>> assumptionsByDecl = new();

  public AuditReport(DafnyOptions options) {
    this.options = options;
  }

  private void UseDecl(Declaration decl) {
    declsWithEntries.Add(decl);
    switch (decl) {
      case MemberDecl memberDecl:
        UseDecl(memberDecl.EnclosingClass);
        break;
      case TopLevelDeclWithMembers topDecl:
        modulesWithEntries.Add(topDecl.EnclosingModuleDefinition);
        break;
    }
  }
  public void AddAssumptions(Declaration decl, IEnumerable<Assumption> assumptions) {
    var explicitAssumptions = assumptions.Where(a => a.desc.IsExplicit);
    var assumptionsToAdd = explicitAssumptions.Any() ? explicitAssumptions : assumptions;
    if (assumptionsToAdd.Any()) {
      assumptionsByDecl.Add(decl, assumptionsToAdd);
      UseDecl(decl);
    }
  }

  public IEnumerable<KeyValuePair<Declaration, IEnumerable<Assumption>>> AllAssumptions() {
    return assumptionsByDecl;
  }

  public IEnumerable<Assumption> AllAssumptionsForDecl(Declaration decl) {
    return allAssumptionsByDecl.TryGetValue(decl, out var assumptions)
      ? assumptions : [];
  }

  private string RenderRow(string beg, string sep, string end, IEnumerable<string> cells) {
    return beg + String.Join(sep, cells) + end + "\n";
  }

  private string GetFullName(Declaration decl) {
    if (decl is MemberDecl m) {
      return m.FullDafnyName;
    } else if (decl is ModuleDecl mod) {
      return mod.FullDafnyName;
    } else if (decl is TopLevelDecl tld) {
      return tld.FullDafnyName;
    } else {
      return decl.Name;
    }
  }
  private IEnumerable<string> IssueRow(Declaration decl, Assumption a, string issue, string mitigation, Func<string, string> targetFormatter) {
    return new List<string>() {
      GetFullName(decl),
      (!(decl is ICallable c && c.IsGhost)).ToString(),
      Attributes.Contains(decl.Attributes, "axiom").ToString(),
      Attributes.Contains(decl.Attributes, "extern").ToString(),
      targetFormatter(issue),
      targetFormatter(mitigation)
    };
  }

  private string RenderAssumptionRows(Declaration decl, IEnumerable<Assumption> assumptions, string beg, string sep, string end, Func<string, string> targetFormatter) {
    var rows = assumptions
      .Select(a => RenderRow(beg, sep, end, IssueRow(decl, a, a.desc.Issue, a.desc.Mitigation, targetFormatter)));
    return String.Concat(rows);
  }

  private string RenderAssumptionRowsMarkdown(Declaration decl, IEnumerable<Assumption> a) {
    return RenderAssumptionRows(decl, a, "| ", " | ", " |",
      s => Assumption.UpdateVerbatim(s, "`", "`"));
  }

  private string RenderAssumptionRowsHTML(Declaration decl, IEnumerable<Assumption> a) {
    return RenderAssumptionRows(decl, a, "<tr><td>", "</td><td>", "</td></tr>",
      s => Assumption.UpdateVerbatim(s, "<code>", "</code>"));
  }

  public string RenderHTMLTable() {
    var header =
      "<tr><th>Name</th><th>Compiled</th><th>Explicit Assumption</th>" +
      "<th>Extern</th><th>Issue</th><th>Mitigation</th></tr>\n";
    var rows = assumptionsByDecl.Select(entry => RenderAssumptionRowsHTML(entry.Key, entry.Value));
    return header + String.Concat(rows);
  }

  public string RenderMarkdownTable() {
    var header =
      "|Name|Compiled|Explicit Assumption|Extern|Issue|Mitigation|\n" +
      "|----|--------|-------------------|------|-----|----------|\n";
    var rows = assumptionsByDecl.Select(entry => RenderAssumptionRowsMarkdown(entry.Key, entry.Value));
    return header + String.Concat(rows);
  }

  private void AppendMarkdownIETFDescription(AssumptionDescription desc, StringBuilder text) {
    var issue = Assumption.UpdateVerbatim(desc.Issue, "`", "`");
    var mitigation = Assumption.UpdateVerbatim(desc.MitigationIetf, "`", "`");
    text.AppendLine("");
    text.AppendLine($"* {issue} {mitigation}");
  }

  public string RenderMarkdownIETF() {
    StringBuilder text = new StringBuilder();

    foreach (var module in modulesWithEntries) {
      if (module.TryToAvoidName) {
        text.AppendLine($"# Default module");
      } else {
        text.AppendLine($"# Module `{module.Name}`");
      }
      foreach (var topLevelDecl in module.TopLevelDecls) {
        if (!declsWithEntries.Contains(topLevelDecl)) {
          continue;
        }
        text.AppendLine("");
        if (topLevelDecl is DefaultClassDecl) {
          text.AppendLine($"## Top level");
        } else {
          text.AppendLine($"## Type `{topLevelDecl.Name}`");
        }

        foreach (var a in AllAssumptionsForDecl(topLevelDecl)) {
          AppendMarkdownIETFDescription(a.desc, text);
        }

        if (topLevelDecl is not TopLevelDeclWithMembers topLevelDeclWithMembers) {
          continue;
        }
        foreach (var decl in topLevelDeclWithMembers.Members) {
          if (!declsWithEntries.Contains(decl)) {
            continue;
          }

          text.AppendLine("");
          text.AppendLine($"### Member `{decl.Name}`");
          foreach (var a in AllAssumptionsForDecl(decl)) {
            AppendMarkdownIETFDescription(a.desc, text);
          }
        }
      }
    }

    return text.ToString();
  }

  public string RenderText() {
    var text = new StringBuilder();

    foreach (var (decl, assumptions) in assumptionsByDecl) {
      foreach (var assumption in assumptions) {
        text.AppendLine($"{decl.Origin.OriginToString(options)}:{assumption.Warning()}");
      }
    }

    return text.ToString();
  }

  public static AuditReport BuildReport(Program program) {
    AuditReport report = new(program.Options);

    report.allAssumptionsByDecl = program.Assumptions(null)
      .GroupBy(a => a.decl)
      .ToDictionary(g => g.Key,
                    g => g.Select(a => a));

    foreach (var moduleDefinition in program.Modules()) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
        report.AddAssumptions(topLevelDecl, report.AllAssumptionsForDecl(topLevelDecl));

        if (topLevelDecl is not TopLevelDeclWithMembers topLevelDeclWithMembers) {
          continue;
        }
        foreach (var decl in topLevelDeclWithMembers.Members) {
          if (decl.Origin.FromIncludeDirective(program)) {
            // Don't audit included code
            continue;
          }

          report.AddAssumptions(decl, report.AllAssumptionsForDecl(decl));
        }
      }
    }

    return report;
  }
}
