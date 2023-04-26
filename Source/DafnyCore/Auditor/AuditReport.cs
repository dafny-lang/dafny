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
  private HashSet<Declaration> declsWithEntries = new();
  private HashSet<ModuleDefinition> modulesWithEntries = new();
  private Dictionary<Declaration, IEnumerable<Assumption>> assumptionsByDecl = new();

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
    var explicitAssumptions = assumptions.Where(a => a.desc.isExplicit);
    var assumptionsToAdd = explicitAssumptions.Any() ? explicitAssumptions : assumptions;
    if (assumptionsToAdd.Any()) {
      assumptionsByDecl.Add(decl, assumptionsToAdd);
      UseDecl(decl);
    }
  }

  public IEnumerable<KeyValuePair<Declaration, IEnumerable<Assumption>>> AllAssumptions() {
    return assumptionsByDecl;
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
      .Select(a => RenderRow(beg, sep, end, IssueRow(decl, a, a.desc.issue, a.desc.mitigation, targetFormatter)));
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
    var issue = Assumption.UpdateVerbatim(desc.issue, "`", "`");
    var mitigation = Assumption.UpdateVerbatim(desc.mitigation, "`", "`");
    var mustMitigation = char.ToLower(mitigation[0]) + mitigation.Substring(1);
    text.AppendLine("");
    text.AppendLine($"* {issue} MUST {mustMitigation}");
  }

  public string RenderMarkdownIETF() {
    StringBuilder text = new StringBuilder();

    foreach (var module in modulesWithEntries) {
      if (module.IsDefaultModule) {
        text.AppendLine($"# Default module");
      } else {
        text.AppendLine($"# Module `{module.Name}`");
      }
      foreach (var topLevelDecl in module.TopLevelDecls) {
        if (!declsWithEntries.Contains(topLevelDecl)) {
          continue;
        }
        text.AppendLine("");
        if (topLevelDecl is ClassDecl classDecl && classDecl.IsDefaultClass) {
          text.AppendLine($"## Top level");
        } else {
          text.AppendLine($"## Type `{topLevelDecl.Name}`");
        }

        foreach (var a in topLevelDecl.Assumptions()) {
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
          foreach (var a in decl.Assumptions()) {
            AppendMarkdownIETFDescription(a.desc, text);
          }
        }
      }
    }

    return text.ToString();
  }

  public string RenderText() {
    StringBuilder text = new StringBuilder();

    foreach (var (decl, assumptions) in assumptionsByDecl) {
      foreach (var assumption in assumptions) {
        text.AppendLine($"{ErrorReporter.TokenToString(decl.tok)}:{assumption.Warning(decl)}");
      }
    }

    return text.ToString();
  }

  public static AuditReport BuildReport(Program program) {
    AuditReport report = new();

    foreach (var moduleDefinition in program.Modules()) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
        report.AddAssumptions(topLevelDecl, topLevelDecl.Assumptions());
        if (topLevelDecl is not TopLevelDeclWithMembers topLevelDeclWithMembers) {
          continue;
        }

        foreach (var decl in topLevelDeclWithMembers.Members) {
          report.AddAssumptions(decl, decl.Assumptions());
        }
      }
    }

    return report;
  }
}
