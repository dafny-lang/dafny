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
  private Dictionary<Declaration, AssumptionProperties> assumptionsByDecl = new();

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
  public void AddAssumptions(Declaration decl, AssumptionProperties assumptions) {
    if (assumptions.HasAssumptions()) {
      assumptionsByDecl.Add(decl, assumptions);
      UseDecl(decl);
    }
  }

  public IEnumerable<Assumption> AllAssumptions() {
    return assumptionsByDecl.Select((e, _) => new Assumption(e.Key, e.Value));
  }

  private string RenderRow(string beg, string sep, string end, IEnumerable<string> cells) {
    return beg + String.Join(sep, cells) + end;
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
  private IEnumerable<string> IssueRow(Assumption a, string issue, string mitigation, Func<string, string> targetFormatter) {
    return new List<string>() {
      GetFullName(a.decl),
      (!a.props.IsGhost).ToString(),
      a.props.HasAxiomAttribute.ToString(),
      a.props.HasExternAttribute.ToString(),
      targetFormatter(issue),
      targetFormatter(mitigation)
    };
  }

  private string RenderAssumptionRows(Assumption a, string beg, string sep, string end, Func<string, string> targetFormatter) {
    var rows = a.props
      .Description()
      .Select((desc, _) => RenderRow(beg, sep, end, IssueRow(a, desc.issue, desc.mitigation, targetFormatter)));
    return rows.Count() > 0 ? String.Join("\n", rows) : a.ToString();
  }

  private string UpdateVerbatim(string text, string beg, string end) {
    return text.Replace("[", beg).Replace("]", end);
  }

  private string RenderAssumptionRowsMarkdown(Assumption a) {
    return RenderAssumptionRows(a, "| ", " | ", " |",
      s => UpdateVerbatim(s, "`", "`"));
  }

  private string RenderAssumptionRowsHTML(Assumption a) {
    return RenderAssumptionRows(a, "<tr><td>", "</td><td>", "</td></tr>",
      s => UpdateVerbatim(s, "<code>", "</code>"));
  }

  public string RenderHTMLTable() {
    var header =
      "<tr><th>Name</th><th>Compiled</th><th>Explicit Assumption</th>" +
      "<th>Extern</th><th>Issue</th><th>Mitigation</th></tr>\n";
    var rows = AllAssumptions().Select(RenderAssumptionRowsHTML);
    return header + String.Join("\n", rows);
  }

  public string RenderMarkdownTable() {
    var header =
      "|Name|Compiled|Explicit Assumption|Extern|Issue|Mitigation|\n" +
      "|----|--------|-------------------|------|-----|----------|\n";
    var rows = AllAssumptions().Select(RenderAssumptionRowsMarkdown);
    return header + String.Join("\n", rows);
  }

  private void AppendMarkdownIETFDescription(AssumptionDescription desc, StringBuilder text) {
    var issue = UpdateVerbatim(desc.issue, "`", "`");
    var mitigation = desc.mitigation.Replace("[", "`").Replace("]", "`");
    var mustMitigation = char.ToLower(mitigation[0]) + mitigation.Substring(1);
    text.AppendLine("");
    text.AppendLine($"* {issue} MUST {mustMitigation}");
  }

  public string RenderMarkdownIETF() {
    StringBuilder text = new StringBuilder();

    foreach (var module in modulesWithEntries) {
      text.AppendLine($"# Module `{module.Name}`");
      foreach (var topLevelDecl in module.TopLevelDecls) {
        if (!declsWithEntries.Contains(topLevelDecl)) {
          continue;
        }
        text.AppendLine("");
        text.AppendLine($"## Type `{topLevelDecl.Name}`");

        if (assumptionsByDecl.ContainsKey(topLevelDecl)) {
          foreach (var desc in assumptionsByDecl[topLevelDecl].Description()) {
            AppendMarkdownIETFDescription(desc, text);
          }
        }

        if (topLevelDecl is not TopLevelDeclWithMembers topLevelDeclWithMembers) {
          continue;
        }
        foreach (var decl in topLevelDeclWithMembers.Members) {
          if (!declsWithEntries.Contains(decl)) {
            continue;
          }

          text.AppendLine("");
          text.AppendLine($"## Member `{decl.Name}`");
          if (assumptionsByDecl.ContainsKey(decl)) {
            foreach (var desc in assumptionsByDecl[decl].Description()) {
              AppendMarkdownIETFDescription(desc, text);
            }
          }
        }
      }
    }

    return text.ToString();
  }

  public string RenderText() {
    StringBuilder text = new StringBuilder();

    foreach (var assumption in AllAssumptions()) {
      foreach (var warning in assumption.Warnings()) {
        var decl = assumption.decl;
        text.AppendLine($"{ErrorReporter.TokenToString(decl.tok)}:{warning}");
      }
    }

    return text.ToString();
  }
}