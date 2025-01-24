using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Dafny.Triggers;

internal class TriggerAnnotation {
  public readonly bool IsTriggerKiller;
  internal readonly ISet<IVariable> Variables;
  internal readonly List<TriggerTerm> PrivateTerms;
  internal readonly List<TriggerTerm> ExportedTerms;

  internal TriggerAnnotation(bool isTriggerKiller,
    IEnumerable<IVariable> variables,
    IEnumerable<TriggerTerm> allTerms,
    IEnumerable<TriggerTerm> privateTerms = null) {
    this.IsTriggerKiller = isTriggerKiller;
    this.Variables = new HashSet<IVariable>(variables);
    this.PrivateTerms = [.. privateTerms ?? []];
    this.ExportedTerms = [.. allTerms == null ? [] : allTerms.Except(this.PrivateTerms)];
  }

  public override string ToString() {
    StringBuilder sb = new StringBuilder();
    string indent = "  {0}", nindent = "\n  - {0}", subindent = "\n    * {0}";

    sb.AppendFormat(indent, IsTriggerKiller);

    sb.AppendFormat(nindent, "Variables:");
    foreach (var bv in Variables) {
      sb.AppendFormat(subindent, bv.Name);
    }

    sb.AppendFormat(nindent, "Exported terms:");
    foreach (var term in ExportedTerms) {
      sb.AppendFormat(subindent, term);
    }

    if (PrivateTerms.Any()) {
      sb.AppendFormat(nindent, "Private terms:");
      foreach (var term in PrivateTerms) {
        sb.AppendFormat(subindent, term);
      }
    }

    return sb.ToString();
  }
}