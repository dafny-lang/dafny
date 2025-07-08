using System.Collections.Generic;

namespace Microsoft.Dafny.Triggers;

internal class TriggerAnnotationsCache {
  public readonly Dictionary<Expression, HashSet<OldExpr>> ExpressionsInOldContext;
  public readonly Dictionary<Expression, TriggerAnnotation> Annotations;

  /// <summary>
  /// For certain operations, the TriggersCollector class needs to know whether
  /// a particular expression is under an old(...) wrapper. This is in particular
  /// true for generating trigger terms (but it is not for checking whether something
  /// is a trigger killer, so passing an empty set here for that case would be fine.
  /// </summary>
  public TriggerAnnotationsCache(Dictionary<Expression, HashSet<OldExpr>> expressionsInOldContext) {
    this.ExpressionsInOldContext = expressionsInOldContext;
    Annotations = new Dictionary<Expression, TriggerAnnotation>();
  }
}