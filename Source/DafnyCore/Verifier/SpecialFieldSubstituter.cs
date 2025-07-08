using System.Collections.Generic;

namespace Microsoft.Dafny {
  /**
   * A substituter for references to special fields (like out-params) in method specifications.
   */
  internal class SpecialFieldSubstituter : Substituter {
    private readonly Dictionary<string, Expression> fieldMap;

    internal SpecialFieldSubstituter(Dictionary<string, Expression> fieldMap)
      : base(null, new(), new()) {
      this.fieldMap = fieldMap;
    }

    public override Expression Substitute(Expression expr) {
      if (expr is MemberSelectExpr {
        Obj: ThisExpr,
        Member: SpecialField {
          SpecialId: SpecialField.ID.UseIdParam,
          IdParam: string idParam
        }
      } && fieldMap.TryGetValue(idParam, out var replacement)) {
        return replacement;
      }
      return base.Substitute(expr);
    }
  }
}