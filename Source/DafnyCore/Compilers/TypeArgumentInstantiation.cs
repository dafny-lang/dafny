using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Compilers;

/// <summary>
/// A "TypeArgumentInstantiation" is essentially a pair consisting of a formal type parameter and an actual type for that parameter.
/// </summary>
public class TypeArgumentInstantiation {
  public readonly TypeParameter Formal;
  public readonly Type Actual;

  public TypeArgumentInstantiation(TypeParameter formal, Type actual) {
    Contract.Requires(formal != null);
    Contract.Requires(actual != null);
    Formal = formal;
    Actual = actual;
  }

  /// <summary>
  /// Uses "formal" for both formal and actual.
  /// </summary>
  public TypeArgumentInstantiation(TypeParameter formal) {
    Contract.Requires(formal != null);
    Formal = formal;
    Actual = new UserDefinedType(formal);
  }

  public static List<TypeArgumentInstantiation> ListFromMember(MemberDecl member, List<Type> /*?*/ classActuals, List<Type> /*?*/ memberActuals) {
    Contract.Requires(classActuals == null || classActuals.Count == (member.EnclosingClass == null ? 0 : member.EnclosingClass.TypeArgs.Count));
    Contract.Requires(memberActuals == null || memberActuals.Count == (member is ICallable ic ? ic.TypeArgs.Count : 0));

    var r = new List<TypeArgumentInstantiation>();
    void add(List<TypeParameter> formals, List<Type> actuals) {
      Contract.Assert(formals.Count == actuals.Count);
      for (var i = 0; i < formals.Count; i++) {
        r.Add(new TypeArgumentInstantiation(formals[i], actuals[i]));
      }
    };

    if (classActuals != null && classActuals.Count != 0) {
      Contract.Assert(member.EnclosingClass.TypeArgs.TrueForAll(ta => ta.Parent is TopLevelDecl));
      add(member.EnclosingClass.TypeArgs, classActuals);
    }
    if (memberActuals != null && member is ICallable icallable) {
      Contract.Assert(icallable.TypeArgs.TrueForAll(ta => !(ta.Parent is TopLevelDecl)));
      add(icallable.TypeArgs, memberActuals);
    }
    return r;
  }

  public static List<TypeArgumentInstantiation> ListFromClass(TopLevelDecl cl, List<Type> actuals) {
    Contract.Requires(cl != null);
    Contract.Requires(actuals != null);
    Contract.Requires(cl.TypeArgs.Count == actuals.Count);

    var r = new List<TypeArgumentInstantiation>();
    for (var i = 0; i < cl.TypeArgs.Count; i++) {
      r.Add(new TypeArgumentInstantiation(cl.TypeArgs[i], actuals[i]));
    }
    return r;
  }

  public static List<TypeArgumentInstantiation> ListFromFormals(List<TypeParameter> formals) {
    Contract.Requires(formals != null);
    return formals.ConvertAll(tp => new TypeArgumentInstantiation(tp, new UserDefinedType(tp)));
  }

  public static List<TypeParameter> ToFormals(List<TypeArgumentInstantiation> typeArgs) {
    Contract.Requires(typeArgs != null);
    return typeArgs.ConvertAll(ta => ta.Formal);
  }

  public static List<Type> ToActuals(List<TypeArgumentInstantiation> typeArgs) {
    Contract.Requires(typeArgs != null);
    return typeArgs.ConvertAll(ta => ta.Actual);
  }
}