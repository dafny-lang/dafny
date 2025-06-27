//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;

namespace Microsoft.Dafny {
  /// <summary>
  /// A piece of "Advice" is information about a default type.
  ///
  /// A "newtype" of a base type "B" defines a new type that is distinct from "B", with the constructors, operators, and members of "B"
  /// cloned for the new type. For example,
  ///     newtype MyInt = int
  /// defines the type "MyInt". It has the same constructors of "int" (for example, the constructors "7" and "19") and the same operators
  /// as "int" (for example, "+"). As another example,
  ///     newtype MyIntSet = set<int>
  /// defines the type "MyIntSet", and thus set displays (like "{2, 3}"), set comprehensions (like "set x | 0 <= x < 10 :: 2 * x"),
  /// and set operators (like "+") are cloned for the new type.
  ///
  /// Consequently, built-in constructors (like "7" and "{2, 3}") are overloaded. Type inference can therefore not immediately
  /// the type of these constructors. Using the examples above, the type of "7" could be either "int" or "MyInt". (For numeric constructors
  /// like "7", the type could also be the bitvector type of any width as well as the type "ORDINAL".) During type inference,
  /// if any of these constructors is used with specific types, then the overloading can be resolved. But if there are other such types,
  /// as for example in this program:
  ///     method Main() {
  ///       var x := 7 + 19;
  ///       print x, "\n";
  ///     }
  /// then the "Advice" kicks in.
  ///
  /// So, a piece of "Advice" is saying that a given "PreType" should have a specific type *if* the program does not have any other
  /// specific type for it.
  /// </summary>
  public abstract class Advice {
    public readonly PreType PreType;

    public Advice(PreType pretype) {
      PreType = pretype;
    }

    public abstract string WhatString { get; }

    public bool Apply(PreTypeResolver preTypeResolver) {
      if (PreType.Normalize() is PreTypeProxy proxy) {
        ActOnAdvice(proxy, preTypeResolver);
        return true;
      }
      return false;
    }

    public bool ApplyFor(PreTypeProxy proxy, PreTypeResolver preTypeResolver) {
      if (PreType.Normalize() == proxy) {
        ActOnAdvice(proxy, preTypeResolver);
        return true;
      }
      return false;
    }

    private void ActOnAdvice(PreTypeProxy proxy, PreTypeResolver preTypeResolver) {
      // Note, the following debug print may come out _before_ the "Type inference state ..." header, if ActOnAdvice is called
      // during what is only a partial constraint solving round.
      preTypeResolver.Constraints.DebugPrint($"    acting on advice, setting {proxy} := {WhatString}");

      var adviceType = GetAdviceType(preTypeResolver);
      proxy.Set(adviceType);
    }

    protected abstract PreType GetAdviceType(PreTypeResolver preTypeResolver);
  }

  public class TypeAdvice : Advice {
    private readonly PreType adviceType;
    public TypeAdvice(PreType preType, PreType adviceType)
      : base(preType) {
      this.adviceType = adviceType;
    }

    public override string WhatString => adviceType.ToString();

    protected override PreType GetAdviceType(PreTypeResolver preTypeResolver) {
      return adviceType;
    }
  }

  public class CommonAdvice : Advice {
    public enum Target {
      Bool,
      Char,
      Int,
      Real,
      String,
      Object
    }

    private readonly Target what;

    public override string WhatString => what == Target.Object ? PreType.TypeNameObjectQ : what.ToString().ToLower();

    public CommonAdvice(PreType preType, Target advice)
      : base(preType) {
      what = advice;
    }

    protected override PreType GetAdviceType(PreTypeResolver preTypeResolver) {
      Type StringDecl() {
        var s = preTypeResolver.resolver.moduleInfo.TopLevels["string"];
        return new UserDefinedType(s.Origin, s.Name, s, []);
      }

      var target = what switch {
        Target.Bool => preTypeResolver.Type2PreType(Type.Bool),
        Target.Char => preTypeResolver.Type2PreType(Type.Char),
        Target.Int => preTypeResolver.Type2PreType(Type.Int),
        Target.Real => preTypeResolver.Type2PreType(Type.Real),
        Target.String => preTypeResolver.Type2PreType(StringDecl()),
        Target.Object => preTypeResolver.Type2PreType(preTypeResolver.resolver.SystemModuleManager.ObjectQ()),
        _ => throw new Cce.UnreachableException() // unexpected case
      };
      return target;
    }
  }
}
