//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;

namespace Microsoft.Dafny {
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
      preTypeResolver.Constraints.DebugPrint($"    DEBUG: acting on advice, setting {proxy} := {WhatString}");

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
        return new UserDefinedType(s.tok, s.Name, s, new List<Type>());
      }

      var target = what switch {
        Target.Bool => preTypeResolver.Type2PreType(Type.Bool),
        Target.Char => preTypeResolver.Type2PreType(Type.Char),
        Target.Int => preTypeResolver.Type2PreType(Type.Int),
        Target.Real => preTypeResolver.Type2PreType(Type.Real),
        Target.String => preTypeResolver.Type2PreType(StringDecl()),
        Target.Object => preTypeResolver.Type2PreType(preTypeResolver.resolver.SystemModuleManager.ObjectQ()),
        _ => throw new cce.UnreachableException() // unexpected case
      };
      return target;
    }
  }
}
