using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class TypeUtil {
    public static Dictionary<TypeParameter, Type> TypeSubstitutionMap(List<TypeParameter> formals, List<Type> actuals) {
      Contract.Requires(formals != null);
      Contract.Requires(actuals != null);
      Contract.Requires(formals.Count == actuals.Count);
      var subst = new Dictionary<TypeParameter, Type>();
      for (int i = 0; i < formals.Count; i++) {
        subst.Add(formals[i], actuals[i]);
      }
      return subst;
    }

    /// <summary>
    /// If the substitution has no effect, the return value is pointer-equal to 'type'
    /// </summary>
    public static Type SubstType(Type type, Dictionary<TypeParameter, Type> subst) {
      Contract.Requires(type != null);
      Contract.Requires(cce.NonNullDictionaryAndValues(subst));
      Contract.Ensures(Contract.Result<Type>() != null);

      if (type is BasicType) {
        return type;
      } else if (type is SelfType) {
        Type t;
        if (subst.TryGetValue(((SelfType)type).TypeArg, out t)) {
          return cce.NonNull(t);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unresolved SelfType
        }
      } else if (type is MapType) {
        var t = (MapType)type;
        var dom = SubstType(t.Domain, subst);
        if (dom is InferredTypeProxy) {
          ((InferredTypeProxy)dom).KeepConstraints = true;
        }
        var ran = SubstType(t.Range, subst);
        if (ran is InferredTypeProxy) {
          ((InferredTypeProxy)ran).KeepConstraints = true;
        }
        if (dom == t.Domain && ran == t.Range) {
          return type;
        } else {
          return new MapType(t.Finite, dom, ran);
        }
      } else if (type is CollectionType) {
        var t = (CollectionType)type;
        var arg = SubstType(t.Arg, subst);
        if (arg is InferredTypeProxy) {
          ((InferredTypeProxy)arg).KeepConstraints = true;
        }
        if (arg == t.Arg) {
          return type;
        } else if (type is SetType) {
          var st = (SetType)type;
          return new SetType(st.Finite, arg);
        } else if (type is MultiSetType) {
          return new MultiSetType(arg);
        } else if (type is SeqType) {
          return new SeqType(arg);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected collection type
        }
      } else if (type is ArrowType) {
        var t = (ArrowType)type;
        return new ArrowType(t.tok, (ArrowTypeDecl)t.ResolvedClass, t.Args.ConvertAll(u => SubstType(u, subst)), SubstType(t.Result, subst));
      } else if (type is UserDefinedType) {
        var t = (UserDefinedType)type;
        if (t.ResolvedClass is TypeParameter tp) {
          if (subst.TryGetValue(tp, out var s)) {
            Contract.Assert(t.TypeArgs.Count == 0);
            return cce.NonNull(s);
          } else {
            return type;
          }
        } else if (t.ResolvedClass != null) {
          List<Type> newArgs = null;  // allocate it lazily
          var resolvedClass = t.ResolvedClass;
          var isArrowType = ArrowType.IsPartialArrowTypeName(resolvedClass.Name) || ArrowType.IsTotalArrowTypeName(resolvedClass.Name);
#if TEST_TYPE_SYNONYM_TRANSPARENCY
          if (resolvedClass is TypeSynonymDecl && resolvedClass.Name == "type#synonym#transparency#test") {
            // Usually, all type parameters mentioned in the definition of a type synonym are also type parameters
            // to the type synonym itself, but in this instrumented testing, that is not so, so we also do a substitution
            // in the .Rhs of the synonym.
            var syn = (TypeSynonymDecl)resolvedClass;
            var r = SubstType(syn.Rhs, subst);
            if (r != syn.Rhs) {
              resolvedClass = new TypeSynonymDecl(syn.tok, syn.Name, syn.TypeArgs, syn.Module, r, null);
              newArgs = new List<Type>();
            }
          }
#endif
          for (int i = 0; i < t.TypeArgs.Count; i++) {
            Type p = t.TypeArgs[i];
            Type s = SubstType(p, subst);
            if (s is InferredTypeProxy && !isArrowType) {
              ((InferredTypeProxy)s).KeepConstraints = true;
            }
            if (s != p && newArgs == null) {
              // lazily construct newArgs
              newArgs = new List<Type>();
              for (int j = 0; j < i; j++) {
                newArgs.Add(t.TypeArgs[j]);
              }
            }
            if (newArgs != null) {
              newArgs.Add(s);
            }
          }
          if (newArgs == null) {
            // there were no substitutions
            return type;
          } else {
            // Note, even if t.NamePath is non-null, we don't care to keep that syntactic part of the expression in what we return here
            return new UserDefinedType(t.tok, t.Name, resolvedClass, newArgs);
          }
        } else {
          // there's neither a resolved param nor a resolved class, which means the UserDefinedType wasn't
          // properly resolved; just return it
          return type;
        }
      } else if (type is TypeProxy) {
        TypeProxy t = (TypeProxy)type;
        if (t.T == null) {
          return type;
        }
        var s = SubstType(t.T, subst);
        return s == t.T ? type : s;
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    /// <summary>
    /// Return a type that is like "type", but with type arguments "arguments".
    /// </summary>
    public static Type ReplaceTypeArguments(Type type, List<Type> arguments) {
      Contract.Requires(type != null);
      Contract.Requires(!(type is TypeProxy));
      Contract.Requires(!(type is SelfType));
      Contract.Requires(arguments != null);
      Contract.Requires(type.TypeArgs.Count == arguments.Count);

      if (type is BasicType) {
        return type;
      } else if (type is MapType) {
        var t = (MapType)type;
        return new MapType(t.Finite, arguments[0], arguments[1]);
      } else if (type is SetType) {
        var st = (SetType)type;
        return new SetType(st.Finite, arguments[0]);
      } else if (type is MultiSetType) {
        return new MultiSetType(arguments[0]);
      } else if (type is SeqType) {
        return new SeqType(arguments[0]);
      } else if (type is ArrowType) {
        var t = (ArrowType)type;
        return new ArrowType(t.tok, (ArrowTypeDecl)t.ResolvedClass, arguments);
      } else if (type is UserDefinedType) {
        var t = (UserDefinedType)type;
        return new UserDefinedType(t.tok, t.Name, t.ResolvedClass, arguments);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

}
