// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
#nullable enable

using System;
using System.Linq;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny {

  /// <summary>
  /// This class stores various transformations that could be useful to perform
  /// on types extracted from DafnyModel (e.g. to convert Boogie type names
  /// back to the original Dafny names)
  /// </summary>
  public static class DafnyModelTypeUtils {

    private static readonly Regex ModuleSeparatorRegex = new("(?<=[^_](__)*)_m");
    private static readonly Regex UnderscoreRemovalRegex = new("__");
    private static readonly Regex TupleRegex = new("_[Ss]ystem\\._?[Tt]uple#?");

    public static Type GetNonNullable(Type type) {
      if (type is not UserDefinedType userType) {
        return type;
      }

      return new UserDefinedType(new Token(),
        userType.Name.TrimEnd('?'), userType.TypeArgs);
    }

    public static Type ReplaceTypeVariables(Type type, Type with) {
      var result = ReplaceType(type, t => t.Name.Contains('$'), _ => with);
      FillInTypeArgs(result, with);
      return result;
    }

    /// <summary>
    /// Recursively replace all types within <param>type</param> that satisfy
    /// <param>condition</param>
    /// </summary>
    public static Type ReplaceType(Type type, Func<UserDefinedType, Boolean> condition,
      Func<UserDefinedType, Type> replacement) {
      if ((type is not UserDefinedType userType) || (type is ArrowType) || (type.AsArrowType != null)) {
        return TransformType(type, t => ReplaceType(t, condition, replacement));
      }
      var newType = condition(userType) ? replacement(userType) : type;
      newType.TypeArgs = newType.TypeArgs.ConvertAll(t =>
        TransformType(t, t => ReplaceType(t, condition, replacement)));
      if (newType is not UserDefinedType newUserType) {
        return newType;
      }
      return new UserDefinedType(newUserType.Tok, newUserType.Name,
        newUserType.TypeArgs);
    }

    public static Type GetInDafnyFormat(Type type) {
      if ((type is not UserDefinedType userType) || (type is ArrowType) || (type.AsArrowType != null)) {
        return TransformType(type, GetInDafnyFormat);
      }
      // The line below converts "_m" used in boogie to separate modules to ".":
      var newName = ModuleSeparatorRegex.Replace(userType.Name, ".");
      // strip everything after @, this is done for type variables:
      newName = newName.Split("@")[0];
      // The code below converts every "__" to "_":
      newName = UnderscoreRemovalRegex.Replace(newName, "_");
      newName = ConvertTupleName(newName);
      newName = string.Join(".", newName.Split(".")
        .Where(part => part != "_module" && part != "_default" && part != "_System"));
      return new UserDefinedType(new Token(), newName,
        type.TypeArgs.ConvertAll(t => TransformType(t, GetInDafnyFormat)));
    }

    public static string ConvertTupleName(string name) {
      return TupleRegex.Replace(name, "_tuple#");
    }

    /// <summary>
    /// Recursively transform all UserDefinedType objects within a given type
    /// </summary>
    private static Type TransformType(Type type, Func<UserDefinedType, Type> transform) {
      if (type is ArrowType || type.AsArrowType != null) {
        var arrowType = type.AsArrowType;
        return new ArrowType(new Token(),
          arrowType.Args.Select(t => TransformType(t, transform)).ToList(),
          TransformType(arrowType.Result, transform));
      }
      switch (type) {
        case BasicType:
          return type;
        case MapType mapType when mapType.HasTypeArg():
          return new MapType(mapType.Finite,
            TransformType(mapType.Domain, transform),
            TransformType(mapType.Range, transform));
        case SeqType seqType when seqType.HasTypeArg():
          return new SeqType(TransformType(seqType.Arg, transform));
        case SetType setType when setType.HasTypeArg():
          return new SetType(setType.Finite, TransformType(setType.Arg, transform));
        case MultiSetType multiSetType when multiSetType.HasTypeArg():
          return new MultiSetType(TransformType(multiSetType, transform));
        case UserDefinedType userDefinedType:
          return transform(userDefinedType);
        case InferredTypeProxy inferredTypeProxy:
          var tmp = new InferredTypeProxy();
          tmp.T = TransformType(inferredTypeProxy.T, transform);
          return tmp;
      }
      return type;
    }

    /// <summary>
    /// Whenever a collection type does not have an argument, fill it in with the provided arg type
    /// </summary>
    private static void FillInTypeArgs(Type type, Type arg) {
      switch (type) {
        case BasicType:
          return;
        case MapType mapType when !mapType.HasTypeArg():
          mapType.SetTypeArgs(arg, arg);
          return;
        case SeqType seqType when !seqType.HasTypeArg():
          seqType.SetTypeArg(arg);
          return;
        case SetType setType when !setType.HasTypeArg():
          setType.SetTypeArg(arg);
          return;
        case MultiSetType multiSetType when !multiSetType.HasTypeArg():
          multiSetType.SetTypeArg(arg);
          return;
        case UserDefinedType userDefinedType:
          userDefinedType.TypeArgs.ForEach(typ => FillInTypeArgs(typ, arg));
          return;
        case InferredTypeProxy inferredTypeProxy:
          FillInTypeArgs(inferredTypeProxy.T, arg);
          return;
      }
    }
  }
}