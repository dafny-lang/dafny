// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Dafny;
using MapType = Microsoft.Dafny.MapType;
using Token = Microsoft.Dafny.Token;
using Type = Microsoft.Dafny.Type;

namespace DafnyServer.CounterexampleGeneration {

  /// <summary>
  /// This class stores various transformations that could be useful to perform
  /// on types extracted from DafnyModel (e.g. to convert Boogie type names
  /// back to the original Dafny names)
  /// </summary>
  public static class DafnyModelTypeUtils {

    private static readonly Regex ModuleSeparatorRegex = new("(?<=[^_](__)*)_m");
    private static readonly Regex UnderscoreRemovalRegex = new("__");

    // Used to distinguish between class types and algebraic datatypes
    public class DatatypeType : UserDefinedType {
      public DatatypeType(UserDefinedType type)
        : base(new Token(), type.Name, type.TypeArgs) { }
    }

    public static Type GetNonNullable(Type type) {
      if (type is not UserDefinedType userType) {
        return type;
      }

      var newType = new UserDefinedType(new Token(),
        userType.Name.TrimEnd('?'), userType.TypeArgs);
      if (type is DatatypeType) {
        return new DatatypeType(newType);
      }
      return newType;
    }

    public static Type ReplaceTypeVariables(Type type, Type with) {
      return ReplaceType(type, t => t.Name.Contains('$'), _ => with);
    }

    /// <summary>
    /// Recursively replace all types within <param>type</param> that satisfy
    /// <param>condition</param>
    /// </summary>
    public static Type ReplaceType(Type type, Func<UserDefinedType, Boolean> condition,
      Func<UserDefinedType, Type> replacement) {
      if ((type is not UserDefinedType userType) || (type is ArrowType)) {
        return TransformType(type, t => ReplaceType(t, condition, replacement));
      }
      var newType = condition(userType) ? replacement(userType) : type;
      newType.TypeArgs = newType.TypeArgs.ConvertAll(t =>
        TransformType(t, t => ReplaceType(t, condition, replacement)));
      if (newType is not UserDefinedType newUserType) {
        return newType;
      }
      newUserType = new UserDefinedType(newUserType.tok, newUserType.Name,
        newUserType.TypeArgs);
      if (newType is DatatypeType) {
        return new DatatypeType(newUserType);
      }
      return newUserType;
    }

    public static Type GetInDafnyFormat(Type type) {
      if ((type is not UserDefinedType userType) || (type is ArrowType)) {
        return TransformType(type, GetInDafnyFormat);
      }
      // The line below converts "_m" used in boogie to separate modules to ".":
      var newName = ModuleSeparatorRegex.Replace(userType.Name, ".");
      // strip everything after @, this is done for type variables:
      newName = newName.Split("@")[0];
      // The code below converts every "__" to "_":
      newName = UnderscoreRemovalRegex.Replace(newName, "_");
      var newType = new UserDefinedType(new Token(), newName,
        type.TypeArgs.ConvertAll(t => TransformType(t, GetInDafnyFormat)));
      if (type is DatatypeType) {
        return new DatatypeType(newType);
      }
      return newType;
    }

    /// <summary>
    /// Recursively transform all UserDefinedType objects within a given type
    /// </summary>
    public static Type TransformType(Type type, Func<UserDefinedType, Type> transform) {
      switch (type) {
        case Microsoft.Dafny.BasicType:
          return type;
        case MapType mapType:
          return new MapType(mapType.Finite,
            TransformType(mapType.Domain, transform),
            TransformType(mapType.Range, transform));
        case SeqType seqType:
          return new SeqType(TransformType(seqType.Arg, transform));
        case SetType setType:
          return new SetType(setType.Finite, TransformType(setType.Arg, transform));
        case MultiSetType multiSetType:
          return new MultiSetType(TransformType(multiSetType, transform));
        case ArrowType arrowType:
          return new ArrowType(new Token(),
            arrowType.Args.Select(t => TransformType(t, transform)).ToList(),
            TransformType(arrowType.Result, transform));
        case UserDefinedType userDefinedType:
          return transform(userDefinedType);
        case InferredTypeProxy inferredTypeProxy:
          var tmp = new InferredTypeProxy();
          tmp.T = TransformType(inferredTypeProxy.T, transform);
          return tmp;
      }
      return type;
    }
  }
}