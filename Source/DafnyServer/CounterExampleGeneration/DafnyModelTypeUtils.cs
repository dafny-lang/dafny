using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie;
using Microsoft.Dafny;
using MapType = Microsoft.Dafny.MapType;
using Type = Microsoft.Dafny.Type;

namespace DafnyServer.CounterexampleGeneration {

  public class DafnyModelTypeUtils {
    
    private static readonly Regex ModuleSeparatorRegex = new("(?<=[^_](__)*)_m");
    private static readonly Regex UnderscoreRemovalRegex = new("__");

    public class DatatypeType : UserDefinedType {
      public DatatypeType(UserDefinedType type) : base(new Token(), type.Name, type.TypeArgs) { }
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
    
    public static Type UseFullName(Type type) {
      return ReplaceType(type, _ => true, type => 
        new UserDefinedType(new Token(), type?.ResolvedClass.FullName, type.TypeArgs));
    }
    
    public static Type ReplaceType(Type type, Func<UserDefinedType, Boolean> condition, 
      Func<UserDefinedType, Type> replacement) {
      if ((type is not UserDefinedType userType) || (type is ArrowType)) {
        return TransformType(type, t => ReplaceType(t, condition, replacement));
      }
      var newType = condition(userType) ? replacement(userType) : type;
      // TODO: What if ReplaceTypeVariable is used to replace type with something that has type variables?
      newType.TypeArgs = type.TypeArgs.ConvertAll(t => 
          TransformType(t, t => ReplaceType(t, condition, replacement)));
      return newType;
    }

    private static Type TransformType(Type type, Func<Type, Type> transform) {
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
        case UserDefinedType:
          return transform(type);
      }
      return type;
    }
  }
}