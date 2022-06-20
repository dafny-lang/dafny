using System;
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
      return new UserDefinedType(new Token(), newName,
        type.TypeArgs.ConvertAll(t => TransformType(t, GetInDafnyFormat)));
    }

    public static Type GetNonNullable(Type type) {
      if (type is not UserDefinedType userType) {
        return type;
      }
      return new UserDefinedType(new Token(), userType.Name.TrimEnd('?'),
        userType.TypeArgs);
    }

    public static Type ReplaceTypeVariables(Type type, Type with) {
      if ((type is not UserDefinedType userType) || (type is ArrowType)) {
        return TransformType(type, t => ReplaceTypeVariables(t, with));
      }
      if (userType.Name.Contains('$')) {
        return with;
      }
      return new UserDefinedType(new Token(), userType.Name,
        type.TypeArgs.ConvertAll(t => 
          TransformType(t, t => ReplaceTypeVariables(t, with))));
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