using System;
using System.Collections.Generic;
using System.Text.RegularExpressions;

namespace DafnyServer.CounterexampleGeneration {
  /// <summary>
  /// Represents the type of a DafnyModelVariable.
  /// </summary>
  public class DafnyModelType {

    public readonly string Name;
    public readonly List<DafnyModelType> TypeArgs;

    private static readonly Regex ModuleSeparatorRegex = new("(?<=[^_](__)*)_m");
    private static readonly Regex UnderscoreRemovalRegex = new("__");

    public DafnyModelType(string name, IEnumerable<DafnyModelType> typeArgs) {
      Name = name;
      TypeArgs = new List<DafnyModelType>(typeArgs);
    }

    public DafnyModelType(string name) :
      this(name, new List<DafnyModelType>()) {
    }

    public override string ToString() {
      if (TypeArgs.Count == 0) {
        return Name;
      }
      return Name + "<" + string.Join(",", TypeArgs) + ">";
    }

    /// <summary>
    /// Recursively convert this type's name and the names of its type arguments
    /// to the Dafny format. So, for instance,
    /// Mo__dule___mModule2__.Cla____ss is converted to
    /// Mo_dule_.Module2_.Cla__ss
    /// </summary>
    public DafnyModelType InDafnyFormat() {
      // The line below converts "_m" used in boogie to separate modules to ".":
      var newName = ModuleSeparatorRegex.Replace(Name, ".");
      // strip everything after @, this is done for type variables:
      newName = newName.Split("@")[0];
      // The code below converts every "__" to "_":
      newName = UnderscoreRemovalRegex.Replace(newName, "_");
      return new(newName, TypeArgs.ConvertAll(type => type.InDafnyFormat()));
    }

    public DafnyModelType GetNonNullable() {
      var newName = Name.Trim('?');
      return new DafnyModelType(newName, TypeArgs);
    }

    public DafnyModelType ReplaceTypeVariables(DafnyModelType with) {
      // Assigns the given value to all type variables
      if (Name.Contains("$")) {
        return with;
      }
      return new(Name, TypeArgs.ConvertAll(type =>
        type.ReplaceTypeVariables(with)));
    }

    public override int GetHashCode() {
      int hash = Name.GetHashCode();
      foreach (var typ in TypeArgs) {
        hash = 31 * typ.GetHashCode();
      }
      return hash;
    }

    public override bool Equals(object other) {
      if (other is not DafnyModelType typ) {
        return false;
      }
      return typ.ToString() == ToString();
    }

    /// <summary>
    /// Parse a string into a type.
    /// </summary>
    public static DafnyModelType FromString(string type) {
      type = Regex.Replace(type, " ", "");
      if (!type.Contains("<")) {
        return new DafnyModelType(type);
      }
      List<DafnyModelType> typeArgs = new();
      int id = type.IndexOf("<", StringComparison.Ordinal);
      var name = type[..id];
      id++; // skip the first '<' since it opens the argument list
      int lastId = id;
      int openBrackets = 0;
      while (id < type.Length) {
        switch (type[id]) {
          case '<':
            openBrackets += 1;
            break;
          case '>':
            openBrackets -= 1;
            break;
          case ',':
            if (openBrackets == 0) { // Skip ',' belonging to nested types
              typeArgs.Add(FromString(type.Substring(lastId, id - lastId)));
              lastId = id + 1;
            }
            break;
        }
        id++;
      }
      typeArgs.Add(FromString(type.Substring(lastId, id - lastId - 1)));
      return new DafnyModelType(name, typeArgs);
    }
  }
}