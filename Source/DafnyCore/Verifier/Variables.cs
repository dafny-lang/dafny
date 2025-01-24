using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class Variables : OrderedDictionary<string, Variable> {
  public Variables() : base(v => v.Name) {
  }

}