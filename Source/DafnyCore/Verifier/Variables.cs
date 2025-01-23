using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class Variables() : OrderedDictionary<string, Variable>(v => v.Name);