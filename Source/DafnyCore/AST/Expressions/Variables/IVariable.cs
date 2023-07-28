using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

[ContractClass(typeof(IVariableContracts))]
public interface IVariable : IDeclarationOrUsage {
  string Name {
    get;
  }
  string DafnyName {  // what the user thinks he wrote
    get;
  }
  string DisplayName { // what the user thinks he wrote but with special treatment for wilcards
    get;
  }
  string UniqueName {
    get;
  }
  bool HasBeenAssignedUniqueName {  // unique names are not assigned until the Translator; if you don't already know if that stage has run, this boolean method will tell you
    get;
  }
  static FreshIdGenerator CompileNameIdGenerator = new FreshIdGenerator();
  string AssignUniqueName(FreshIdGenerator generator);
  string SanitizedName {
    get;
  }
  string CompileName {
    get;
  }

  PreType PreType {
    get;
    set;
  }
  Type Type {
    get;
  }
  Type OptionalType {
    get;
  }
  bool IsMutable {
    get;
  }
  bool IsGhost {
    get;
  }
  void MakeGhost();
}