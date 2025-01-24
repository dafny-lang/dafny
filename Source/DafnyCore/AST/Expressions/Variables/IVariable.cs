using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

[ContractClass(typeof(IVariableContracts))]
public interface IVariable : ISymbol {
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
  string AssignUniqueName(VerificationIdGenerator generator);

  /// <summary>
  /// A name suitable for compilation, but without the unique identifier.
  /// Useful to generate readable identifiers in the generated source code.
  /// </summary>
  string CompileNameShadowable { get; }
  string GetOrCreateCompileName(CodeGenIdGenerator generator);

  PreType PreType {
    get;
    set;
  }
  Type Type {
    get;
  }

  /// <summary>
  /// For a description of the difference between .Type and .UnnormalizedType, see Expression.UnnormalizedType.
  /// </summary>
  Type UnnormalizedType {
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