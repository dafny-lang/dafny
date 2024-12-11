using System;
using System.Diagnostics.Contracts;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

[ContractClassFor(typeof(IVariable))]
public abstract class IVariableContracts : TokenNode, IVariable {
  public string Name {
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
    }
  }
  public string DafnyName {
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
    }
  }
  public string DisplayName {
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
    }
  }
  public string UniqueName {
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
    }
  }
  public bool HasBeenAssignedUniqueName {
    get {
      throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
    }
  }
  public string SanitizedName(CodeGenIdGenerator generator) {
    Contract.Ensures(Contract.Result<string>() != null);
    throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
  }

  public string CompileNameShadowable {
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
    }
  }
  public string GetOrCreateCompileName(CodeGenIdGenerator generator) {
    Contract.Ensures(Contract.Result<string>() != null);
    throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
  }
  public Type Type {
    get {
      Contract.Ensures(Contract.Result<Type>() != null);
      throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
    }
  }
  public Type UnnormalizedType {
    get {
      Contract.Ensures(Contract.Result<Type>() != null);
      throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
    }
  }
  public Type OptionalType {
    get {
      Contract.Ensures(Contract.Result<Type>() != null);
      throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
    }
  }

  public PreType PreType { get; set; }

  public bool IsMutable {
    get {
      throw new NotImplementedException();
    }
  }
  public bool IsGhost {
    get {
      throw new NotImplementedException();
    }
  }
  public void MakeGhost() {
    throw new NotImplementedException();
  }
  public string AssignUniqueName(VerificationIdGenerator generator) {
    Contract.Ensures(Contract.Result<string>() != null);
    throw new NotImplementedException();
  }

  public abstract IOrigin NavigationToken { get; }
  public SymbolKind? Kind => throw new NotImplementedException();
  public string GetDescription(DafnyOptions options) {
    throw new NotImplementedException();
  }
}