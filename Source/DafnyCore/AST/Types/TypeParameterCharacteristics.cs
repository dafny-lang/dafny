namespace Microsoft.Dafny;

public struct TypeParameterCharacteristics {
  public SourceOrigin SourceOrigin = null;
  public TypeParameter.EqualitySupportValue EqualitySupport;  // the resolver may change this value from Unspecified to InferredRequired (for some signatures that may immediately imply that equality support is required)
  public Type.AutoInitInfo AutoInit;
  public bool HasCompiledValue => AutoInit == Type.AutoInitInfo.CompilableValue;
  public bool IsNonempty => AutoInit != Type.AutoInitInfo.MaybeEmpty;
  public bool ContainsNoReferenceTypes;

  public static TypeParameterCharacteristics Default() {
    return new TypeParameterCharacteristics {
      EqualitySupport = TypeParameter.EqualitySupportValue.Unspecified,
      AutoInit = Type.AutoInitInfo.MaybeEmpty,
      ContainsNoReferenceTypes = false,
    };
  }

  public TypeParameterCharacteristics(TypeParameter.EqualitySupportValue equalitySupport,
    Type.AutoInitInfo autoInit, bool containsNoReferenceTypes) {
    EqualitySupport = equalitySupport;
    AutoInit = autoInit;
    ContainsNoReferenceTypes = containsNoReferenceTypes;
  }
  public override string ToString() {
    string result = "";
    if (EqualitySupport == TypeParameter.EqualitySupportValue.Required) {
      result += ",==";
    }
    if (HasCompiledValue) {
      result += ",0";
    }
    if (AutoInit == Type.AutoInitInfo.Nonempty) {
      result += ",00";
    }
    if (ContainsNoReferenceTypes) {
      result += ",!new";
    }
    if (result.Length != 0) {
      result = "(" + result.Substring(1) + ")";
    }
    return result;
  }
}