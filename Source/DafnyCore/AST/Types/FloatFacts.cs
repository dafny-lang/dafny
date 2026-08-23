namespace Microsoft.Dafny;

/// <summary>
/// The representation-level facts about a floating-point type, bundled so that no two of them can
/// be derived separately and disagree. Modelled on NativeType (see NewtypeDecl.cs), which does the
/// same for a newtype's native representation.
///
/// fp is the only family of two basic types, so an fp site nearly always needs a width-dependent
/// fact (builtin prefix, precision, typed zero) after its guard. Deriving that fact from the type a
/// second time is what let a normalized guard pair with an unnormalized name and emit fp64_neg
/// returning float24e8. Obtained only via Type.FloatRepresentation, which answers "is this fp?" in
/// the same step, so there is nothing left to disagree with.
///
/// Exactly two instances exist, so reference equality is width equality, and is false when either
/// side is not fp.
/// </summary>
public sealed class FloatFacts {
  public static readonly FloatFacts Fp32 = new FloatFacts(24, 8, "fp32");
  public static readonly FloatFacts Fp64 = new FloatFacts(53, 11, "fp64");

  public int SignificandBits { get; }
  public int ExponentBits { get; }

  /// <summary>Dafny type name, Boogie builtin prefix and message word: one string for all three.</summary>
  public string Name { get; }

  private FloatFacts(int significandBits, int exponentBits, string name) {
    SignificandBits = significandBits;
    ExponentBits = exponentBits;
    Name = name;
  }

  public bool IsFp32 => ReferenceEquals(this, Fp32);

  public Type DafnyType => IsFp32 ? Type.Fp32 : Type.Fp64;

  public void Deconstruct(out int significandBits, out int exponentBits) {
    significandBits = SignificandBits;
    exponentBits = ExponentBits;
  }
}
