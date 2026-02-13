using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public class TupleTypeDecl : IndDatatypeDecl {
  public List<bool> ArgumentGhostness;

  public int Dims => ArgumentGhostness.Count;

  public int NonGhostDims => ArgumentGhostness.Count(x => !x);

  [CanBeNull] public TupleTypeDecl NonGhostTupleTypeDecl { get; }

  /// <summary>
  /// Construct a resolved built-in tuple type with "dim" arguments.  "systemModule" is expected to be the _System module.
  /// </summary>
  public TupleTypeDecl(List<bool> argumentGhostness, ModuleDefinition systemEnclosingModule, [CanBeNull] TupleTypeDecl nonGhostTupleTypeDecl, Attributes attributes)
    : this(systemEnclosingModule, CreateCovariantTypeParameters(argumentGhostness.Count), argumentGhostness, attributes) {
    Contract.Requires(0 <= argumentGhostness.Count);
    Contract.Requires(systemEnclosingModule != null);

    // Resolve the type parameters here
    Contract.Assert(TypeArgs.Count == Dims);
    for (var i = 0; i < Dims; i++) {
      var tp = TypeArgs[i];
      tp.Parent = this;
      tp.PositionalIndex = i;
    }

    NonGhostTupleTypeDecl = nonGhostTupleTypeDecl;
  }

  private TupleTypeDecl(ModuleDefinition systemEnclosingModule, List<TypeParameter> typeArgs, List<bool> argumentGhostness, Attributes attributes)
    : base(SourceOrigin.NoToken, new Name(SystemModuleManager.TupleTypeName(argumentGhostness)), systemEnclosingModule, typeArgs,
      CreateConstructors(typeArgs, argumentGhostness),
      [], [], attributes, false) {
    Contract.Requires(systemEnclosingModule != null);
    Contract.Requires(typeArgs != null);
    Contract.Assert(Ctors.Count == 1);
    ArgumentGhostness = argumentGhostness;
    foreach (var ctor in Ctors) {
      ctor.EnclosingDatatype = this;  // resolve here
      GroundingCtor = ctor;
      TypeParametersUsedInConstructionByGroundingCtor = new bool[typeArgs.Count];
      for (int i = 0; i < typeArgs.Count; i++) {
        TypeParametersUsedInConstructionByGroundingCtor[i] = !argumentGhostness[i];
      }
    }
    this.EqualitySupport = argumentGhostness.Contains(true) ? ES.Never : ES.ConsultTypeArguments;

    // Resolve parent type information - not currently possible for tuples to have any parent traits
    ParentTypeInformation = new InheritanceInformationClass();
  }
  private static List<TypeParameter> CreateCovariantTypeParameters(int dims) {
    Contract.Requires(0 <= dims);
    var ts = new List<TypeParameter>();
    for (int i = 0; i < dims; i++) {
      var tp = new TypeParameter(SourceOrigin.NoToken, new Name("T" + i), TPVarianceSyntax.Covariant_Strict);
      tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype = true;
      ts.Add(tp);
    }
    return ts;
  }

  /// <summary>
  /// Creates the one and only constructor of the tuple type.
  /// </summary>
  private static List<DatatypeCtor> CreateConstructors(List<TypeParameter> typeArgs, List<bool> argumentGhostness) {
    Contract.Requires(typeArgs != null);
    var formals = new List<Formal>();
    var nonGhostArgs = 0;
    for (int i = 0; i < typeArgs.Count; i++) {
      string compileName;
      if (argumentGhostness[i]) {
        // This name is irrelevant, since it won't be used in compilation. Give it a strange name
        // that would alert us of any bug that nevertheless tries to access this name.
        compileName = "this * ghost * arg * should * never * be * compiled * " + i.ToString();
      } else {
        compileName = nonGhostArgs.ToString();
        nonGhostArgs++;
      }
      var tp = typeArgs[i];
      var f = new Formal(Token.NoToken, i.ToString(), new UserDefinedType(Token.NoToken, tp), true, argumentGhostness[i], null, nameForCompilation: compileName);
      formals.Add(f);
    }
    string ctorName = SystemModuleManager.TupleTypeCtorName(typeArgs.Count);
    var ctor = new DatatypeCtor(SourceOrigin.NoToken, new Name(ctorName), false, formals, null);
    return [ctor];
  }

  public override string SanitizedName =>
    sanitizedName ??= $"Tuple{SystemModuleManager.ArgumentGhostnessToString(ArgumentGhostness)}";

  public override string GetCompileName(DafnyOptions options) => NonGhostTupleTypeDecl?.GetCompileName(options) ?? $"Tuple{NonGhostDims}";
}