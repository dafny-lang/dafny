// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace FactorPathsOptimizationTest {

  public partial class __default {
    public static void TestApply()
    {
      RAST._ITypeParamDecl _1255_T__Decl;
      _1255_T__Decl = RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("T"), Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType));
      RAST._ITypeParamDecl _1256_T__Decl__simp;
      _1256_T__Decl__simp = RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("T"), Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyType"))));
      RAST._IType _1257_T;
      _1257_T = RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("T"));
      RAST._IPath _1258_std__any__Any;
      _1258_std__any__Any = (((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
      RAST._IType _1259_Any;
      _1259_Any = RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
      Dafny.ISequence<Dafny.Rune> _1260___e00 = (FactorPathsOptimization.__default.apply(RAST.Mod.create_Mod(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("onemodule"), Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1255_T__Decl), RAST.Fields.create_NamedFields(Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("a"), (_1258_std__any__Any).AsType())))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1255_T__Decl), (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1257_T)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements())), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1255_T__Decl), (_1258_std__any__Any).AsType(), ((((RAST.__default.crate).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("onemodule"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1257_T)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))))))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.Rune> _1261___e10 = (RAST.Mod.create_Mod(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("onemodule"), Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PRIV(), _1258_std__any__Any)), RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1256_T__Decl__simp), RAST.Fields.create_NamedFields(Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("a"), _1259_Any)))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1256_T__Decl__simp), (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1257_T)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements())), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1256_T__Decl__simp), _1259_Any, (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1257_T)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements())))))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if (!((_1260___e00).Equals(_1261___e10))) {
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Left:\n")));
        Dafny.Helpers.Print((_1260___e00).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Right:\n")));
        Dafny.Helpers.Print((_1261___e10).ToVerbatimString(false));
        throw new Dafny.HaltException("Backends/Rust/Dafny-compiler-rust-path-simplification.dfy(12,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      Dafny.ISequence<Dafny.Rune> _1262___e01 = (FactorPathsOptimization.__default.apply(RAST.Mod.create_Mod(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("onemodule"), Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1255_T__Decl), (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastObject"))).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")))), (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1257_T)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))))))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.Rune> _1263___e11 = (RAST.Mod.create_Mod(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("onemodule"), Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PRIV(), (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastObject")))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1256_T__Decl__simp), (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastObject"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")))), (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1257_T)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements())))))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if (!((_1262___e01).Equals(_1263___e11))) {
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Left:\n")));
        Dafny.Helpers.Print((_1262___e01).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Right:\n")));
        Dafny.Helpers.Print((_1263___e11).ToVerbatimString(false));
        throw new Dafny.HaltException("Backends/Rust/Dafny-compiler-rust-path-simplification.dfy(29,4): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
    }
  }
} // end of namespace FactorPathsOptimizationTest