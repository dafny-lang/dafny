// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace FactorPathsOptimizationTest {

  public partial class __default {
    public static void ShouldBeEqual(RAST._IMod a, RAST._IMod b)
    {
      Dafny.ISequence<Dafny.Rune> _0_sA;
      _0_sA = (a)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.Rune> _1_sB;
      _1_sB = (b)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      if (!(_0_sA).Equals(_1_sB)) {
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Got:\n"), _0_sA), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"))).ToVerbatimString(false));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Expected:\n"), _1_sB), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"))).ToVerbatimString(false));
        if (!((_0_sA).Equals(_1_sB))) {
          throw new Dafny.HaltException("Backends/Rust/Dafny-compiler-rust-path-simplification.dfy(12,6): " + Dafny.Sequence<Dafny.Rune>.UnicodeFromString("expectation violation").ToVerbatimString(false));}
      }
    }
    public static void TestApply()
    {
      RAST._ITypeParamDecl _0_T__Decl;
      _0_T__Decl = RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("T"), Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType));
      RAST._ITypeParamDecl _1_T__Decl__simp;
      _1_T__Decl__simp = RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("T"), Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyType"))));
      RAST._IType _2_T;
      _2_T = RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("T"));
      RAST._IPath _3_std__any__Any;
      _3_std__any__Any = (((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
      RAST._IType _4_Any;
      _4_Any = RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
      FactorPathsOptimizationTest.__default.ShouldBeEqual(Dafny.Helpers.Id<Func<RAST._IMod, RAST._IMod>>(FactorPathsOptimization.__default.apply(RAST.__default.crate))(RAST.Mod.create_Mod(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("onemodule"), Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_0_T__Decl), RAST.Fields.create_NamedFields(Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("a"), (_3_std__any__Any).AsType())))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_0_T__Decl), (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(_2_T)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements())), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_0_T__Decl), (_3_std__any__Any).AsType(), ((((RAST.__default.crate).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("onemodule"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_2_T)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))))), RAST.Mod.create_Mod(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("onemodule"), Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyType")))), RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), _3_std__any__Any)), RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1_T__Decl__simp), RAST.Fields.create_NamedFields(Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("a"), _4_Any)))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1_T__Decl__simp), (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(_2_T)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements())), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1_T__Decl__simp), _4_Any, (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(_2_T)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements())))));
      FactorPathsOptimizationTest.__default.ShouldBeEqual(Dafny.Helpers.Id<Func<RAST._IMod, RAST._IMod>>(FactorPathsOptimization.__default.apply(RAST.__default.crate))(RAST.Mod.create_Mod(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("onemodule"), Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_0_T__Decl), (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastObject"))).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")))), (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(_2_T)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))))), RAST.Mod.create_Mod(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("onemodule"), Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyType")))), RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastObject")))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1_T__Decl__simp), (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastObject"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")))), (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))).Apply(Dafny.Sequence<RAST._IType>.FromElements(_2_T)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements())))));
    }
  }
} // end of namespace FactorPathsOptimizationTest