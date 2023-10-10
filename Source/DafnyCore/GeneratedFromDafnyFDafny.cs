// Dafny program Dafny-compiler-fdafny.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 4.3.0.0
// Command-line arguments: translate cs --output GeneratedFromDafnyFDafny.cs Compilers/FDafny/Dafny-compiler-fdafny.dfy
// Dafny-compiler-fdafny.dfy


module {:extern ""DCOMPD""} DCOMP {

  import opened DAST
  class COMP {
    static method Compile(p: seq<Module>) returns (s: string)
      decreases p
    {
      print p;
      s := ""Hello"";
    }

    static method EmitCallToMain(fullName: seq<string>) returns (s: string)
      decreases fullName
    {
      s := ""Emit Main"";
    }
  }
}

module {:extern ""DAST""} DAST {
  datatype Module = Module(name: string, isExtern: bool, body: seq<ModuleItem>)

  datatype ModuleItem = Module(Module) | Class(Class) | Trait(Trait) | Newtype(Newtype) | Datatype(Datatype)

  datatype Type = Path(seq<Ident>, typeArgs: seq<Type>, resolved: ResolvedType) | Nullable(Type) | Tuple(seq<Type>) | Array(element: Type, dims: nat) | Seq(element: Type) | Set(element: Type) | Multiset(element: Type) | Map(key: Type, value: Type) | Arrow(args: seq<Type>, result: Type) | Primitive(Primitive) | Passthrough(string) | TypeArg(Ident)

  datatype Primitive = Int | Real | String | Bool | Char

  datatype ResolvedType = Datatype(path: seq<Ident>) | Trait(path: seq<Ident>) | Newtype(Type)

  datatype Ident = Ident(id: string)

  datatype Class = Class(name: string, enclosingModule: Ident, typeParams: seq<Type>, superClasses: seq<Type>, fields: seq<Field>, body: seq<ClassItem>)

  datatype Trait = Trait(name: string, typeParams: seq<Type>, body: seq<ClassItem>)

  datatype Datatype = Datatype(name: string, enclosingModule: Ident, typeParams: seq<Type>, ctors: seq<DatatypeCtor>, body: seq<ClassItem>, isCo: bool)

  datatype DatatypeCtor = DatatypeCtor(name: string, args: seq<Formal>, hasAnyArgs: bool)

  datatype Newtype = Newtype(name: string, typeParams: seq<Type>, base: Type, witnessStmts: seq<Statement>, witnessExpr: Optional<Expression>)

  datatype ClassItem = Method(Method)

  datatype Field = Field(formal: Formal, defaultValue: Optional<Expression>)

  datatype Formal = Formal(name: string, typ: Type)

  datatype Method = Method(isStatic: bool, hasBody: bool, overridingPath: Optional<seq<Ident>>, name: string, typeParams: seq<Type>, params: seq<Formal>, body: seq<Statement>, outTypes: seq<Type>, outVars: Optional<seq<Ident>>)

  datatype Optional<T> = Some(T) | None

  datatype Statement = DeclareVar(name: string, typ: Type, maybeValue: Optional<Expression>) | Assign(lhs: AssignLhs, value: Expression) | If(cond: Expression, thn: seq<Statement>, els: seq<Statement>) | Labeled(lbl: string, body: seq<Statement>) | While(cond: Expression, body: seq<Statement>) | Foreach(boundName: string, boundType: Type, over: Expression, body: seq<Statement>) | Call(on: Expression, name: string, typeArgs: seq<Type>, args: seq<Expression>, outs: Optional<seq<Ident>>) | Return(expr: Expression) | EarlyReturn | Break(toLabel: Optional<string>) | TailRecursive(body: seq<Statement>) | JumpTailCallStart | Halt | Print(Expression)

  datatype AssignLhs = Ident(Ident) | Select(expr: Expression, field: string) | Index(expr: Expression, indices: seq<Expression>)

  datatype CollKind = Seq | Array | Map

  datatype BinOp = Eq(referential: bool, nullable: bool) | Neq(referential: bool, nullable: bool) | Div | EuclidianDiv | Mod | EuclidianMod | Implies | In | NotIn | SetDifference | Concat | Passthrough(string)

  datatype Expression = Literal(Literal) | Ident(string) | Companion(seq<Ident>) | Tuple(seq<Expression>) | New(path: seq<Ident>, typeArgs: seq<Type>, args: seq<Expression>) | NewArray(dims: seq<Expression>, typ: Type) | DatatypeValue(path: seq<Ident>, typeArgs: seq<Type>, variant: string, isCo: bool, contents: seq<(string, Expression)>) | Convert(value: Expression, from: Type, typ: Type) | SeqConstruct(length: Expression, elem: Expression) | SeqValue(elements: seq<Expression>, typ: Type) | SetValue(elements: seq<Expression>) | MapValue(mapElems: seq<(Expression, Expression)>) | This | Ite(cond: Expression, thn: Expression, els: Expression) | UnOp(unOp: UnaryOp, expr: Expression) | BinOp(op: BinOp, left: Expression, right: Expression) | ArrayLen(expr: Expression, dim: nat) | Select(expr: Expression, field: string, isConstant: bool, onDatatype: bool) | SelectFn(expr: Expression, field: string, onDatatype: bool, isStatic: bool, arity: nat) | Index(expr: Expression, collKind: CollKind, indices: seq<Expression>) | IndexRange(expr: Expression, isArray: bool, low: Optional<Expression>, high: Optional<Expression>) | TupleSelect(expr: Expression, index: nat) | Call(on: Expression, name: Ident, typeArgs: seq<Type>, args: seq<Expression>) | Lambda(params: seq<Formal>, retType: Type, body: seq<Statement>) | BetaRedex(values: seq<(Formal, Expression)>, retType: Type, expr: Expression) | IIFE(name: Ident, typ: Type, value: Expression, iifeBody: Expression) | Apply(expr: Expression, args: seq<Expression>) | TypeTest(on: Expression, dType: seq<Ident>, variant: string) | InitializationValue(typ: Type) | BoolBoundedPool | SetBoundedPool(of: Expression) | SeqBoundedPool(of: Expression, includeDuplicates: bool) | IntRange(lo: Expression, hi: Expression)

  datatype UnaryOp = Not | BitwiseNot | Cardinality

  datatype Literal = BoolLiteral(bool) | IntLiteral(string, Type) | DecLiteral(string, string, Type) | StringLiteral(string) | CharLiteral(char) | Null(Type)
}
")]

namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace _System

namespace DCOMPD {


  public partial class COMP {
    public COMP() {
    }
    public static Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.Helpers.Print((p));
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hello");
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Emit Main");
      return s;
    }
  }
} // end of namespace DCOMPD
namespace _module {

} // end of namespace _module
