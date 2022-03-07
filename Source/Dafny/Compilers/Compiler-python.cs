using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Numerics;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class PythonCompiler : Compiler {
    public PythonCompiler(ErrorReporter reporter) : base(reporter) {
    }

    public override string TargetLanguage => "Python";
    const string DafnySetClass = "_dafny.Set";
    const string DafnyMultiSetClass = "_dafny.MultiSet";
    const string DafnySeqClass = "_dafny.Seq";
    const string DafnyMapClass = "_dafny.Map";
    protected override string StmtTerminator { get => ""; }
    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
      wr.WriteLine("# Dafny program {0} compiled into Python", program.Name);
      ReadRuntimeSystem("DafnyRuntime.py", wr);
      wr.WriteLine();
    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      Coverage.EmitSetup(wr);
      wr.WriteLine("_module._default.Main()", mainMethod.EnclosingClass, mainMethod);
    }

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw) {
      var wr = (cw as PythonCompiler.ClassWriter).MethodWriter;
      return wr.WriteLine("def Main():");
    }

    protected override ConcreteSyntaxTree CreateModule(string moduleName, bool isDefault, bool isExtern,
        string libraryName, ConcreteSyntaxTree wr) {
      return wr.NewBlock($"class {IdProtect(moduleName)}:", open: BlockStyle.Nothing, close: BlockStyle.Newline);
    }

    protected override string GetHelperModuleName() {
      throw new NotImplementedException();
    }

    private static string MangleName(string name) {
      return name.StartsWith("__") ? name[1..] : name;
    }

    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string fullPrintName,
        List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {
      wr.Write("class {0}:", MangleName(name));
      var methodWriter = wr.NewBlock(open: BlockStyle.Newline, close: BlockStyle.Nothing);
      if (cls is ClassDecl d) {
        if (d.Members.FindAll(m => !m.IsGhost).Count == 0) {
          methodWriter.WriteLine("pass");
        }
      }
      return new ClassWriter(this, methodWriter, null);
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters,
      List<Type> superClasses, IToken tok,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {

      if (dt is TupleTypeDecl) {
        return null;
      } else {
        throw new NotImplementedException();
      }

    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      var cw = (ClassWriter)CreateClass(IdProtect(sst.EnclosingModuleDefinition.CompileName), IdName(sst), sst, wr);
      var w = cw.MethodWriter;
      var udt = UserDefinedType.FromTopLevelDecl(sst.tok, sst);
      string d;
      d = TypeInitializationValue(udt, wr, sst.tok, false, false);

      w.NewBlock("def Default():", "", BlockStyle.Newline, BlockStyle.Nothing).WriteLine($"return {d}", "");
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix,
      out bool needsCastAfterArithmetic) {
      throw new NotImplementedException();
    }

    protected class ClassWriter : IClassWriter {
      public readonly PythonCompiler Compiler;
      public readonly ConcreteSyntaxTree MethodWriter;
      public readonly ConcreteSyntaxTree FieldWriter;

      public ClassWriter(PythonCompiler compiler, ConcreteSyntaxTree methodWriter, ConcreteSyntaxTree fieldWriter) {
        Contract.Requires(compiler != null);
        Contract.Requires(methodWriter != null);
        Contract.Requires(fieldWriter != null);
        this.Compiler = compiler;
        this.MethodWriter = methodWriter;
        this.FieldWriter = fieldWriter;
      }

      public ConcreteSyntaxTree CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
        bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateMethod(m, typeArgs, createBody, MethodWriter, forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
        List<Formal> formals, Type resultType, IToken tok, bool isStatic,
        bool createBody, MemberDecl member, bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member,
          MethodWriter, forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IToken tok,
        bool isStatic,
        bool isConst, bool createBody, MemberDecl member, bool forBodyInheritance) {
        return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, MethodWriter);
      }

      public ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IToken tok, bool isStatic,
        bool createBody,
        MemberDecl member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        return Compiler.CreateGetterSetter(name, resultType, tok, isStatic, createBody, out setterWriter, MethodWriter);
      }

      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type,
          IToken tok, string rhs, Field field) {
        Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, FieldWriter);
      }

      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        throw new NotSupportedException();
      }

      public ConcreteSyntaxTree ErrorWriter() => MethodWriter;

      public void Finish() {

      }
    }

    private void DeclareField(string name, bool isStatic, bool isConst, Type type, IToken tok, string rhs,
      ConcreteSyntaxTree fieldWriter) {
      throw new NotImplementedException();
    }

    private ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IToken tok, bool isStatic,
      bool createBody, out ConcreteSyntaxTree setterWriter, ConcreteSyntaxTree methodWriter) {
      throw new NotImplementedException();
    }

    private ConcreteSyntaxTree CreateGetter(string name, Type resultType, IToken tok, bool isStatic, bool createBody,
        ConcreteSyntaxTree methodWriter) {
      return methodWriter.NewBlock($"def {name}():", open: BlockStyle.Newline, close: BlockStyle.Nothing);
    }

    private ConcreteSyntaxTree CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
      ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      wr.Write($"def {IdName(m)}(");

      WriteFormals("", m.Ins, wr);
      var w = wr.NewBlock("):", open: BlockStyle.Newline, close: BlockStyle.Newline);
      return w;

    }

    private ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
        List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member,
        ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      wr.Write($"def {name}(");
      WriteFormals("", formals, wr);
      return wr.NewBlock("):", open: BlockStyle.Newline, close: BlockStyle.Newline);
    }


    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IToken tok) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }
    protected override string TypeName(Type type, ConcreteSyntaxTree wr, Bpl.IToken tok, MemberDecl/*?*/ member = null) {
      return TypeName(type, wr, tok, boxed: false, member);
    }
    private string TypeName(Type type, ConcreteSyntaxTree wr, Bpl.IToken tok, bool boxed, MemberDecl /*?*/ member = null) {
      return TypeName(type, wr, tok, boxed, false, member);
    }
    private string TypeName(Type type, ConcreteSyntaxTree wr, Bpl.IToken tok, bool boxed, bool erased, MemberDecl/*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

      var xType = type.NormalizeExpand();

      switch (xType) {
        case BoolType: {
            return "bool";
          }
        case CharType: {
            return "char";
          }
        case IntType or BigOrdinalType: {
            return "int";
          }
        case UserDefinedType udt: {
            var s = FullTypeName(udt, member);
            return TypeName_UDT(s, udt, wr, udt.tok);
          }
      }

      Contract.Assert(false);
      throw new NotImplementedException();
    }

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IToken tok,
      bool usePlaceboValue,
      bool constructTypeParameterDefaultsFromTypeDescriptors) {
      var xType = type.NormalizeExpandKeepConstraints();

      switch (xType) {
        case BoolType: {
            return "False";
          }
        case CharType: {
            return CharType.DefaultValueAsString;
          }
        case IntType or BigOrdinalType: {
            return "int(0)";
          }
        case UserDefinedType udt: {
            var cl = udt.ResolvedClass;
            Contract.Assert(cl != null);
            if (cl is SubsetTypeDecl td) {
              return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
            }
            break;
          }
      }

      Contract.Assert(false);
      throw new cce.UnreachableException();  // unexpected type
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance,
      List<Type> typeArgs, ConcreteSyntaxTree wr, IToken tok) {
      string s = IdProtect(fullCompileName);
      return s;
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl member) {
      type = UserDefinedType.UpcastToMemberEnclosingType(type, member);
      return TypeName(type, wr, tok, member);
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IToken tok, bool isInParam,
      ConcreteSyntaxTree wr) {
      if (isInParam) {
        wr.Write("{0}{1}", prefix, name);
        return true;
      } else {
        return false;
      }
    }

    protected override void DeclareLocalVar(string name, Type type, IToken tok, bool leaveRoomForRhs, string rhs,
        ConcreteSyntaxTree wr) {
      wr.Write(name);
      if (type != null) { wr.Write($": {TypeName(type, wr, tok)}"); }
      if (rhs != null) { wr.Write($" = {rhs}"); }
      wr.WriteLine();
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IToken tok, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;
    protected override bool SupportsMultipleReturns => true;

    protected override void DeclareLocalOutVar(string name, Type type, IToken tok, string rhs, bool useReturnStyleOuts,
        ConcreteSyntaxTree wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      // emit nothing
    }

    protected override string GenerateLhsDecl(string target, Type type, ConcreteSyntaxTree wr, IToken tok) {
      return $"{target}: {TypeName(type, wr, tok)}";
    }

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      wr.Write("_dafny.print(");
      TrExpr(arg, wr, false);
      wr.WriteLine(")");
    }

    protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr) {
      outParams = outParams.Where(f => !f.IsGhost).ToList();
      wr.Write("return");
      if (outParams.Count > 0) {
        wr.Write($" {outParams.Comma(IdName)}");
      }
      wr.WriteLine();
    }

    protected override ConcreteSyntaxTree CreateLabeledCode(string label, bool createContinueLabel, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitBreak(string label, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitYield(ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitAbsurd(string message, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitHalt(IToken tok, Expression messageExpr, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitIf(out ConcreteSyntaxTree guardWriter, bool hasElse, ConcreteSyntaxTree wr) {
      wr.Write("if ");
      guardWriter = wr.Fork();
      if (hasElse) {
        var thn = wr.NewBlock(":", "el", BlockStyle.Newline, BlockStyle.Nothing);
        return thn;
      } else {
        var thn = wr.NewBlock(":", open: BlockStyle.Newline, close: BlockStyle.Nothing);
        return thn;
      }
    }

    protected override ConcreteSyntaxTree EmitBlock(ConcreteSyntaxTree wr) {
      return wr.NewBlock("if True:", open: BlockStyle.Newline, close: BlockStyle.Nothing);
    }

    protected override ConcreteSyntaxTree EmitForStmt(IToken tok, IVariable loopIndex, bool goingUp, string endVarName,
      List<Statement> body, LList<Label> labels, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, string bound, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override string GetQuantifierName(string bvType) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType,
      string boundVarName,
      Type boundVarType, bool introduceBoundVar, IToken tok, out ConcreteSyntaxTree collectionWriter,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs,
      out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitNew(Type type, IToken tok, CallStmt initCall, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitNewArray(Type elmtType, IToken tok, List<Expression> dimensions, bool mustInitialize,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      if (e.Value is bool value) {
        wr.Write("{0}", value);

      } else if (e is StringLiteralExpr) {
        var str = (StringLiteralExpr)e;
        TrStringLiteral(str, wr);
      } else if (e.Value is BigInteger) {
        var i = (BigInteger)e.Value;
        wr.Write($"{i}");
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {

      if (!isVerbatim) {
        wr.Write("\"{0}\"", str);
      } else {
        var n = str.Length;
        wr.Write("\"");
        for (var i = 0; i < n; i++) {
          if (str[i] == '\"' && i + 1 < n && str[i + 1] == '\"') {
            wr.Write("\\\"");
            i++;
          } else if (str[i] == '\\') {
            wr.Write("\\\\");
          } else if (str[i] == '\n') {
            wr.Write("\\n");
          } else if (str[i] == '\r') {
            wr.Write("\\r");
          } else {
            wr.Write(str[i]);
          }
        }
        wr.Write("\"");
      }

    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
      bool inLetExprBody,
      FCE_Arg_Translator tr) {
      throw new NotImplementedException();
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitAddTupleToList(string ingredients, string tupleTypeArgs,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitTupleSelect(string prefix, int i, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }
    public static string PublicIdProtect(string name) {
      Contract.Requires(name != null);
      switch (name) {
        default:
          return MangleName(name);
      }
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl member = null) {
      if (udt is ArrowType) {
        return ArrowType.Arrow_FullCompileName;
      }

      var cl = udt.ResolvedClass;
      if (cl is TypeParameter) {
        return IdProtect(udt.CompileName);
      } else {
        return IdProtect(cl.FullCompileName);
      }


    }

    protected override void EmitThis(ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, Type receiverType,
        out string compiledName, out string preString, out string postString) {
      compiledName = "";
      preString = "";
      postString = "";
      switch (id) {
        case SpecialField.ID.UseIdParam:
          compiledName = IdProtect((string)idParam);
          break;
        default:
          Contract.Assert(false); // unexpected ID
          break;
      }
    }

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member,
        List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap, Type expectedType,
        string additionalCustomParameter = null, bool internalAccess = false) {
      return SimpleLvalue(w => {
        w.Write("{0}.{1}()", TypeName_Companion(objType, w, member.tok, member), IdName(member));
      });
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<string> indices, Type elmtType, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
      CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray,
      bool inLetExprBody,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void
      EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void
      EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitApplyExpr(Type functionType, IToken tok, Expression function,
      List<Expression> arguments, bool inLetExprBody,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
      List<Type> boundTypes, Type resultType, IToken resultTok,
      bool inLetExprBody, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor,
      List<Type> typeArgs, Type bvType,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IToken tok, List<string> inNames,
      Type resultType, ConcreteSyntaxTree wr,
      bool untyped = false) {
      throw new NotImplementedException();
    }

    protected override void CreateIIFE(string bvName, Type bvType, IToken bvTok, Type bodyType, IToken bodyTok,
      ConcreteSyntaxTree wr,
      out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IToken resultTok, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IToken resultTok, string bvName,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op,
      Expression e0, Expression e1, Bpl.IToken tok, Type resultType,
      out string opString,
      out string preOpString,
      out string postOpString,
      out string callString,
      out string staticCallString,
      out bool reverseArguments,
      out bool truncateResult,
      out bool convertE1_to_int,
      ConcreteSyntaxTree errorWr) {

      opString = null;
      preOpString = "";
      postOpString = "";
      callString = null;
      staticCallString = null;
      reverseArguments = false;
      truncateResult = false;
      convertE1_to_int = false;

      switch (op) {
        case BinaryExpr.ResolvedOpcode.Add:
          opString = "+"; break;

        case BinaryExpr.ResolvedOpcode.Mul:
          opString = "*"; break;

        case BinaryExpr.ResolvedOpcode.EqCommon:
          opString = "=="; break;

        default:
          base.CompileBinOp(op, e0, e1, tok, resultType,
            out opString, out preOpString, out postOpString, out callString, out staticCallString, out reverseArguments,
            out truncateResult, out convertE1_to_int,
            errorWr);
          break;
      }
    }


    protected override void EmitITE(Expression guard, Expression thn, Expression els, Type resultType, bool inLetExprBody, ConcreteSyntaxTree wr) {
      Contract.Requires(guard != null);
      Contract.Requires(thn != null);
      Contract.Requires(thn.Type != null);
      Contract.Requires(els != null);
      Contract.Requires(resultType != null);
      Contract.Requires(wr != null);

      resultType = resultType.NormalizeExpand();
      var thenExpr = Expr(thn, inLetExprBody);
      var castedThenExpr = resultType.Equals(thn.Type.NormalizeExpand()) ? thenExpr : Cast(resultType, thenExpr);
      var elseExpr = Expr(els, inLetExprBody);
      var castedElseExpr = resultType.Equals(els.Type.NormalizeExpand()) ? elseExpr : Cast(resultType, elseExpr);
      wr.Format($"{castedThenExpr} if {Expr(guard, inLetExprBody)} else {castedElseExpr}");
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IToken tok,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IToken tok, List<Expression> elements,
      bool inLetExprBody, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitMapDisplay(MapType mt, IToken tok, List<ExpressionPair> elements, bool inLetExprBody,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
      throw new NotImplementedException();
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      throw new NotImplementedException();
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IToken tok, string collName, Expression term,
      bool inLetExprBody,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, IToken tok, string collName,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    public override bool TextualTargetIsExecutable => true;

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText,
      string /*?*/ callToMain, string /*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
      compilationResult = null;
      if (runAfterCompile) {
        Contract.Assert(callToMain != null); // this is part of the contract of CompileTargetProgram
        // Since the program is to be run soon, nothing further is done here. Any compilation errors (that is, any errors
        // in the emitted program--this should never happen if the compiler itself is correct) will be reported as 'python'
        // will run the program.
        return true;
      } else {
        // compile now
        return SendToNewPythonProcess(dafnyProgramName, targetProgramText, null, targetFilename, otherFileNames,
          outputWriter);
      }
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string /*?*/ callToMain,
        string targetFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter) {

      return SendToNewPythonProcess(dafnyProgramName, targetProgramText, callToMain, targetFilename, otherFileNames,
        outputWriter);
    }

    bool SendToNewPythonProcess(string dafnyProgramName, string targetProgramText, string /*?*/ callToMain,
        string targetFilename, ReadOnlyCollection<string> otherFileNames, TextWriter outputWriter) {
      Contract.Requires(targetFilename != null || otherFileNames.Count == 0);

      var psi = new ProcessStartInfo("python3", "") {
        CreateNoWindow = true,
        UseShellExecute = false,
        RedirectStandardInput = true,
        RedirectStandardOutput = false,
        RedirectStandardError = false,
      };

      try {
        using var pythonProcess = Process.Start(psi);
        foreach (var filename in otherFileNames) {
          WriteFromFile(filename, pythonProcess.StandardInput);
        }

        pythonProcess.StandardInput.Write(targetProgramText);
        if (callToMain != null && DafnyOptions.O.RunAfterCompile) {
          pythonProcess.StandardInput.Write(callToMain);
        }

        pythonProcess.StandardInput.Flush();
        pythonProcess.StandardInput.Close();
        pythonProcess.WaitForExit();
        return pythonProcess.ExitCode == 0;
      } catch (Exception e) {
        outputWriter.WriteLine("Error: Unable to start python ({0}): {1}", psi.FileName, e.Message);
        return false;
      }
    }
  }
}