//-----------------------------------------------------------------------------
//
// Copyright (C) Amazon.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using System.Collections.ObjectModel;
using System.Diagnostics;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class JavaScriptCompiler : Compiler {
    public JavaScriptCompiler(ErrorReporter reporter)
    : base(reporter) {
    }

    public override string TargetLanguage => "JavaScript";

    protected override void EmitHeader(Program program, TargetWriter wr) {
      wr.WriteLine("// Dafny program {0} compiled into JavaScript", program.Name);
      wr.WriteLine(@"
const BigNumber = require('bignumber.js');
BigNumber.config({ MODULO_MODE: BigNumber.EUCLID })
let _dafny = (function() {
  let $module = {};
  $module.Tuple = class Tuple extends Array {
    constructor(...elems) {
      super(...elems);
    }
    toString() {
      return ""("" + this.join("", "") + "")"";
    }
  }
  $module.Seq = class Seq extends Array {
    constructor(...elems) {
      super(...elems);
    }
    toString() {
      return ""["" + this.join("", "") + ""]"";
    }
  }
  $module.areEqual = function() {
    return false;  // TODO
  }
  $module.seqUpdate = function(s, i, v) {
    let t = s.slice();
    t[i] = v;
    return t;
  }
  $module.newArray = function(initValue, ...dims) {
    return { dims: dims, elmts: buildArray(initValue, ...dims) };
  }
  $module.EuclideanDivision = function(a, b) {
    if (a.isPositive()) {
      if (b.isPositive()) {
        // +a +b: a/b
        return a.dividedToIntegerBy(b);
      } else {
        // +a -b: -(a/(-b))
        return a.dividedToIntegerBy(b.negated()).negated();
      }
    } else {
      if (b.isPositive()) {
        // -a +b: -((-a-1)/b) - 1
        return a.negated().minus(1).dividedToIntegerBy(b).negated().minus(1);
      } else {
        // -a -b: ((-a-1)/(-b)) + 1
        return a.negated().minus(1).dividedToIntegerBy(b.negated()).plus(1);
      }
    }
  }
  return $module;

  function buildArray(initValue, ...dims) {
    if (dims.length === 0) {
      return initValue;
    } else {
      let a = Array(dims[0]);
      let b = Array.from(a, (x) => buildArray(initValue, ...dims.slice(1)));
      return b;
    }
  }
})();
");
    }

    public override void EmitCallToMain(Method mainMethod, TextWriter wr) {
      wr.WriteLine("{0}.{1}();", mainMethod.EnclosingClass.FullCompileName, IdName(mainMethod));
    }
      
    protected override BlockTargetWriter CreateModule(string moduleName, TargetWriter wr) {
      var w = wr.NewBigBlock(string.Format("let {0} = (function()", moduleName), ")(); // end of module " + moduleName);
      w.Indent();
      w.WriteLine("let $module = {};");
      w.BodySuffix = string.Format("{0}return $module;{1}", w.IndentString, w.NewLine);
      return w;
    }

    protected override BlockTargetWriter CreateClass(string name, List<TypeParameter>/*?*/ typeParameters, List<Type>/*?*/ superClasses, Bpl.IToken tok, out TargetWriter instanceFieldsWriter, TargetWriter wr) {
      wr.Indent();
      var w = wr.NewBlock(string.Format("$module.{0} = class {0}", name), ";");
      w.Indent();
      instanceFieldsWriter = w.NewBlock("constructor ()");
      return w;
    }

    protected override BlockTargetWriter CreateTrait(string name, List<Type>/*?*/ superClasses, Bpl.IToken tok, out TargetWriter instanceFieldsWriter, out TargetWriter staticMemberWriter, TargetWriter wr) {
      wr.Indent();
      var w = wr.NewBlock(string.Format("$module.{0} = class {0}", IdProtect(name)), ";");
      w.Indent();
      instanceFieldsWriter = w.NewBlock("constructor ()");
      staticMemberWriter = w;
      return w;
    }

    protected override void DeclareDatatype(DatatypeDecl dt, TargetWriter wr) {
      // $module.Dt = class Dt {
      //   constructor(tag) {
      //     this.$tag = tag;
      //   }
      //   static create_Ctor0(field0, field1, ...) {
      //     let $dt = new Dt(0);
      //     $dt.field0 = field0;
      //     $dt.field1 = field1;
      //     ...
      //     return $dt;
      //   }
      //   static create_Ctor1(...) {
      //     let $dt = new Dt(1);
      //     ...
      //   }
      //   ...
      //
      //   get is_Ctor0 { return this.$tag == 0; }
      //   get is_Ctor1 { return this.$tag == 1; }
      //   ...
      //
      //   toString() {
      //     ...
      //   }
      //   equals(other) {
      //     ...
      //   }
      // }
      // TODO: need Default member (also for co-datatypes)
      // TODO: if HasFinitePossibleValues, need enumerator of values

      string DtT = dt.CompileName;
      string DtT_protected = IdProtect(DtT);

      wr.Indent();
      // from here on, write everything into the new block created here:
      wr = wr.NewNamedBlock("$module.{0} = class {0}", DtT_protected);

      wr.Indent();
      wr.WriteLine("constructor(tag) { this.$tag = tag; }");


      // query properties
      var i = 0;
      foreach (var ctor in dt.Ctors) {
        // collect the names of non-ghost arguments
        var argNames = new List<string>();
        var k = 0;
        foreach (var formal in ctor.Formals) {
          if (!formal.IsGhost) {
            argNames.Add(FormalName(formal, k));
            k++;
          }
        }
        // static create_Ctor0(params) { return {$tag:0, p0: pararms0, p1: params1, ...}; }
        wr.Indent();
        wr.Write("static create_{0}(", ctor.CompileName);
        wr.Write(Util.Comma(argNames, nm => nm));
        var w = wr.NewBlock(")");
        w.Indent();
        w.WriteLine("let $dt = new {0}({1});", DtT_protected, i);
        foreach (var arg in argNames) {
          w.Indent();
          w.WriteLine("$dt.{0} = {0};", arg);
        }
        w.Indent();
        w.WriteLine("return $dt;");
        i++;
      }

      // query properties
      i = 0;
      foreach (var ctor in dt.Ctors) {
        // get is_Ctor0() { return _D is Dt_Ctor0; }
        wr.Indent();
        wr.WriteLine("get is_{0}() {{ return this.$tag === {1}; }}", ctor.CompileName, i);
        i++;
      }

      if (dt is IndDatatypeDecl && !(dt is TupleTypeDecl)) {
        // toString method
        wr.Indent();
        var w = wr.NewBlock("toString()");
        i = 0;
        foreach (var ctor in dt.Ctors) {
          var cw = EmitIf(string.Format("this.$tag == {0}", i), true, w);
          cw.Indent();
          cw.Write("return \"{0}.{1}\"", dt.Name, ctor.Name);
          var sep = " + \"(\" + ";
          var anyFormals = false;
          var k = 0;
          foreach (var arg in ctor.Formals) {
            if (!arg.IsGhost) {
              anyFormals = true;
              cw.Write("{0}this.{1}.toString()", sep, FormalName(arg, k));
              sep = " + \", \" + ";
              k++;
            }
          }
          if (anyFormals) {
            cw.Write(" + \")\"");
          }
          cw.WriteLine(";");
          i++;
        }
        w = w.NewBlock("");
        w.Indent();
        w.WriteLine("return \"<unexpected>\";");
      }

      // equals method
      wr.Indent();
      using (var w = wr.NewBlock("equals(other)")) {
        using (var thn = EmitIf("this === other", true, w)) {
          EmitReturnExpr("true", thn);
        }
        i = 0;
        foreach (var ctor in dt.Ctors) {
          var thn = EmitIf(string.Format("this.$tag == {0}", i), true, w);
          using (var guard = new TargetWriter()) {
            guard.Write("other.$tag == {0}", i);
            var k = 0;
            foreach (Formal arg in ctor.Formals) {
              if (!arg.IsGhost) {
                string nm = FormalName(arg, k);
                if (IsDirectlyComparable(arg.Type)) {
                  guard.Write(" && this.{0} === oth.{0}", nm);
                } else {
                  guard.Write(" && _dafny.areEqual(this.{0}, other.{0})", nm);
                }
                k++;
              }
            }
            EmitReturnExpr(guard.ToString(), thn);
          }
          i++;
        }
        using (var els = w.NewBlock("")) {
          els.Indent();
          els.WriteLine("return false; // unexpected");
        }
      }
    }

    protected override BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody, TargetWriter wr) {
      if (!createBody) {
        return null;
      }
      wr.Indent();
      wr.Write("{0}{1}(", m.IsStatic ? "static " : "", IdName(m));
      int nIns = WriteFormals("", m.Ins, wr);
      var w = wr.NewBlock(")");

      if (!m.IsStatic) {
        w.Indent(); w.WriteLine("let _this = this;");
      }
      if (m.IsTailRecursive) {
        w.Indent();
        w = w.NewBlock("TAIL_CALL_START: while (true)");
      }
      var r = new TargetWriter(w.IndentLevel);
      EmitReturn(m.Outs, r);
      w.BodySuffix = r.ToString();
      return w;
    }

    protected override BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member, TargetWriter wr) {
      if (!createBody) {
        return null;
      }
      wr.Indent();
      wr.Write("{0}{1}(", isStatic ? "static " : "", name);
      int nIns = WriteFormals("", formals, wr);
      var w = wr.NewBlock(")", ";");
      if (!isStatic) {
        w.Indent(); w.WriteLine("let _this = this;");
      }
      return w;
    }

    protected override BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, TargetWriter wr) {
      if (createBody) {
        wr.Indent();
        wr.Write("{0}get {1}()", isStatic ? "static " : "", name);
        var w = wr.NewBlock("", ";");
        if (!isStatic) {
          w.Indent(); w.WriteLine("let _this = this;");
        }
        return w;
      } else {
        return null;
      }
    }

    protected override BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, out TargetWriter setterWriter, TargetWriter wr) {
      if (createBody) {
        wr.Indent();
        wr.Write("{0}get {1}()", isStatic ? "static " : "", name);
        var wGet = wr.NewBlock("", ";");
        if (!isStatic) {
          wGet.Indent(); wGet.WriteLine("let _this = this;");
        }

        wr.Indent();
        wr.Write("{0}set {1}(value)", isStatic ? "static " : "", name);
        var wSet = wr.NewBlock("", ";");
        if (!isStatic) {
          wSet.Indent(); wSet.WriteLine("let _this = this;");
        }

        setterWriter = wSet;
        return wGet;
      } else {
        setterWriter = null;
        return null;
      }
    }

    protected override void EmitJumpToTailCallStart(TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("continue TAIL_CALL_START;");
    }

    public override string TypeInitializationValue(Type type, TextWriter/*?*/ wr, Bpl.IToken/*?*/ tok) {
      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return "'D'";
      } else if (xType is IntType || xType is BigOrdinalType || xType is RealType || xType is BitvectorType) {
        return "0";
      } else if (xType is CollectionType) {
        return TypeName(xType, wr, tok) + ".Empty";
      }

      var udt = (UserDefinedType)xType;
      if (udt.ResolvedParam != null) {
        return "Dafny.Helpers.Default<" + TypeName_UDT(udt.FullCompileName, udt.TypeArgs, wr, udt.tok) + ">()";
      }
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        if (td.Witness != null) {
          return TypeName_UDT(udt.FullCompileName, udt.TypeArgs, wr, udt.tok) + ".Witness";
        } else if (td.NativeType != null) {
          return "0";
        } else {
          return TypeInitializationValue(td.BaseType, wr, tok);
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        if (td.Witness != null) {
          return TypeName_UDT(udt.FullCompileName, udt.TypeArgs, wr, udt.tok) + ".Witness";
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            return string.Format("null)");
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) => rangeDefaultValue)
            return string.Format("function () {{ return {0}; }}", rangeDefaultValue);
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl) {
            // non-null array type; we know how to initialize them
            return "[]";
          } else {
            // non-null (non-array) type
            // even though the type doesn't necessarily have a known initializer, it could be that the the compiler needs to
            // lay down some bits to please the C#'s compiler's different definite-assignment rules.
            return string.Format("default({0})", TypeName(xType, wr, udt.tok));
          }
        } else {
          return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok);
        }
      } else if (cl is ClassDecl) {
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "0";
        } else {
          return "null";
        }
      } else if (cl is DatatypeDecl) {
        var s = "@" + udt.FullCompileName;
        var rc = cl;
        if (DafnyOptions.O.IronDafny &&
            !(xType is ArrowType) &&
            rc != null &&
            rc.Module != null &&
            !rc.Module.IsDefaultModule) {
          s = "@" + rc.FullCompileName;
        }
        if (udt.TypeArgs.Count != 0) {
          s += "<" + TypeNames(udt.TypeArgs, wr, udt.tok) + ">";
        }
        return string.Format("new {0}()", s);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }

    }

    protected override string TypeName_UDT(string fullCompileName, List<Type> typeArgs, TextWriter wr, Bpl.IToken tok) {
      Contract.Requires(fullCompileName != null);
      Contract.Requires(typeArgs != null);
      string s = IdProtect(fullCompileName);
      return s;
    }

    protected override string TypeName_Companion(Type type, TextWriter wr, Bpl.IToken tok) {
      var udt = type as UserDefinedType;
      if (udt != null && udt.ResolvedClass is TraitDecl) {
        if (udt.TypeArgs.Count != 0 && udt.TypeArgs.Exists(argType => argType.NormalizeExpand().IsObjectQ)) {
          // TODO: This is a restriction for .NET, but may not need to be a restriction for JavaScript
          Error(udt.tok, "compilation does not support type 'object' as a type parameter; consider introducing a ghost", wr);
        }
      }
      return TypeName(type, wr, tok);
    }

    // ----- Declarations -------------------------------------------------------------

    protected override void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs, TargetWriter wr) {
      wr.Indent();
      if (isStatic) {
        var w = wr.NewNamedBlock("static get {0}()", name);
        EmitReturnExpr(rhs, w);
      } else {
        wr.WriteLine("this.{0} = {1};", name, rhs);
      }
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, Bpl.IToken tok, bool isInParam, TextWriter wr) {
      if (isInParam) {
        wr.Write("{0}{1}", prefix, name);
        return true;
      } else {
        return false;
      }
    }

    protected override void DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, bool leaveRoomForRhs, string/*?*/ rhs, TargetWriter wr) {
      wr.Indent();
      wr.Write("let {0}", name);
      if (leaveRoomForRhs) {
        Contract.Assert(rhs == null);  // follows from precondition
      } else if (rhs != null) {
        wr.WriteLine(" = {0};", rhs);
      } else {
        wr.WriteLine(";");
      }
    }

    protected override void DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, Expression rhs, bool inLetExprBody, TargetWriter wr) {
      wr.Indent();
      wr.Write("let {0} = ", name);
      TrExpr(rhs, wr, inLetExprBody);
      wr.WriteLine(";");
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;

    protected override void DeclareOutCollector(string collectorVarName, TargetWriter wr) {
      wr.Write("let {0} = ", collectorVarName);
    }

    protected override void DeclareLocalOutVar(string name, Type type, Bpl.IToken tok, string rhs, TargetWriter wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override void EmitOutParameterSplits(string outCollector, List<string> actualOutParamNames, TargetWriter wr) {
      if (actualOutParamNames.Count == 1) {
        EmitAssignment(actualOutParamNames[0], outCollector, wr);
      } else {
        for (var i = 0; i < actualOutParamNames.Count; i++) {
          wr.Indent();
          wr.WriteLine("{0} = {1}[{2}];", actualOutParamNames[i], outCollector, i);
        }
      }
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, Bpl.IToken tok, TextWriter wr) {
      // emit nothing
    }

    protected override string GenerateLhsDecl(string target, Type/*?*/ type, TextWriter wr, Bpl.IToken tok) {
      return "let " + target;
    }

    // ----- Statements -------------------------------------------------------------

    protected override void EmitPrintStmt(TargetWriter wr, Expression arg) {
      wr.Indent();
      wr.Write("process.stdout.write(");
      TrParenExpr(arg, wr, false);
      wr.WriteLine(".toString());");
    }

    protected override void EmitReturn(List<Formal> outParams, TargetWriter wr) {
      wr.Indent();
      if (outParams.Count == 0) {
        wr.WriteLine("return;");
      } else if (outParams.Count == 1) {
        wr.WriteLine("return {0};", IdName(outParams[0]));
      } else {
        wr.WriteLine("return [{0}];", Util.Comma(outParams, IdName));
      }
    }

    protected override void EmitBreak(string label, TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("break {0};", label);
    }

    protected override void EmitYield(TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("yield null;");
    }

    protected override void EmitAbsurd(TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("throw new Error('unexpected control point');");
    }

    protected override BlockTargetWriter CreateForLoop(string indexVar, string bound, TargetWriter wr) {
      wr.Indent();
      var w = wr.NewNamedBlock("for (let {0} = 0; {0} < {1}; {0}++)", indexVar, bound);
      return w;
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitNew(Type type, Bpl.IToken tok, CallStmt/*?*/ initCall, TargetWriter wr) {
      wr.Write("new {0}()", TypeName(type, wr, tok));
    }

    protected override void EmitNewArray(Type elmtType, Bpl.IToken tok, List<Expression> dimensions, bool mustInitialize, TargetWriter wr) {
      var initValue = mustInitialize ? DefaultValue(elmtType, wr, tok) : null;
      if (dimensions.Count == 1) {
        // handle the common case of 1-dimensional arrays separately
        wr.Write("Array");
        TrParenExpr(dimensions[0], wr, false);
        if (initValue != null) {
          wr.Write(".fill({0})", initValue);
        }
      } else {
        // the general case
        wr.Write("_dafny.newArray({0}", initValue ?? "undefined");
        foreach (var dim in dimensions) {
          wr.Write(", ");
          TrExpr(dim, wr, false);
        }
        wr.Write(")");
      }
    }

    protected override void EmitLiteralExpr(TextWriter wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write(TypeName(e.Type, wr, e.tok));
      } else if (e.Value == null) {
        wr.Write("null");
      } else if (e.Value is bool) {
        wr.Write((bool)e.Value ? "true" : "false");
      } else if (e is CharLiteralExpr) {
        var v = (string)e.Value;
        wr.Write("'{0}'", v == "\\0" ? "\\u0000" : v);  // JavaScript doesn't have a \0
      } else if (e is StringLiteralExpr) {
        var str = (StringLiteralExpr)e;
        // TODO: the string should be converted to a Dafny seq<char>
        TrStringLiteral(str, wr);
      } else if (AsNativeType(e.Type) != null) {
        wr.Write((BigInteger)e.Value + AsNativeType(e.Type).Suffix);
      } else if (e.Value is BigInteger) {
        var i = (BigInteger)e.Value;
        if (-9007199254740991 <= i && i <= 9007199254740991) {
          wr.Write("new BigNumber({0})", i);
        } else {
          wr.Write("new BigNumber(\"{0}\")", i);
        }
      } else if (e.Value is Basetypes.BigDec) {
        var n = (Basetypes.BigDec)e.Value;
        wr.Write("new BigNumber(\"{0}e{1}\")", n.Mantissa, n.Exponent);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, TextWriter wr) {
      var n = str.Length;
      wr.Write("\"");
      for (var i = 0; i < n; i++) {
        if (str[i] == '\\' && str[i+1] == '0') {
          wr.Write("\\u0000");
          i++;
        } else if (str[i] == '\n') {  // may appear in a verbatim string
          wr.Write("\\n");
        } else if (str[i] == '\r') {  // may appear in a verbatim string
          wr.Write("\\r");
        } else {
          wr.Write(str[i]);
        }
      }
      wr.Write("\"");
    }

    protected override void EmitThis(TargetWriter wr) {
      wr.Write("_this");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string dtName, string ctorName, string arguments, TargetWriter wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      if (dt is TupleTypeDecl) {
        wr.Write("_dafny.Tuple.of({0})", arguments);
      } else {
        wr.Write("{0}.{1}.create_{2}({3})", dt.Module.CompileName, dtName, ctorName, arguments);
      }
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, out string compiledName, out string preString, out string postString) {
      compiledName = "";
      preString = "";
      postString = "";
      switch (id) {
        case SpecialField.ID.UseIdParam:
          compiledName = (string)idParam;
          break;
        case SpecialField.ID.ArrayLength:
          compiledName = idParam == null ? "length" : "dims[" + (int)idParam + "]";
          break;
        case SpecialField.ID.Floor:
          compiledName = "ToBigInteger()";
          break;
        case SpecialField.ID.IsLimit:
          preString = "Dafny.Helpers.BigOrdinal_IsLimit(";
          postString = ")";
          break;
        case SpecialField.ID.IsSucc:
          preString = "Dafny.Helpers.BigOrdinal_IsSucc(";
          postString = ")";
          break;
        case SpecialField.ID.Offset:
          preString = "Dafny.Helpers.BigOrdinal_Offset(";
          postString = ")";
          break;
        case SpecialField.ID.IsNat:
          preString = "Dafny.Helpers.BigOrdinal_IsNat(";
          postString = ")";
          break;
        case SpecialField.ID.Keys:
          compiledName = "Keys";
          break;
        case SpecialField.ID.Values:
          compiledName = "Values";
          break;
        case SpecialField.ID.Items:
          compiledName = "Items";
          break;
        case SpecialField.ID.Reads:
          compiledName = "_reads";
          break;
        case SpecialField.ID.Modifies:
          compiledName = "_modifies";
          break;
        case SpecialField.ID.New:
          compiledName = "_new";
          break;
        default:
          Contract.Assert(false); // unexpected ID
          break;
      }
    }

    protected override void EmitMemberSelect(MemberDecl member, bool isLValue, TargetWriter wr) {
      if (isLValue && member is ConstantField) {
        wr.Write("._{0}", member.CompileName);
      } else if (member is DatatypeDestructor dtor) {
        if (dtor.EnclosingClass is TupleTypeDecl) {
          wr.Write("[{0}]", dtor.Name);
        } else {
          wr.Write(".{0}", IdName(member));
        }
      } else if (!isLValue && member is SpecialField sf) {
        string compiledName, preStr, postStr;
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, out compiledName, out preStr, out postStr);
        if (compiledName.Length != 0) {
          wr.Write(".{0}", compiledName);
        } else {
          // this member selection is handled by some kind of enclosing function call, so nothing to do here
        }
      } else {
        wr.Write(".{0}", IdName(member));
      }
    }

    protected override void EmitArraySelect(List<string> indices, TargetWriter wr) {
      if (indices.Count == 1) {
        wr.Write("[{0}]", indices[0]);
      } else {
        wr.Write(".elmts");
        foreach (var index in indices) {
          wr.Write("[{0}]", index);
        }
      }
    }

    protected override void EmitArraySelect(List<Expression> indices, bool inLetExprBody, TargetWriter wr) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      if (indices.Count == 1) {
        wr.Write("[");
        TrExpr(indices[0], wr, inLetExprBody);
        wr.Write("]");
      } else {
        wr.Write(".elmts");
        foreach (var index in indices) {
          wr.Write("[");
          TrExpr(index, wr, inLetExprBody);
          wr.Write("]");
        }
      }
    }

    protected override void EmitSeqSelect(Expression source, Expression index, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(source, wr, inLetExprBody);
      wr.Write("[");
      TrExpr(index, wr, inLetExprBody);
      wr.Write("]");
    }

    protected override void EmitSeqUpdate(Expression source, Expression index, Expression value, bool inLetExprBody, TargetWriter wr) {
      wr.Write("_dafny.seqUpdate(");
      TrExpr(source, wr, inLetExprBody);
      wr.Write(", ");
      TrExpr(index, wr, inLetExprBody);
      wr.Write(", ");
      TrExpr(value, wr, inLetExprBody);
      wr.Write(")");
    }

    protected override void EmitSeqSelectRange(Expression source, Expression/*?*/ lo, Expression/*?*/ hi, bool fromArray, bool inLetExprBody, TargetWriter wr) {
      if (fromArray) {
        wr.Write("_dafny.Seq.of(...");
      }
      TrParenExpr(source, wr, inLetExprBody);
      if (lo != null) {
        wr.Write(".slice(");
        TrExpr(lo, wr, inLetExprBody);
        if (hi != null) {
          wr.Write(", ");
          TrExpr(hi, wr, inLetExprBody);
        }
        wr.Write(")");
      } else if (hi != null) {
        wr.Write(".slice(0, ");
        TrExpr(hi, wr, inLetExprBody);
        wr.Write(")");
      } else if (fromArray) {
        wr.Write(".slice()");
      }
      if (fromArray) {
        wr.Write(")");
      }
    }

    protected override void EmitApplyExpr(Type functionType, Bpl.IToken tok, Expression function, List<Expression> arguments, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(function, wr, inLetExprBody);
      TrExprList(arguments, wr, inLetExprBody);
    }

    protected override void EmitBetaRedex(string boundVars, List<Expression> arguments, string typeArgs, bool inLetExprBody, System.Action makeBody, TargetWriter wr) {
      wr.Write("(({0}) => ", boundVars);
      makeBody();
      wr.Write(")");
      TrExprList(arguments, wr, inLetExprBody);
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, TargetWriter wr) {
      if (ctor.EnclosingDatatype is TupleTypeDecl) {
        wr.Write("({0})[{1}]", source, formalNonGhostIndex);
      } else {
        var dtorName = FormalName(dtor, formalNonGhostIndex);
        wr.Write("({0}).{1}", source, dtorName);
      }
    }

    protected override BlockTargetWriter CreateLambda(List<Type> inTypes, Bpl.IToken tok, List<string> inNames, Type resultType, TargetWriter wr) {
      wr.Write("function (");
      Contract.Assert(inTypes.Count == inNames.Count);  // guaranteed by precondition
      for (var i = 0; i < inNames.Count; i++) {
        wr.Write("{0}{1}", i == 0 ? "" : ", ", inNames[i]);
      }
      var w = wr.NewBlock(")");
      w.SetBraceStyle(BlockTargetWriter.BraceStyle.Space, BlockTargetWriter.BraceStyle.Nothing);
      return w;
    }

    protected override TargetWriter CreateIIFE(Expression source, bool inLetExprBody, Type sourceType, Bpl.IToken sourceTok, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      var w = wr.NewNamedBlock("function ({0})", bvName);
      w.SetBraceStyle(BlockTargetWriter.BraceStyle.Space, BlockTargetWriter.BraceStyle.Nothing);
      w.Indent();
      w.Write("return ");
      w.BodySuffix = ";" + w.NewLine;

      wr.Write("(");
      TrExpr(source, wr, inLetExprBody);
      wr.Write(")");
      return w;
    }

    protected override TargetWriter CreateIIFE(string source, Type sourceType, Bpl.IToken sourceTok, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      var w = wr.NewNamedBlock("function ({0})", bvName);
      w.SetBraceStyle(BlockTargetWriter.BraceStyle.Space, BlockTargetWriter.BraceStyle.Nothing);
      w.Indent();
      w.Write("return ");
      w.BodySuffix = ";" + w.NewLine;

      wr.Write("({0})", source);
      return w;
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, TargetWriter wr) {
      switch (op) {
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("!", expr, wr, inLetExprBody);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          TrParenExpr("~", expr, wr, inLetExprBody);
          break;
        case ResolvedUnaryOp.Cardinality:
          TrParenExpr(expr, wr, inLetExprBody);
          wr.Write(".length");
          break;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
      }
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
      TextWriter errorWr) {

      opString = null;
      preOpString = "";
      postOpString = "";
      callString = null;
      staticCallString = null;
      reverseArguments = false;
      truncateResult = false;
      convertE1_to_int = false;

      switch (op) {
        case BinaryExpr.ResolvedOpcode.Iff:
          opString = "==="; break;
        case BinaryExpr.ResolvedOpcode.Imp:
          preOpString = "!"; opString = "||"; break;
        case BinaryExpr.ResolvedOpcode.Or:
          opString = "||"; break;
        case BinaryExpr.ResolvedOpcode.And:
          opString = "&&"; break;
        case BinaryExpr.ResolvedOpcode.BitwiseAnd:
          opString = "&"; break;
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
          opString = "|"; break;
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
          opString = "^"; break;

        case BinaryExpr.ResolvedOpcode.EqCommon: {
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "===";
            } else if (e0.Type.IsRefType) {
              // Dafny's type rules are slightly different C#, so we may need a cast here.
              // For example, Dafny allows x==y if x:array<T> and y:array<int> and T is some
              // type parameter.
              opString = "=== (object)";
            } else if (IsDirectlyComparable(e0.Type)) {
              opString = "===";
            } else {
              callString = "equals";
            }
            break;
          }
        case BinaryExpr.ResolvedOpcode.NeqCommon: {
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "!==";
            } else if (e0.Type.IsRefType) {
              // Dafny's type rules are slightly different C#, so we may need a cast here.
              // For example, Dafny allows x==y if x:array<T> and y:array<int> and T is some
              // type parameter.
              opString = "!= (object)";
            } else if (IsDirectlyComparable(e0.Type)) {
              opString = "!=";
            } else {
              preOpString = "!";
              callString = "Equals";
            }
            break;
          }

        case BinaryExpr.ResolvedOpcode.Lt:
        case BinaryExpr.ResolvedOpcode.LtChar:
          opString = "<"; break;
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.LeChar:
          opString = "<="; break;
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.GeChar:
          opString = ">="; break;
        case BinaryExpr.ResolvedOpcode.Gt:
        case BinaryExpr.ResolvedOpcode.GtChar:
          opString = ">"; break;
        case BinaryExpr.ResolvedOpcode.LeftShift:
          opString = "<<"; truncateResult = true; convertE1_to_int = true; break;
        case BinaryExpr.ResolvedOpcode.RightShift:
          opString = ">>"; convertE1_to_int = true; break;
        case BinaryExpr.ResolvedOpcode.Add:
          callString = "plus"; truncateResult = true; break;
        case BinaryExpr.ResolvedOpcode.Sub:
          callString = "minus"; truncateResult = true; break;
        case BinaryExpr.ResolvedOpcode.Mul:
          callString = "multipliedBy"; truncateResult = true; break;
        case BinaryExpr.ResolvedOpcode.Div:
          if (resultType.IsIntegerType || (AsNativeType(resultType) != null && AsNativeType(resultType).LowerBound < BigInteger.Zero)) {
            staticCallString = "_dafny.EuclideanDivision";
          } else if (AsNativeType(resultType) != null) {
            opString = "/";
          } else {
            callString = "dividedBy";  // for reals
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (resultType.IsIntegerType || (AsNativeType(resultType) != null && AsNativeType(resultType).LowerBound < BigInteger.Zero)) {
            callString = "mod";
          } else {
            opString = "%";  // for reals
          }
          break;
        case BinaryExpr.ResolvedOpcode.SetEq:
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
        case BinaryExpr.ResolvedOpcode.SeqEq:
        case BinaryExpr.ResolvedOpcode.MapEq:
          callString = "equals"; break;
        case BinaryExpr.ResolvedOpcode.SetNeq:
        case BinaryExpr.ResolvedOpcode.MultiSetNeq:
        case BinaryExpr.ResolvedOpcode.SeqNeq:
        case BinaryExpr.ResolvedOpcode.MapNeq:
          preOpString = "!"; callString = "equals"; break;
        case BinaryExpr.ResolvedOpcode.ProperSubset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
          callString = "IsProperSubsetOf"; break;
        case BinaryExpr.ResolvedOpcode.Subset:
        case BinaryExpr.ResolvedOpcode.MultiSubset:
          callString = "IsSubsetOf"; break;
        case BinaryExpr.ResolvedOpcode.Superset:
        case BinaryExpr.ResolvedOpcode.MultiSuperset:
          callString = "IsSupersetOf"; break;
        case BinaryExpr.ResolvedOpcode.ProperSuperset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
          callString = "IsProperSupersetOf"; break;
        case BinaryExpr.ResolvedOpcode.Disjoint:
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
        case BinaryExpr.ResolvedOpcode.MapDisjoint:
          callString = "IsDisjointFrom"; break;
        case BinaryExpr.ResolvedOpcode.InSet:
        case BinaryExpr.ResolvedOpcode.InMultiSet:
        case BinaryExpr.ResolvedOpcode.InMap:
          callString = "Contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.NotInSet:
        case BinaryExpr.ResolvedOpcode.NotInMultiSet:
        case BinaryExpr.ResolvedOpcode.NotInMap:
          preOpString = "!"; callString = "Contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          callString = "Union"; break;
        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          callString = "Intersect"; break;
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          callString = "Difference"; break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          callString = "IsProperPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Prefix:
          callString = "IsPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Concat:
          callString = "Concat"; break;
        case BinaryExpr.ResolvedOpcode.InSeq:
          callString = "Contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.NotInSeq:
          preOpString = "!"; callString = "Contains"; reverseArguments = true; break;

        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected binary expression
      }
    }

    // ----- Target compilation and execution -------------------------------------------------------------

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      bool hasMain, bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
      if (DafnyOptions.O.RunAfterCompile) {
        // to make the output look that like for C#
        outputWriter.WriteLine("Program compiled successfully");
      }
      return base.CompileTargetProgram(dafnyProgramName, targetProgramText, targetFilename, otherFileNames, hasMain, runAfterCompile, outputWriter, out compilationResult);
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string targetFilename, ReadOnlyCollection<string> otherFileNames,
      object compilationResult, TextWriter outputWriter) {

      string args = "";
      if (targetFilename != null) {
        args += targetFilename;
        foreach (var s in otherFileNames) {
          args += " " + s;
        }
      } else {
        Contract.Assert(otherFileNames.Count == 0);  // according to the precondition
      }
      var psi = new ProcessStartInfo("node", args) {
        CreateNoWindow = true,
        UseShellExecute = false,
        RedirectStandardInput = true,
        RedirectStandardOutput = false,
        RedirectStandardError = false,
      };

      try {
        using (var nodeProcess = Process.Start(psi)) {
          if (targetFilename == null) {
            nodeProcess.StandardInput.Write(targetProgramText);
            nodeProcess.StandardInput.Flush();
            nodeProcess.StandardInput.Close();
          }
          nodeProcess.WaitForExit();
          return nodeProcess.ExitCode == 0;
        }
      } catch (System.ComponentModel.Win32Exception e) {
        outputWriter.WriteLine("Error: Unable to start node.js ({0}): {1}", psi.FileName, e.Message);
        return false;
      }
    }
  }
}
