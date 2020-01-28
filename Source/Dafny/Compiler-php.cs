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

namespace Microsoft.Dafny
{
    public class PhpCompiler : Compiler
    {
        public PhpCompiler(ErrorReporter reporter)
        : base(reporter)
        {
        }

        public override string TargetLanguage => "PHP";

        protected override void EmitHeader(Program program, TargetWriter wr)
        {
            wr.WriteLine("<?php");
            wr.WriteLine("declare(strict_types=1);"); // Weak-typing in PHP is bad.
            wr.WriteLine("// Dafny program {0} compiled into PHP", program.Name);
        }

        public String PhpifyNamespaces(String fullCompileName)
        {
            return fullCompileName.Replace('.', '\\');
        }
        
        // PHP requires variables be prefixed with $
        protected override string IdName(IVariable v) {
            Contract.Requires(v != null);
            return IdProtect("$" + v.CompileName);
        }

        public override void EmitCallToMain(Method mainMethod, TargetWriter wr)
        {
            wr.WriteLine("namespace {");
            wr.WriteLine("\t\\{0}::{1}();", this.PhpifyNamespaces(mainMethod.EnclosingClass.FullCompileName), IdName(mainMethod));
            wr.WriteLine("}");
        }

        protected override BlockTargetWriter CreateStaticMain(IClassWriter cw)
        {
            var wr = (cw as PhpCompiler.ClassWriter).MethodWriter;
            return wr.NewBlock("public static function main()");
        }

        protected override TargetWriter CreateModule(string moduleName, bool isDefault, bool isExtern, string/*?*/ libraryName, TargetWriter wr)
        {
            var namespaced = this.PhpifyNamespaces(moduleName);
            var w = wr.NewBigBlock("namespace " + namespaced + "", "// end of module " + namespaced);
            return w;
        }

        protected override string GetHelperModuleName() => "_dafny";

        protected override IClassWriter CreateClass(string name, bool isExtern, string/*?*/ fullPrintName, List<TypeParameter>/*?*/ typeParameters, List<Type>/*?*/ superClasses, Bpl.IToken tok, TargetWriter wr)
        {
            var w = wr.NewBlock(string.Format("class {0}" + (isExtern ? " extends {0}" : ""), name), "");
            w.Write("public function __construct(");
            if (typeParameters != null)
            {
                WriteRuntimeTypeDescriptorsFormals(typeParameters, false, w);
            }
            var fieldWriter = w.NewBlock(")");
            if (fullPrintName != null)
            {
                fieldWriter.WriteLine("$this->_tname = \"{0}\";", fullPrintName);
            }
            if (typeParameters != null)
            {
                foreach (var tp in typeParameters)
                {
                    if (tp.Characteristics.MustSupportZeroInitialization)
                    {
                        fieldWriter.WriteLine("$this->{0} = ${0};", "rtd_" + tp.CompileName);
                    }
                }
            }
            var methodWriter = w;
            return new ClassWriter(this, methodWriter, fieldWriter);
        }

        protected override IClassWriter CreateTrait(string name, bool isExtern, List<Type>/*?*/ superClasses, Bpl.IToken tok, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override BlockTargetWriter CreateIterator(IteratorDecl iter, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override IClassWriter/*?*/ DeclareDatatype(DatatypeDecl dt, TargetWriter wr) 
        {
            if (dt is TupleTypeDecl)
            {
                // Tuple types are declared once and for all in DafnyRuntime.php
                return null;
            }
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }
        
        protected override IClassWriter DeclareNewtype(NewtypeDecl nt, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void DeclareSubsetType(SubsetTypeDecl sst, TargetWriter wr)
        {
            var cw = CreateClass(IdName(sst), sst.TypeArgs, wr) as PhpCompiler.ClassWriter;
            var w = cw.MethodWriter;
            if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled)
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            using (var wDefault = w.NewBlock("public static function Default()"))
            {
                var udt = UserDefinedType.FromTopLevelDecl(sst.tok, sst);
                var d = TypeInitializationValue(udt, wr, sst.tok, false);
                wDefault.WriteLine("return {0};", d);
            }
        }

        protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic)
        {
            literalSuffix = "";
            needsCastAfterArithmetic = false;
            switch (sel)
            {
                case NativeType.Selection.Number:
                    name = "int";
                    break;
                default:
                    Contract.Assert(false);  // unexpected native type
                    throw new cce.UnreachableException();  // to please the compiler
            }
        }

        protected class ClassWriter : IClassWriter
        {
            public readonly PhpCompiler Compiler;
            public readonly BlockTargetWriter MethodWriter;
            public readonly BlockTargetWriter FieldWriter;

            public ClassWriter(PhpCompiler compiler, BlockTargetWriter methodWriter, BlockTargetWriter fieldWriter)
            {
                Contract.Requires(compiler != null);
                Contract.Requires(methodWriter != null);
                Contract.Requires(fieldWriter != null);
                this.Compiler = compiler;
                this.MethodWriter = methodWriter;
                this.FieldWriter = fieldWriter;
            }

            public BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody)
            {
                return Compiler.CreateMethod(m, createBody, MethodWriter);
            }
            public BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member)
            {
                return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, MethodWriter);
            }
            public BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member)
            {
                return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, MethodWriter);
            }
            public BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member, out TargetWriter setterWriter)
            {
                return Compiler.CreateGetterSetter(name, resultType, tok, isStatic, createBody, out setterWriter, MethodWriter);
            }
            public void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs)
            {
                Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, FieldWriter);
            }
            public TextWriter/*?*/ ErrorWriter() => MethodWriter;
            public void Finish() { }
        }

        protected BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody, TargetWriter wr)
        {
            if (!createBody)
            {
                return null;
            }

            var customReceiver = NeedsCustomReceiver(m);
            wr.Write("{0}function {1}(", m.IsStatic || customReceiver ? "static " : "", IdName(m));
            var nTypes = WriteRuntimeTypeDescriptorsFormals(m.TypeArgs, false, wr);
            if (customReceiver)
            {
                var nt = m.EnclosingClass;
                var receiverType = UserDefinedType.FromTopLevelDecl(m.tok, nt);
                DeclareFormal(nTypes != 0 ? ", " : "", "$_this", receiverType, m.tok, true, wr);
            }
            int nIns = WriteFormals(nTypes != 0 || customReceiver ? ", " : "", m.Ins, wr);
            var w = wr.NewBlock(")");

            if (!m.IsStatic && !customReceiver)
            {
                w.WriteLine("$_this = $this;");
            }
            if (m.IsTailRecursive)
            {
                w = w.NewBlock("/* TAIL_CALL_START: */ while (true)");
            }
            var r = new TargetWriter(w.IndentLevel);
            EmitReturn(m.Outs, r);
            w.BodySuffix = r.ToString();
            return w;
        }

        protected BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member, TargetWriter wr)
        {
            if (!createBody)
            {
                return null;
            }

            var customReceiver = NeedsCustomReceiver(member);
            wr.Write("{0} function {1}(", isStatic || customReceiver ? "static " : "", name);
            var nTypes = typeArgs == null ? 0 : WriteRuntimeTypeDescriptorsFormals(typeArgs, false, wr);
            if (customReceiver)
            {
                var nt = member.EnclosingClass;
                var receiverType = UserDefinedType.FromTopLevelDecl(tok, nt);
                DeclareFormal(nTypes != 0 ? ", " : "", "$_this", receiverType, tok, true, wr);
            }
            int nIns = WriteFormals(nTypes != 0 || customReceiver ? ", " : "", formals, wr);
            var w = wr.NewBlock(")", ";");
            if (!isStatic && !customReceiver)
            {
                w.WriteLine("$_this = $this;");
            }
            return w;
        }

        int WriteRuntimeTypeDescriptorsFormals(List<TypeParameter> typeParams, bool useAllTypeArgs, TargetWriter wr, string prefix = "")
        {
            Contract.Requires(typeParams != null);
            Contract.Requires(wr != null);

            int c = 0;
            foreach (var tp in typeParams)
            {
                if (useAllTypeArgs || tp.Characteristics.MustSupportZeroInitialization)
                {
                    wr.Write("${0}{1}", prefix, "rtd_" + tp.CompileName);
                    prefix = ", ";
                    c++;
                }
            }
            return c;
        }

        protected override int EmitRuntimeTypeDescriptorsActuals(List<Type> typeArgs, List<TypeParameter> formals, Bpl.IToken tok, bool useAllTypeArgs, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        string RuntimeTypeDescriptor(Type type, Bpl.IToken tok, TextWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, TargetWriter wr)
        {
            if (createBody)
            {
                wr.Write("{0} function {1}()", isStatic ? "static " : "", name);
                var w = wr.NewBlock("", ";");
                if (!isStatic)
                {
                    w.WriteLine("$_this = this;");
                }
                return w;
            }
            else
            {
                return null;
            }
        }

        protected BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, out TargetWriter setterWriter, TargetWriter wr)
        {
            if (createBody)
            {
                wr.Write("{0} function {1}()", isStatic ? "static " : "", name);
                var wGet = wr.NewBlock("", ";");
                if (!isStatic)
                {
                    wGet.WriteLine("$_this = $this;");
                }

                wr.Write("{0} function {1}($value)", isStatic ? "static " : "", name);
                var wSet = wr.NewBlock("", ";");
                if (!isStatic)
                {
                    wSet.WriteLine("$_this = $this;");
                }

                setterWriter = wSet;
                return wGet;
            }
            else
            {
                setterWriter = null;
                return null;
            }
        }

        protected override void EmitJumpToTailCallStart(TargetWriter wr)
        {
            //            wr.WriteLine("continue TAIL_CALL_START;");
        }

        protected override string TypeName(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member = null)
        {
            Contract.Ensures(Contract.Result<string>() != null);
            Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

            var xType = type.NormalizeExpand();
            if (xType is TypeProxy)
            {
                // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
                return "object";
            }

            if (xType is BoolType)
            {
                return "bool";
            }
            else if (xType is CharType)
            {
                return "string";
            }
            else if (xType is IntType || xType is BigOrdinalType)
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            else if (xType is RealType)
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            else if (xType is BitvectorType)
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            else if (xType.AsNewtype != null && member == null)
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            else if (xType.IsObjectQ)
            {
                return "object";
            }
            else if (xType.IsArrayType)
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            else if (xType is UserDefinedType)
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            else if (xType is SetType)
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            else if (xType is SeqType)
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            else if (xType is MultiSetType)
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            else if (xType is MapType)
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            else
            {
                Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
            }
        }

        public override string TypeInitializationValue(Type type, TextWriter/*?*/ wr, Bpl.IToken/*?*/ tok, bool inAutoInitContext)
        {
            var xType = type.NormalizeExpandKeepConstraints();
            if (xType is BoolType)
            {
                return "false";
            }
            else if (xType is CharType)
            {
                return "'D'";
            }
            else if (xType is IntType || xType is BigOrdinalType)
            {
                return "new BigNumber(0)";
            }
            else if (xType is RealType)
            {
                return "_dafny.BigRational.ZERO";
            }
            else if (xType is BitvectorType)
            {
                var t = (BitvectorType)xType;
                return t.NativeType != null ? "0" : "new BigNumber(0)";
            }
            else if (xType is SetType)
            {
                return "_dafny.Set.Empty";
            }
            else if (xType is MultiSetType)
            {
                return "_dafny.MultiSet.Empty";
            }
            else if (xType is SeqType)
            {
                return "_dafny.Seq.of()";
            }
            else if (xType is MapType)
            {
                return "_dafny.Map.Empty";
            }

            var udt = (UserDefinedType)xType;
            if (udt.ResolvedParam != null)
            {
                if (inAutoInitContext && !udt.ResolvedParam.Characteristics.MustSupportZeroInitialization)
                {
                    return "undefined";
                }
                else
                {
                    return string.Format("{0}->Default", RuntimeTypeDescriptor(udt, udt.tok, wr));
                }
            }
            var cl = udt.ResolvedClass;
            Contract.Assert(cl != null);
            if (cl is NewtypeDecl)
            {
                var td = (NewtypeDecl)cl;
                if (td.Witness != null)
                {
                    return TypeName_UDT(FullTypeName(udt), udt.TypeArgs, wr, udt.tok) + ".Witness";
                }
                else if (td.NativeType != null)
                {
                    return "0";
                }
                else
                {
                    return TypeInitializationValue(td.BaseType, wr, tok, inAutoInitContext);
                }
            }
            else if (cl is SubsetTypeDecl)
            {
                var td = (SubsetTypeDecl)cl;
                if (td.Witness != null)
                {
                    return TypeName_UDT(FullTypeName(udt), udt.TypeArgs, wr, udt.tok) + ".Witness";
                }
                else if (td.WitnessKind == SubsetTypeDecl.WKind.Special)
                {
                    // WKind.Special is only used with -->, ->, and non-null types:
                    Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
                    if (ArrowType.IsPartialArrowTypeName(td.Name))
                    {
                        return "null";
                    }
                    else if (ArrowType.IsTotalArrowTypeName(td.Name))
                    {
                        var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, inAutoInitContext);
                        // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) => rangeDefaultValue)
                        return string.Format("function () {{ return {0}; }}", rangeDefaultValue);
                    }
                    else if (((NonNullTypeDecl)td).Class is ArrayClassDecl)
                    {
                        // non-null array type; we know how to initialize them
                        var arrayClass = (ArrayClassDecl)((NonNullTypeDecl)td).Class;
                        if (arrayClass.Dims == 1)
                        {
                            return "[]";
                        }
                        else
                        {
                            return string.Format("_dafny.newArray(null, {0})", Util.Comma(arrayClass.Dims, _ => "0"));
                        }
                    }
                    else
                    {
                        // non-null (non-array) type
                        // even though the type doesn't necessarily have a known initializer, it could be that the the compiler needs to
                        // lay down some bits to please the C#'s compiler's different definite-assignment rules.
                        return "null";
                    }
                }
                else
                {
                    return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, inAutoInitContext);
                }
            }
            else if (cl is ClassDecl)
            {
                bool isHandle = true;
                if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle)
                {
                    return "0";
                }
                else
                {
                    return "null";
                }
            }
            else if (cl is DatatypeDecl)
            {
                var dt = (DatatypeDecl)cl;
                var s = dt is TupleTypeDecl ? "_dafny.Tuple" : FullTypeName(udt);
                var w = new TargetWriter();
                w.Write("{0}.Rtd(", s);
                List<TypeParameter> usedTypeFormals;
                List<Type> usedTypeArgs;
                UsedTypeParameters(dt, udt.TypeArgs, out usedTypeFormals, out usedTypeArgs);
                EmitRuntimeTypeDescriptorsActuals(usedTypeArgs, usedTypeFormals, udt.tok, true, w);
                w.Write(").Default");
                return w.ToString();
            }
            else
            {
                Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
            }
        }

        protected override string TypeName_UDT(string fullCompileName, List<Type> typeArgs, TextWriter wr, Bpl.IToken tok)
        {
            Contract.Assume(fullCompileName != null);  // precondition; this ought to be declared as a Requires in the superclass
            Contract.Assume(typeArgs != null);  // precondition; this ought to be declared as a Requires in the superclass
            string s = IdProtect(fullCompileName);
            return s;
        }

        protected override string TypeName_Companion(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member)
        {
            // There are no companion classes for PHP
            return TypeName(type, wr, tok, member);
        }

        // ----- Declarations -------------------------------------------------------------

        protected void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs, TargetWriter wr)
        {
            if (isStatic)
            {
                var w = wr.NewNamedBlock("public static function {0}()", name);
                EmitReturnExpr(rhs, w);
            }
            else
            {
                wr.WriteLine("$this->{0} = {1};", name, rhs);
            }
        }

        protected override bool DeclareFormal(string prefix, string name, Type type, Bpl.IToken tok, bool isInParam, TextWriter wr)
        {
            if (isInParam)
            {
                wr.Write("{0}{1}", prefix, name);
                return true;
            }
            else
            {
                return false;
            }
        }

        protected override void DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, bool leaveRoomForRhs, string/*?*/ rhs, TargetWriter wr)
        {
            if (type != null)
            {
                wr.WriteLine("/** @var {0} {1} */", type.ToString(), name);
            }
            wr.Write("{0}", name);
            if (leaveRoomForRhs)
            {
                Contract.Assert(rhs == null);  // follows from precondition
            }
            else if (rhs != null)
            {
                wr.WriteLine(" = {0};", rhs);
            }
            else
            {
                // Safe default.
                wr.WriteLine(" = null; // undefined");
            }
        }

        protected override TargetWriter DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, TargetWriter wr)
        {
            wr.Write("{0} = ", name);
            var w = wr.Fork();
            wr.WriteLine(";");
            return w;
        }

        protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;

        protected override void DeclareOutCollector(string collectorVarName, TargetWriter wr)
        {
            wr.Write("{0} = ", collectorVarName);
        }

        protected override void DeclareLocalOutVar(string name, Type type, Bpl.IToken tok, string rhs, bool useReturnStyleOuts, TargetWriter wr)
        {
            DeclareLocalVar(name, type, tok, false, rhs, wr);
        }

        protected override void EmitOutParameterSplits(string outCollector, List<string> actualOutParamNames, TargetWriter wr)
        {
            if (actualOutParamNames.Count == 1)
            {
                EmitAssignment(actualOutParamNames[0], null, outCollector, null, wr);
            }
            else
            {
                for (var i = 0; i < actualOutParamNames.Count; i++)
                {
                    wr.WriteLine("{0} = {1}[{2}];", actualOutParamNames[i], outCollector, i);
                }
            }
        }

        protected override void EmitActualTypeArgs(List<Type> typeArgs, Bpl.IToken tok, TextWriter wr)
        {
            // emit nothing
        }

        protected override string GenerateLhsDecl(string target, Type/*?*/ type, TextWriter wr, Bpl.IToken tok)
        {
            return target;
        }

        // ----- Statements -------------------------------------------------------------

        protected override void EmitPrintStmt(TargetWriter wr, Expression arg)
        {
            // wr.Write("echo _dafny.toString(");
            wr.Write("echo ");
            TrExpr(arg, wr, false);
            wr.WriteLine(";");
        }

        protected override void EmitReturn(List<Formal> outParams, TargetWriter wr)
        {
            outParams = outParams.Where(f => !f.IsGhost).ToList();
            if (outParams.Count == 0)
            {
                wr.WriteLine("return;");
            }
            else if (outParams.Count == 1)
            {
                wr.WriteLine("return {0};", IdName(outParams[0]));
            }
            else
            {
                wr.WriteLine("return [{0}];", Util.Comma(outParams, IdName));
            }
        }

        protected override TargetWriter CreateLabeledCode(string label, TargetWriter wr)
        {
            return wr.NewNamedBlock("L{0}:", label);
        }

        protected override void EmitBreak(string/*?*/ label, TargetWriter wr)
        {
            if (label == null)
            {
                wr.WriteLine("break;");
            }
            else
            {
                wr.WriteLine("break L{0};", label);
            }
        }

        protected override void EmitYield(TargetWriter wr)
        {
            wr.WriteLine("yield null;");
        }

        protected override void EmitAbsurd(string/*?*/ message, TargetWriter wr)
        {
            if (message == null)
            {
                message = "unexpected control point";
            }
            wr.WriteLine("throw new Error(\"{0}\");", message);
        }

        protected override BlockTargetWriter CreateForLoop(string indexVar, string bound, TargetWriter wr)
        {
            return wr.NewNamedBlock("for (${0} = 0; ${0} < ${1}; ++${0})", indexVar, bound);
        }

        protected override BlockTargetWriter CreateDoublingForLoop(string indexVar, int start, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitIncrementVar(string varName, TargetWriter wr)
        {
            wr.WriteLine("${0} = {0}->plus(1);", varName);
        }

        protected override void EmitDecrementVar(string varName, TargetWriter wr)
        {
            wr.WriteLine("${0} = {0}->minus(1);", varName);
        }

        protected override string GetQuantifierName(string bvType)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override BlockTargetWriter CreateForeachLoop(string boundVar, Type/*?*/ boundVarType, out TargetWriter collectionWriter, TargetWriter wr, string/*?*/ altBoundVarName = null, Type/*?*/ altVarType = null, Bpl.IToken/*?*/ tok = null)
        {
            wr.Write("for (${0} of $", boundVar);
            collectionWriter = wr.Fork();
            if (altBoundVarName == null)
            {
                return wr.NewBlock(")");
            }
            else if (altVarType == null)
            {
                return wr.NewBlockWithPrefix(")", "${0} = ${1};", altBoundVarName, boundVar);
            }
            else
            {
                return wr.NewBlockWithPrefix(")", "${0} = ${1};", altBoundVarName, boundVar);
            }
        }

        // ----- Expressions -------------------------------------------------------------

        protected override void EmitNew(Type type, Bpl.IToken tok, CallStmt/*?*/ initCall, TargetWriter wr)
        {
            var cl = (type.NormalizeExpand() as UserDefinedType)?.ResolvedClass;
            if (cl != null && cl.Name == "object")
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            else
            {
                wr.Write("new {0}(", TypeName(type, wr, tok));
                EmitRuntimeTypeDescriptorsActuals(type.TypeArgs, cl.TypeArgs, tok, false, wr);
                wr.Write(")");
            }
        }

        protected override void EmitNewArray(Type elmtType, Bpl.IToken tok, List<Expression> dimensions, bool mustInitialize, TargetWriter wr)
        {
            var initValue = mustInitialize ? DefaultValue(elmtType, wr, tok) : null;
            if (dimensions.Count == 1)
            {
                // handle the common case of 1-dimensional arrays separately
                wr.Write("array_fill(0, ");
                TrParenExpr(dimensions[0], wr, false);
                if (initValue != null)
                {
                    wr.Write(", {0}", initValue);
                }
                wr.Write(")");
            }
            else
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
        }

        protected override void EmitLiteralExpr(TextWriter wr, LiteralExpr e)
        {
            if (e is StaticReceiverExpr)
            {
                wr.Write(TypeName(e.Type, wr, e.tok));
            }
            else if (e.Value == null)
            {
                wr.Write("null");
            }
            else if (e.Value is bool)
            {
                wr.Write((bool)e.Value ? "true" : "false");
            }
            else if (e is CharLiteralExpr)
            {
                var v = (string)e.Value;
                wr.Write("'{0}'", v);  // PHP doesn't have a \0
            }
            else if (e is StringLiteralExpr)
            {
                var str = (StringLiteralExpr)e;
                // TODO: the string should be converted to a Dafny seq<char>
                TrStringLiteral(str, wr);
            }
            else if (AsNativeType(e.Type) != null)
            {
                wr.Write((BigInteger)e.Value);
            }
            else if (e.Value is BigInteger)
            {
                var i = (BigInteger)e.Value;
                EmitIntegerLiteral(i, wr);
            }
            else if (e.Value is Basetypes.BigDec)
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            else
            {
                Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
            }
        }
        void EmitIntegerLiteral(BigInteger i, TextWriter wr)
        {
            Contract.Requires(wr != null);
            if (i.IsZero)
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            else if (i.IsOne)
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
            else if (-0x20_0000_0000_0000L < i && i < 0x20_0000_0000_0000L)
            {
                wr.Write("{0}", i);
            }
        }

        protected override void EmitStringLiteral(string str, bool isVerbatim, TextWriter wr)
        {
            var n = str.Length;
            if (!isVerbatim)
            {
                wr.Write("\"{0}\"", str);
            }
            else
            {
                wr.Write("\"");
                for (var i = 0; i < n; i++)
                {
                    if (str[i] == '\"' && i + 1 < n && str[i + 1] == '\"')
                    {
                        wr.Write("\\\"");
                        i++;
                    }
                    else if (str[i] == '\\')
                    {
                        wr.Write("\\\\");
                    }
                    else if (str[i] == '\n')
                    {
                        wr.Write("\\n");
                    }
                    else if (str[i] == '\r')
                    {
                        wr.Write("\\r");
                    }
                    else
                    {
                        wr.Write(str[i]);
                    }
                }
                wr.Write("\"");
            }
        }

        protected override TargetWriter EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, TargetWriter wr, bool inLetExprBody, FCE_Arg_Translator tr)
        {
            string nativeName = null, literalSuffix = null;
            bool needsCast = false;
            var nativeType = AsNativeType(e0.Type);
            if (nativeType != null)
            {
                GetNativeInfo(nativeType.Sel, out nativeName, out literalSuffix, out needsCast);
            }

            var bv = e0.Type.AsBitVectorType;
            if (bv.Width == 0)
            {
                tr(e0, wr, inLetExprBody);
            }
            else
            {
                throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
            }
        }

        protected override void EmitEmptyTupleList(string tupleTypeArgs, TargetWriter wr)
        {
            wr.Write("[]", tupleTypeArgs);
        }

        protected override TargetWriter EmitAddTupleToList(string ingredients, string tupleTypeArgs, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitTupleSelect(string prefix, int i, TargetWriter wr)
        {
            wr.Write("{0}[{1}]", prefix, i);
        }

        protected override string IdProtect(string name)
        {
            return PublicIdProtect(name);
        }

        public static string PublicIdProtect(string name)
        {
            Contract.Requires(name != null);
            switch (name)
            {
                case "arguments":
                case "await":
                case "boolean":
                case "byte":
                case "catch":
                case "continue":
                case "debugger":
                case "default":
                case "delete":
                case "do":
                case "double":
                case "enum":
                case "eval":
                case "final":
                case "finally":
                case "float":
                case "for":
                case "goto":
                case "implements":
                case "instanceof":
                case "interface":
                case "let":
                case "long":
                case "native":
                case "package":
                case "private":
                case "protected":
                case "public":
                case "short":
                case "super":
                case "switch":
                case "synchronized":
                case "throw":
                case "throws":
                case "transient":
                case "try":
                case "typeof":
                case "void":
                case "volatile":
                case "with":
                    return "_" + name + "_";
                default:
                    return name;
            }
        }

        protected override string FullTypeName(UserDefinedType udt, MemberDecl/*?*/ member = null)
        {
            Contract.Assume(udt != null);  // precondition; this ought to be declared as a Requires in the superclass
            if (udt is ArrowType)
            {
                return ArrowType.Arrow_FullCompileName;
            }
            var cl = udt.ResolvedClass;
            if (cl == null)
            {
                return IdProtect(udt.CompileName);
            }
            else if (cl is ClassDecl cdecl && cdecl.IsDefaultClass && Attributes.Contains(cl.Module.Attributes, "extern") &&
            member != null && Attributes.Contains(member.Attributes, "extern"))
            {
                // omit the default class name ("_default") in extern modules, when the class is used to qualify an extern member
                Contract.Assert(!cl.Module.IsDefaultModule);  // default module is not marked ":extern"
                return IdProtect(cl.Module.CompileName);
            }
            else
            {
                return IdProtect(cl.Module.CompileName) + "\\" + IdProtect(cl.CompileName);
            }
        }

        protected override void EmitThis(TargetWriter wr)
        {
            wr.Write("$_this");
        }

        protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, TargetWriter wr)
        {
            var dt = dtv.Ctor.EnclosingDatatype;
            EmitDatatypeValue(dt, dtv.Ctor, dtv.IsCoCall, arguments, wr);
        }

        void EmitDatatypeValue(DatatypeDecl dt, DatatypeCtor ctor, bool isCoCall, string arguments, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, out string compiledName, out string preString, out string postString)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override TargetWriter EmitMemberSelect(MemberDecl member, bool isLValue, Type expectedType, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override TargetWriter EmitArraySelect(List<string> indices, Type elmtType, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override TargetWriter EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override string ArrayIndexToInt(string arrayIndex)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value, bool inLetExprBody, TargetWriter wr, bool nativeIndex = false)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitSeqSelectRange(Expression source, Expression/*?*/ lo, Expression/*?*/ hi, bool fromArray, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitApplyExpr(Type functionType, Bpl.IToken tok, Expression function, List<Expression> arguments, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override TargetWriter EmitBetaRedex(List<string> boundVars, List<Expression> arguments, string typeArgs, List<Type> boundTypes, Type resultType, Bpl.IToken tok, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, Type bvType, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override BlockTargetWriter CreateLambda(List<Type> inTypes, Bpl.IToken tok, List<string> inNames, Type resultType, TargetWriter wr, bool untyped = false)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override TargetWriter CreateIIFE_ExprBody(Expression source, bool inLetExprBody, Type sourceType, Bpl.IToken sourceTok, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr)
        {
            var w = wr.NewExprBlock("function ({0})", bvName);
            w.Write("return ");
            w.BodySuffix = ";" + w.NewLine;
            TrParenExpr(source, wr, inLetExprBody);
            return w;
        }

        protected override TargetWriter CreateIIFE_ExprBody(string source, Type sourceType, Bpl.IToken sourceTok, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override BlockTargetWriter CreateIIFE0(Type resultType, Bpl.IToken resultTok, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override BlockTargetWriter CreateIIFE1(int source, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        bool IsDirectlyComparable(Type t)
        {
            Contract.Requires(t != null);
            return t.IsBoolType || t.IsCharType || AsNativeType(t) != null || t.IsRefType;
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
          TextWriter errorWr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitIsZero(string varName, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitCollectionDisplay(CollectionType ct, Bpl.IToken tok, List<Expression> elements, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitMapDisplay(MapType mt, Bpl.IToken tok, List<ExpressionPair> elements, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitCollectionBuilder_New(CollectionType ct, Bpl.IToken tok, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override void EmitCollectionBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override TargetWriter EmitMapBuilder_Add(MapType mt, Bpl.IToken tok, string collName, Expression term, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException("This is not currently implemented in the PHP compiler.");
        }

        protected override string GetCollectionBuilder_Build(CollectionType ct, Bpl.IToken tok, string collName, TargetWriter wr)
        {
            // collections are built in place
            return collName;
        }

        protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, TargetWriter wr)
        {
            TrParenExpr("$_dafny->SingleValue", e, wr, inLetExprBody);
        }

        // ----- Target compilation and execution -------------------------------------------------------------

        public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
          bool hasMain, bool runAfterCompile, TextWriter outputWriter, out object compilationResult)
        {
            compilationResult = null;
            if (!DafnyOptions.O.RunAfterCompile || callToMain == null)
            {
                // compile now
                return SendToNewPhpProcess(dafnyProgramName, targetProgramText, null, targetFilename, otherFileNames, outputWriter);
            }
            else
            {
                // Since the program is to be run soon, nothing further is done here. Any compilation errors (that is, any errors
                // in the emitted program--this should never happen if the compiler itself is correct) will be reported as 'node'
                // will run the program.
                return true;
            }
        }

        public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string targetFilename, ReadOnlyCollection<string> otherFileNames,
          object compilationResult, TextWriter outputWriter)
        {

            return SendToNewPhpProcess(dafnyProgramName, targetProgramText, callToMain, targetFilename, otherFileNames, outputWriter);
        }

        bool SendToNewPhpProcess(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string targetFilename, ReadOnlyCollection<string> otherFileNames,
          TextWriter outputWriter)
        {
            Contract.Requires(targetFilename != null || otherFileNames.Count == 0);

            var args = targetFilename != null && otherFileNames.Count == 0 ? targetFilename : "";
            var psi = new ProcessStartInfo("php", args)
            {
                CreateNoWindow = true,
                UseShellExecute = false,
                RedirectStandardInput = true,
                RedirectStandardOutput = false,
                RedirectStandardError = false,
            };

            try
            {
                using (var phpProcess = Process.Start(psi))
                {
                    if (args == "")
                    {
                        foreach (var filename in otherFileNames)
                        {
                            WriteFromFile(filename, phpProcess.StandardInput);
                        }
                        phpProcess.StandardInput.Write(targetProgramText);
                        if (callToMain != null)
                        {
                            phpProcess.StandardInput.Write(callToMain);
                        }
                        phpProcess.StandardInput.Flush();
                        phpProcess.StandardInput.Close();
                    }
                    phpProcess.WaitForExit();
                    return phpProcess.ExitCode == 0;
                }
            }
            catch (System.ComponentModel.Win32Exception e)
            {
                outputWriter.WriteLine("Error: Unable to start php ({0}): {1}", psi.FileName, e.Message);
                return false;
            }
        }
    }
}
