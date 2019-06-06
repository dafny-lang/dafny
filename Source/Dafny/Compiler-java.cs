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
    public class JavaCompiler : Compiler {
        public JavaCompiler (ErrorReporter reporter)
            : base(reporter) {
        }

        public override String TargetLanguage => "Java";

        private String ModuleName;
        private String MainModuleName;
        
        private static List<Import> StandardImports =
            new List<Import> {
                new Import { Name = "_dafny", Path = "dafny" },
            };
        private readonly List<Import> Imports = new List<Import>(StandardImports);
        
        //RootImportWriter writes additional imports to the main file.
        private TargetWriter RootImportWriter;
        private TargetWriter RootImportDummyWriter;
        
        private struct Import {
            public string Name, Path;
            public bool SuppressDummy; // TODO: Not sure what this does, might not need it? (Copied from Compiler-go.cs)
        }
        
        protected override void EmitHeader(Program program, TargetWriter wr) {
            wr.WriteLine("// Dafny program {0} compiled into Java", program.Name);
            
            ModuleName = MainModuleName = HasMain(program, out _) ? "main" : Path.GetFileNameWithoutExtension(program.Name);
            
            wr.WriteLine("package {0};", ModuleName);
            wr.WriteLine();
            // Keep the import writers so that we can import subsequent modules into the main one
            EmitImports(wr, out RootImportWriter, out RootImportDummyWriter);
            // TODO: Finish this method override
        }
        
        // TODO: Same format as compiler-go.cs, might need to follow C# depending on how DafnyRuntime.java looks
        protected override void EmitBuiltInDecls(BuiltIns builtIns, TargetWriter wr) {
            var rt = wr.NewFile("dafny/dafny.java");
//            ReadRuntimeSystem("DafnyRuntime.java", rt); Commented out beceause DafnyRuntime.java does not exist yet.
        }

        // Creates file header for each module's file.
        // TODO: Finish the part after EmitImports
        void EmitModuleHeader(TargetWriter wr) {
            wr.WriteLine("// Package {0}", ModuleName);
            wr.WriteLine("// Dafny module {0} compiled into Java", ModuleName);
            wr.WriteLine();
            wr.WriteLine("package {0};", ModuleName);
            wr.WriteLine();
            wr.WriteLine("import java.*;"); // TODO: See if it is really necessary to import all of Java, though C# compiler imports all of System
            EmitImports(wr, out _, out _);
        }

        void EmitImports(TargetWriter wr, out TargetWriter importWriter, out TargetWriter importDummyWriter) {
            throw new NotImplementedException();
            importDummyWriter = wr.ForkSection();
            foreach (var import in Imports) {
                EmitImport(import, wr, importDummyWriter);
            }
        }
        
        // TODO: Figure out what importDummyWriter is and whether we need it or not.
        private void EmitImport(Import import, TargetWriter importWriter, TargetWriter importDummyWriter) {
//            var id = IdProtect(import.Name);
            var path = import.Path;

            importWriter.WriteLine("import {0}.*;", path);
            importWriter.WriteLine();

//            if (!import.SuppressDummy) {
//                importDummyWriter.WriteLine("var _ {0}.{1}", id, DummyTypeName);
//            }
        }

        // TODO: Function needs to follow Go format because module will be in a separate file, so add module to Imports list
        protected override TargetWriter CreateModule(string moduleName, bool isDefault, bool isExtern, string /*?*/ libraryName, TargetWriter wr) {
            string pkgName = IdProtect(moduleName);
            var import = new Import{ Name=moduleName, Path=pkgName };
            var filename = string.Format("{0}/{0}.java", pkgName);
            var w = wr.NewFile(filename);
            ModuleName = moduleName;
            EmitModuleHeader(w);
            
            var s = string.Format("package {0};", IdProtect(moduleName));
            return wr.NewBigBlock(s, " // end of " + s);
        }

        protected override string GetHelperModuleName()
        {
            throw new NotImplementedException();
        }


        //TODO: Complete ClassWriter class, CreateClass function, TrExpr function
        protected override void DeclareSubsetType(SubsetTypeDecl sst, TargetWriter wr) {
            ClassWriter cw = CreateClass(IdName(sst), sst.TypeArgs, wr) as ClassWriter;
            if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
                var sw = new TargetWriter(cw.InstanceMemberWriter.IndentLevel, true);
                TrExpr(sst.Witness, sw, false);
                cw.DeclareField("Witness", true, true, sst.Rhs, sst.tok, sw.ToString());
            }
        }

        protected class ClassWriter : IClassWriter {
            public readonly JavaCompiler Compiler;
            public readonly BlockTargetWriter InstanceMemberWriter;
            public readonly BlockTargetWriter StaticMemberWriter;
            
            public ClassWriter(JavaCompiler compiler, BlockTargetWriter instanceMemberWriter, BlockTargetWriter staticMemberWriter = null) {
                Contract.Requires(compiler != null);
                Contract.Requires(instanceMemberWriter != null);
                this.Compiler = compiler;
                this.InstanceMemberWriter = instanceMemberWriter;
                this.StaticMemberWriter = staticMemberWriter == null ? instanceMemberWriter : staticMemberWriter;
            }

            public BlockTargetWriter Writer(bool isStatic) {
                return isStatic ? StaticMemberWriter : InstanceMemberWriter;
            }
            
            // TODO: Define all of these undefined methods.
            public BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody) {
                return Compiler.CreateMethod(m, createBody, Writer(m.IsStatic));
            }
            public BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member) {
                throw new NotImplementedException();
//                return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, Writer(isStatic));
            }
            public BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member) {
                throw new NotImplementedException();
//                return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, Writer(isStatic));
            }
            public BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member, out TargetWriter setterWriter) {
                throw new NotImplementedException();
//                return Compiler.CreateGetterSetter(name, resultType, tok, isStatic, createBody, out setterWriter, Writer(isStatic));
            }
            public void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs) {
                throw new NotImplementedException();
//                Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, Writer(isStatic));
            }
            public TextWriter/*?*/ ErrorWriter() => InstanceMemberWriter;

            public void Finish() { }
        }
        
        protected BlockTargetWriter CreateMethod(Method m, bool createBody, TargetWriter wr) {
            string targetReturnTypeReplacement = null;
            foreach (var p in m.Outs) {
                if (!p.IsGhost) {
                    if (targetReturnTypeReplacement == null) {
                        targetReturnTypeReplacement = TypeName(p.Type, wr, p.tok);
                    } else if (targetReturnTypeReplacement != null) {
                        // there's more than one out-parameter, so bail
                        targetReturnTypeReplacement = null;
                        break;
                    }
                }
            }
            wr.Write("{0}{1}", createBody ? "public " : "", m.IsStatic ? "static " : "");
            if (m.TypeArgs.Count != 0) {
                wr.Write("<{0}>", TypeParameters(m.TypeArgs));
            }
            wr.WriteLine("{0} {1}", targetReturnTypeReplacement ?? "void", IdName(m));
            
            wr.Write("(");
            WriteFormals("", m.Ins, wr);
            
            if (!createBody) {
                wr.WriteLine(");");
                return null;
            } else {
                var w = wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
                // TODO: Maybe later, add optimization for tail-recursion and remove the comments
                // TODO: Figure out what implication static has on declaring this, whether it is necessary, and how to get current class name
                /*if (m.IsTailRecursive) {
                    if (!m.IsStatic) {
                        w.WriteLine("var _this = this;");
                    }
                    w.IndentLess(); w.WriteLine("TAIL_CALL_START: ;");
                }*/
                return w;
            }
        }
        
        string TypeParameters(List<TypeParameter> targs) {
            Contract.Requires(cce.NonNullElements(targs));
            Contract.Ensures(Contract.Result<string>() != null);

            return Util.Comma(targs, tp => IdName(tp));
        }
        
        // Function copied and pasted from Compiler-Csharp.cs, will be modified later if deemed necessary.
        protected override string TypeName(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member = null) { 
            Contract.Ensures(Contract.Result<string>() != null); 
            Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass
            
            var xType = type.NormalizeExpand(); 
            if (xType is TypeProxy) { 
                // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
                return "object"; 
            }
            
            if (xType is BoolType) { 
                return "bool"; 
            } else if (xType is CharType) { 
                return "char"; 
            } else if (xType is IntType || xType is BigOrdinalType) { 
                return "BigInteger"; 
            } else if (xType is RealType) { 
                return "Dafny.BigRational"; //TODO: change the data structure to match the one in DafnyRuntime.java
            } else if (xType is BitvectorType) { 
                var t = (BitvectorType)xType; 
                return t.NativeType != null ? GetNativeTypeName(t.NativeType) : "BigInteger"; 
            } else if (xType.AsNewtype != null) { 
                var nativeType = xType.AsNewtype.NativeType; 
                if (nativeType != null) { 
                    return GetNativeTypeName(nativeType); 
                } 
                return TypeName(xType.AsNewtype.BaseType, wr, tok); 
            } else if (xType.IsObjectQ) { 
                return "object"; 
            } else if (xType.IsArrayType) { 
                ArrayClassDecl at = xType.AsArrayType; 
                Contract.Assert(at != null);  // follows from type.IsArrayType
                Type elType = UserDefinedType.ArrayElementType(xType);
                string typeNameSansBrackets, brackets; 
                TypeName_SplitArrayName(elType, wr, tok, out typeNameSansBrackets, out brackets); 
                return typeNameSansBrackets + TypeNameArrayBrackets(at.Dims) + brackets; 
            } else if (xType is UserDefinedType) { 
                var udt = (UserDefinedType)xType; 
                var s = FullTypeName(udt, member); 
                var cl = udt.ResolvedClass; 
                bool isHandle = true; 
                if (cl != null && Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) { 
                    return "ulong"; //TODO: Make sure DafnyRuntime.java has a data structure to handle unsigned longs.
                } else if (DafnyOptions.O.IronDafny && 
                           !(xType is ArrowType) && 
                           cl != null && 
                           cl.Module != null && 
                           !cl.Module.IsDefaultModule) { 
                    s = cl.FullCompileName; 
                } 
                return TypeName_UDT(s, udt.TypeArgs, wr, udt.tok); 
            } else if (xType is SetType) { 
                Type argType = ((SetType)xType).Arg; 
                if (ComplicatedTypeParameterForCompilation(argType)) { 
                    Error(tok, "compilation of set<TRAIT> is not supported; consider introducing a ghost", wr); 
                } 
                return DafnySetClass + "<" + TypeName(argType, wr, tok) + ">"; 
            } else if (xType is SeqType) { 
                Type argType = ((SeqType)xType).Arg; 
                if (ComplicatedTypeParameterForCompilation(argType)) { 
                    Error(tok, "compilation of seq<TRAIT> is not supported; consider introducing a ghost", wr); 
                } 
                return DafnySeqClass + "<" + TypeName(argType, wr, tok) + ">"; 
            } else if (xType is MultiSetType) { 
                Type argType = ((MultiSetType)xType).Arg; 
                if (ComplicatedTypeParameterForCompilation(argType)) { 
                    Error(tok, "compilation of multiset<TRAIT> is not supported; consider introducing a ghost", wr); 
                } 
                return DafnyMultiSetClass + "<" + TypeName(argType, wr, tok) + ">"; 
            } else if (xType is MapType) { 
                Type domType = ((MapType)xType).Domain; 
                Type ranType = ((MapType)xType).Range; 
                if (ComplicatedTypeParameterForCompilation(domType) || ComplicatedTypeParameterForCompilation(ranType)) { 
                    Error(tok, "compilation of map<TRAIT, _> or map<_, TRAIT> is not supported; consider introducing a ghost", wr); 
                } 
                return DafnyMapClass + "<" + TypeName(domType, wr, tok) + "," + TypeName(ranType, wr, tok) + ">"; 
            } else { 
                Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
            }
        }
        
        // Copied from Compiler-C#, seemed most applicable to Java compiler due to similar data types.
        // TODO: verify, change if necessary to match Java language specifications
        protected override string FullTypeName(UserDefinedType udt, MemberDecl/*?*/ member = null) {
            Contract.Assume(udt != null);  // precondition; this ought to be declared as a Requires in the superclass
            if (udt is ArrowType) {
                return ArrowType.Arrow_FullCompileName;
            }
            var cl = udt.ResolvedClass;
            if (cl == null) {
                return IdProtect(udt.CompileName);
            } else if (cl.Module.IsDefaultModule) {
                return IdProtect(cl.CompileName);
            } else {
                return IdProtect(cl.Module.CompileName) + "." + IdProtect(cl.CompileName);
            }
        }
        
        protected override bool DeclareFormal(string prefix, string name, Type type, Bpl.IToken tok, bool isInParam, TextWriter wr)
        {
            if (isInParam) {
                wr.Write("{0}{1} {2}", prefix, TypeName(type, wr, tok), name);
                return true;
            } else {
                return false;
            }
        }
        
        protected override string TypeName_UDT(string fullCompileName, List<Type> typeArgs, TextWriter wr, Bpl.IToken tok) {
            Contract.Assume(fullCompileName != null);  // precondition; this ought to be declared as a Requires in the superclass
            Contract.Assume(typeArgs != null);  // precondition; this ought to be declared as a Requires in the superclass
            string s = IdProtect(fullCompileName);
            if (typeArgs.Count != 0) {
                if (typeArgs.Exists(ComplicatedTypeParameterForCompilation)) {
                    Error(tok, "compilation does not support trait types as a type parameter; consider introducing a ghost", wr);
                }
                s += "<" + TypeNames(typeArgs, wr, tok) + ">";
            }
            return s;
        }

        protected override string IdProtect(string name) {
            return PublicIdProtect(name);
        }

        public static string PublicIdProtect(string name)
        {
            if (name == "" || name.First() == '_')
            {
                return name; // no need to further protect this name
            }

            // TODO: Finish with all the public IDs that need to be protected
            switch (name)
            {
                //keywords Java 8 and before
                // https://docs.oracle.com/javase/tutorial/java/nutsandbolts/_keywords.html
                case "abstract":
                case "assert":
                case "break":
                case "byte":
                case "case":
                case "catch":
                case "char":
                case "class":
                case "continue":
                case "default":
                case "do":
                case "double":
                case "else":
                case "enum":
                case "extends":
                case "final":
                case "finally":
                case "float":
                case "for":
                case "if":
                case "implements":
                case "import":
                case "instanceof":
                case "int":
                case "interface":
                case "long":
                case "native":
                case "new":
                case "package":
                case "private":
                case "protected":
                case "public":
                case "return":
                case "short":
                case "static":
                case "strictfp":
                case "super":
                case "switch":
                case "synchronized":
                case "this":
                case "throw":
                case "throws":
                case "transient":
                case "try":
                case "void":
                case "volatile":
                case "while":
                // keywords since Java 9
                case "exports":
                case "module":
                case "requires":
                // no longer used in Java but still reserved as keywords
                case "const":
                case "goto":
                // special identifiers since Java 10
                case "var":
                // literal values
                case "false":
                case "null":
                case "true":
                    return name + "_"; // TODO: figure out what to do here (C# uses @, Go uses _, JS uses _$$_)
                default:
                    return name; //Package name is not a keyword, so it can be used
            }
        }
        
        // ABSTRACT METHOD DECLARATIONS FOR THE SAKE OF BUILDING PROGRAM
        protected override BlockTargetWriter CreateStaticMain(IClassWriter wr)
        {
            throw new NotImplementedException();
        }
        
        protected override void EmitJumpToTailCallStart(TargetWriter wr)
        {
            throw new NotImplementedException();
        }
        
        public override string TypeInitializationValue(Type type, TextWriter wr, Bpl.IToken tok, bool inAutoInitContext)
        {
            throw new NotImplementedException();
        }

        protected override string TypeName_Companion(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl member)
        {
            throw new NotImplementedException();
        }

        protected override void DeclareLocalVar(string name, Type type, Bpl.IToken tok, bool leaveRoomForRhs, string rhs, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override TargetWriter DeclareLocalVar(string name, Type type, Bpl.IToken tok, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void DeclareLocalOutVar(string name, Type type, Bpl.IToken tok, string rhs, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitActualTypeArgs(List<Type> typeArgs, Bpl.IToken tok, TextWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override string GenerateLhsDecl(string target, Type type, TextWriter wr, Bpl.IToken tok)
        {
            throw new NotImplementedException();
        }

        protected override void EmitPrintStmt(TargetWriter wr, Expression arg)
        {
            throw new NotImplementedException();
        }

        protected override void EmitReturn(List<Formal> outParams, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override TargetWriter CreateLabeledCode(string label, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitBreak(string label, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitYield(TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitAbsurd(string message, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitThis(TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, out string compiledName, out string preString, out string postString)
        {
            throw new NotImplementedException();
        }

        protected override TargetWriter EmitMemberSelect(MemberDecl member, bool isLValue, Type expectedType, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override TargetWriter EmitArraySelect(List<string> indices, Type elmtType, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override TargetWriter EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value, bool inLetExprBody,
            TargetWriter wr, bool nativeIndex = false)
        {
            throw new NotImplementedException();
        }

        protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray, bool inLetExprBody,
            TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitApplyExpr(Type functionType, Bpl.IToken tok, Expression function, List<Expression> arguments, bool inLetExprBody,
            TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override TargetWriter EmitBetaRedex(List<string> boundVars, List<Expression> arguments, string typeArgs, List<Type> boundTypes, Type resultType,
            Bpl.IToken resultTok, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, Type bvType,
            TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override BlockTargetWriter CreateLambda(List<Type> inTypes, Bpl.IToken tok, List<string> inNames, Type resultType, TargetWriter wr,
            bool untyped = false)
        {
            throw new NotImplementedException();
        }

        protected override TargetWriter CreateIIFE_ExprBody(Expression source, bool inLetExprBody, Type sourceType, Bpl.IToken sourceTok,
            Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override TargetWriter CreateIIFE_ExprBody(string source, Type sourceType, Bpl.IToken sourceTok, Type resultType, Bpl.IToken resultTok,
            string bvName, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override BlockTargetWriter CreateIIFE0(Type resultType, Bpl.IToken resultTok, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op, Expression e0, Expression e1, Bpl.IToken tok, Type resultType, out string opString,
            out string preOpString, out string postOpString, out string callString, out string staticCallString,
            out bool reverseArguments, out bool truncateResult, out bool convertE1_to_int, TextWriter errorWr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitIsZero(string varName, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitCollectionDisplay(CollectionType ct, Bpl.IToken tok, List<Expression> elements, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitMapDisplay(MapType mt, Bpl.IToken tok, List<ExpressionPair> elements, bool inLetExprBody, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitCollectionBuilder_New(CollectionType ct, Bpl.IToken tok, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitCollectionBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody,
            TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override TargetWriter EmitMapBuilder_Add(MapType mt, Bpl.IToken tok, string collName, Expression term, bool inLetExprBody,
            TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override string GetCollectionBuilder_Build(CollectionType ct, Bpl.IToken tok, string collName, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override IClassWriter CreateClass(string name, bool isExtern, string fullPrintName, List<TypeParameter> typeParameters, List<Type> superClasses,
            Bpl.IToken tok, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override IClassWriter CreateTrait(string name, bool isExtern, List<Type> superClasses, Bpl.IToken tok, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override BlockTargetWriter CreateDoublingForLoop(string indexVar, int start, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitIncrementVar(string varName, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitDecrementVar(string varName, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override string GetQuantifierName(string bvType)
        {
            throw new NotImplementedException();
        }

        protected override BlockTargetWriter CreateForeachLoop(string boundVar, Type boundVarType, out TargetWriter collectionWriter,
            TargetWriter wr, string altBoundVarName = null, Type altVarType = null, Bpl.IToken tok = null)
        {
            throw new NotImplementedException();
        }

        protected override BlockTargetWriter CreateForLoop(string indexVar, string bound, TargetWriter wr) {
            throw new Exception();
        }

        protected override void EmitNew(Type type, Bpl.IToken tok, CallStmt initCall, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitNewArray(Type elmtType, Bpl.IToken tok, List<Expression> dimensions, bool mustInitialize, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitLiteralExpr(TextWriter wr, LiteralExpr e)
        {
            throw new NotImplementedException();
        }

        protected override void EmitStringLiteral(string str, bool isVerbatim, TextWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override TargetWriter EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, TargetWriter wr, bool inLetExprBody,
            FCE_Arg_Translator tr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitEmptyTupleList(string tupleTypeArgs, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override TargetWriter EmitAddTupleToList(string ingredients, string tupleTypeArgs, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitTupleSelect(string prefix, int i, TargetWriter wr)
        {
            throw new NotImplementedException();
        }
        
        protected override BlockTargetWriter CreateIIFE1(int source, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr)
        {
            throw new NotImplementedException();
        }
        
        protected override BlockTargetWriter CreateIterator(IteratorDecl iter, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void DeclareDatatype(DatatypeDecl dt, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void DeclareNewtype(NewtypeDecl nt, TargetWriter wr)
        {
            throw new NotImplementedException();
        }
    }
}
