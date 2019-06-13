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
        private TargetWriter RootImportDummyWriter; // TODO: Remove if not deemed necessary.
        
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
            EmitImports(wr, out RootImportWriter);
            wr.WriteLine();
        }
        
        // TODO: Same format as compiler-go.cs, might need to follow C# depending on how DafnyRuntime.java looks
        protected override void EmitBuiltInDecls(BuiltIns builtIns, TargetWriter wr) {
            var rt = wr.NewFile("dafny/dafny.java");
            // ReadRuntimeSystem("DafnyRuntime.java", rt); Commented out beceause DafnyRuntime.java does not exist yet.
        }

        // Creates file header for each module's file.
        void EmitModuleHeader(TargetWriter wr) {
            wr.WriteLine("// Package {0}", ModuleName);
            wr.WriteLine("// Dafny module {0} compiled into Java", ModuleName);
            wr.WriteLine();
            wr.WriteLine("package {0};", ModuleName);
            wr.WriteLine();
            wr.WriteLine("import java.*;"); // TODO: See if it is really necessary to import all of Java, though C# compiler imports all of System
            EmitImports(wr, out _);
            wr.WriteLine();
        }

        void EmitImports(TargetWriter wr, out TargetWriter importWriter) {
            importWriter = wr.ForkSection();
            foreach (var import in Imports) {
                EmitImport(import, importWriter);
            }
        }
        
        private void EmitImport(Import import, TargetWriter importWriter) {
            var path = import.Path;

            importWriter.WriteLine("import {0}.*;", path);
        }
        
        protected override TargetWriter CreateModule(string moduleName, bool isDefault, bool isExtern, string /*?*/ libraryName, TargetWriter wr)
        {
            string pkgName;
            if (libraryName != null) {
                pkgName = libraryName;
            } else {
                pkgName = IdProtect(moduleName);
            }
            var import = new Import{ Name=moduleName, Path=pkgName };
            var filename = string.Format("{0}/{0}.java", pkgName);
            var w = wr.NewFile(filename);
            ModuleName = moduleName;
            EmitModuleHeader(w);
            AddImport(import);
            return w;
        }

        private void AddImport(Import import) {
            EmitImport(import, RootImportWriter);
            Imports.Add(import);
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
            
            public BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody) {
                return Compiler.CreateMethod(m, createBody, Writer(m.IsStatic));
            }
            public BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member) {
                return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, Writer(isStatic));
            }
            
            // TODO: Decide if we need to make the getters/setters, since all fields are public anyway.
            public BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member) {
                throw new NotImplementedException();
                // return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, Writer(isStatic));
            }
            public BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member, out TargetWriter setterWriter) {
                throw new NotImplementedException();
                // return Compiler.CreateGetterSetter(name, resultType, tok, isStatic, createBody, out setterWriter, Writer(isStatic));
            }
            public void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs) {
                Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, Writer(isStatic));
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
            wr.Write("{0} {1}", targetReturnTypeReplacement ?? "void", IdName(m));
            wr.Write("(");
            WriteFormals("", m.Ins, wr);
            if (!createBody) {
                wr.WriteLine(");");
                return null; // We do not want to write a function body, so instead of returning a BTW, we return null.
            } else {
                var w = wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
                // TODO: Maybe later, add optimization for tail-recursion and remove the comments
                // TODO: Figure out what implication static has on declaring this, whether it is necessary, and use Object _this = this;
                /*if (m.IsTailRecursive) {
                    if (!m.IsStatic) {
                        w.WriteLine("var _this = this;");
                    }
                    w.IndentLess(); w.WriteLine("TAIL_CALL_START: ;");
                }*/
                return w;
            }
        }

        protected BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs,
            List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member,
            TargetWriter wr) {
            wr.Write("{0}{1}", createBody ? "public " : "", isStatic ? "static " : "");
            if (typeArgs != null && typeArgs.Count != 0) {
                wr.Write("<{0}>", TypeParameters(typeArgs));
            }
            wr.Write("{0} {1}(", TypeName(resultType, wr, tok), name);
            WriteFormals("", formals, wr);
            if (!createBody) {
                wr.WriteLine(");");
                return null; // We do not want to write a function body, so instead of returning a BTW, we return null.
            } else {
                BlockTargetWriter w;
                if (formals.Count > 1) {
                    w = wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
                } else {
                    w = wr.NewBlock(")");
                }
                return w;
            }
        }

        protected void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs,
            TargetWriter wr) {
            wr.WriteLine("public {0}{1}{2} {3} = {4};", isStatic ? "static " : "", isConst ? "final " : "", TypeName(type, wr, tok), name, rhs);
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
                return "BigDecimal"; //TODO: change the data structure to match the one in DafnyRuntime.java
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
                return "Object"; 
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
                    return "ulong"; // TODO: Make sure DafnyRuntime.java has a data structure to handle unsigned longs.
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
        
        protected override bool DeclareFormal(string prefix, string name, Type type, Bpl.IToken tok, bool isInParam, TextWriter wr) {
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

        protected override IClassWriter CreateClass(string name, bool isExtern, string /*?*/ fullPrintName,
            List<TypeParameter> /*?*/ typeParameters, List<Type> /*?*/ superClasses, Bpl.IToken tok, TargetWriter wr) {
            var filename = string.Format("{0}/{0}.java", name);
            var w = wr.NewFile(filename);
            w.WriteLine("// Class {0}", name);
            w.WriteLine("// Dafny class {0} compiled into Java", name);
            w.WriteLine("package {0};", ModuleName);
            w.WriteLine();
            wr.WriteLine("import java.*;"); // TODO: See if it is really necessary to import all of Java, though C# compiler imports all of System
            EmitImports(w, out _);
            w.WriteLine();
            w.WriteLine("public class {0}", name);
            if (typeParameters != null && typeParameters.Count != 0) {
                w.Write("<{0}>", TypeParameters(typeParameters));
            }
            // Since Java does not support multiple inheritance, we are assuming a list of "superclasses" is a list of interfaces
            if (superClasses != null) {
                string sep = " implements ";
                foreach (var trait in superClasses) {
                    w.Write("{0}{1}", sep, TypeName(trait, w, tok));
                    sep = ", ";
                }
            }
            return new ClassWriter(this, w.NewBlock(""));
        }
        
        protected override void EmitLiteralExpr(TextWriter wr, LiteralExpr e) {
            if (e is StaticReceiverExpr) {
                wr.Write(TypeName(e.Type, wr, e.tok));
            } else if (e.Value == null) {
                wr.Write("({0}) null", TypeName(e.Type, wr, e.tok));
            } else if (e.Value is bool) {
                wr.Write((bool)e.Value ? "true" : "false");
            } else if (e is CharLiteralExpr) {
                wr.Write("'{0}'", (string) e.Value);
            } else if (e is StringLiteralExpr) {
                var str = (StringLiteralExpr)e;
                wr.Write("new DafnyString(");
                TrStringLiteral(str, wr);
                wr.Write(")");
            } else if (AsNativeType(e.Type) != null) {
                string literalSuffix;
                GetNativeInfo(AsNativeType(e.Type).Sel, out _, out literalSuffix, out _);
                wr.Write((BigInteger)e.Value + literalSuffix);
            } else if (e.Value is BigInteger i) {
                wr.Write("new BigInteger(\"{0}\")", i);
            } else if (e.Value is Basetypes.BigDec n) {
                wr.Write("new BigDecimal(\"{0}E{1}\")", n.Mantissa, n.Exponent);
            } else {
                Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
            }
        }
        
        protected override void EmitStringLiteral(string str, bool isVerbatim, TextWriter wr) {
            if (!isVerbatim) {
                wr.Write("\"{0}\"", str);
            } else {
                //TODO: This is taken from Go and JS since Java doesn't have raw string literals, modify and make better if possible.
                var n = str.Length;
                wr.Write("\"");
                for (var i = 0; i < n; i++) {
                    if (str[i] == '\"' && i+1 < n && str[i+1] == '\"') {
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

        protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix,
            out bool needsCastAfterArithmetic) {
            literalSuffix = "";
            needsCastAfterArithmetic = false;
            switch (sel) {
                // TODO: When the unsigned types get created in DafnyRuntime.java, make sure the names match the ones here
                case NativeType.Selection.Byte:
                    name = "Dafny.DafnyByte";
                    break;
                case NativeType.Selection.SByte:
                    name = "byte";
                    break;
                case NativeType.Selection.UShort:
                    name = "Dafny.DafnyUShort";
                    break;
                case NativeType.Selection.Short:
                    name = "short";
                    break;
                case NativeType.Selection.UInt:
                    name = "Dafny.DafnyUInt";
                    break;
                case NativeType.Selection.Int:
                    name = "int";
                    break;
                case NativeType.Selection.ULong:
                    name = "Dafny.DafnyULong";
                    break;
                case NativeType.Selection.Number:
                case NativeType.Selection.Long:
                    name = "long";
                    literalSuffix = "L";
                    break;
                default:
                    Contract.Assert(false);  // unexpected native type
                    throw new cce.UnreachableException();  // to please the compiler
            }
        }
        
        protected override void EmitThis(TargetWriter wr) {
            wr.Write("_this");
        }
        
        protected override void DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, bool leaveRoomForRhs, string/*?*/ rhs, TargetWriter wr) {
            wr.Write("{0} {1}", TypeName(type, wr, tok), name);
            if (leaveRoomForRhs) {
                Contract.Assert(rhs == null);  // follows from precondition
            } else if (rhs != null) {
                wr.WriteLine(" = {0};", rhs);
            } else {
                wr.WriteLine(";");
            }
        }
        
        protected override void EmitCollectionDisplay(CollectionType ct, Bpl.IToken tok, List<Expression> elements, bool inLetExprBody, TargetWriter wr) {
            wr.Write("new {0}", TypeName(ct, wr, tok));
            TrExprList(elements, wr, inLetExprBody);
        }
        
        protected override void EmitMapDisplay(MapType mt, Bpl.IToken tok, List<ExpressionPair> elements, bool inLetExprBody, TargetWriter wr) {
            wr.Write("new HashMap<>() {{{{\n");
            foreach (ExpressionPair p in elements) {
                wr.Write("put(");
                TrExpr(p.A, wr, inLetExprBody);
                wr.Write(", ");
                TrExpr(p.B, wr, inLetExprBody);
                wr.Write(");\n");
            }
            wr.Write("}}}}");
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
                case SpecialField.ID.ArrayLengthInt:
                    compiledName = idParam == null ? "length" : "dims[" + (int)idParam + "]";
                    if (id == SpecialField.ID.ArrayLength) {
                        preString = "new BigInteger(";
                        postString = ")";
                    }
                    break;
                case SpecialField.ID.Floor:
                    compiledName = "toBigInteger()";
                    break;
                case SpecialField.ID.IsLimit:
                    preString = "Dafny.BigOrdinal.IsLimit(";
                    postString = ")";
                    break;
                case SpecialField.ID.IsSucc:
                    preString = "Dafny.BigOrdinal.IsSucc(";
                    postString = ")";
                    break;
                case SpecialField.ID.Offset:
                    preString = "Dafny.BigOrdinal.Offset(";
                    postString = ")";
                    break;
                case SpecialField.ID.IsNat:
                    preString = "Dafny.BigOrdinal.IsNat(";
                    postString = ")";
                    break;
                case SpecialField.ID.Keys:
                    compiledName = "keySet()";
                    break;
                case SpecialField.ID.Values:
                    compiledName = "values()";
                    break;
                case SpecialField.ID.Items:
                    compiledName = "entrySet()";
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
        
        protected override TargetWriter EmitMemberSelect(MemberDecl member, bool isLValue, Type expectedType, TargetWriter wr) {
            var wSource = wr.Fork();
            if (isLValue && member is ConstantField) {
                wr.Write("._{0}", member.CompileName);
            } else if (!isLValue && member is SpecialField sf) {
                string compiledName, preStr, postStr;
                GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, out compiledName, out preStr, out postStr);
                if (compiledName.Length != 0) {
                    wr.Write(".{0}", compiledName);
                }
            } else {
                wr.Write(".{0}", IdName(member));
            }
            return wSource;
        }
        
        protected override string TypeName_Companion(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl member) {
            var udt = type as UserDefinedType;
            if (udt != null && udt.ResolvedClass is TraitDecl) {
                string s = udt.FullCompanionCompileName;
                Contract.Assert(udt.TypeArgs.Count == 0);  // traits have no type parameters
                return s;
            } else {
                return TypeName(type, wr, tok, member);
            }
        }
        
        protected override TargetWriter EmitArraySelect(List<string> indices, Type elmtType, TargetWriter wr) {
            Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
            var w = wr.Fork();
            if (indices.Count == 1) {
                wr.Write("[(int) {0}]", indices[0]);
            } else {
                wr.Write(".elmts");
                foreach (var index in indices) {
                    wr.Write("[(int) {0}]", index);
                }
            }
            return w;
        }

        protected override TargetWriter EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody, TargetWriter wr) {
            Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
            var w = wr.Fork();
            if (indices.Count == 1) {
                wr.Write("[(int) ");
                TrParenExpr(indices[0], wr, inLetExprBody);
                wr.Write("]");
            } else {
                wr.Write(".elmts");
                foreach (var index in indices) {
                    wr.Write("[(int) ");
                    TrParenExpr(index, wr, inLetExprBody);
                    wr.Write("]");
                }
            }
            return w;
        }
        
        protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray, bool inLetExprBody, TargetWriter wr) {
            if (fromArray) {
                wr.Write("new DafnySequence(Arrays.asList(Arrays.copyOfRange(");
            }
            TrParenExpr(source, wr, inLetExprBody);
            if (fromArray) {
                wr.Write(", ");
                if (lo != null) {
                    TrExpr(lo, wr, inLetExprBody);
                } else {
                    wr.Write("0");
                }
                wr.Write(", ");
                if (hi != null) {
                    TrExpr(hi, wr, inLetExprBody);
                } else {
                    TrParenExpr(source, wr, inLetExprBody);
                    wr.Write(".length");
                }
                wr.Write(")))");
            } else {
                if (lo != null && hi != null) {
                    wr.Write(".subsequence(");
                    TrExpr(lo, wr, inLetExprBody);
                    wr.Write(", ");
                    TrExpr(hi, wr, inLetExprBody);
                    wr.Write(")");
                }
                else if (lo != null) {
                    wr.Write(".drop");
                    TrParenExpr(lo, wr, inLetExprBody);
                }
                else if (hi != null) {
                    wr.Write(".take");
                    TrParenExpr(hi, wr, inLetExprBody);
                }
            }
        }
        
        protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody, TargetWriter wr) {
            // Taken from C# compiler, assuming source is a DafnySequence type.
            TrParenExpr(source, wr, inLetExprBody);
            TrParenExpr(".select", index, wr, inLetExprBody);
        }

        protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, TargetWriter wr) {
            TrParenExpr(expr.E, wr, inLetExprBody);
            wr.Write(".asDafnyMultiset()");
        }
        
        protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value, bool inLetExprBody,
            TargetWriter wr, bool nativeIndex = false) {
            TrParenExpr(source, wr, inLetExprBody);
            wr.Write(".update(");
            TrExpr(index, wr, inLetExprBody);
            wr.Write(", ");
            TrExpr(value, wr, inLetExprBody);
            wr.Write(")");
        }

        protected override string IdProtect(string name) {
            return PublicIdProtect(name);
        }

        public static string PublicIdProtect(string name) {
            if (name == "" || name.First() == '_') {
                return name; // no need to further protect this name
            }

            // TODO: Finish with all the public IDs that need to be protected
            switch (name) {
                // keywords Java 8 and before
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
                    return name; // Package name is not a keyword, so it can be used
            }
        }
        
        // ABSTRACT METHOD DECLARATIONS FOR THE SAKE OF BUILDING PROGRAM
        protected override string GetHelperModuleName()
        {
            throw new NotImplementedException();
        }
        
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

        protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, TargetWriter wr)
        {
            throw new NotImplementedException();
        }

        protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, TargetWriter wr)
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
