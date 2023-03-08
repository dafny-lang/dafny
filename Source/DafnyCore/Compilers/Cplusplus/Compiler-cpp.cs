//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.Collections.ObjectModel;
using JetBrains.Annotations;

namespace Microsoft.Dafny.Compilers {
  class CppCompiler : SinglePassCompiler {

    private readonly ReadOnlyCollection<string> headers;

    public CppCompiler(DafnyOptions options, ErrorReporter reporter, ReadOnlyCollection<string> headers) : base(options, reporter) {
      this.headers = headers;
    }

    public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
      Feature.UnboundedIntegers,
      Feature.RealNumbers,
      Feature.CollectionsOfTraits,
      Feature.Codatatypes,
      Feature.Multisets,
      Feature.ExternalClasses,
      Feature.Traits,
      Feature.Iterators,
      Feature.NonNativeNewtypes,
      Feature.RuntimeTypeDescriptors,
      Feature.MultiDimensionalArrays,
      Feature.CollectionsOfTraits,
      Feature.Quantifiers,
      Feature.NewObject,
      Feature.BitvectorRotateFunctions,
      Feature.NonSequentializableForallStatements,
      Feature.FunctionValues,
      Feature.ArrayLength,
      Feature.Ordinals,
      Feature.MapItems,
      Feature.Codatatypes,
      Feature.LetSuchThatExpressions,
      Feature.NonNativeNewtypes,
      Feature.TypeTests,
      Feature.SubsetTypeTests,
      Feature.SequenceDisplaysOfCharacters,
      Feature.MapComprehensions,
      Feature.ExactBoundedPool,
      Feature.RunAllTests,
      Feature.MethodSynthesis,
      Feature.UnicodeChars,
      Feature.ConvertingValuesToStrings
    };

    private List<DatatypeDecl> datatypeDecls = new();
    private List<string> classDefaults = new();

    /*
     * Unlike other Dafny and Dafny's other backends, C++ cares about
     * the order in which types are declared.  To make this more likely
     * to succeed, we emit type information as gradually as possible
     * in hopes that definitions are in place when needed.
     */

    // Forward declarations of class and struct names
    private ConcreteSyntaxTree modDeclsWr = null;
    private ConcreteSyntaxTree modDeclWr = null;
    // Dafny datatype declarations
    private ConcreteSyntaxTree dtDeclsWr = null;
    private ConcreteSyntaxTree dtDeclWr = null;
    // Dafny class declarations
    private ConcreteSyntaxTree classDeclsWr = null;
    private ConcreteSyntaxTree classDeclWr = null;
    // Dedicated hash-function definitions for each type
    private ConcreteSyntaxTree hashWr = null;

    const string DafnySetClass = "DafnySet";
    const string DafnyMultiSetClass = "DafnyMultiset";
    const string DafnySeqClass = "DafnySequence";
    const string DafnyMapClass = "DafnyMap";

    protected override string ModuleSeparator => "::";
    protected override string ClassAccessor => "->";

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
      // This seems to be a good place to check for unsupported options
      if (UnicodeCharEnabled) {
        throw new UnsupportedFeatureException(program.GetFirstTopLevelToken(), Feature.UnicodeChars);
      }

      wr.WriteLine("// Dafny program {0} compiled into Cpp", program.Name);
      wr.WriteLine("#include \"DafnyRuntime.h\"");
      foreach (var header in this.headers) {
        wr.WriteLine("#include \"{0}\"", header);
      }

      // For "..."s string literals, to avoid interpreting /0 as the C end of the string, cstring-style
      wr.WriteLine("using namespace std::literals;");

      var filenameNoExtension = program.Name.Substring(0, program.Name.Length - 4);
      var headerFileName = String.Format("{0}.h", filenameNoExtension);
      wr.WriteLine("#include \"{0}\"", headerFileName);

      var headerFileWr = wr.NewFile(headerFileName);
      headerFileWr.WriteLine("// Dafny program {0} compiled into a Cpp header file", program.Name);
      headerFileWr.WriteLine("#pragma once");
      headerFileWr.WriteLine("#include \"DafnyRuntime.h\"");

      this.modDeclsWr = headerFileWr.Fork();
      this.dtDeclsWr = headerFileWr.Fork();
      this.classDeclsWr = headerFileWr.Fork();
      this.hashWr = headerFileWr.Fork();

      var rt = wr.NewFile("DafnyRuntime.h");

      if (Options.IncludeRuntime) {
        ReadRuntimeSystem(program, "DafnyRuntime.h", rt);
      }

    }
    protected override void EmitFooter(Program program, ConcreteSyntaxTree wr) {
      // Define default values for each datatype
      foreach (var dt in this.datatypeDecls) {
        var wd = wr.NewBlock(String.Format("template <{0}>\nstruct get_default<{1}::{2}{3} >",
          TypeParameters(dt.TypeArgs),
          dt.EnclosingModuleDefinition.GetCompileName(Options),
          dt.GetCompileName(Options),
          InstantiateTemplate(dt.TypeArgs)), ";");
        var wc = wd.NewBlock(String.Format("static {0}::{1}{2} call()",
          dt.EnclosingModuleDefinition.GetCompileName(Options),
          dt.GetCompileName(Options),
          InstantiateTemplate(dt.TypeArgs)));
        wc.WriteLine("return {0}::{1}{2}();", dt.EnclosingModuleDefinition.GetCompileName(Options), dt.GetCompileName(Options), InstantiateTemplate(dt.TypeArgs));
      }

      // Define default values for each class
      foreach (var classDefault in classDefaults) {
        wr.WriteLine(classDefault);
      }
    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      var w = wr.NewBlock("int main(int argc, char *argv[])");
      var tryWr = w.NewBlock("try");
      tryWr.WriteLine(string.Format("{0}::{1}::{2}(dafny_get_args(argc, argv));", mainMethod.EnclosingClass.EnclosingModuleDefinition.GetCompileName(Options), mainMethod.EnclosingClass.GetCompileName(Options), mainMethod.Name));
      var catchWr = w.NewBlock("catch (DafnyHaltException & e)");
      catchWr.WriteLine("std::cout << \"Program halted: \" << e.what() << std::endl;");
    }

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw, string argsParameterName) {
      var wr = (cw as ClassWriter).MethodWriter;
      return wr.NewBlock($"int main(DafnySequence<DafnySequence<char>> {argsParameterName})");
    }

    protected override ConcreteSyntaxTree CreateModule(string moduleName, bool isDefault, bool isExtern, string/*?*/ libraryName, ConcreteSyntaxTree wr) {
      var s = string.Format("namespace {0} ", IdProtect(moduleName));
      string footer = "// end of " + s + " declarations";
      this.modDeclWr = this.modDeclsWr.NewBlock(s, footer);
      string footer1 = "// end of " + s + " datatype declarations";
      this.dtDeclWr = this.dtDeclsWr.NewBlock(s, footer1);
      string footer2 = "// end of " + s + " class declarations";
      this.classDeclWr = this.classDeclsWr.NewBlock(s, footer2);
      string footer3 = "// end of " + s;
      return wr.NewBlock(s, footer3);
    }

    private string TypeParameters(List<TypeParameter> targs) {
      Contract.Requires(cce.NonNullElements(targs));
      Contract.Ensures(Contract.Result<string>() != null);
      if (targs != null) {
        return Util.Comma(targs, tp => "typename " + IdName(tp));
      } else {
        return "";
      }
    }

    private string DeclareTemplate(List<TypeParameter> typeArgs) {
      var targs = "";
      if (typeArgs != null && typeArgs.Count > 0) {
        targs = String.Format("template <{0}>", TypeParameters(typeArgs));
      }
      return targs;
    }

    private string DeclareTemplate(List<Type> typeArgs) {
      var targs = "";
      if (typeArgs != null && typeArgs.Count > 0) {
        targs = String.Format("template <{0}>", Util.Comma(typeArgs, t => "typename " + TypeName(t, null, null)));
      }
      return targs;
    }

    private string InstantiateTemplate(List<TypeParameter> typeArgs) {
      if (typeArgs != null) {
        var targs = "";
        if (typeArgs.Count > 0) {
          targs = String.Format("<{0}>", Util.Comma(typeArgs, ta => ta.GetCompileName(Options)));
        }
        return targs;
      } else {
        return "";
      }
    }

    private string InstantiateTemplate(List<Type> typeArgs) {
      if (typeArgs != null) {
        var targs = "";
        if (typeArgs.Count > 0) {
          targs = String.Format("<{0}>", Util.Comma(typeArgs, ta => TypeName(ta, null, Token.NoToken)));
        }

        return targs;
      } else {
        return "";
      }
    }

    protected override string GetHelperModuleName() => "_dafny";

    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string/*?*/ fullPrintName, List<TypeParameter>/*?*/ typeParameters, TopLevelDecl cls, List<Type>/*?*/ superClasses, IToken tok, ConcreteSyntaxTree wr) {
      if (isExtern) {
        throw new UnsupportedFeatureException(tok, Feature.ExternalClasses, String.Format("extern in class {0}", name));
      }
      if (superClasses != null && superClasses.Any(trait => !trait.IsObject)) {
        throw new UnsupportedFeatureException(tok, Feature.Traits, String.Format("traits in class {0}", name));
      }

      var classDeclWriter = modDeclWr;
      var classDefWriter = this.classDeclWr;

      if (typeParameters != null && typeParameters.Count > 0) {
        classDeclWriter.WriteLine(DeclareTemplate(typeParameters));
        classDefWriter.WriteLine(DeclareTemplate(typeParameters));
      }

      var methodDeclWriter = classDefWriter.NewBlock(string.Format("class {0}", name), ";");
      var methodDefWriter = wr;

      classDeclWriter.WriteLine("class {0};", name);

      methodDeclWriter.Write("public:\n");
      methodDeclWriter.WriteLine("// Default constructor");
      methodDeclWriter.WriteLine("{0}() {{}}", name);

      // Create the code for the specialization of get_default
      var fullName = moduleName + "::" + name;
      var getDefaultStr = String.Format("template <{0}>\nstruct get_default<std::shared_ptr<{1}{2} > > {{\n",
        TypeParameters(typeParameters),
        fullName,
        InstantiateTemplate(typeParameters));
      getDefaultStr += String.Format("static std::shared_ptr<{0}{1} > call() {{\n",
        fullName,
        InstantiateTemplate(typeParameters));
      getDefaultStr += String.Format("return std::shared_ptr<{0}{1} >();", fullName, InstantiateTemplate(typeParameters));
      getDefaultStr += "}\n};";
      this.classDefaults.Add(getDefaultStr);

      var fieldWriter = methodDeclWriter;

      return new ClassWriter(name, this, methodDeclWriter, methodDefWriter, fieldWriter, wr);
    }

    protected override bool SupportsProperties { get => false; }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters /*?*/,
      TopLevelDecl trait, List<Type> superClasses /*?*/, IToken tok, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(tok, Feature.Traits, String.Format("traits in class {0}", name));
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(iter.tok, Feature.Iterators);
    }

    protected bool IsRecursiveConstructor(DatatypeDecl dt, DatatypeCtor ctor) {
      foreach (var dtor in ctor.Destructors) {
        if (dtor.Type is UserDefinedType t) {
          if (t.ResolvedClass == dt) {
            return true;
          }
        }
      }
      return false;
    }

    protected bool IsRecursiveDatatype(DatatypeDecl dt) {
      foreach (var ctor in dt.Ctors) {
        if (IsRecursiveConstructor(dt, ctor)) {
          return true;
        }
      }
      return false;
    }

    // Uniform naming convention
    protected string DatatypeSubStructName(DatatypeCtor ctor, bool inclTemplateArgs = false) {
      string args = "";
      if (inclTemplateArgs) {
        args = InstantiateTemplate(ctor.EnclosingDatatype.TypeArgs);
      }
      return String.Format("{0}_{1}{2}", IdProtect(ctor.EnclosingDatatype.GetCompileName(Options)), ctor.GetCompileName(Options), args);
    }

    protected override bool DatatypeDeclarationAndMemberCompilationAreSeparate => false;
    public override bool SupportsDatatypeWrapperErasure => false;

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree writer) {
      if (dt is TupleTypeDecl) {
        // Tuple types are declared once and for all in DafnyRuntime.h
        return null;
      }

      this.datatypeDecls.Add(dt);

      string DtT = dt.GetCompileName(Options);
      string DtT_protected = IdProtect(DtT);

      // Forward declaration of the type
      this.modDeclWr.WriteLine("{0}\nstruct {1};", DeclareTemplate(dt.TypeArgs), DtT_protected);
      var wdecl = this.dtDeclWr;
      var wdef = writer;

      if (IsRecursiveDatatype(dt)) { // Note that if this is true, there must be more than one constructor!
        // Add some forward declarations
        wdecl.WriteLine("{0}\nstruct {1};", DeclareTemplate(dt.TypeArgs), DtT_protected);
        wdecl.WriteLine("{2}\nbool operator==(const {0}{1} &left, const {0}{1} &right); ", DtT_protected, InstantiateTemplate(dt.TypeArgs), DeclareTemplate(dt.TypeArgs));
      }

      // Optimize a not-uncommon case
      if (dt.IsRecordType) {
        var ctor = dt.Ctors[0];
        var ws = wdecl.NewBlock(String.Format("{0}\nstruct {1}", DeclareTemplate(dt.TypeArgs), DtT_protected), ";");

        // Declare the struct members
        var i = 0;
        var argNames = new List<string>();
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            ws.WriteLine("{0} {1};", TypeName(arg.Type, wdecl, arg.tok), FormalName(arg, i));
            argNames.Add(FormalName(arg, i));
            i++;
          }
        }

        if (argNames.Count > 0) {
          // Create a constructor with arguments
          ws.Write("{0}(", DtT_protected);
          WriteFormals("", ctor.Formals, ws);
          ws.Write(")");
          if (argNames.Count > 0) {
            // Add initializers
            ws.Write(" :");
            ws.Write(Util.Comma(argNames, nm => String.Format(" {0} ({0})", IdProtect(nm))));
          }

          ws.WriteLine(" {}");
        }

        // Create a constructor with no arguments
        ws.WriteLine("{0}();", DtT_protected);
        var wc = wdef.NewNamedBlock("{1}\n{0}{2}::{0}()", DtT_protected, DeclareTemplate(dt.TypeArgs), InstantiateTemplate(dt.TypeArgs));
        foreach (var arg in ctor.Formals) {
          if (!arg.IsGhost) {
            wc.WriteLine("{0} = {1};", arg.CompileName, DefaultValue(arg.Type, wc, arg.tok));
          }
        }

        // Overload the comparison operator
        var wrCompOp = ws.NewNamedBlock("friend bool operator==(const {0} &left, const {0} &right)", DtT_protected);
        wrCompOp.Write("\treturn true");
        foreach (var arg in argNames) {
          wrCompOp.WriteLine("\t\t&& left.{0} == right.{0}", arg);
        }
        wrCompOp.WriteLine(";");

        // Overload the not-comparison operator
        ws.WriteLine("friend bool operator!=(const {0} &left, const {0} &right) {{ return !(left == right); }} ", DtT_protected);

        wdecl.WriteLine("{0}\ninline bool is_{1}(const struct {2}{3} d) {{ (void) d; return true; }}", DeclareTemplate(dt.TypeArgs), ctor.GetCompileName(Options), DtT_protected, InstantiateTemplate(dt.TypeArgs));

        // Define a custom hasher
        hashWr.WriteLine("template <{0}>", TypeParameters(dt.TypeArgs));
        var fullName = dt.EnclosingModuleDefinition.GetCompileName(Options) + "::" + DtT_protected + InstantiateTemplate(dt.TypeArgs);
        var hwr = hashWr.NewBlock(string.Format("struct std::hash<{0}>", fullName), ";");
        var owr = hwr.NewBlock(string.Format("std::size_t operator()(const {0}& x) const", fullName));
        owr.WriteLine("size_t seed = 0;");
        foreach (var arg in ctor.Formals) {
          if (!arg.IsGhost) {
            owr.WriteLine("hash_combine<{0}>(seed, x.{1});", TypeName(arg.Type, owr, dt.tok), arg.CompileName);
          }
        }
        owr.WriteLine("return seed;");
      } else {

        /*** Create one struct for each constructor ***/
        foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
          string structName = DatatypeSubStructName(ctor);
          var wstruct = wdecl.NewBlock(String.Format("{0}\nstruct {1}", DeclareTemplate(dt.TypeArgs), structName), ";");
          // Declare the struct members
          var i = 0;
          foreach (Formal arg in ctor.Formals) {
            if (!arg.IsGhost) {
              if (arg.Type is UserDefinedType udt && udt.ResolvedClass == dt) {  // Recursive declaration needs to use a pointer
                wstruct.WriteLine("std::shared_ptr<{0}> {1};", TypeName(arg.Type, wdecl, arg.tok), FormalName(arg, i));
              } else {
                wstruct.WriteLine("{0} {1};", TypeName(arg.Type, wdecl, arg.tok), FormalName(arg, i));
              }
              i++;
            }
          }

          // Overload the comparison operator
          wstruct.WriteLine("friend bool operator==(const {0} &left, const {0} &right) {{ ", structName);

          var preReturn = wstruct.Fork();
          wstruct.Write("\treturn true ");
          i = 0;
          foreach (Formal arg in ctor.Formals) {
            if (!arg.IsGhost) {
              if (arg.Type is UserDefinedType udt && udt.ResolvedClass == dt) {  // Recursive destructor needs to use a pointer
                wstruct.WriteLine("\t\t&& *(left.{0}) == *(right.{0})", FormalName(arg, i));
              } else {
                wstruct.WriteLine("\t\t&& left.{0} == right.{0}", FormalName(arg, i));
              }
              i++;
            }
          }

          if (i == 0) { // Avoid a warning from the C++ compiler
            preReturn.WriteLine("(void)left; (void) right;");
          }

          wstruct.WriteLine(";\n}");

          // Overload the not-comparison operator
          wstruct.WriteLine("friend bool operator!=(const {0} &left, const {0} &right) {{ return !(left == right); }} ", structName);

          // Define a custom hasher
          hashWr.WriteLine("template <{0}>", TypeParameters(dt.TypeArgs));
          var fullName = dt.EnclosingModuleDefinition.GetCompileName(Options) + "::" + structName + InstantiateTemplate(dt.TypeArgs);
          var hwr = hashWr.NewBlock(string.Format("struct std::hash<{0}>", fullName), ";");
          var owr = hwr.NewBlock(string.Format("std::size_t operator()(const {0}& x) const", fullName));
          owr.WriteLine("size_t seed = 0;");
          int argCount = 0;
          foreach (var arg in ctor.Formals) {
            if (!arg.IsGhost) {
              if (arg.Type is UserDefinedType udt && udt.ResolvedClass == dt) {
                // Recursive destructor needs to use a pointer
                owr.WriteLine("hash_combine<std::shared_ptr<{0}>>(seed, x.{1});", TypeName(arg.Type, owr, dt.tok), arg.CompileName);
              } else {
                owr.WriteLine("hash_combine<{0}>(seed, x.{1});", TypeName(arg.Type, owr, dt.tok), arg.CompileName);
              }
              argCount++;
            }
          }
          if (argCount == 0) {
            owr.WriteLine("(void)x;");
          }
          owr.WriteLine("return seed;");
        }

        /*** Declare the overall tagged union ***/
        var ws = wdecl.NewBlock(String.Format("{0}\nstruct {1}", DeclareTemplate(dt.TypeArgs), DtT_protected), ";");
        ws.WriteLine("std::variant<{0}> v;", Util.Comma(dt.Ctors, ctor => DatatypeSubStructName(ctor, true)));

        // Declare static "constructors" for each Dafny constructor
        foreach (var ctor in dt.Ctors) {
          var wc = ws.NewNamedBlock("static {0} create_{1}({2})",
            DtT_protected, ctor.GetCompileName(Options),
            DeclareFormals(ctor.Formals));
          wc.WriteLine("{0}{1} COMPILER_result;", DtT_protected, InstantiateTemplate(dt.TypeArgs));
          wc.WriteLine("{0} COMPILER_result_subStruct;", DatatypeSubStructName(ctor, true));

          foreach (Formal arg in ctor.Formals) {
            if (!arg.IsGhost) {
              if (arg.Type is UserDefinedType udt && udt.ResolvedClass == dt) {
                // This is a recursive destuctor, so we need to allocate space and copy the input in
                wc.WriteLine("COMPILER_result_subStruct.{0} = std::make_shared<{1}>({0});", arg.CompileName,
                  DtT_protected);
              } else {
                wc.WriteLine("COMPILER_result_subStruct.{0} = {0};", arg.CompileName);
              }
            }
          }

          wc.WriteLine("COMPILER_result.v = COMPILER_result_subStruct;");
          wc.WriteLine("return COMPILER_result;");
        }

        // Declare a default constructor
        ws.WriteLine("{0}();", DtT_protected);
        var wd = wdef.NewNamedBlock(String.Format("{1}\n{0}{2}::{0}()", DtT_protected, DeclareTemplate(dt.TypeArgs), InstantiateTemplate(dt.TypeArgs)));
        var default_ctor = dt.Ctors[0]; // Arbitrarily choose the first one
        wd.WriteLine("{0} COMPILER_result_subStruct;", DatatypeSubStructName(default_ctor, true));
        foreach (Formal arg in default_ctor.Formals) {
          if (!arg.IsGhost) {
            wd.WriteLine("COMPILER_result_subStruct.{0} = {1};", arg.CompileName,
              DefaultValue(arg.Type, wd, arg.tok));
          }
        }

        wd.WriteLine("v = COMPILER_result_subStruct;");

        // Declare a default destructor
        ws.WriteLine("~{0}() {{}}", DtT_protected);

        {
          // Declare a default copy constructor (just in case any of our components are non-trivial, i.e., contain smart_ptr)
          var wcc = ws.NewNamedBlock(String.Format("{0}(const {0} &other)", DtT_protected));
          wcc.WriteLine("v = other.v;");
        }
        {
          // Declare a default copy assignment operator (just in case any of our components are non-trivial, i.e., contain smart_ptr)
          var wcc = ws.NewNamedBlock(String.Format("{0}& operator=(const {0} other)", DtT_protected));
          wcc.WriteLine("v = other.v;");
          wcc.WriteLine("return *this;");
        }

        // Declare type queries, both as members and general-purpose functions
        foreach (var ctor in dt.Ctors) {
          var name = DatatypeSubStructName(ctor);
          var holds = String.Format("std::holds_alternative<{0}{1}>", name, InstantiateTemplate(dt.TypeArgs));
          ws.WriteLine("bool is_{0}() const {{ return {1}(v); }}", name, holds);
          wdecl.WriteLine("{0}\ninline bool is_{1}(const struct {2}{3} d);", DeclareTemplate(dt.TypeArgs), name, DtT_protected, InstantiateTemplate(dt.TypeArgs));
          wdef.WriteLine("{0}\ninline bool is_{1}(const struct {2}{3} d) {{ return {4}(d.v); }}",
            DeclareTemplate(dt.TypeArgs), name, DtT_protected, InstantiateTemplate(dt.TypeArgs), holds);
        }

        // Overload the comparison operator
        ws.WriteLine("friend bool operator==(const {0} &left, const {0} &right) {{ ", DtT_protected);
        ws.WriteLine("\treturn left.v == right.v;\n}");

        // Create destructors
        foreach (var ctor in dt.Ctors) {
          foreach (var dtor in ctor.Destructors) {
            if (dtor.EnclosingCtors[0] == ctor) {
              var arg = dtor.CorrespondingFormals[0];
              if (!arg.IsGhost && arg.HasName) {
                var returnType = TypeName(arg.Type, ws, arg.tok);
                if (arg.Type is UserDefinedType udt && udt.ResolvedClass == dt) {
                  // This is a recursive destuctor, so return a pointer
                  returnType = String.Format("std::shared_ptr<{0}>", returnType);
                }

                var wDtor = ws.NewNamedBlock("{0} dtor_{1}()", returnType,
                  arg.CompileName);
                if (dt.IsRecordType) {
                  wDtor.WriteLine("return this.{0};", IdName(arg));
                } else {
                  var n = dtor.EnclosingCtors.Count;
                  for (int i = 0; i < n - 1; i++) {
                    var ctor_i = dtor.EnclosingCtors[i];
                    var ctor_name = DatatypeSubStructName(ctor_i);
                    Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[i].CompileName);
                    wDtor.WriteLine("if (is_{0}()) {{ return std::get<{0}{1}>(v).{2}; }}",
                      ctor_name, InstantiateTemplate(dt.TypeArgs), IdName(arg));
                  }

                  Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[n - 1].CompileName);
                  var final_ctor_name = DatatypeSubStructName(dtor.EnclosingCtors[n - 1], true);
                  wDtor.WriteLine("return std::get<{0}>(v).{1}; ",
                    final_ctor_name, IdName(arg));
                }
              }
            }
          }
        }

        // Overload the not-comparison operator
        ws.WriteLine("friend bool operator!=(const {0} &left, const {0} &right) {{ return !(left == right); }} ", DtT_protected);

        // Define a custom hasher for the struct as a whole
        hashWr.WriteLine("template <{0}>", TypeParameters(dt.TypeArgs));
        var fullStructName = dt.EnclosingModuleDefinition.GetCompileName(Options) + "::" + DtT_protected;
        var hwr2 = hashWr.NewBlock(string.Format("struct std::hash<{0}{1}>", fullStructName, InstantiateTemplate(dt.TypeArgs)), ";");
        var owr2 = hwr2.NewBlock(string.Format("std::size_t operator()(const {0}{1}& x) const", fullStructName, InstantiateTemplate(dt.TypeArgs)));
        owr2.WriteLine("size_t seed = 0;");
        var index = 0;
        foreach (var ctor in dt.Ctors) {
          var ifwr = owr2.NewBlock(string.Format("if (x.is_{0}())", DatatypeSubStructName(ctor)));
          ifwr.WriteLine("hash_combine<uint64>(seed, {0});", index);
          ifwr.WriteLine("hash_combine<struct {0}::{1}>(seed, std::get<{0}::{1}>(x.v));", dt.EnclosingModuleDefinition.GetCompileName(Options), DatatypeSubStructName(ctor, true));
          index++;
        }
        owr2.WriteLine("return seed;");

        if (IsRecursiveDatatype(dt)) {
          // Emit a custom hasher for a pointer to this type
          hashWr.WriteLine("template <{0}>", TypeParameters(dt.TypeArgs));
          hwr2 = hashWr.NewBlock(string.Format("struct std::hash<std::shared_ptr<{0}{1}>>", fullStructName, InstantiateTemplate(dt.TypeArgs)), ";");
          owr2 = hwr2.NewBlock(string.Format("std::size_t operator()(const std::shared_ptr<{0}{1}>& x) const", fullStructName, InstantiateTemplate(dt.TypeArgs)));
          owr2.WriteLine("struct std::hash<{0}{1}> hasher;", fullStructName, InstantiateTemplate(dt.TypeArgs));
          owr2.WriteLine("std::size_t h = hasher(*x);");
          owr2.WriteLine("return h;");
        }
      }

      return null;
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      if (nt.NativeType != null) {
        if (nt.NativeType.Name != nt.Name) {
          string nt_name_def, literalSuffice_def;
          bool needsCastAfterArithmetic_def;
          GetNativeInfo(nt.NativeType.Sel, out nt_name_def, out literalSuffice_def, out needsCastAfterArithmetic_def);
          wr.WriteLine("typedef {0} {1};", nt_name_def, nt.Name);
        }
      } else {
        throw new UnsupportedFeatureException(nt.tok, Feature.NonNativeNewtypes, String.Format("non-native newtype {0}", nt));
      }
      var className = "class_" + IdName(nt);
      var cw = CreateClass(nt.EnclosingModuleDefinition.GetCompileName(Options), className, nt, wr) as ClassWriter;
      var w = cw.MethodDeclWriter;
      if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var witness = new ConcreteSyntaxTree(w.RelativeIndentLevel);
        var wStmts = w.Fork();
        if (nt.NativeType == null) {
          witness.Append(Expr(nt.Witness, false, wStmts));
        } else {
          TrParenExpr(nt.Witness, witness, false, wStmts);
          witness.Write(".toNumber()");
        }
        DeclareField(className, nt.TypeArgs, "Witness", true, true, nt.BaseType, nt.tok, witness.ToString(), w, wr);
      }

      string nt_name, literalSuffice;
      bool needsCastAfterArithmetic;
      GetNativeInfo(nt.NativeType.Sel, out nt_name, out literalSuffice, out needsCastAfterArithmetic);
      var wDefault = w.NewBlock(string.Format("static {0} get_Default()", nt_name));
      var udt = new UserDefinedType(nt.tok, nt.Name, nt, new List<Type>());
      var d = TypeInitializationValue(udt, wr, nt.tok, false, false);
      wDefault.WriteLine("return {0};", d);

      return cw;
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      if (sst.Name == "nat") {
        return;  // C++ does not support Nats
      }

      string templateDecl = "";
      if (sst.Var.Type is SeqType s) {
        templateDecl = DeclareTemplate(s.TypeArgs[0].TypeArgs);  // We want the type args (if any) for the seq-elt type, not the seq
      } else {
        templateDecl = DeclareTemplate(sst.Var.Type.TypeArgs);
      }

      this.modDeclWr.WriteLine("{0} using {1} = {2};", templateDecl, IdName(sst), TypeName(sst.Var.Type, wr, sst.tok));

      var className = "class_" + IdName(sst);
      var cw = CreateClass(sst.EnclosingModuleDefinition.GetCompileName(Options), className, sst, wr) as ClassWriter;
      var w = cw.MethodDeclWriter;

      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var witness = new ConcreteSyntaxTree(w.RelativeIndentLevel);
        witness.Append(Expr(sst.Witness, false, w));
        DeclareField(className, sst.TypeArgs, "Witness", true, true, sst.Rhs, sst.tok, witness.ToString(), w, wr);
      }

      var wDefault = w.NewBlock(String.Format("static {0}{1} get_Default()", IdName(sst), InstantiateTemplate(sst.TypeArgs)));
      var udt = new UserDefinedType(sst.tok, sst.Name, sst,
        sst.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp)));
      var d = TypeInitializationValue(udt, wr, sst.tok, false, false);
      wDefault.WriteLine("return {0};", d);
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      literalSuffix = "";
      needsCastAfterArithmetic = false;
      switch (sel) {
        case NativeType.Selection.Byte:
          name = "uint8";
          break;
        case NativeType.Selection.SByte:
          name = "int8";
          break;
        case NativeType.Selection.UShort:
          name = "uint16";
          break;
        case NativeType.Selection.Short:
          name = "int16";
          break;
        case NativeType.Selection.UInt:
          name = "uint32";
          break;
        case NativeType.Selection.Int:
          name = "int32";
          break;
        case NativeType.Selection.ULong:
          name = "uint64";
          break;
        case NativeType.Selection.Number:
        case NativeType.Selection.Long:
          name = "int64";
          break;
        default:
          Contract.Assert(false);  // unexpected native type
          throw new cce.UnreachableException();  // to please the compiler
      }
    }

    protected class ClassWriter : IClassWriter {
      public string ClassName;
      public readonly CppCompiler Compiler;
      public readonly ConcreteSyntaxTree MethodDeclWriter;
      public readonly ConcreteSyntaxTree MethodWriter;
      public readonly ConcreteSyntaxTree FieldWriter;
      public readonly ConcreteSyntaxTree Finisher;

      public ClassWriter(string className, CppCompiler compiler, ConcreteSyntaxTree methodDeclWriter, ConcreteSyntaxTree methodWriter, ConcreteSyntaxTree fieldWriter, ConcreteSyntaxTree finisher) {
        Contract.Requires(compiler != null);
        Contract.Requires(methodDeclWriter != null);
        Contract.Requires(methodWriter != null);
        Contract.Requires(fieldWriter != null);
        this.ClassName = className;
        this.Compiler = compiler;
        this.MethodDeclWriter = methodDeclWriter;
        this.MethodWriter = methodWriter;
        this.FieldWriter = fieldWriter;
        this.Finisher = finisher;
      }

      public ConcreteSyntaxTree/*?*/ CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateMethod(m, typeArgs, createBody, MethodDeclWriter, MethodWriter, lookasideBody);
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        throw new UnsupportedFeatureException(m.tok, Feature.MethodSynthesis);
      }

      public ConcreteSyntaxTree/*?*/ CreateFunction(string name, List<TypeArgumentInstantiation>/*?*/ typeArgs,
        List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member, bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateFunction(member.EnclosingClass.GetCompileName(Compiler.Options),
          member.EnclosingClass.TypeArgs, name, typeArgs, formals, resultType, tok, isStatic, createBody, member,
          MethodDeclWriter, MethodWriter, lookasideBody);
      }
      public ConcreteSyntaxTree/*?*/ CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IToken tok, bool isStatic, bool isConst, bool createBody, MemberDecl/*?*/ member, bool forBodyInheritance) {
        return Compiler.CreateGetter(name, enclosingDecl, resultType, tok, isStatic, isConst, createBody, MethodDeclWriter, MethodWriter);
      }
      public ConcreteSyntaxTree/*?*/ CreateGetterSetter(string name, Type resultType, IToken tok, bool createBody, MemberDecl/*?*/ member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        return Compiler.CreateGetterSetter(name, resultType, tok, createBody, out setterWriter, MethodWriter);
      }
      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type, IToken tok, string rhs, Field field) {
        Compiler.DeclareField(ClassName, enclosingDecl.TypeArgs, name, isStatic, isConst, type, tok, rhs, FieldWriter, Finisher);
      }
      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        throw new cce.UnreachableException();  // InitializeField should be called only for those compilers that set ClassesRedeclareInheritedFields to false.
      }
      public ConcreteSyntaxTree/*?*/ ErrorWriter() => MethodWriter;
      public void Finish() { }
    }

    protected ConcreteSyntaxTree/*?*/ CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, ConcreteSyntaxTree wdr, ConcreteSyntaxTree wr, bool lookasideBody) {
      List<Formal> nonGhostOuts = m.Outs.Where(o => !o.IsGhost).ToList();
      string targetReturnTypeReplacement = null;
      if (nonGhostOuts.Count == 1) {
        targetReturnTypeReplacement = TypeName(nonGhostOuts[0].Type, wr, nonGhostOuts[0].tok);
      } else if (nonGhostOuts.Count > 1) {
        targetReturnTypeReplacement = String.Format("struct Tuple{0}", InstantiateTemplate(nonGhostOuts.ConvertAll(n => n.Type)));
      }

      if (!createBody) {
        return null;
      }

      if (typeArgs.Count != 0) {
        var formalTypeParameters = TypeArgumentInstantiation.ToFormals(ForTypeParameters(typeArgs, m, lookasideBody));
        // Filter out type parameters we've already emitted at the class level, to avoid shadowing
        // the class' template parameter (which C++ treats as an error)
        formalTypeParameters = formalTypeParameters.Where(param =>
          m.EnclosingClass.TypeArgs == null || !m.EnclosingClass.TypeArgs.Contains(param)).ToList();
        wdr.WriteLine(DeclareTemplate(formalTypeParameters));
        wr.WriteLine(DeclareTemplate(formalTypeParameters));
      }

      if (m.EnclosingClass.TypeArgs != null && m.EnclosingClass.TypeArgs.Count > 0) {
        wr.WriteLine(DeclareTemplate(m.EnclosingClass.TypeArgs));
      }

      wr.Write("{0} {1}{2}::{3}",
        targetReturnTypeReplacement ?? "void",
        m.EnclosingClass.GetCompileName(Options),
        InstantiateTemplate(m.EnclosingClass.TypeArgs),
        IdName(m));

      wdr.Write("{0}{1} {2}",
        m.IsStatic ? "static " : "",
        targetReturnTypeReplacement ?? "void",
        IdName(m));

      wr.Write("(");
      wdr.Write("(");
      int nIns = WriteFormals("", m.Ins, wr);
      WriteFormals("", m.Ins, wdr);
      if (targetReturnTypeReplacement == null) {
        WriteFormals(nIns == 0 ? "" : ", ", m.Outs, wr);
        WriteFormals(nIns == 0 ? "" : ", ", m.Outs, wdr);
      }
      wdr.Write(");\n");

      var block = wr.NewBlock(")", null, BlockStyle.NewlineBrace, BlockStyle.NewlineBrace);

      if (targetReturnTypeReplacement != null) {
        var beforeReturnBlock = block.Fork(0);
        EmitReturn(m.Outs, block);
        return beforeReturnBlock;
      }
      return block;
    }

    protected ConcreteSyntaxTree/*?*/ CreateFunction(string className, List<TypeParameter> classArgs, string name, List<TypeArgumentInstantiation>/*?*/ typeArgs, List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member, ConcreteSyntaxTree wdr, ConcreteSyntaxTree wr, bool lookasideBody) {
      if (!createBody) {
        return null;
      }

      if (typeArgs.Count != 0) {
        var formalTypeParameters = TypeArgumentInstantiation.ToFormals(ForTypeParameters(typeArgs, member, lookasideBody));
        // Filter out type parameters we've already emitted at the class level, to avoid shadowing
        // the class' template parameter (which C++ treats as an error)
        formalTypeParameters = formalTypeParameters.Where(param =>
          !classArgs.Contains(param)).ToList();
        wdr.WriteLine(DeclareTemplate(formalTypeParameters));
        wr.WriteLine(DeclareTemplate(formalTypeParameters));
      }
      if (classArgs != null && classArgs.Count != 0) {
        wr.WriteLine(DeclareTemplate(classArgs));
      }

      wdr.Write("{0}{1} {2}",
        isStatic ? "static " : "",
        TypeName(resultType, wr, tok),
        name);
      wr.Write("{0} {1}{2}::{3}",
        TypeName(resultType, wr, tok),
        className,
        InstantiateTemplate(classArgs),
        name);

      wdr.Write("(");
      wr.Write("(");
      WriteFormals("", formals, wdr);
      int nIns = WriteFormals("", formals, wr);

      wdr.Write(");");
      var w = wr.NewBlock(")", null, BlockStyle.NewlineBrace, BlockStyle.NewlineBrace);

      return w;
    }

    protected override void TypeArgDescriptorUse(bool isStatic, bool lookasideBody, TopLevelDeclWithMembers cl, out bool needsTypeParameter, out bool needsTypeDescriptor) {
      needsTypeParameter = false;
      needsTypeDescriptor = false;
    }

    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IToken tok) {
      Contract.Requires(type != null);
      Contract.Requires(tok != null);
      Contract.Requires(wr != null);
      throw new UnsupportedFeatureException(tok, Feature.RuntimeTypeDescriptors, string.Format("RuntimeTypeDescriptor {0} not yet supported", type));
    }

    protected ConcreteSyntaxTree/*?*/ CreateGetter(string name, TopLevelDecl cls, Type resultType, IToken tok, bool isStatic, bool isConst, bool createBody, ConcreteSyntaxTree wdr, ConcreteSyntaxTree wr) {
      // Compiler insists on using Getter for constants, but we just use the raw variable name to hold the value,
      // because o/w Compiler tries to use the Getter function as an Lvalue in assignments
      // Unfortunately, Compiler doesn't tell us what the initial value is, so we hack around it
      // by declaring the variable and a function to statically initialize it

      ConcreteSyntaxTree w = null;
      string postfix = null;
      if (createBody) {
        w = wdr.NewNamedBlock("{0}{1} init__{2}()", isStatic ? "static " : "", TypeName(resultType, wr, tok), name);
        postfix = String.Format(" init__{0}()", name);
      }
      DeclareField(cls.GetCompileName(Options), cls.TypeArgs, name, isStatic, isConst, resultType, tok, postfix, wdr, wr);
      //wdr.Write("{0}{1} {2}{3};", isStatic ? "static " : "", TypeName(resultType, wr, tok), name, postfix);
      return w;
    }

    protected ConcreteSyntaxTree/*?*/ CreateGetterSetter(string name, Type resultType, IToken tok, bool createBody, out ConcreteSyntaxTree setterWriter, ConcreteSyntaxTree wr) {
      // We don't use getter/setter pairs; we just embed the trait's fields.
      if (createBody) {
        var abyss = new ConcreteSyntaxTree();
        setterWriter = abyss;
        return abyss.NewBlock("");
      } else {
        setterWriter = null;
        return null;
      }
    }

    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      wr.WriteLine("TAIL_CALL_START:");
      return wr;
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      wr.WriteLine("goto TAIL_CALL_START;");
    }

    protected void Warn(string msg, IToken tok) {
      // TODO, fix.
      Console.Error.WriteLine("WARNING: {3} ({0}:{1}:{2})", tok.Filename, tok.line, tok.col, msg);
    }

    // Because we use reference counting (via shared_ptr), the TypeName of a class differs
    // depending on whether we are declaring a variable or talking about the class itself.
    // Use class_name = true if you want the actual name of the class, not the type used when declaring variables/arguments/etc.
    protected string TypeName(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member = null, bool class_name = false) {
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
        UnsupportedFeatureError(tok, Feature.UnboundedIntegers);
        return "BigNumber";
      } else if (xType is RealType) {
        UnsupportedFeatureError(tok, Feature.RealNumbers);
        return "Dafny.BigRational";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? GetNativeTypeName(t.NativeType) : "BigNumber";
      } else if (xType.AsNewtype != null) {
        NativeType nativeType = xType.AsNewtype.NativeType;
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
        if (at.Dims == 1) {
          return "DafnyArray<" + TypeName(elType, wr, tok, null, false) + ">";
        } else {
          throw new UnsupportedFeatureException(tok, Feature.MultiDimensionalArrays);
        }
      } else if (xType is UserDefinedType) {
        var udt = (UserDefinedType)xType;
        var s = FullTypeName(udt, member);
        var cl = udt.ResolvedClass;
        bool isHandle = true;
        if (cl != null && Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "ulong";
        }
        if (class_name || xType.IsTypeParameter || xType.IsOpaqueType || xType.IsDatatype) {  // Don't add pointer decorations to class names or type parameters
          return IdProtect(s) + ActualTypeArgs(xType.TypeArgs);
        } else {
          return TypeName_UDT(s, udt, wr, udt.tok);
        }
      } else if (xType is SetType) {
        Type argType = ((SetType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(TypeParameter.TPVariance.Co, argType)) {
          UnsupportedFeatureError(tok, Feature.CollectionsOfTraits, "compilation of set<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return DafnySetClass + "<" + TypeName(argType, wr, tok) + ">";
      } else if (xType is SeqType) {
        Type argType = ((SeqType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(TypeParameter.TPVariance.Co, argType)) {
          UnsupportedFeatureError(tok, Feature.CollectionsOfTraits, "compilation of seq<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return DafnySeqClass + "<" + TypeName(argType, wr, tok) + ">";
      } else if (xType is MultiSetType) {
        Type argType = ((MultiSetType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(TypeParameter.TPVariance.Co, argType)) {
          UnsupportedFeatureError(tok, Feature.CollectionsOfTraits, "compilation of multiset<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return DafnyMultiSetClass + "<" + TypeName(argType, wr, tok) + ">";
      } else if (xType is MapType) {
        Type domType = ((MapType)xType).Domain;
        Type ranType = ((MapType)xType).Range;
        if (ComplicatedTypeParameterForCompilation(TypeParameter.TPVariance.Co, domType) || ComplicatedTypeParameterForCompilation(TypeParameter.TPVariance.Co, ranType)) {
          UnsupportedFeatureError(tok, Feature.CollectionsOfTraits, "compilation of map<TRAIT, _> or map<_, TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return DafnyMapClass + "<" + TypeName(domType, wr, tok) + "," + TypeName(ranType, wr, tok) + ">";
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    internal override string TypeName(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass
      return TypeName(type, wr, tok, member, false);
    }

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IToken tok, bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return CharType.DefaultValueAsString;
      } else if (xType is IntType || xType is BigOrdinalType) {
        UnsupportedFeatureError(tok, Feature.UnboundedIntegers);
        return "new BigNumber(0)";
      } else if (xType is RealType) {
        UnsupportedFeatureError(tok, Feature.RealNumbers);
        return "_dafny.BigRational.ZERO";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        if (t.NativeType != null) {
          return "0";
        } else {
          Warn("Non-native bitvector type used.  Code will not compile.", tok);
          return "new BigNumber(0)";
        }
      } else if (xType is SetType) {
        var s = (SetType)xType;
        return String.Format("DafnySet<{0}>::empty()", TypeName(s.Arg, wr, tok));
      } else if (xType is MultiSetType) {
        throw new UnsupportedFeatureException(tok, Feature.Multisets);
      } else if (xType is SeqType) {
        return string.Format("DafnySequence<{0}>()", TypeName(xType.AsSeqType.Arg, wr, tok, null, false));
      } else if (xType is MapType) {
        var m = (MapType)xType;
        return String.Format("DafnyMap<{0},{1}>::empty()", TypeName(m.Domain, wr, tok), TypeName(m.Range, wr, tok));
      }

      var udt = (UserDefinedType)xType;
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is TypeParameter || cl is OpaqueTypeDecl) {
        var hasCompiledValue = (cl is TypeParameter ? ((TypeParameter)cl).Characteristics : ((OpaqueTypeDecl)cl).Characteristics).HasCompiledValue;
        if (Attributes.Contains(udt.ResolvedClass.Attributes, "extern")) {
          // Assume the external definition includes a default value
          return String.Format("{1}::get_{0}_default()", IdProtect(udt.Name), udt.ResolvedClass.EnclosingModuleDefinition.GetCompileName(Options));
        } else if (usePlaceboValue && !hasCompiledValue) {
          return String.Format("get_default<{0}>::call()", IdProtect(udt.GetCompileName(Options)));
        } else {
          return String.Format("get_default<{0}>::call()", IdProtect(udt.GetCompileName(Options)));
        }
      } else if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        if (td.Witness != null) {
          return td.EnclosingModuleDefinition.GetCompileName(Options) + "::class_" + td.GetCompileName(Options) + "::Witness";
        } else if (td.NativeType != null) {
          return "0";
        } else {
          return TypeInitializationValue(td.BaseType, wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        if (td.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
          return td.EnclosingModuleDefinition.GetCompileName(Options) + "::class_" + td.GetCompileName(Options) + "::Witness";
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            return "nullptr";
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) => rangeDefaultValue)
            return string.Format("function () {{ return {0}; }}", rangeDefaultValue);
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl) {
            // non-null array type; we know how to initialize them
            var arrayClass = (ArrayClassDecl)((NonNullTypeDecl)td).Class;
            Type elType = UserDefinedType.ArrayElementType(xType);
            if (arrayClass.Dims == 1) {
              return string.Format("DafnyArray<{0}>::Null()", TypeName(elType, wr, tok));
            } else {
              return string.Format("_dafny.newArray(nullptr, {0})", Util.Comma(arrayClass.Dims, _ => "0"));
            }
          } else {
            // non-null (non-array) type
            // even though the type doesn't necessarily have a known initializer, it could be that the the compiler needs to
            // lay down some bits to please the C++ compiler's different definite-assignment rules.
            return "nullptr";
          }
        } else {
          return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
        }
      } else if (cl is ClassDecl) {
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "0";
        } else {
          if (cl is ArrayClassDecl) {
            var arrayClass = (ArrayClassDecl)cl;
            Type elType = UserDefinedType.ArrayElementType(xType);
            if (arrayClass.Dims == 1) {
              return string.Format("DafnyArray<{0}>::Null()", TypeName(elType, wr, tok));
            } else {
              throw new UnsupportedFeatureException(tok, Feature.MultiDimensionalArrays);
            }
          } else {
            return "nullptr";
          }
        }
      } else if (cl is DatatypeDecl) {
        var dt = (DatatypeDecl)cl;
        var s = dt is TupleTypeDecl ? "Tuple" : FullTypeName(udt);
        var w = new ConcreteSyntaxTree();
        w.Write("{0}{1}()", s, InstantiateTemplate(udt.TypeArgs));
        return w.ToString();
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }

    }

    private string ActualTypeArgs(List<Type> typeArgs) {
      return typeArgs.Count > 0
        ? String.Format(" <{0}> ", Util.Comma(typeArgs, tp => TypeName(tp, null, Token.NoToken))) : "";
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance, List<Type> typeArgs,
      ConcreteSyntaxTree wr, IToken tok, bool omitTypeArguments) {
      Contract.Assume(fullCompileName != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(typeArgs != null);  // precondition; this ought to be declared as a Requires in the superclass
      string s = IdProtect(fullCompileName);
      return String.Format("std::shared_ptr<{0}{1}>", s, ActualTypeArgs(typeArgs));
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member) {
      // There are no companion classes for Cpp
      var t = TypeName(type, wr, tok, member, true);
      return t;
    }

    // ----- Declarations -------------------------------------------------------------
    protected override void DeclareExternType(OpaqueTypeDecl d, Expression compileTypeHint, ConcreteSyntaxTree wr) {
      if (compileTypeHint.AsStringLiteral() == "struct") {
        modDeclWr.WriteLine("// Extern declaration of {1}\n{0} struct {1};", DeclareTemplate(d.TypeArgs), d.Name);
      } else {
        Error(d.tok, "Opaque type ('{0}') with unrecognized extern attribute {1} cannot be compiled.  Expected {{:extern compile_type_hint}}, e.g., 'struct'.", wr, d.FullName, compileTypeHint.AsStringLiteral());
      }
    }

    protected void DeclareField(string className, List<TypeParameter> targs, string name, bool isStatic, bool isConst, Type type, IToken tok, string rhs, ConcreteSyntaxTree wr, ConcreteSyntaxTree finisher) {
      var r = rhs != null ? rhs : DefaultValue(type, wr, tok);
      var t = TypeName(type, wr, tok);
      if (isStatic) {
        wr.WriteLine("static {0} {1};", t, name);
        finisher.WriteLine("{5} {0} {1}{4}::{2} = {3};", t, className, name, r, InstantiateTemplate(targs), DeclareTemplate(targs));
      } else {
        wr.WriteLine("{0} {1} = {2};", t, name, r);
      }
    }

    private string DeclareFormalString(string prefix, string name, Type type, IToken tok, bool isInParam) {
      if (isInParam) {
        var result = String.Format("{0}{2} {1}", prefix, name, TypeName(type, null, tok));
        if (name == "__noArgsParameter") {
          result += " __attribute__((unused))";
        }

        return result;
      } else {
        return null;
      }
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IToken tok, bool isInParam, ConcreteSyntaxTree wr) {
      var formal_str = DeclareFormalString(prefix, name, type, tok, isInParam);
      if (formal_str != null) {
        wr.Write(formal_str);
        return true;
      } else {
        return false;
      }
    }

    private string DeclareFormals(List<Formal> formals) {
      var i = 0;
      var ret = "";
      var sep = "";
      foreach (Formal arg in formals) {
        if (!arg.IsGhost) {
          string name = FormalName(arg, i);
          string decl = DeclareFormalString(sep, name, arg.Type, arg.tok, arg.InParam);
          if (decl != null) {
            ret += decl;
            sep = ", ";
          }
          i++;
        }
      }
      return ret;
    }

    protected override void DeclareLocalVar(string name, Type/*?*/ type, IToken/*?*/ tok, bool leaveRoomForRhs, string/*?*/ rhs, ConcreteSyntaxTree wr) {
      if (type != null) {
        wr.Write("{0} ", TypeName(type, wr, tok));
      } else {
        wr.Write("auto ");
      }
      wr.Write("{0}", name);
      if (leaveRoomForRhs) {
        Contract.Assert(rhs == null);  // follows from precondition
      } else if (rhs != null) {
        wr.WriteLine(" = {0};", rhs);
      } else {
        wr.WriteLine(";");
      }
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type/*?*/ type, IToken/*?*/ tok, ConcreteSyntaxTree wr) {
      if (type != null) {
        wr.Write("{0} ", TypeName(type, wr, tok));
      } else {
        wr.Write("auto ");
      }
      wr.Write("{0} = ", name);
      var w = wr.Fork();
      wr.WriteLine(";");
      return w;
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;

    protected override void DeclareOutCollector(string collectorVarName, ConcreteSyntaxTree wr) {
      wr.Write("auto {0} = ", collectorVarName);
    }

    protected override void DeclareLocalOutVar(string name, Type type, IToken tok, string rhs, bool useReturnStyleOuts, ConcreteSyntaxTree wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override void EmitOutParameterSplits(string outCollector, List<string> actualOutParamNames, ConcreteSyntaxTree wr) {
      if (actualOutParamNames.Count == 1) {
        EmitAssignment(actualOutParamNames[0], null, outCollector, null, wr);
      } else {
        for (var i = 0; i < actualOutParamNames.Count; i++) {
          wr.WriteLine("{0} = {1}.template get<{2}>();", actualOutParamNames[i], outCollector, i);
        }
      }
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      wr.Write(ActualTypeArgs(typeArgs));
    }

    protected override string GenerateLhsDecl(string target, Type/*?*/ type, ConcreteSyntaxTree wr, IToken tok) {
      return "auto " + target;
    }

    protected void EmitNullText(Type type, ConcreteSyntaxTree wr) {
      var xType = type.NormalizeExpand();
      if (xType.IsArrayType) {
        ArrayClassDecl at = xType.AsArrayType;
        Contract.Assert(at != null);  // follows from xType.IsArrayType
        Type elType = UserDefinedType.ArrayElementType(xType);
        if (at.Dims == 1) {
          wr.Write("DafnyArray<{0}>::Null()", TypeName(elType, wr, null));
        } else {
          throw new UnsupportedFeatureException(Token.NoToken, Feature.MultiDimensionalArrays);
        }
      } else {
        wr.Write("nullptr");
      }
    }

    protected override void EmitNull(Type type, ConcreteSyntaxTree wr) {
      EmitNullText(type, wr);
    }

    // ----- Statements -------------------------------------------------------------

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      var wStmts = wr.Fork();
      wr.Write("dafny_print(");
      wr.Append(Expr(arg, false, wStmts));
      wr.WriteLine(");");
    }

    protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr) {
      outParams = outParams.Where(f => !f.IsGhost).ToList();
      if (!outParams.Any()) {
        wr.WriteLine("return;");
      } else if (outParams.Count == 1) {
        wr.WriteLine("return {0};", IdName(outParams[0]));
      } else {
        wr.WriteLine("return Tuple{0}({1});", InstantiateTemplate(outParams.ConvertAll(o => o.Type)), Util.Comma(outParams, IdName));
      }
    }

    protected override ConcreteSyntaxTree CreateLabeledCode(string label, bool createContinueLabel, ConcreteSyntaxTree wr) {
      var w = wr.Fork();
      var prefix = createContinueLabel ? "continue_" : "after_";
      wr.Fork(-1).WriteLine($"{prefix}{label}: ;");
      return w;
    }

    protected override void EmitBreak(string/*?*/ label, ConcreteSyntaxTree wr) {
      if (label == null) {
        wr.WriteLine("break;");
      } else {
        wr.WriteLine("goto after_{0};", label);
      }
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
      wr.WriteLine("goto continue_{0};", label);
    }

    protected override void EmitYield(ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.Iterators);
    }

    protected override void EmitAbsurd(string/*?*/ message, ConcreteSyntaxTree wr) {
      if (message == null) {
        message = "unexpected control point";
      }
      wr.WriteLine("throw \"{0}\";", message);
    }

    protected override void EmitHalt(IToken tok, Expression messageExpr, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.Write("throw DafnyHaltException(");
      if (tok != null) {
        wr.Write("\"" + Dafny.ErrorReporter.TokenToString(tok) + ": \" + ");
      }

      if (messageExpr.Type.IsStringType) {
        wr.Write("ToVerbatimString(");
        wr.Append(Expr(messageExpr, false, wStmts));
        wr.Write(")");
      } else {
        throw new UnsupportedFeatureException(tok, Feature.ConvertingValuesToStrings);
      }

      wr.WriteLine(");");
    }

    protected override ConcreteSyntaxTree EmitForStmt(IToken tok, IVariable loopIndex, bool goingUp, string /*?*/ endVarName,
      List<Statement> body, LList<Label> labels, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(tok, Feature.ForLoops, "for loops have not yet been implemented");
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, string bound, ConcreteSyntaxTree wr, string start = null) {
      start = start ?? "0";
      return wr.NewNamedBlock("for (auto {0} = {2}; {0} < {1}; {0}++)", indexVar, bound, start);
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      return wr.NewNamedBlock("for (unsigned long long {0} = 1; ; {0} = {0} * 2)", indexVar, start);
    }

    protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine("{0} += 1;", varName);
    }

    protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine("{0} = {0} -= 1;", varName);
    }

    protected override string GetQuantifierName(string bvType) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.Quantifiers);
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IToken tok,
      out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      wr.Write("for ({1} {0} : ", tmpVarName, TypeName(collectionElementType, wr, tok));
      collectionWriter = wr.Fork();
      var wwr = wr.NewBlock(")");
      return wwr;
    }

    [CanBeNull]
    protected override string GetSubtypeCondition(string tmpVarName, Type boundVarType, IToken tok, ConcreteSyntaxTree wPreconditions) {
      string typeTest;
      if (boundVarType.IsRefType) {
        if (boundVarType.IsObject || boundVarType.IsObjectQ) {
          typeTest = "true";
        } else if (boundVarType.IsTraitType) {
          typeTest = $"_dafny.InstanceOfTrait({tmpVarName}, {TypeName(boundVarType, wPreconditions, tok)})";
        } else {
          typeTest = $"typeid({tmpVarName}) is typeid({TypeName(boundVarType, wPreconditions, tok)})";
        }
        if (boundVarType.IsNonNullRefType) {
          typeTest = $"{tmpVarName} != null && {typeTest}";
        } else {
          typeTest = $"{tmpVarName} == null || {typeTest}";
        }
      } else {
        typeTest = "true";
      }

      return typeTest == "true" ? null : typeTest;
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type collectionElementType, bool introduceBoundVar, IToken tok, ConcreteSyntaxTree wr) {
      var typeName = TypeName(boundVarType, wr, tok);
      wr.WriteLine("{0}{1} = ({2}){3};", introduceBoundVar ? typeName + " " : "", boundVarName, typeName, tmpVarName);
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs, out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      wr.Write($"for (auto {boundVarName} : ");
      collectionWriter = wr.Fork();
      return wr.NewBlock(")");
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitNew(Type type, IToken tok, CallStmt initCall /*?*/, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var cl = (type.NormalizeExpand() as UserDefinedType)?.ResolvedClass;
      if (cl != null && cl.Name == "object") {
        //wr.Write("_dafny.NewObject()");
        throw new UnsupportedFeatureException(tok, Feature.NewObject,
          "Tried to emit new generic object, which C++ doesn't do");
      } else {
        var ctor = initCall == null ? null : (Constructor)initCall.Method;  // correctness of cast follows from precondition of "EmitNew"
        wr.Write("std::make_shared<{0}> (", TypeName(type, wr, tok, null, true));
        var tas = TypeArgumentInstantiation.ListFromClass(cl, type.TypeArgs);
        var sep = "";
        EmitTypeDescriptorsActuals(tas, tok, wr, ref sep);
        string q, n;
        if (ctor != null && ctor.IsExtern(Options, out q, out n)) {
          // the arguments of any external constructor are placed here
          for (int i = 0; i < ctor.Ins.Count; i++) {
            Formal p = ctor.Ins[i];
            if (!p.IsGhost) {
              wr.Write(sep);
              wr.Append(Expr(initCall.Args[i], false, wStmts));
              sep = ", ";
            }
          }
        }
        wr.Write(")");
      }
    }

    protected override void EmitNewArray(Type elementType, IToken tok, List<string> dimensions,
        bool mustInitialize, [CanBeNull] string exampleElement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var initValue = mustInitialize ? DefaultValue(elementType, wr, tok) : null;
      // TODO: Handle initValue
      if (dimensions.Count == 1) {
        // handle the common case of 1-dimensional arrays separately
        wr.Write($"DafnyArray<{TypeName(elementType, wr, tok)}>::New({dimensions[0]})");
      } else {
        throw new UnsupportedFeatureException(tok, Feature.MultiDimensionalArrays);
      }
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write(TypeName(e.Type, wr, e.tok));
      } else if (e.Value == null) {
        EmitNullText(e.Type, wr);
      } else if (e.Value is bool) {
        wr.Write((bool)e.Value ? "true" : "false");
      } else if (e is CharLiteralExpr) {
        var v = (string)e.Value;
        wr.Write("'{0}'", v);
      } else if (e is StringLiteralExpr) {
        var str = (StringLiteralExpr)e;
        wr.Write("DafnySequenceFromString(");
        TrStringLiteral(str, wr);
        wr.Write(")");
      } else if (AsNativeType(e.Type) is NativeType nt) {
        wr.Write("({0}){1}", GetNativeTypeName(nt), (BigInteger)e.Value);
        if ((BigInteger)e.Value > 9223372036854775807) {
          // Avoid compiler warning: integer literal is too large to be represented in a signed integer type
          wr.Write("U");
        }
      } else if (e.Value is BigInteger i) {
        EmitIntegerLiteral(i, wr);
      } else if (e.Value is BaseTypes.BigDec) {
        throw new UnsupportedFeatureException(e.tok, Feature.RealNumbers);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
      }
    }
    void EmitIntegerLiteral(BigInteger i, ConcreteSyntaxTree wr) {
      Contract.Requires(wr != null);
      wr.Write(i.ToString());
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
      var n = str.Length;
      if (!isVerbatim) {
        wr.Write($"\"{TranslateEscapes(str)}\"");
      } else {
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

      // Use the postfix "..."s operator (operator""s) to convert to std::string values
      // without interpreting /0 as a terminator:
      // https://en.cppreference.com/w/cpp/string/basic_string/operator%22%22s
      wr.Write("s");
    }

    private static string TranslateEscapes(string s) {
      s = Util.ReplaceNullEscapesWithCharacterEscapes(s);
      // TODO: Other cases, once we address the fact that we shouldn't be
      // using the C++ char as the Dafny 16-bit char in the first place.
      return s;
    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      string nativeName = null, literalSuffix = null;
      bool needsCastAfterArithmetic = false;
      if (bvType.NativeType != null) {
        GetNativeInfo(bvType.NativeType.Sel, out nativeName, out literalSuffix, out needsCastAfterArithmetic);
      }

      if (bvType.NativeType == null) {
        throw new UnsupportedFeatureException(Token.NoToken, Feature.UnboundedIntegers, "EmitBitvectorTruncation with BigInteger value");
      } else if (bvType.NativeType.Bitwidth == bvType.Width) {
        // no truncation needed
        return wr;
      } else {
        wr.Write("((");
        var middle = wr.Fork();
        // print in hex, because that looks nice
        wr.Write(") & 0x{0:X}{1})", (1UL << bvType.Width) - 1, literalSuffix);
        return middle;
      }
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
      bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      throw new UnsupportedFeatureException(e0.tok, Feature.BitvectorRotateFunctions);
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.NonSequentializableForallStatements);
    }

    protected override ConcreteSyntaxTree EmitAddTupleToList(string ingredients, string tupleTypeArgs, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.NonSequentializableForallStatements);
    }

    protected override void EmitTupleSelect(string prefix, int i, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.NonSequentializableForallStatements);
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }

    public override string PublicIdProtect(string name) {
      Contract.Requires(name != null);
      switch (name) {
        // Taken from: https://www.w3schools.in/cplusplus-tutorial/keywords/
        // Keywords
        case "asm":
        case "auto":
        case "bool":
        case "break":
        case "case":
        case "catch":
        case "char":
        case "class":
        case "const":
        case "const_cast":
        case "continue":
        case "default":
        case "delete":
        case "do":
        case "double":
        case "dynamic_cast":
        case "else":
        case "enum":
        case "explicit":
        case "export":
        case "extern":
        case "false":
        case "float":
        case "for":
        case "friend":
        case "goto":
        case "if":
        case "inline":
        case "int":
        case "long":
        case "mutable":
        case "namespace":
        case "new":
        case "operator":
        case "private":
        case "public":
        case "register":
        case "reinterpret_cast":
        case "return":
        case "short":
        case "signed":
        case "sizeof":
        case "static":
        case "static_cast":
        case "struct":
        case "switch":
        case "template":
        case "this":
        case "throw":
        case "true":
        case "try":
        case "typedef":
        case "typeid":
        case "typename":
        case "union":
        case "unsigned":
        case "using":
        case "virtual":
        case "void":
        case "volatile":
        case "wchar_t":
        case "while":

        // Also reserved
        case "And":
        case "and_eq":
        case "bitand":
        case "bitor":
        case "compl":
        case "not":
        case "not_eq":
        case "or":
        case "or_eq":
        case "xor":
        case "xor_eq":
          return name + "_";
        default:
          return name;
      }
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl/*?*/ member = null) {
      Contract.Assume(udt != null);  // precondition; this ought to be declared as a Requires in the superclass
      if (udt is ArrowType) {
        throw new UnsupportedFeatureException(udt.tok, Feature.FunctionValues, string.Format("UserDefinedTypeName {0}", udt.Name));
        //return ArrowType.Arrow_FullCompileName;
      }
      var cl = udt.ResolvedClass;
      if (cl is TypeParameter) {
        return IdProtect(udt.GetCompileName(Options));
      } else if (cl is ClassDecl cdecl && cdecl.IsDefaultClass && Attributes.Contains(cl.EnclosingModuleDefinition.Attributes, "extern") &&
                 member != null && Attributes.Contains(member.Attributes, "extern")) {
        // omit the default class name ("_default") in extern modules, when the class is used to qualify an extern member
        Contract.Assert(!cl.EnclosingModuleDefinition.IsDefaultModule); // default module is not marked ":extern"
        return IdProtect(cl.EnclosingModuleDefinition.GetCompileName(Options));
      } else if (Attributes.Contains(cl.Attributes, "extern")) {
        return IdProtect(cl.EnclosingModuleDefinition.GetCompileName(Options)) + "::" + IdProtect(cl.Name);
      } else if (cl is TupleTypeDecl) {
        if (udt.TypeArgs.Count > 0) {
          return "Tuple";
        } else {
          return "Tuple0"; // Need to special case this, as C++ won't infer the correct type arguments
        }
      } else {
        return IdProtect(cl.EnclosingModuleDefinition.GetCompileName(Options)) + "::" + IdProtect(cl.GetCompileName(Options));
      }
    }

    protected override void EmitThis(ConcreteSyntaxTree wr) {
      wr.Write("this");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, ConcreteSyntaxTree wr) {
      EmitDatatypeValue(dtv, dtv.Ctor, dtv.IsCoCall, arguments, wr);
    }

    void EmitDatatypeValue(DatatypeValue dtv, DatatypeCtor ctor, bool isCoCall, string arguments, ConcreteSyntaxTree wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      var dtName = dt.GetCompileName(Options);
      var ctorName = ctor.GetCompileName(Options);

      if (dt is TupleTypeDecl) {
        var tuple = dt as TupleTypeDecl;
        var types = new List<Type>();
        foreach (var arg in dtv.Arguments) {
          types.Add(arg.Type);
        }

        if (types.Count == 0) {
          wr.Write("Tuple0()");
        } else {
          wr.Write("Tuple{0}({1})", InstantiateTemplate(types), arguments);
        }
      } else if (!isCoCall) {
        // Ordinary constructor (that is, one that does not guard any co-recursive calls)
        // Generate:  Dt.create_Ctor(arguments)
        if (dt.Ctors.Count == 1) {
          wr.Write("{3}::{0}{1}({2})",
            dtName,
            InstantiateTemplate(dt.TypeArgs),
            arguments,
            dt.EnclosingModuleDefinition.GetCompileName(Options));
        } else {
          wr.Write("{4}::{0}{1}::create_{2}({3})",
            dtName, ActualTypeArgs(dtv.InferredTypeArgs), ctorName,
            arguments, dt.EnclosingModuleDefinition.GetCompileName(Options));
        }

      } else {
        // Co-recursive call
        // Generate:  Dt.lazy_Ctor(($dt) => Dt.create_Ctor($dt, args))
        wr.Write("{0}.lazy_{1}(($dt) => ", dtName, ctorName);
        wr.Write("{0}.create_{1}($dt{2}{3})", dtName, ctorName, arguments.Length == 0 ? "" : ", ", arguments);
        wr.Write(")");
      }
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, Type receiverType, out string compiledName, out string preString, out string postString) {
      compiledName = "";
      preString = "";
      postString = "";
      switch (id) {
        case SpecialField.ID.UseIdParam:
          compiledName = (string)idParam;
          break;
        case SpecialField.ID.ArrayLength:
        case SpecialField.ID.ArrayLengthInt:
          throw new UnsupportedFeatureException(Token.NoToken, Feature.ArrayLength);
        case SpecialField.ID.Floor:
          compiledName = "int()";
          break;
        case SpecialField.ID.IsLimit:
          throw new UnsupportedFeatureException(Token.NoToken, Feature.Ordinals);
        case SpecialField.ID.IsSucc:
          throw new UnsupportedFeatureException(Token.NoToken, Feature.Ordinals);
        case SpecialField.ID.Offset:
          throw new UnsupportedFeatureException(Token.NoToken, Feature.Ordinals);
        case SpecialField.ID.IsNat:
          throw new UnsupportedFeatureException(Token.NoToken, Feature.Ordinals);
        case SpecialField.ID.Keys:
          compiledName = "dafnyKeySet()";
          break;
        case SpecialField.ID.Values:
          compiledName = "dafnyValues()";
          break;
        case SpecialField.ID.Items:
          throw new UnsupportedFeatureException(Token.NoToken, Feature.MapItems);
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

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member, List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap,
      Type expectedType, string/*?*/ additionalCustomParameter = null, bool internalAccess = false) {
      if (member.IsStatic && member is ConstantField) {
        // This used to work, but now obj comes in wanting to use TypeName on the class, which results in (std::shared_ptr<_module::MyClass>)::c;
        //return SuffixLvalue(obj, "::{0}", member.CompileName);
        return SimpleLvalue(wr => {
          wr.Write("{0}::{1}::{2}", IdProtect(member.EnclosingClass.EnclosingModuleDefinition.GetCompileName(Options)), IdProtect(member.EnclosingClass.GetCompileName(Options)), IdProtect(member.GetCompileName(Options)));
        });
      } else if (member is DatatypeDestructor dtor && dtor.EnclosingClass is TupleTypeDecl) {
        return SuffixLvalue(obj, ".get<{0}>()", dtor.Name);
      } else if (member is SpecialField sf2 && sf2.SpecialId == SpecialField.ID.UseIdParam && sf2.IdParam is string fieldName
                 && fieldName.StartsWith("is_")) {
        // Ugly hack of a check to figure out if this is a datatype query: f.Constructor?
        return SuffixLvalue(obj, ".is_{0}_{1}()", IdProtect(sf2.EnclosingClass.GetCompileName(Options)), fieldName.Substring(3));
      } else if (member is SpecialField sf) {
        string compiledName, preStr, postStr;
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, objType, out compiledName, out preStr, out postStr);
        if (sf.SpecialId == SpecialField.ID.Keys || sf.SpecialId == SpecialField.ID.Values) {
          return SuffixLvalue(obj, ".{0}", compiledName);
        } else if (sf is DatatypeDestructor dtor2) {
          if (!(dtor2.EnclosingClass is IndDatatypeDecl)) {
            UnsupportedFeatureError(dtor2.tok, Feature.Codatatypes,
              String.Format("Unexpected use of a destructor {0} that isn't for an inductive datatype.  Panic!",
                member.Name));
          }

          var dt = dtor2.EnclosingClass as IndDatatypeDecl;
          return SimpleLvalue(wr => {
            if (dt.Ctors.Count > 1) {
              if (dtor2.Type is UserDefinedType udt && udt.ResolvedClass == dt) {
                // This a recursively defined datatype; need to dereference the pointer
                wr.Write("*");
              }

              wr.Write("(");
              obj(wr);
              wr.Write(".dtor_{0}()", sf.GetCompileName(Options));
            } else {
              wr.Write("(");
              obj(wr);
              wr.Write(".{0}", sf.GetCompileName(Options));
            }

            wr.Write(")");
          });
        } else if (!member.IsStatic && compiledName.Length != 0) {
          return SuffixLvalue(obj, "->{0}", compiledName);
        } else if (compiledName.Length != 0) {
          return SuffixLvalue(obj, "::{0}", compiledName);
        } else {
          // this member selection is handled by some kind of enclosing function call, so nothing to do here
          return SimpleLvalue(obj);
        }
      } else if (member is Function) {
        return StringLvalue(String.Format("{0}::{1}::{2}",
          IdProtect(member.EnclosingClass.EnclosingModuleDefinition.GetCompileName(Options)),
          IdName(member.EnclosingClass),
          IdName(member)
        ));
      } else {
        return SuffixLvalue(obj, "->{0}", IdName(member));
      }
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<string> indices, Type elmtType, ConcreteSyntaxTree wr) {
      var w = wr.Fork();
      foreach (var index in indices) {
        wr.Write(".at({0})", index);
      }
      return w;
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      var w = wr.Fork();
      foreach (var index in indices) {
        wr.Write(".at(");
        wr.Append(Expr(index, inLetExprBody, wStmts));
        wr.Write(")");
      }
      return w;
    }

    protected override void EmitExprAsNativeInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(expr, wr, inLetExprBody, wStmts);
      if (AsNativeType(expr.Type) == null) {
        wr.Write(".toNumber()");
      }
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(source, wr, inLetExprBody, wStmts);
      if (source.Type.NormalizeExpand() is SeqType) {
        // seq
        wr.Write(".select(");
        wr.Append(Expr(index, inLetExprBody, wStmts));
        wr.Write(")");
      } else {
        // map or imap
        wr.Write(".get(");
        wr.Append(Expr(index, inLetExprBody, wStmts));
        wr.Write(")");
      }
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
        CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(source, wr, inLetExprBody, wStmts);
      wr.Write(".update(");
      wr.Append(Expr(index, inLetExprBody, wStmts));
      wr.Write(", ");
      wr.Append(Expr(value, inLetExprBody, wStmts));
      wr.Write(")");
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo /*?*/, Expression hi /*?*/,
        bool fromArray, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (fromArray) {
        string typeName = "";

        if (source.Type.TypeArgs.Count == 0 && source.Type is UserDefinedType udt && udt.ResolvedClass != null &&
            udt.ResolvedClass is TypeSynonymDecl tsd) {
          // Hack to workaround type synonyms wrapped around the actual array type
          // TODO: Come up with a more systematic way of resolving this!
          typeName = TypeName(tsd.Rhs.TypeArgs[0], wr, source.tok, null, false);
        } else {
          typeName = TypeName(source.Type.TypeArgs[0], wr, source.tok, null, false);
        }
        if (lo == null) {
          if (hi == null) {
            wr.Write("DafnySequence<{0}>::SeqFromArray", typeName);
            TrParenExpr(source, wr, inLetExprBody, wStmts);
          } else {
            wr.Write("DafnySequence<{0}>::SeqFromArrayPrefix(", typeName);
            TrParenExpr(source, wr, inLetExprBody, wStmts);
            wr.Write(",");
            TrParenExpr(hi, wr, inLetExprBody, wStmts);
            wr.Write(")");
          }
        } else {
          if (hi == null) {
            wr.Write("DafnySequence<{0}>::SeqFromArraySuffix(", typeName);
            TrParenExpr(source, wr, inLetExprBody, wStmts);
            wr.Write(",");
            TrParenExpr(lo, wr, inLetExprBody, wStmts);
            wr.Write(")");
          } else {
            wr.Write("DafnySequence<{0}>::SeqFromArraySlice(", typeName);
            TrParenExpr(source, wr, inLetExprBody, wStmts);
            wr.Write(",");
            TrParenExpr(lo, wr, inLetExprBody, wStmts);
            wr.Write(",");
            TrParenExpr(hi, wr, inLetExprBody, wStmts);
            wr.Write(")");
          }
        }
      } else {
        TrParenExpr(source, wr, inLetExprBody, wStmts);

        if (hi != null) {
          TrParenExpr(".take", hi, wr, inLetExprBody, wStmts);
        }
        if (lo != null) {
          TrParenExpr(".drop", lo, wr, inLetExprBody, wStmts);
        }
      }
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("DafnySequence<{0}>::Create(", TypeName(expr.Type, wr, expr.tok, null, false));
      wr.Append(Expr(expr.N, inLetExprBody, wStmts));
      wr.Write(", ");
      wr.Append(Expr(expr.Initializer, inLetExprBody, wStmts));
      wr.Write(")");
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(expr.tok, Feature.Multisets);
    }

    protected override void EmitApplyExpr(Type functionType, IToken tok, Expression function, List<Expression> arguments,
        bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(function, wr, inLetExprBody, wStmts);
      TrExprList(arguments, wr, inLetExprBody, wStmts);
    }

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
      List<Type> boundTypes, Type resultType, IToken tok, bool inLetExprBody, ConcreteSyntaxTree wr,
      ref ConcreteSyntaxTree wStmts) {
      wr.Write("(({0}) => ", Util.Comma(boundVars));
      var w = wr.Fork();
      wr.Write(")");
      TrExprList(arguments, wr, inLetExprBody, wStmts);
      return w;
    }

    protected override void EmitConstructorCheck(string source, DatatypeCtor ctor, ConcreteSyntaxTree wr) {
      wr.Write("is_{1}({0})", source, DatatypeSubStructName(ctor));
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, Type bvType, ConcreteSyntaxTree wr) {
      if (ctor.EnclosingDatatype is TupleTypeDecl) {
        wr.Write("({0}).template get<{1}>()", source, formalNonGhostIndex);
      } else {
        var dtorName = FormalName(dtor, formalNonGhostIndex);
        if (dtor.Type is UserDefinedType udt && udt.ResolvedClass == ctor.EnclosingDatatype) {
          // Recursively defined datatype requires a dereference here
          wr.Write("*");
        }

        if (ctor.EnclosingDatatype.Ctors.Count > 1) {
          wr.Write("(({0}).dtor_{1}())", source, dtorName);
        } else {
          wr.Write("(({0}).{1})", source, dtorName);
        }
      }
    }

    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IToken tok, List<string> inNames,
        Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
      wr.Write("function (");
      Contract.Assert(inTypes.Count == inNames.Count);  // guaranteed by precondition
      for (var i = 0; i < inNames.Count; i++) {
        wr.Write("{0}{1}", i == 0 ? "" : ", ", inNames[i]);
      }
      var w = wr.NewExprBlock(")");
      return w;
    }

    protected override void CreateIIFE(string bvName, Type bvType, IToken bvTok, Type bodyType, IToken bodyTok,
      ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      var w = wr.NewExprBlock("[&]({0} {1}) -> {2} ", TypeName(bvType, wr, bvTok), bvName, TypeName(bodyType, wr, bodyTok));
      wStmts = w.Fork();
      w.Write("return ");
      wrBody = w.Fork();
      w.WriteLine(";");
      wr.Write("(");
      wrRhs = wr.Fork();
      wr.Write(")");
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IToken resultTok, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var w = wr.NewBigExprBlock("[&] ", " ()");
      return w;
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IToken resultTok, string bvName,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(resultTok, Feature.LetSuchThatExpressions);
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      switch (op) {
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("!", expr, wr, inLetExprBody, wStmts);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          if (AsNativeType(expr.Type) != null) {
            wr.Write("~ ");
            TrParenExpr(expr, wr, inLetExprBody, wStmts);
          } else {
            TrParenExpr(expr, wr, inLetExprBody, wStmts);
            wr.Write(".Not()");
          }
          break;
        case ResolvedUnaryOp.Cardinality:
          TrParenExpr(expr, wr, inLetExprBody, wStmts);
          wr.Write(".size()");
          break;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
      }
    }

    bool IsDirectlyComparable(Type t) {
      Contract.Requires(t != null);
      return t.IsBoolType || t.IsCharType || AsNativeType(t) != null;
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op,
      Expression e0, Expression e1, IToken tok, Type resultType,
      out string opString,
      out string preOpString,
      out string postOpString,
      out string callString,
      out string staticCallString,
      out bool reverseArguments,
      out bool truncateResult,
      out bool convertE1_to_int,
      out bool coerceE1,
      ConcreteSyntaxTree errorWr) {

      opString = null;
      preOpString = "";
      postOpString = "";
      callString = null;
      staticCallString = null;
      reverseArguments = false;
      truncateResult = false;
      convertE1_to_int = false;
      coerceE1 = false;

      switch (op) {
        case BinaryExpr.ResolvedOpcode.Iff:
          opString = "=="; break;
        case BinaryExpr.ResolvedOpcode.Imp:
          preOpString = "!"; opString = "||"; break;
        case BinaryExpr.ResolvedOpcode.Or:
          opString = "||"; break;
        case BinaryExpr.ResolvedOpcode.And:
          opString = "&&"; break;
        case BinaryExpr.ResolvedOpcode.BitwiseAnd:
          if (AsNativeType(resultType) != null) {
            opString = "&";
          } else {
            callString = "And";
          }
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
          if (AsNativeType(resultType) != null) {
            opString = "|";
          } else {
            callString = "Or";
          }
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
          if (AsNativeType(resultType) != null) {
            opString = "^";
          } else {
            callString = "Xor";
          }
          break;

        case BinaryExpr.ResolvedOpcode.EqCommon: {
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "==";
            } else if (IsDirectlyComparable(e0.Type)) {
              opString = "==";
            } else if (e0.Type.IsRefType) {
              opString = "==";
            } else {
              //staticCallString = "==";
              opString = "==";
            }
            break;
          }
        case BinaryExpr.ResolvedOpcode.NeqCommon: {
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "!=";
              postOpString = "/* handle */";
            } else if (IsDirectlyComparable(e0.Type)) {
              opString = "!=";
            } else if (e0.Type.IsRefType) {
              opString = "!=";
            } else {
              opString = "!=";
            }
            break;
          }

        case BinaryExpr.ResolvedOpcode.Lt:
        case BinaryExpr.ResolvedOpcode.LtChar:
          opString = "<";
          break;
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.LeChar:
          opString = "<=";
          break;
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.GeChar:
          opString = ">=";
          break;
        case BinaryExpr.ResolvedOpcode.Gt:
        case BinaryExpr.ResolvedOpcode.GtChar:
          opString = ">";
          break;
        case BinaryExpr.ResolvedOpcode.LeftShift:
          if (resultType.IsBitVectorType) {
            truncateResult = true;
          }
          if (AsNativeType(resultType) != null) {
            opString = "<<";
          } else {
            throw new UnsupportedFeatureException(tok, Feature.NonNativeNewtypes,
              "LeftShift of non-native type");
          }
          break;
        case BinaryExpr.ResolvedOpcode.RightShift:
          if (AsNativeType(resultType) != null) {
            opString = ">>";
            if (AsNativeType(e1.Type) == null) {
              postOpString = ".Uint64()";
            }
          } else {
            throw new UnsupportedFeatureException(tok, Feature.NonNativeNewtypes,
              "LeftShift of non-native type");
          }
          break;
        case BinaryExpr.ResolvedOpcode.Add:
          if (resultType.IsBitVectorType) {
            truncateResult = true;
          }
          if (resultType.IsCharType || AsNativeType(resultType) != null) {
            opString = "+";
          } else {
            throw new UnsupportedFeatureException(tok, Feature.NonNativeNewtypes,
              "Add of non-native type");
          }
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          if (resultType.IsBitVectorType) {
            truncateResult = true;
          }
          if (resultType.IsCharType || AsNativeType(resultType) != null) {
            opString = "-";
          } else {
            throw new UnsupportedFeatureException(tok, Feature.NonNativeNewtypes,
                          "Subtraction of non-native type");
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          if (resultType.IsBitVectorType) {
            truncateResult = true;
          }
          if (AsNativeType(resultType) != null) {
            opString = "*";
          } else {
            throw new UnsupportedFeatureException(tok, Feature.NonNativeNewtypes,
                          "Multiplication of non-native type");
          }
          break;
        case BinaryExpr.ResolvedOpcode.Div:
          if (AsNativeType(resultType) != null) {
            var nt = AsNativeType(resultType);
            if (nt.LowerBound < BigInteger.Zero) {
              // Want Euclidean division for signed types
              staticCallString = "EuclideanDivision_" + GetNativeTypeName(AsNativeType(resultType));
            } else {
              // Native division is fine for unsigned
              opString = "/";
            }
          } else {
            callString = "DivBy";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (AsNativeType(resultType) != null) {
            var nt = AsNativeType(resultType);
            if (nt.LowerBound < BigInteger.Zero) {
              // Want Euclidean division for signed types
              staticCallString = "_dafny.Mod" + Capitalize(GetNativeTypeName(AsNativeType(resultType)));
            } else {
              // Native division is fine for unsigned
              opString = "%";
            }
          } else {
            callString = "Modulo";
          }
          break;
        case BinaryExpr.ResolvedOpcode.SetEq:
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
        case BinaryExpr.ResolvedOpcode.MapEq:
        case BinaryExpr.ResolvedOpcode.SeqEq:
          callString = "equals"; break;
        case BinaryExpr.ResolvedOpcode.SetNeq:
        case BinaryExpr.ResolvedOpcode.MultiSetNeq:
        case BinaryExpr.ResolvedOpcode.MapNeq:
        case BinaryExpr.ResolvedOpcode.SeqNeq:
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
          callString = "IsDisjointFrom"; break;
        case BinaryExpr.ResolvedOpcode.InSet:
        case BinaryExpr.ResolvedOpcode.InMultiSet:
        case BinaryExpr.ResolvedOpcode.InMap:
          callString = "contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.NotInSet:
        case BinaryExpr.ResolvedOpcode.NotInMultiSet:
        case BinaryExpr.ResolvedOpcode.NotInMap:
          preOpString = "!"; callString = "contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          callString = "Union"; break;
        case BinaryExpr.ResolvedOpcode.MapMerge:
          callString = "Merge"; break;
        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          callString = "Intersection"; break;
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          callString = "Difference"; break;
        case BinaryExpr.ResolvedOpcode.MapSubtraction:
          callString = "Subtract"; break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          callString = "IsProperPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Prefix:
          callString = "IsPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Concat:
          callString = "concatenate"; break;
        case BinaryExpr.ResolvedOpcode.InSeq:
          callString = "contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.NotInSeq:
          preOpString = "!"; callString = "contains"; reverseArguments = true; break;

        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected binary expression
      }
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      wr.Write("{0} == 0", varName);
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Int) || e.E.Type.IsBitVectorType || e.E.Type.IsCharType) {
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
          throw new UnsupportedFeatureException(e.tok, Feature.RealNumbers);
        } else if (e.ToType.IsCharType) {
          wr.Write("(char)");
          TrParenExpr(e.E, wr, inLetExprBody, wStmts);
        } else {
          // (int or bv or char) -> (int or bv or ORDINAL)
          var fromNative = AsNativeType(e.E.Type);
          var toNative = AsNativeType(e.ToType);
          if (fromNative != null && toNative != null) {
            // from a native, to a native -- simple!
            wr.Write(GetNativeTypeName(toNative));
            TrParenExpr(e.E, wr, inLetExprBody, wStmts);
          } else if (e.E.Type.IsCharType) {
            Contract.Assert(fromNative == null);
            if (toNative == null) {
              throw new UnsupportedFeatureException(e.tok, Feature.UnboundedIntegers);
            } else {
              // char -> native
              wr.Write($"({GetNativeTypeName(toNative)})");
              TrParenExpr(e.E, wr, inLetExprBody, wStmts);
            }
          } else if (fromNative == null && toNative == null) {
            // big-integer (int or bv) -> big-integer (int or bv or ORDINAL), so identity will do
            wr.Append(Expr(e.E, inLetExprBody, wStmts));
          } else if (fromNative != null) {
            Contract.Assert(toNative == null); // follows from other checks

            // native (int or bv) -> big-integer (int or bv)
            wr.Write("_dafny.IntOf{0}(", Capitalize(GetNativeTypeName(fromNative)));
            wr.Append(Expr(e.E, inLetExprBody, wStmts));
            wr.Write(')');
          } else {
            // any (int or bv) -> native (int or bv)
            // Consider some optimizations
            var literal = PartiallyEvaluate(e.E);
            UnaryOpExpr u = e.E.Resolved as UnaryOpExpr;
            MemberSelectExpr m = e.E.Resolved as MemberSelectExpr;
            if (literal != null) {
              // Optimize constant to avoid intermediate BigInteger
              wr.Write("{0}({1})", GetNativeTypeName(toNative), literal);
            } else if (u != null && u.Op == UnaryOpExpr.Opcode.Cardinality) {
              wr.Write("({0})(", GetNativeTypeName(toNative));
              TrParenExpr(u.E, wr, inLetExprBody, wStmts);
              wr.Write(".size())");
            } else if (m != null && m.MemberName == "Length" && m.Obj.Type.IsArrayType) {
              // Optimize .Length to avoid intermediate BigInteger
              wr.Write("({0})(", GetNativeTypeName(toNative));
              TrParenExpr(m.Obj, wr, inLetExprBody, wStmts);
              wr.Write(".size())");
            } else {
              // no optimization applies; use the standard translation
              TrParenExpr(e.E, wr, inLetExprBody, wStmts);
              wr.Write(".{0}()", Capitalize(GetNativeTypeName(toNative)));
            }

          }
        }
      } else if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
        Contract.Assert(AsNativeType(e.E.Type) == null);
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // real -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          wr.Append(Expr(e.E, inLetExprBody, wStmts));
        } else {
          // real -> (int or bv)
          TrParenExpr(e.E, wr, inLetExprBody, wStmts);
          wr.Write(".Int()");
          if (AsNativeType(e.ToType) is NativeType nt) {
            wr.Write(".{0}()", Capitalize(GetNativeTypeName(nt)));
          }
        }
      } else {
        Contract.Assert(e.E.Type.IsBigOrdinalType);
        Contract.Assert(e.ToType.IsNumericBased(Type.NumericPersuasion.Int));
        // identity will do
        wr.Append(Expr(e.E, inLetExprBody, wStmts));
      }
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IToken tok, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(tok, Feature.TypeTests);
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IToken tok, List<Expression> elements,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (ct is SetType) {
        wr.Write("DafnySet<{0}>::Create({{", TypeName(ct.TypeArgs[0], wr, tok, null, false));
        for (var i = 0; i < elements.Count; i++) {
          wr.Append(Expr(elements[i], inLetExprBody, wStmts));
          if (i < elements.Count - 1) {
            wr.Write(",");
          }
        }
        wr.Write("})");
      } else if (ct is MultiSetType) {
        throw new UnsupportedFeatureException(tok, Feature.Multisets);
      } else {
        Contract.Assert(ct is SeqType);  // follows from precondition
        if (ct.Arg.IsCharType) {
          throw new UnsupportedFeatureException(tok, Feature.SequenceDisplaysOfCharacters);
        } else {
          wr.Write("DafnySequence<{0}>::Create({{", TypeName(ct.TypeArgs[0], wr, tok, null, false));
          for (var i = 0; i < elements.Count; i++) {
            wr.Append(Expr(elements[i], inLetExprBody, wStmts));
            if (i < elements.Count - 1) {
              wr.Write(",");
            }
          }
          wr.Write("})");
        }
      }
    }

    protected override void EmitMapDisplay(MapType mt, IToken tok, List<ExpressionPair> elements,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("DafnyMap<{0},{1}>::Create({{",
               TypeName(mt.TypeArgs[0], wr, tok, null, false),
               TypeName(mt.TypeArgs[1], wr, tok, null, false));
      string sep = "";
      foreach (ExpressionPair p in elements) {
        wr.Write(sep);
        wr.Write("{");
        wr.Append(Expr(p.A, inLetExprBody, wStmts));
        wr.Write(",");
        wr.Append(Expr(p.B, inLetExprBody, wStmts));
        wr.Write("}");
        sep = ", ";
      }
      wr.Write("})");
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
      var wrVarInit = DeclareLocalVar(collectionName, null, null, wr);
      wrVarInit.Write("DafnySet<{0}>()", TypeName(e.Type.AsSetType.Arg, wrVarInit, e.tok, null, false));
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      throw new UnsupportedFeatureException(e.tok, Feature.MapComprehensions);
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, ConcreteSyntaxTree wr) {
      Contract.Assume(ct is SetType || ct is MultiSetType);  // follows from precondition
      if (ct is MultiSetType) {
        // This should never occur since there is no syntax for multiset comprehensions yet
        throw new cce.UnreachableException();
      }
      var wStmts = wr.Fork();
      wr.Write("{0}.set.emplace(", collName);
      wr.Append(Expr(elmt, inLetExprBody, wStmts));
      wr.WriteLine(");");
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IToken tok, string collName, Expression term, bool inLetExprBody, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(tok, Feature.MapComprehensions);
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, IToken tok, string collName, ConcreteSyntaxTree wr) {
      // collections are built in place
      return collName;
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.ExactBoundedPool);
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }
  }
}
