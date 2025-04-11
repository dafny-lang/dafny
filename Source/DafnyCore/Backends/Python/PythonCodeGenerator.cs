using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using DafnyCore.Backends.Python;
using DafnyCore.Options;
using JetBrains.Annotations;
using Microsoft.BaseTypes;

namespace Microsoft.Dafny.Compilers {

  class PythonCodeGenerator : SinglePassCodeGenerator {

    private bool PythonModuleMode;
    private string PythonModuleName;

    public PythonCodeGenerator(DafnyOptions options, ErrorReporter reporter) : base(options, reporter) {
      var pythonModuleName = Options.Get(PythonBackend.PythonModuleNameCliOption);
      PythonModuleMode = pythonModuleName != null;
      if (PythonModuleMode) {
        PythonModuleName = pythonModuleName.ToString();
      }

      if (Options?.CoverageLegendFile != null) {
        Imports.Add("DafnyProfiling", "DafnyProfiling");
      }
    }

    // Key: Fully-qualified module name with python-module-name/outer-module
    // Value: Dafny-generated Python module name without python-module-name/outer-module
    // This separation is used to identify nested extern modules,
    //   which currently cannot be used with python-module-name/outer-module.
    private readonly Dictionary<string, string> Imports = new Dictionary<string, string>();

    public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
      Feature.SubsetTypeTests,
      Feature.MethodSynthesis,
      Feature.RuntimeCoverageReport
    };

    public override string ModuleSeparator => "_";

    private const string DafnyRuntimeModule = "_dafny";
    private const string DafnyDefaultModule = "module_";
    private const string DafnySystemModule = "System_";
    private static readonly ISet<string> DafnyRuntimeGeneratedModuleNames = new HashSet<string> { DafnySystemModule, };
    const string DafnySetClass = $"{DafnyRuntimeModule}.Set";
    const string DafnyMultiSetClass = $"{DafnyRuntimeModule}.MultiSet";
    const string DafnySeqClass = $"{DafnyRuntimeModule}.Seq";
    private string DafnySeqMakerFunction => UnicodeCharEnabled ? $"{DafnyRuntimeModule}.SeqWithoutIsStrInference" : DafnySeqClass;
    const string DafnyArrayClass = $"{DafnyRuntimeModule}.Array";
    const string DafnyMapClass = $"{DafnyRuntimeModule}.Map";
    const string DafnyDefaults = $"{DafnyRuntimeModule}.defaults";
    string FormatDefaultTypeParameterValue(TopLevelDecl tp) {
      Contract.Requires(tp is TypeParameter or AbstractTypeDecl);
      return $"default_{tp.GetCompileName(Options)}";
    }
    protected override string StmtTerminator { get => ""; }
    protected override string True { get => "True"; }
    protected override string False { get => "False"; }
    protected override string Conj { get => "and"; }
    private static readonly IEnumerable<string> Keywords = new HashSet<string> { "False", "None", "True", "and", "as"
      , "assert", "async", "await", "break", "class", "continue", "def", "del", "enum", "elif", "else", "except"
      , "finally", "for", "from", "global", "if", "import", "in", "is", "lambda", "nonlocal", "not", "or", "pass"
      , "raise", "return", "try", "while", "with", "yield" };
    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
      wr.WriteLine($"# Dafny program {program.Name} compiled into Python");
      if (Options.IncludeRuntime) {
        EmitRuntimeSource("DafnyRuntimePython", wr);
      }
      if (Options.Get(CommonOptionBag.UseStandardLibraries) && Options.Get(CommonOptionBag.TranslateStandardLibrary)) {
        EmitRuntimeSource("DafnyStandardLibraries_py", wr);
      }

      Imports.Add(DafnyRuntimeModule, DafnyRuntimeModule);
      EmitImports(null, null, wr);
      wr.WriteLine();
    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      Coverage.EmitSetup(wr);
      var moduleName = IdProtect(mainMethod.EnclosingClass.EnclosingModuleDefinition.GetCompileName(Options));
      if (moduleName != DafnyDefaultModule) {
        wr.WriteLine($"import {moduleName}");
      }
      if (UnicodeCharEnabled) {
        wr.NewBlockPy("try:")
          .WriteLine($"dafnyArgs = [{DafnyRuntimeModule}.SeqWithoutIsStrInference(map({DafnyRuntimeModule}.CodePoint, a)) for a in sys.argv]")
          .WriteLine($"{mainMethod.EnclosingClass.GetFullCompileName(Options)}.{(IssueCreateStaticMain(mainMethod) ? "StaticMain" : IdName(mainMethod))}(dafnyArgs)");
      } else {
        wr.NewBlockPy("try:")
        .WriteLine($"dafnyArgs = [{DafnyRuntimeModule}.Seq(a) for a in sys.argv]")
        .WriteLine($"{mainMethod.EnclosingClass.GetFullCompileName(Options)}.{(IssueCreateStaticMain(mainMethod) ? "StaticMain" : IdName(mainMethod))}(dafnyArgs)");
      }
      wr.NewBlockPy($"except {DafnyRuntimeModule}.HaltException as e:")
        .WriteLine($"{DafnyRuntimeModule}.print(\"[Program halted] \" + e.message + \"\\n\")")
        .WriteLine("sys.exit(1)");
      Coverage.EmitTearDown(wr);
    }

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw, string argsParameterName) {
      var mw = ((ClassWriter)cw).MethodWriter.WriteLine("@staticmethod");
      return mw.NewBlockPy($"def StaticMain({argsParameterName}):");
    }

    protected override ConcreteSyntaxTree CreateModule(ModuleDefinition module, string moduleName, bool isDefault,
      ModuleDefinition externModule,
      string libraryName, Attributes moduleAttributes, ConcreteSyntaxTree wr) {
      var pythonModuleName = PythonModuleMode ? PythonModuleName + "." : "";

      moduleName = PublicModuleIdProtect(moduleName);
      // Nested extern modules should be written inside a folder
      var file = wr.NewFile($"{moduleName.Replace(".", "/")}.py");
      EmitImports(moduleName, pythonModuleName, file);
      return file;
    }

    protected override void DependOnModule(Program program, ModuleDefinition module, ModuleDefinition externModule,
      string libraryName) {
      var dependencyPythonModuleName = "";

      // If the module being depended on was compiled using module mode,
      // this module needs to rely on it using the dependency's translation record,
      // even if this module is not using module mode
      var translatedRecord = program.Compilation.AlreadyTranslatedRecord;
      translatedRecord.OptionsByModule.TryGetValue(module.FullDafnyName, out var moduleOptions);
      object dependencyModuleName = null;
      moduleOptions?.TryGetValue(PythonBackend.PythonModuleNameCliOption.Name, out dependencyModuleName);
      if (dependencyModuleName is string && !string.IsNullOrEmpty((string)dependencyModuleName)) {
        dependencyPythonModuleName = dependencyModuleName is string name ? (string)dependencyModuleName + "." : "";
        if (String.IsNullOrEmpty(dependencyPythonModuleName)) {
          Reporter.Warning(MessageSource.Compiler, ResolutionErrors.ErrorId.none, Token.Cli,
            $"Python Module Name not found for the module {module.GetCompileName(Options)}");
        }
      }

      var dependencyCompileName = IdProtect(module.GetCompileName(Options));
      // Don't import an empty module.
      // Empty modules aren't generated, so their imports aren't valid.
      if (!TranslationRecord.ModuleEmptyForCompilation(module)) {
        Imports.Add(dependencyPythonModuleName + dependencyCompileName, dependencyCompileName);
      }
    }

    private void EmitImports(string moduleName, string pythonModuleName, ConcreteSyntaxTree wr) {
      wr.WriteLine("import sys");
      wr.WriteLine("from typing import Callable, Any, TypeVar, NamedTuple");
      wr.WriteLine("from math import floor");
      wr.WriteLine("from itertools import count");
      wr.WriteLine();
      // Don't emit `import module_` for generated modules in the DafnyRuntimePython.
      // The DafnyRuntimePython doesn't have a module.py file, so the import isn't valid.
      if (!(DafnyRuntimeGeneratedModuleNames.Contains(moduleName))) {
        wr.WriteLine($"import {(PythonModuleMode ? PythonModuleName + "." + DafnyDefaultModule : DafnyDefaultModule)} as {DafnyDefaultModule}");
      }
      foreach (var module in Imports) {
        if (module.Value.Contains(".")) {
          // This code branch only applies to extern modules. (ex. module {:extern "a.b.c"})
          // If module.Value has `.`s in it, it is a nested extern module.
          // (Non-extern nested modules with `.`s in their names
          // will have their `.`s replaced with `_` before this code is executed,
          // ex. module M.N --> "M_N", and will not hit this branch.)
          // 
          // Nested externs currently CANNOT be used with python-module-name:
          //
          // 1. (Python behavior; not able to be changed)
          // Aliased Python modules cannot have `.`s in their name.
          // ex. with `import X as Y`, `Y` cannot have `.`s.
          //
          // 2. (Dafny behavior; able to be changed, but don't need to change)
          // Inside Dafny-generated Python modules,
          // references to modules do not contain the python-module-name prefix.
          // ex. If python-module-name=X.Y, and we have nested extern module "a.b.c",
          //     code generation ignores the prefix and writes `a.b.c`.
          //     Similarly, an extern non-nested module `E` is not prefixed and is generated as `E`,
          //     and a non-extern nested module `M.N` is prefixed and generated as `X.Y.M_N`.
          // (Similarly, extern modules do not contain the outer-module prefix).
          // 
          // 1. and 2. taken together prevent nested extern modules from being used with python-module-name.
          // The reference to the nested extern inside generated code MUST be `a.b.c` due to 1).
          // However, the aliased import cannot have `.`s in it due to 2).
          // So nested externs cannot be aliased.
          // Nested non-externs can be aliased (since, in 2., any nested `.`s are replaced with `_`s).
          // Non-nested externs can be aliased (since, in 2., `Y` does not have `.`s).
          //
          // There are several possible paths to supporting these features together:
          // - Modify behavior in 1 to apply prefixe (python-module-name/outer-module) to externs.
          //   This is out of scope for python-module-name, since the outer-module prefix also does not apply to externs.
          //   These are both "prefixes", and I expect any solution for python-module-name should also apply to outer-module.
          // - Modify nested extern behavior to replace `.`s with `_`s, similar to nested non-externs.
          if (!module.Value.Equals(module.Key)) {
            throw new NotSupportedException($"Nested extern modules cannot be used with python-module-name. Nested extern: {module.Value}");
          }
          // Import the nested extern module directly.
          // ex. module {:extern "a.b.c"} ==> `import a.b.c`
          wr.WriteLine($"import {module.Value}");
        } else {
          // Here, module.Key == [python-module-name][outer-module][module.Value].
          // However, in the body of the generated module, Dafny-generated code only references module.Value.
          // Alias the import to module.Value so generated code can use the module.
          //
          // ex. python-module-name `X.Y`, outer-module=`A.B`:
          // module `M` ==> `import X.Y.A_B_M as M`
          // module `M.N` ==> `import X.Y.A_B_M_N as M_N`
          // non-nested extern module `E` ==> `import X.Y.E as E` (outer-module prefix not applied to externs)
          // nested extern modules not supported with python-module-name/outer-module prefixes.
          wr.WriteLine($"import {module.Key} as {module.Value}");
        }
      }
      if (moduleName != null) {
        wr.WriteLine();
        wr.WriteLine($"# Module: {moduleName}");
        Imports.Add(pythonModuleName + moduleName, moduleName);
      }
    }

    protected override string GetHelperModuleName() => DafnyRuntimeModule;

    private static string MangleName(string name) {
      if (Keywords.Contains(name)) {
        name = $"{name}_";
      } else {
        while (name.StartsWith("_")) {
          name = $"{name[1..]}_";
        }
        if (name.Length > 0 && char.IsDigit(name[0])) {
          name = $"d_{name}";
        }
      }
      return name;
    }

    protected override IClassWriter CreateClass(string moduleName, bool isExtern, string/*?*/ fullPrintName,
      List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> superClasses, IOrigin tok, ConcreteSyntaxTree wr) {
      var realSuperClasses = superClasses?.Where(trait => !trait.IsObject).ToList() ?? [];
      var baseClasses = realSuperClasses.Any()
        ? $"({realSuperClasses.Comma(trait => TypeName(trait, wr, tok))})"
        : "";
      var name = IdName(cls);
      var methodWriter = wr.NewBlockPy(header: $"class {IdProtect(name)}{baseClasses}:");

      var relevantTypeParameters = typeParameters.Where(NeedsTypeDescriptor).ToList();
      var args = relevantTypeParameters.Comma(tp => tp.GetCompileName(Options));
      if (!string.IsNullOrEmpty(args)) { args = $", {args}"; }
      var isNewtypeWithTraits = cls is NewtypeDecl { Traits: { Count: > 0 } };
      if (isNewtypeWithTraits) {
        args += ", value";
      }
      var block = methodWriter.NewBlockPy(header: $"def  __init__(self{args}):", close: BlockStyle.Newline);
      foreach (var tp in relevantTypeParameters) {
        block.WriteLine("self.{0} = {0}", tp.GetCompileName(Options));
      }
      var constructorWriter = block.Fork();
      block.WriteLine("pass");

      if (cls is not DefaultClassDecl && (fullPrintName != null || isNewtypeWithTraits)) {
        var wBody = methodWriter.NewBlockPy("def __dafnystr__(self) -> str:");
        if (isNewtypeWithTraits) {
          wBody.WriteLine("return _dafny.string_of(self._value)");
        } else {
          wBody.WriteLine($"return \"{fullPrintName}\"");
        }
      }

      return new ClassWriter(this, constructorWriter, methodWriter);
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters,
      TraitDecl trait, List<Type> superClasses, IOrigin tok, ConcreteSyntaxTree wr) {
      var methodWriter = wr.NewBlockPy(header: $"class {IdProtect(name)}:");
      // Avoids problems with member-less traits 
      if (trait is TraitDecl tr && tr.Members.All(m => m.IsGhost || !m.IsStatic)) {
        methodWriter.WriteLine("pass");
      }
      return new ClassWriter(this, methodWriter, methodWriter);
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      var cw = (ClassWriter)CreateClass(PublicModuleIdProtect(iter.EnclosingModuleDefinition.GetCompileName(Options)), false,
        iter.FullName, iter.TypeArgs, iter, null, iter.Origin, wr);
      var constructorWriter = cw.ConstructorWriter;
      var w = cw.MethodWriter;
      // here come the fields
      Constructor ct = null;
      foreach (var member in iter.Members) {
        switch (member) {
          case Field { IsGhost: false } f:
            DeclareField(IdName(f), false, false, f.Type, f.Origin, PlaceboValue(f.Type, constructorWriter, f.Origin, true), constructorWriter);
            break;
          case Constructor constructor:
            Contract.Assert(ct == null);  // we're expecting just one constructor
            ct = constructor;
            break;
        }
      }
      Contract.Assert(ct != null);  // we do expect a constructor
      constructorWriter.WriteLine("self._iter = None");

      var nonNullIns = ct.Ins.Where(f => !f.IsGhost).ToList();
      var args = nonNullIns.Select(IdName).Prepend("self").Comma();
      var wCtor = w.NewBlockPy($"def {IdName(ct)}({args}):");
      foreach (var p in nonNullIns) {
        wCtor.WriteLine("self.{0} = {0}", IdName(p));
      }
      wCtor.WriteLine("self._iter = self.TheIterator()");

      var wMoveNext = w.NewBlockPy("def MoveNext(self):");
      wMoveNext.NewBlockPy("try:")
        .WriteLine("next(self._iter)")
        .WriteLine("return True");
      wMoveNext.NewBlockPy("except (StopIteration, TypeError) as e:")
        .WriteLine("return False");

      return w.NewBlockPy("def TheIterator(self):");
    }

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {

      if (dt is TupleTypeDecl) {
        return null;
      }

      var DtT = IdProtect(dt.GetCompileName(Options));

      var baseClasses = dt.ParentTypeInformation.UniqueParentTraits().Any()
        ? $"({dt.ParentTypeInformation.UniqueParentTraits().Comma(trait => TypeName(trait, wr, dt.Origin))})"
        : "";
      var btw = wr.NewBlockPy($"class {DtT}{baseClasses}:", close: BlockStyle.Newline);

      if (dt.HasFinitePossibleValues) {
        btw.WriteLine($"@{DafnyRuntimeModule}.classproperty");
        var w = btw.NewBlockPy(
          $"def AllSingletonConstructors(cls):");
        var values = dt.Ctors.Select(ctor =>
          ctor.IsGhost
          ? ForcePlaceboValue(UserDefinedType.FromTopLevelDecl(dt.Origin, dt), w, dt.Origin)
          : $"{DtCtorDeclarationName(ctor)}()");
        w.WriteLine($"return [{values.Comma()}]");
      }

      btw.WriteLine($"@classmethod");
      var wDefault = btw.NewBlockPy($"def default(cls, {UsedTypeParameters(dt, true).Comma(FormatDefaultTypeParameterValue)}):");
      var groundingCtor = dt.GetGroundingCtor();
      if (groundingCtor.IsGhost) {
        wDefault.WriteLine($"return lambda: {ForcePlaceboValue(UserDefinedType.FromTopLevelDecl(dt.Origin, dt), wDefault, dt.Origin)}");
      } else if (DatatypeWrapperEraser.GetInnerTypeOfErasableDatatypeWrapper(Options, dt, out var innerType)) {
        wDefault.WriteLine($"return lambda: {DefaultValue(innerType, wDefault, dt.Origin)}");
      } else {
        var wTypeDescriptors = new ConcreteSyntaxTree();
        var typeDescriptorComma = "";
        WriteRuntimeTypeDescriptorsFormals(TypeArgumentInstantiation.ListFromFormals(dt.TypeArgs),
          wTypeDescriptors, ref typeDescriptorComma, FormatDefaultTypeParameterValue);
        var typeDescriptorUses = wTypeDescriptors.ToString();

        var nonGhostFormals = groundingCtor.Formals.Where(f => !f.IsGhost).ToList();
        var arguments = nonGhostFormals.Comma(f => DefaultValue(f.Type, wDefault, f.Origin));
        wDefault.Write("return lambda: ");
        EmitDatatypeValue(dt, groundingCtor, dt is CoDatatypeDecl, typeDescriptorUses, arguments, wDefault, false);
        wDefault.WriteLine();
      }

      // Ensures the inequality is based on equality defined in the constructor
      btw.NewBlockPy("def __ne__(self, __o: object) -> bool:")
        .WriteLine("return not self.__eq__(__o)");

      if (dt is CoDatatypeDecl) {
        var w = wr.NewBlockPy($"class {dt.GetCompileName(Options)}__Lazy({IdName(dt)}):");
        w.NewBlockPy("def __init__(self, _c):")
          .WriteLine("self._c = _c")
          .WriteLine("self._d = None");
        var get = w.NewBlockPy($"def _get(self):");
        get.NewBlockPy("if self._c is not None:")
          .WriteLine("self._d = self._c()")
          .WriteLine("self._c = None");
        get.WriteLine("return self._d");
        w.NewBlockPy("def __dafnystr__(self) -> str:")
          .WriteLine($"return {DafnyRuntimeModule}.string_of(self._get())");
        foreach (var destructor in from ctor in dt.Ctors
                                   let index = 0
                                   from dtor in ctor.Destructors
                                   where dtor.EnclosingCtors[0] == ctor
                                   select dtor.CorrespondingFormals[0] into arg
                                   where !arg.IsGhost
                                   select IdProtect(arg.GetOrCreateCompileName(dt.CodeGenIdGenerator))) {
          w.WriteLine("@property");
          w.NewBlockPy($"def {destructor}(self):")
            .WriteLine($"return self._get().{destructor}");
        }
      }

      foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
        // Class-level fields don't work in all python version due to metaclasses.
        // Adding a more restrictive type would be desirable, but Python expects their definition to precede this.
        var argListX = dt.TypeArgs.Where(NeedsTypeDescriptor)
          .Select(tp => $"('{IdProtect(tp.GetCompileName(Options))}', Any)");
        var argListY = ctor.Destructors.Where(d => !d.IsGhost)
          .Select(d => $"('{IdProtect(d.GetCompileName(Options))}', Any)");
        var argList = argListX.Concat(argListY).Comma();
        var namedtuple = $"NamedTuple('{IdProtect(ctor.GetCompileName(Options))}', [{argList}])";
        var header = $"class {DtCtorDeclarationName(ctor)}({DtT}, {namedtuple}):";
        var constructor = wr.NewBlockPy(header, close: BlockStyle.Newline);
        DatatypeFieldsAndConstructor(ctor, constructor);

        // @property
        // def is_Ctor0(self) -> bool:
        //   return isinstance(self, Dt_Ctor0) }
        btw.WriteLine("@property");
        btw.NewBlockPy($"def is_{ctor.GetCompileName(Options)}(self) -> bool:")
          .WriteLine($"return isinstance(self, {DtCtorDeclarationName(ctor)})");
      }

      return new ClassWriter(this, btw, btw);
    }

    private void DatatypeFieldsAndConstructor(DatatypeCtor ctor, ConcreteSyntaxTree wr) {
      var dt = ctor.EnclosingDatatype;

      // Dt.Ctor
      var fString = (dt.EnclosingModuleDefinition.TryToAvoidName ? "" : dt.EnclosingModuleDefinition.Name + ".") +
                dt.Name + "." + ctor.Name;

      // {self.Dtor0}, {self.Dtor1}, ..., {self.DtorN}
      var args = ctor.Formals
        .Where(f => !f.IsGhost)
        .Select(f => {
          if (f.Type.IsStringType && UnicodeCharEnabled) {
            return $"{{self.{IdProtect(f.CompileName)}.VerbatimString(True)}}";
          } else {
            return $"{{{DafnyRuntimeModule}.string_of(self.{IdProtect(f.CompileName)})}}";
          }
        })
        .Comma();

      if (args.Length > 0 && dt is not CoDatatypeDecl) {
        fString += $"({args})";
      }

      wr.NewBlockPy("def __dafnystr__(self) -> str:")
        .WriteLine($"return f\'{fString.Replace("\'", "\\\'")}\'");

      var argList = ctor.Formals
        .Where(f => !f.IsGhost)
        .Select(f => $"self.{IdProtect(f.CompileName)} == __o.{IdProtect(f.CompileName)}");
      var suffix = args.Length > 0 ? $" and {string.Join(" and ", argList)}" : "";

      wr.NewBlockPy("def __eq__(self, __o: object) -> bool:")
        .WriteLine($"return isinstance(__o, {DtCtorDeclarationName(ctor)}){suffix}");

      wr.NewBlockPy("def __hash__(self) -> int:")
        .WriteLine("return super().__hash__()");
    }

    private string DtCtorDeclarationName(DatatypeCtor ctor, bool full = false) {
      var dt = ctor.EnclosingDatatype;
      return $"{(full ? dt.GetFullCompileName(Options) : IdProtect(dt.GetCompileName(Options)))}_{ctor.GetCompileName(Options)}";
    }

    protected IClassWriter DeclareType(TopLevelDecl d, SubsetTypeDecl.WKind witnessKind, Expression witness, ConcreteSyntaxTree wr) {
      Contract.Requires(d is SubsetTypeDecl or NewtypeDecl);

      var cw = (ClassWriter)CreateClass(IdProtect(d.EnclosingModuleDefinition.GetCompileName(Options)), d, wr);
      var w = cw.MethodWriter;
      var udt = UserDefinedType.FromTopLevelDecl(d.Origin, d);
      w.WriteLine("@staticmethod");
      var block = w.NewBlockPy("def default():");
      var wStmts = block.Fork();
      block.Write("return ");
      if (witnessKind == SubsetTypeDecl.WKind.Compiled) {
        block.Append(Expr(witness, false, wStmts));
      } else {
        block.Write(TypeInitializationValue(udt, wr, d.Origin, false, false));
      }
      block.WriteLine();

      GenerateIsMethod((RedirectingTypeDecl)d, w);

      if (d is NewtypeDecl newtypeDecl && newtypeDecl.Traits.Count != 0) {
        // in constructor:
        //   self._value = value
        cw.ConstructorWriter.WriteLine("self._value = value");
      }

      return cw;
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      return DeclareType(nt, nt.WitnessKind, nt.Witness, wr);
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      DeclareType(sst, sst.WitnessKind, sst.Witness, wr);
    }

    void GenerateIsMethod(RedirectingTypeDecl declWithConstraints, ConcreteSyntaxTree wr) {
      Contract.Requires(declWithConstraints is SubsetTypeDecl or NewtypeDecl);

      if (declWithConstraints.ConstraintIsCompilable) {
        var type = UserDefinedType.FromTopLevelDecl(declWithConstraints.Tok, (TopLevelDecl)declWithConstraints);

        wr.Write($"def {IsMethodName}(");

        var sep = "";
        var count = WriteRuntimeTypeDescriptorsFormals(TypeArgumentInstantiation.ListFromFormals(declWithConstraints.TypeArgs), wr, ref sep,
          FormatDefaultTypeParameterValue);
        wr.Write(sep);

        var sourceFormal = new Formal(declWithConstraints.Tok, "_source", type, true, false, null);
        var wrBody = wr.NewBlockPy($"{IdName(sourceFormal)}):");
        GenerateIsMethodBody(declWithConstraints, sourceFormal, wrBody);
      }
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      literalSuffix = "";
      needsCastAfterArithmetic = false;
      switch (sel) {
        case NativeType.Selection.Byte:
        case NativeType.Selection.SByte:
        case NativeType.Selection.UShort:
        case NativeType.Selection.Short:
        case NativeType.Selection.UInt:
        case NativeType.Selection.Int:
        case NativeType.Selection.Number:
        case NativeType.Selection.ULong:
        case NativeType.Selection.Long:
          name = "int"; break;
        default:
          Contract.Assert(false); // unexpected native type
          throw new cce.UnreachableException(); // to please the compiler
      }
    }

    private class ClassWriter : IClassWriter {
      private readonly PythonCodeGenerator Compiler;
      public readonly ConcreteSyntaxTree ConstructorWriter;
      public readonly ConcreteSyntaxTree MethodWriter;

      public ClassWriter(PythonCodeGenerator compiler, ConcreteSyntaxTree constructorWriter, ConcreteSyntaxTree methodWriter) {
        Contract.Requires(compiler != null);
        Contract.Requires(methodWriter != null);
        Contract.Requires(constructorWriter != null);
        Compiler = compiler;
        ConstructorWriter = constructorWriter;
        MethodWriter = methodWriter;
      }

      public ConcreteSyntaxTree CreateMethod(MethodOrConstructor m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
        bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateMethod(m, typeArgs, createBody, MethodWriter, forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        throw new UnsupportedFeatureException(Token.NoToken, Feature.MethodSynthesis);
      }

      public ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
          List<Formal> formals, Type resultType, IOrigin tok, bool isStatic, bool createBody, MemberDecl member,
          bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member,
          MethodWriter, forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IOrigin tok,
          bool isStatic, bool isConst, bool createBody, MemberDecl member, bool forBodyInheritance) {
        return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, MethodWriter);
      }

      public ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IOrigin tok,
          bool createBody, MemberDecl member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        return Compiler.CreateGetterSetter(name, createBody, out setterWriter, methodWriter: MethodWriter);
      }

      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type,
          IOrigin tok, string rhs, Field field) {
        Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, ConstructorWriter);
      }

      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        throw new cce.UnreachableException();
      }

      public ConcreteSyntaxTree ErrorWriter() => MethodWriter;

      public void Finish() {

      }
    }

    protected override string CompanionMemberIdName(MemberDecl member) {
      if (member.EnclosingClass is NewtypeDecl && member.OverriddenMember != null) {
        return "_Companion_" + IdName(member);
      }
      return base.CompanionMemberIdName(member);
    }

    private void DeclareField(string name, bool isStatic, bool isConst, Type type, IOrigin tok, string rhs,
        ConcreteSyntaxTree fieldWriter) {
      fieldWriter.Write($"self.{name}: {TypeName(type, fieldWriter, tok)}");
      if (rhs != null) {
        fieldWriter.Write($" = {rhs}");
      }
      fieldWriter.WriteLine();
    }

    private ConcreteSyntaxTree CreateGetterSetter(string name, bool createBody, out ConcreteSyntaxTree setterWriter, ConcreteSyntaxTree methodWriter) {
      methodWriter.WriteLine("@property");
      var getterWriter = methodWriter.NewBlockPy(header: $"def {name}(self):");
      methodWriter.WriteLine($"@{name}.setter");
      setterWriter = methodWriter.NewBlockPy(header: $"def {name}(self, value):");
      if (createBody) {
        return getterWriter;
      }
      getterWriter.WriteLine($"return self.{InternalFieldPrefix}{name}");
      setterWriter.WriteLine($"self.{InternalFieldPrefix}{name} = value");
      setterWriter = null;
      return null;
    }

    private ConcreteSyntaxTree CreateGetter(string name, Type resultType, IOrigin tok, bool isStatic, bool createBody, ConcreteSyntaxTree methodWriter) {
      if (!createBody) { return null; }
      methodWriter.WriteLine(isStatic ? $"@{DafnyRuntimeModule}.classproperty" : "@property");
      return methodWriter.NewBlockPy(header: $"def {name}({(isStatic ? "instance" : "self")}):");
    }

    private ConcreteSyntaxTree CreateMethod(MethodOrConstructor m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
        ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      var customReceiver = !forBodyInheritance && NeedsCustomReceiver(m);
      if (m.IsStatic || customReceiver) { wr.WriteLine("@staticmethod"); }
      var protectedName = !forBodyInheritance ? CompanionMemberIdName(m) : IdName(m);
      wr.Write($"def {protectedName}(");
      var sep = "";
      WriteFormals(ForTypeDescriptors(typeArgs, m.EnclosingClass, m, lookasideBody), m.Ins, m.IsStatic, customReceiver, ref sep, wr);
      var body = wr.NewBlockPy("):", close: BlockStyle.Newline);
      if (createBody) {
        if (m.Body.Body.All(s => s.IsGhost)) {
          body.WriteLine("pass");
        }
        return body;
      }
      body.WriteLine("pass");
      return null;
    }

    protected override ConcreteSyntaxTree EmitMethodReturns(MethodOrConstructor m, ConcreteSyntaxTree wr) {
      if (m.Outs.Any(f => !f.IsGhost)) {
        var beforeReturnBlock = wr.Fork();
        EmitReturn(m.Outs, wr);
        return beforeReturnBlock;
      }
      return wr;
    }

    private void WriteFormals(List<TypeArgumentInstantiation> typeParams, List<Formal> formals, bool isStatic,
      bool customReceiver, ref string sep, ConcreteSyntaxTree wr) {
      if (!isStatic && !customReceiver) {
        wr.Write(sep + "self");
        sep = ", ";
      }
      WriteRuntimeTypeDescriptorsFormals(typeParams, wr, ref sep, FormatDefaultTypeParameterValue);
      if (customReceiver) {
        wr.Write(sep + "self");
        sep = ", ";
      }
      WriteFormals(sep, formals, wr);
    }

    private ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
      List<Formal> formals, Type resultType, IOrigin tok, bool isStatic, bool createBody, MemberDecl member,
      ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      if (!createBody) { return null; }
      var customReceiver = !forBodyInheritance && NeedsCustomReceiver(member);
      if (isStatic || customReceiver) { wr.WriteLine("@staticmethod"); }
      var protectedName = !forBodyInheritance ? CompanionMemberIdName(member) : IdName(member);
      wr.Write($"def {protectedName}(");
      var sep = "";
      WriteFormals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, lookasideBody), formals, isStatic, customReceiver, ref sep, wr);
      return wr.NewBlockPy("):", close: BlockStyle.Newline);
    }

    // Unlike the other compilers, we use lambdas to model type descriptors here.
    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IOrigin tok) {
      Contract.Requires(type != null);
      Contract.Requires(tok != null);
      Contract.Requires(wr != null);

      var simplifiedType = DatatypeWrapperEraser.SimplifyTypeAndTrimSubsetTypes(Options, type);
      return simplifiedType switch {
        var x when x.IsBuiltinArrowType => $"{DafnyDefaults}.pointer",
        // unresolved proxy; just treat as bool, since no particular type information is apparently needed for this type
        BoolType or TypeProxy => $"{DafnyDefaults}.bool",
        CharType => UnicodeCharEnabled ? $"{DafnyDefaults}.codepoint" : $"{DafnyDefaults}.char",
        IntType or BitvectorType => $"{DafnyDefaults}.int",
        RealType => $"{DafnyDefaults}.real",
        SeqType or SetType or MultiSetType or MapType => TypeHelperName(simplifiedType.NormalizeExpandKeepConstraints()),
        UserDefinedType udt => udt.ResolvedClass switch {
          TypeParameter tp => TypeParameterDescriptor(tp),
          ClassLikeDecl or NonNullTypeDecl => $"{DafnyDefaults}.pointer",
          DatatypeDecl => DatatypeDescriptor(udt, udt.TypeArgs, udt.Origin),
          NewtypeDecl or SubsetTypeDecl => CustomDescriptor(udt),
          _ => throw new cce.UnreachableException()
        },
        _ => throw new cce.UnreachableException()
      };

      string TypeParameterDescriptor(TypeParameter typeParameter) {
        if ((thisContext != null && typeParameter.Parent is TopLevelDeclWithMembers and not TraitDecl) || typeParameter.Parent is IteratorDecl) {
          return $"self.{typeParameter.GetCompileName(Options)}";
        }
        if (thisContext != null && thisContext.ParentFormalTypeParametersToActuals.TryGetValue(typeParameter, out var instantiatedTypeParameter)) {
          return TypeDescriptor(instantiatedTypeParameter, wr, tok);
        }
        return FormatDefaultTypeParameterValue(type.AsTypeParameter);
      }

      string CustomDescriptor(UserDefinedType userDefinedType) {
        return $"{TypeName_UDT(FullTypeName(userDefinedType), userDefinedType, wr, userDefinedType.Origin)}.default";
      }

      string DatatypeDescriptor(UserDefinedType udt, List<Type> typeArgs, IOrigin tok) {
        var dt = (DatatypeDecl)udt.ResolvedClass;
        var w = new ConcreteSyntaxTree();
        if (dt is TupleTypeDecl) {
          w.Write($"{DafnyDefaults}.tuple(");
        } else {
          w.Write($"{TypeName_UDT(FullTypeName(udt), udt, wr, tok)}.default(");
        }
        EmitTypeDescriptorsActuals(UsedTypeParameters(dt, typeArgs, true), tok, w, true);
        w.Write(")");
        return w.ToString();
      }
    }

    protected override ConcreteSyntaxTree EmitNullTest(bool testIsNull, ConcreteSyntaxTree wr) {
      var wrTarget = wr.ForkInParens();
      wr.Write(testIsNull ? " == None" : " != None");
      return wrTarget;
    }

    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      if (!member.IsStatic) {
        wr.WriteLine("_this = self");
      }
      wr = wr.NewBlockPy($"while True:").NewBlockPy($"with {DafnyRuntimeModule}.label():");
      var body = wr.Fork();
      wr.WriteLine("break");
      return body;
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      wr.WriteLine($"raise {DafnyRuntimeModule}.TailCall()");
    }

    internal override string TypeName(Type type, ConcreteSyntaxTree wr, IOrigin tok, MemberDecl/*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

      var xType = DatatypeWrapperEraser.SimplifyType(Options, type);

      if (xType.IsObjectQ) {
        return "object";
      }

      if (xType.AsNewtype != null && member == null) {
        // when member is given, use UserDefinedType case below
        var newtypeDecl = xType.AsNewtype;
        if (newtypeDecl.NativeType is { } nativeType) {
          return GetNativeTypeName(nativeType);
        }
        return TypeName(newtypeDecl.ConcreteBaseType(xType.TypeArgs), wr, tok);
      }

      switch (xType) {
        case BoolType:
          return "bool";
        case CharType:
          return "str";
        case IntType or BigOrdinalType or BitvectorType:
          return "int";
        case RealType:
          return $"{DafnyRuntimeModule}.BigRational";
        case UserDefinedType udt: {
            var s = FullTypeName(udt, member);
            return TypeName_UDT(s, udt, wr, udt.Origin);
          }
        case CollectionType:
          return TypeHelperName(xType);
      }

      // TODO: I'm not 100% sure this is exhaustive yet
      Contract.Assert(false);
      throw new cce.UnreachableException();
    }

    private string FullName(TopLevelDecl decl) {
      var segments = new List<string> { IdProtect(decl.GetCompileName(Options)) };
      if (decl.EnclosingModuleDefinition != enclosingModule) {
        segments = decl.EnclosingModuleDefinition.GetCompileName(Options).Split('.').Select(PublicModuleIdProtect).Concat(segments).ToList();
      }
      return string.Join('.', segments);
    }

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IOrigin tok,
        bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {

      if (usePlaceboValue) {
        return "None";
      }

      var xType = type.NormalizeExpandKeepConstraints();

      if (xType.IsObjectQ) {
        return "None";
      }

      switch (xType) {
        case BoolType:
          return "False";
        case CharType:
          return UnicodeCharEnabled ? $"{DafnyRuntimeModule}.CodePoint({CharType.DefaultValueAsString})" : CharType.DefaultValueAsString;
        case IntType or BigOrdinalType or BitvectorType:
          return "int(0)";
        case RealType:
          return $"{DafnyRuntimeModule}.BigRational()";
        case CollectionType:
          if (xType is SeqType { Arg: { IsCharType: true } }) {
            var wrString = new ConcreteSyntaxTree();
            StringLiteralWrapper(wrString).Write("\"\"");
            return wrString.ToString();
          } else {
            return $"{TypeHelperName(xType)}({{}})";
          }
        case UserDefinedType udt: {
            var cl = udt.ResolvedClass;
            Contract.Assert(cl != null);
            switch (cl) {
              case SubsetTypeDecl td:
                switch (td.WitnessKind) {
                  case SubsetTypeDecl.WKind.Compiled:
                    return TypeName_UDT(FullName(cl), udt, wr, udt.Origin) + ".default()";
                  case SubsetTypeDecl.WKind.Special:
                    if (ArrowType.IsPartialArrowTypeName(td.Name)) {
                      return "None";
                    }
                    if (td is NonNullTypeDecl decl) {
                      if (decl.Class is ArrayClassDecl arr) {
                        return $"{DafnyArrayClass}(None, {Enumerable.Repeat("0", arr.Dims).Comma()})";
                      }
                      return "None";
                    }
                    Contract.Assert(udt.TypeArgs.Any() && ArrowType.IsTotalArrowTypeName(td.Name));
                    var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, usePlaceboValue,
                      constructTypeParameterDefaultsFromTypeDescriptors);
                    // The final TypeArg contains the result type
                    var arguments = udt.TypeArgs.SkipLast(1).Comma((_, i) => idGenerator.FreshId("x"));
                    return $"(lambda {arguments}: {rangeDefaultValue})";
                  default:
                    return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, usePlaceboValue,
                      constructTypeParameterDefaultsFromTypeDescriptors);
                }

              case NewtypeDecl td:
                if (td.Witness != null) {
                  return TypeName_UDT(FullName(cl), udt, wr, udt.Origin) + ".default()";
                } else {
                  return TypeInitializationValue(td.ConcreteBaseType(udt.TypeArgs), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
                }

              case DatatypeDecl dt:
                var relevantTypeArgs = UsedTypeParameters(dt, udt.TypeArgs, true).ConvertAll(ta => ta.Actual);
                return dt is TupleTypeDecl
                  ? $"({relevantTypeArgs.Comma(arg => DefaultValue(arg, wr, tok, constructTypeParameterDefaultsFromTypeDescriptors))}{(relevantTypeArgs.Count == 1 ? "," : "")})"
                  : $"{FullName(cl)}.default({relevantTypeArgs.Comma(arg => TypeDescriptor(arg, wr, tok))})()";

              case TypeParameter tp:
                return constructTypeParameterDefaultsFromTypeDescriptors
                  ? $"{TypeDescriptor(udt, wr, tok)}()"
                  : $"{FormatDefaultTypeParameterValue(tp)}()";

              case AbstractTypeDecl opaque:
                return FormatDefaultTypeParameterValue(opaque);

              case ClassDecl:
              case TraitDecl:
              case ArrowTypeDecl:
                return "None";
            }
            break;
          }
      }

      Contract.Assert(false);
      throw new cce.UnreachableException();  // unexpected type
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance,
        List<Type> typeArgs, ConcreteSyntaxTree wr, IOrigin tok, bool omitTypeArguments) {
      return fullCompileName;
    }

    internal override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IOrigin tok, MemberDecl member) {
      type = UserDefinedType.UpcastToMemberEnclosingType(type, member);

      if (type.NormalizeExpandKeepConstraints() is UserDefinedType udt) {
        if ((udt.ResolvedClass is DatatypeDecl dt && DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, dt, out _)) ||
            udt.ResolvedClass is SubsetTypeDecl or NewtypeDecl) {
          var s = FullTypeName(udt, member);
          return TypeName_UDT(s, udt, wr, udt.Origin);
        }
      }
      return TypeName(type, wr, tok, member);
    }

    protected override void TypeArgDescriptorUse(bool isStatic, bool lookasideBody, TopLevelDeclWithMembers cl, out bool needsTypeParameter, out bool needsTypeDescriptor) {
      needsTypeDescriptor = false;
      needsTypeParameter = false;
      switch (cl) {
        case DatatypeDecl:
          needsTypeDescriptor = true;
          break;
        case TraitDecl:
          needsTypeDescriptor = isStatic || lookasideBody;
          break;
        case ClassDecl:
          needsTypeDescriptor = isStatic;
          break;
      }
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IOrigin tok, bool isInParam, ConcreteSyntaxTree wr) {
      if (isInParam) {
        wr.Write($"{prefix}{name}");
        return true;
      } else {
        return false;
      }
    }

    protected override void DeclareLocalVar(string name, Type type, IOrigin tok, bool leaveRoomForRhs, string rhs,
        ConcreteSyntaxTree wr) {
      wr.Write(name);
      if (type != null) { wr.Write($": {TypeName(type, wr, tok)}"); }
      if (rhs != null) { wr.Write($" = {rhs}"); }
      if (!leaveRoomForRhs) {
        wr.WriteLine();
      }
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IOrigin tok, ConcreteSyntaxTree wr) {
      var w = new ConcreteSyntaxTree();
      wr.FormatLine($"{name} = {w}");
      return w;
    }

    protected override bool UseReturnStyleOuts(MethodOrConstructor m, int nonGhostOutCount) => true;
    protected override bool SupportsMultipleReturns => true;

    protected override void DeclareLocalOutVar(string name, Type type, IOrigin tok, string rhs, bool useReturnStyleOuts,
        ConcreteSyntaxTree wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IOrigin tok, ConcreteSyntaxTree wr) {
      // emit nothing
    }

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      var wStmts = wr.Fork();
      wr.Write($"{DafnyRuntimeModule}.print(");
      EmitToString(wr, arg, wStmts);
      wr.WriteLine(")");
    }

    private void EmitToString(ConcreteSyntaxTree wr, Expression arg, ConcreteSyntaxTree wStmts) {
      if (UnicodeCharEnabled && DatatypeWrapperEraser.SimplifyTypeAndTrimNewtypes(Options, arg.Type).IsStringType) {
        TrParenExpr(arg, wr, false, wStmts);
        wr.Write(".VerbatimString(False)");
      } else {
        wr.Write($"{DafnyRuntimeModule}.string_of(");
        wr.Append(Expr(arg, false, wStmts));
        wr.Write(")");
      }
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
      var manager = createContinueLabel ? "c_label" : "label";
      var block = wr.NewBlockPy($"with {DafnyRuntimeModule}.{manager}(\"{label}\"):");
      var core = block.Fork();
      block.WriteLine("pass");
      return core;
    }

    protected override void EmitBreak(string label, ConcreteSyntaxTree wr) {
      wr.WriteLine(label != null ? $"raise {DafnyRuntimeModule}.Break(\"{label}\")" : "break");
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
      wr.WriteLine($"raise {DafnyRuntimeModule}.Continue(\"{label}\")");
    }

    protected override void EmitYield(ConcreteSyntaxTree wr) {
      wr.WriteLine("yield");
    }

    protected override void EmitAbsurd(string message, ConcreteSyntaxTree wr) {
      if (message == null) {
        message = "unexpected control point";
      }
      wr.WriteLine($"raise Exception(\"{message}\")");
    }

    protected override void EmitHalt(IOrigin tok, Expression messageExpr, ConcreteSyntaxTree wr) {
      Contract.Requires(tok != null);
      var wStmts = wr.Fork();
      wr.Write($"raise {DafnyRuntimeModule}.HaltException(");
      wr.Write($"\"{tok.OriginToString(Options)}: \" + ");
      EmitToString(wr, messageExpr, wStmts);
      wr.WriteLine(")");
    }

    protected override ConcreteSyntaxTree EmitIf(out ConcreteSyntaxTree guardWriter, bool hasElse, ConcreteSyntaxTree wr) {
      wr.Write("if ");
      guardWriter = wr.Fork();
      return wr.NewBlockPy(":", hasElse ? "el" : "");
    }

    protected override ConcreteSyntaxTree EmitBlock(ConcreteSyntaxTree wr) {
      //This encoding does not provide a new scope
      return wr.NewBlockPy("if True:");
    }

    protected override ConcreteSyntaxTree EmitForStmt(IOrigin tok, IVariable loopIndex, bool goingUp, string endVarName,
      List<Statement> body, List<Label> labels, ConcreteSyntaxTree wr) {
      string iterator;
      var lowWr = new ConcreteSyntaxTree();
      string argumentRemainder;
      if (endVarName == null) {
        iterator = "count";
        argumentRemainder = goingUp ? "" : "-1, -1";
      } else {
        iterator = "range";
        argumentRemainder = goingUp ? $", {endVarName}" : $"-1, {endVarName}-1, -1";
      }
      wr.Format($"for {IdName(loopIndex)} in {iterator}({lowWr}{argumentRemainder})");
      var bodyWr = wr.NewBlockPy($":");
      bodyWr = EmitContinueLabel(labels, bodyWr);
      TrStmtList(body, bodyWr);

      return lowWr;
    }

    protected override ConcreteSyntaxTree CreateWhileLoop(out ConcreteSyntaxTree guardWriter, ConcreteSyntaxTree wr) {
      wr.Write("while ");
      guardWriter = wr.Fork();
      var wBody = wr.NewBlockPy(":");
      return wBody;
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, Action<ConcreteSyntaxTree> boundAction, ConcreteSyntaxTree wr, string start = null) {
      var lowerBound = start == null ? "" : start + ", ";
      var boundWriter = new ConcreteSyntaxTree();
      boundAction(boundWriter);
      var bound = boundWriter.ToString();
      return wr.NewBlockPy($"for {indexVar} in range({lowerBound}{bound}):");
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      return wr.NewBlockPy($"for {indexVar} in {DafnyRuntimeModule}.Doubler({start}):");
    }

    protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine($"{varName} += 1");
    }

    protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine($"{varName} -= 1");
    }

    protected override string GetQuantifierName(string bvType) {
      return $"{DafnyRuntimeModule}.quantifier";
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IOrigin tok,
      out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      collectionWriter = new ConcreteSyntaxTree();
      wr.WriteLine($"{tmpVarName}: {TypeName(collectionElementType, wr, tok)}")
        .Format($"for {tmpVarName} in {collectionWriter}:");
      return wr.NewBlockPy();
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type sourceType, bool introduceBoundVar, IOrigin tok, ConcreteSyntaxTree wr) {
      wr.WriteLine($"{boundVarName}{(introduceBoundVar ? $": {TypeName(boundVarType, wr, tok)}" : "")} = {tmpVarName}");
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs,
        out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      collectionWriter = new ConcreteSyntaxTree();
      return wr.Format($"for {boundVarName} in {collectionWriter}:").NewBlockPy();
    }

    protected override void EmitNew(Type type, IOrigin tok, CallStmt initCall, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var cl = ((UserDefinedType)type.NormalizeExpand()).ResolvedClass;
      var ctor = (Constructor)initCall?.Method;  // correctness of cast follows from precondition of "EmitNew"
      var sep = "";
      wr.Write($"{TypeName(type, wr, tok)}(");
      EmitTypeDescriptorsActuals(TypeArgumentInstantiation.ListFromClass(cl, type.TypeArgs), tok, wr, ref sep);
      wr.Write(ConstructorArguments(initCall, wStmts, ctor, sep));
      wr.Write(")");
    }

    protected override void EmitNewArray(Type elementType, IOrigin tok, List<string> dimensions,
      bool mustInitialize, [CanBeNull] string exampleElement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var initValue = mustInitialize ? DefaultValue(elementType, wr, tok, true) : "None";
      wr.Write($"{DafnyArrayClass}({initValue}, {dimensions.Comma(s => s)})");
    }

    protected static string TranslateEscapes(string s) {
      s = Util.ReplaceNullEscapesWithCharacterEscapes(s);

      s = Util.ExpandUnicodeEscapes(s, false);

      return s;
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      switch (e) {
        case CharLiteralExpr:
          var escaped = TranslateEscapes((string)e.Value);
          if (UnicodeCharEnabled) {
            wr.Write($"{DafnyRuntimeModule}.CodePoint('{escaped}')");
          } else {
            wr.Write($"'{escaped}'");
          }
          break;
        case StringLiteralExpr str:
          TrStringLiteral(str, StringLiteralWrapper(wr));
          break;
        case StaticReceiverExpr:
          wr.Write(TypeName(e.Type, wr, e.Origin));
          break;
        default:
          switch (e.Value) {
            case null:
              wr.Write("None");
              break;
            case bool value:
              wr.Write($"{value}");
              break;
            case BigInteger integer:
              wr.Write($"{integer}");
              break;
            case BigDec n:
              wr.Write($"{DafnyRuntimeModule}.BigRational('{n.Mantissa}e{n.Exponent}')");
              break;
            default:
              // TODO: This may not be exhaustive
              throw new cce.UnreachableException();
          }
          break;
      }
    }

    private ConcreteSyntaxTree StringLiteralWrapper(ConcreteSyntaxTree wr) {
      ConcreteSyntaxTree wrStringGoesHere;
      if (UnicodeCharEnabled) {
        wr.Write($"{DafnySeqMakerFunction}(map({DafnyRuntimeModule}.CodePoint, ");
        wrStringGoesHere = wr.Fork();
        wr.Write("))");
      } else {
        wr.Write($"{DafnySeqMakerFunction}(");
        wrStringGoesHere = wr.Fork();
        wr.Write(")");
      }
      return wrStringGoesHere;
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
      if (!isVerbatim) {
        wr.Write($"\"{TranslateEscapes(str)}\"");
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

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, [CanBeNull] NativeType nativeType,
      bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      var vec = wr.ForkInParens();
      wr.Write($" & ((1 << {bvType.Width}) - 1)");
      return vec;
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
        bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      // (( e0 op1 e1) | (e0 op2 (width - e1)))
      wr = wr.ForkInParens();
      EmitShift(e0, e1, isRotateLeft ? "<<" : ">>", isRotateLeft, true, wr.ForkInParens(), inLetExprBody, wStmts, tr);
      wr.Write(" | ");
      EmitShift(e0, e1, isRotateLeft ? ">>" : "<<", !isRotateLeft, false, wr.ForkInParens(), inLetExprBody, wStmts, tr);
    }

    void EmitShift(Expression e0, Expression e1, string op, bool truncate, bool firstOp, ConcreteSyntaxTree wr,
        bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      var bv = e0.Type.NormalizeToAncestorType().AsBitVectorType;
      if (truncate) {
        wr = EmitBitvectorTruncation(bv, null, true, wr);
      }
      tr(e0, wr, inLetExprBody, wStmts);
      wr.Write($" {op} ");
      if (!firstOp) {
        wr = wr.ForkInParens().Write($"{bv.Width} - ");
      }

      tr(e1, wr.ForkInParens(), inLetExprBody, wStmts);
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
      wr.Write("[]");
    }

    protected override ConcreteSyntaxTree EmitAddTupleToList(string ingredients, string tupleTypeArgs, ConcreteSyntaxTree wr) {
      var wrTuple = new ConcreteSyntaxTree();
      wr.FormatLine($"{ingredients}.append(({wrTuple}))");
      return wrTuple;
    }

    protected override void EmitTupleSelect(string prefix, int i, ConcreteSyntaxTree wr) {
      wr.Write("{0}[{1}]", prefix, i);
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }

    public override string PublicIdProtect(string name) {
      Contract.Requires(name != null);
      return name switch {
        _ => MangleName(name)
      };
    }


    private readonly HashSet<string> ReservedModuleNames = [
      "itertools",
      "math",
      "typing",
      "sys"
    ];

    private string PublicModuleIdProtect(string name) {
      if (ReservedModuleNames.Contains(name)) {
        return "_" + name;
      }
      return IdProtect(name);
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl member = null) {
      if (udt is ArrowType) {
        //TODO: Add deeper types
        return "Callable";
      }

      var cl = udt.ResolvedClass;
      return cl switch {
        TypeParameter => $"TypeVar(\'{IdProtect(cl.GetCompileName(Options))}\')",
        ArrayClassDecl => DafnyArrayClass,
        TupleTypeDecl => "tuple",
        _ => FullName(cl)
      };
    }

    protected override void EmitThis(ConcreteSyntaxTree wr, bool _ = false) {
      var isTailRecursive = enclosingMethod is { IsTailRecursive: true } || enclosingFunction is { IsTailRecursive: true };
      wr.Write(isTailRecursive ? "_this" : "self");
    }

    protected override void EmitNull(Type _, ConcreteSyntaxTree wr) {
      wr.Write("None");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string typeDescriptorArguments, string arguments, ConcreteSyntaxTree wr) {
      EmitDatatypeValue(dtv.Ctor.EnclosingDatatype, dtv.Ctor, dtv.IsCoCall, typeDescriptorArguments, arguments, wr);
    }

    void EmitDatatypeValue(DatatypeDecl dt, DatatypeCtor ctor, bool isCoCall, string typeDescriptorArguments, string arguments,
      ConcreteSyntaxTree wr, bool qualifiedName = true) {
      if (isCoCall) {
        wr.Write($"{FullName(dt)}__Lazy(lambda: ");
        var end = wr.Fork();
        wr.Write(")");
        wr = end;
      }
      if (dt is not TupleTypeDecl) {
        wr.Write($"{DtCtorDeclarationName(ctor, dt.EnclosingModuleDefinition != enclosingModule)}");
      } else if (ctor.Destructors.Count(d => !d.IsGhost) == 1) {
        // 1-tuples need this this for disambiguation
        arguments += ",";
      }
      var sep = typeDescriptorArguments.Length != 0 && arguments.Length != 0 ? ", " : "";
      wr.Write($"({typeDescriptorArguments}{sep}{arguments})");
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
        case SpecialField.ID.Keys:
          compiledName = "keys";
          break;
        case SpecialField.ID.Values:
          compiledName = "values";
          break;
        case SpecialField.ID.Items:
          compiledName = "items";
          break;
        case SpecialField.ID.Floor:
          preString = "floor(";
          postString = ")";
          break;
        case SpecialField.ID.IsLimit:
          preString = $"{DafnyRuntimeModule}.BigOrdinal.is_limit(";
          postString = ")";
          break;
        case SpecialField.ID.IsSucc:
          preString = $"{DafnyRuntimeModule}.BigOrdinal.is_succ(";
          postString = ")";
          break;
        case SpecialField.ID.Offset:
          preString = $"{DafnyRuntimeModule}.BigOrdinal.offset(";
          postString = ")";
          break;
        case SpecialField.ID.IsNat:
          preString = $"{DafnyRuntimeModule}.BigOrdinal.is_nat(";
          postString = ")";
          break;
        case SpecialField.ID.ArrayLength:
        case SpecialField.ID.ArrayLengthInt:
          var dim = idParam is int d and > 0 ? d : 0;
          compiledName = $"length({dim})";
          break;
        default:
          Contract.Assert(false); // unexpected ID
          break;
      }
    }

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member,
      List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap, Type expectedType,
      string additionalCustomParameter = null, bool internalAccess = false) {
      switch (DatatypeWrapperEraser.GetMemberStatus(Options, member)) {
        case DatatypeWrapperEraser.MemberCompileStatus.Identity:
          return SimpleLvalue(obj);
        case DatatypeWrapperEraser.MemberCompileStatus.AlwaysTrue:
          return StringLvalue(True);
        default:
          break;
      }
      switch (member) {
        case DatatypeDestructor dd: {
            var dest = dd.EnclosingClass switch {
              TupleTypeDecl => $"[{dd.CorrespondingFormals[0].NameForCompilation}]",
              _ => $".{IdProtect(dd.GetCompileName(Options))}"
            };
            return SuffixLvalue(obj, dest);
          }
        case ConstantField cf:
          var protectedName = IdProtect(NonglobalVariable.SanitizeName(cf.Name));
          var compiledNameConstantField = (protectedName.Length > 0 && internalAccess ? InternalFieldPrefix : "") + protectedName;
          return SpecialOrConstantField(obj, objType, member, typeArgs, cf, compiledNameConstantField);
        case SpecialField sf: {
            GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, objType, out var compiledName, out _, out _);
            return SpecialOrConstantField(obj, objType, member, typeArgs, sf, compiledName);
          }
        case Field: {
            return SimpleLvalue(w => {
              if (member.IsStatic) { w.Write(TypeName_Companion(objType, w, member.Origin, member)); } else { obj(w); }
              w.Write($".{IdName(member)}");
            });
          }
        case Function fn: {
            if (additionalCustomParameter == null && typeArgs.Count == 0) {
              return SuffixLvalue(obj, $".{IdName(fn)}");
            }
            return SimpleLvalue(w => {
              var args = fn.Ins
                .Where(f => !f.IsGhost)
                .Select(_ => ProtectedFreshId("_eta"))
                .Comma();
              w.Write($"lambda {args}: ");
              obj(w);
              w.Write($".{IdName(fn)}(");
              var sep = "";
              EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), fn.Origin, w, ref sep);
              if (additionalCustomParameter != null) {
                w.Write(sep + additionalCustomParameter);
                sep = ", ";
              }
              if (args.Length > 0) {
                w.Write(sep);
              }
              w.Write(args + ")");
            });
          }
        default:
          return SimpleLvalue(w => {
            w.Write($"{TypeName_Companion(objType, w, member.Origin, member)}.{IdName(member)}({additionalCustomParameter ?? ""})");
          });
      }
    }

    private ILvalue SpecialOrConstantField(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member,
      List<TypeArgumentInstantiation> typeArgs,
      Field field, string compiledName) {
      return SimpleLvalue(w => {
        var customReceiver = NeedsCustomReceiverNotTrait(field);
        if (field.IsStatic || customReceiver) {
          w.Write(TypeName_Companion(objType, w, member.Origin, member));
        } else {
          obj(w);
        }
        if (compiledName.Length > 0) {
          w.Write($".{compiledName}");
        }
        var sep = "(";
        EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), member.Origin, w, ref sep);
        if (customReceiver) {
          w.Write(sep);
          obj(w);
          sep = ", ";
        }
        if (sep != "(") {
          w.Write(")");
        }
      });
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Action<ConcreteSyntaxTree>> indices, Type elmtType, ConcreteSyntaxTree wr) {
      Contract.Assert(indices is { Count: >= 1 });
      var w = wr.Fork();
      wr.Write("[");
      for (var i = 0; i < indices.Count; i++) {
        if (i > 0) {
          wr.Write(", ");
        }
        indices[i](wr);
      }
      wr.Write("]");
      return w;
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      Contract.Assert(indices != null);  // follows from precondition
      var strings = indices.Select<Expression, Action<ConcreteSyntaxTree>>(index => wr => EmitExpr(index, inLetExprBody, wr, wStmts));
      return EmitArraySelect(strings.ToList(), elmtType, wr);
    }

    protected override void EmitExprAsNativeInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      // This is also used for bit shift operators, or more generally any binary operation where CompileBinOp()
      // sets the convertE1_to_int out parameter to true. This compiler always sets that to false, however,
      // so this method is only called for non-sequentializable forall statements.
      TrParenExpr("int", expr, wr, inLetExprBody, wStmts);
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(source, wr, inLetExprBody, wStmts);
      wr.Write("[");
      wr.Append(Expr(index, inLetExprBody, wStmts));
      wr.Write("]");
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
      CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(source, wr, inLetExprBody, wStmts);
      wr.Write(".set(");
      wr.Append(Expr(index, inLetExprBody, wStmts));
      wr.Write(", ");
      wr.Append(CoercedExpr(value, resultCollectionType.ValueArg, inLetExprBody, wStmts));
      wr.Write(")");
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write($"{DafnySeqMakerFunction}(");
      TrParenExpr(source, wr, inLetExprBody, wStmts);
      wr.Write("[");
      if (lo != null) { wr.Append(Expr(lo, inLetExprBody, wStmts)); }
      wr.Write(":");
      if (hi != null) { wr.Append(Expr(hi, inLetExprBody, wStmts)); }

      wr.Write(":])");
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      ConcreteSyntaxTree valueExpression;
      var range = $"range({Expr(expr.N, inLetExprBody, wStmts)})";
      wr.Write(DafnySeqMakerFunction);
      if (expr.Initializer is LambdaExpr lam) {
        valueExpression = Expr(lam.Body, inLetExprBody, wStmts);
        var binder = IdProtect(lam.BoundVars[0].GetOrCreateCompileName(currentIdGenerator));
        wr.Write($"([{valueExpression} for {binder} in {range}])");
      } else {
        valueExpression = Expr(expr.Initializer, inLetExprBody, wStmts);
        wr.Write($"(tuple(map({valueExpression}, {range})))");
      }
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      TrParenExpr(DafnyMultiSetClass, expr.E, wr, inLetExprBody, wStmts);
    }

    protected override void EmitApplyExpr(Type functionType, IOrigin tok, Expression function,
        List<Expression> arguments, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Append(Expr(function, inLetExprBody, wStmts));
      TrExprList(arguments, wr, inLetExprBody, wStmts);
    }

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
      List<Type> boundTypes, Type resultType, IOrigin resultTok, bool inLetExprBody, ConcreteSyntaxTree wr,
      ref ConcreteSyntaxTree wStmts) {
      var functionName = ProtectedFreshId("_lambda");
      wr.Write($"{functionName}");
      TrExprList(arguments, wr, inLetExprBody, wStmts);
      var wrBody = wStmts.NewBlockPy($"def {functionName}({boundVars.Comma()}):", close: BlockStyle.Newline);
      wStmts = wrBody.Fork();
      return EmitReturnExpr(wrBody);
    }

    protected override void EmitDestructor(Action<ConcreteSyntaxTree> source, Formal dtor, int formalNonGhostIndex,
      DatatypeCtor ctor,
      Func<List<Type>> getTypeArgs, Type bvType, ConcreteSyntaxTree wr) {
      source(wr);
      if (DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, ctor.EnclosingDatatype, out var coreDtor)) {
        Contract.Assert(coreDtor.CorrespondingFormals.Count == 1);
        Contract.Assert(dtor == coreDtor.CorrespondingFormals[0]); // any other destructor is a ghost
      } else {
        wr.Write(ctor.EnclosingDatatype is TupleTypeDecl ? $"[{dtor.NameForCompilation}]" : $".{IdProtect(dtor.GetOrCreateCompileName(currentIdGenerator))}");
      }
    }

    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IOrigin tok, List<string> inNames,
        Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
      var functionName = ProtectedFreshId("_lambda");
      wr.Write(functionName);
      return wStmts.NewBlockPy($"def {functionName}({inNames.Comma()}):", close: BlockStyle.Newline);
    }

    protected override void CreateIIFE(string bvName, Type bvType, IOrigin bvTok, Type bodyType, IOrigin bodyTok,
      ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      wrRhs = new ConcreteSyntaxTree();
      var functionName = ProtectedFreshId("_iife");
      wr.Format($"{functionName}({wrRhs})");
      wrBody = wStmts.NewBlockPy($"def {functionName}({bvName}):");
      wStmts = wrBody.Fork();
      wrBody = EmitReturnExpr(wrBody);
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IOrigin resultTok, ConcreteSyntaxTree wr,
        ConcreteSyntaxTree wStmts) {
      var functionName = ProtectedFreshId("_iife");
      wr.WriteLine($"{functionName}()");
      return wStmts.NewBlockPy($"def {functionName}():");
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IOrigin resultTok, string bvName,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var functionName = ProtectedFreshId("_iife");
      wr.WriteLine($"{functionName}({source})");
      return wStmts.NewBlockPy($"def {functionName}({bvName}):");
    }

    protected override ConcreteSyntaxTree FromFatPointer(Type type, ConcreteSyntaxTree wr) {
      if (type.HasFatPointer) {
        var w = wr.ForkInParens();
        wr.Write("._value");
        return w;
      } else {
        return wr;
      }
    }

    protected override ConcreteSyntaxTree ToFatPointer(Type type, ConcreteSyntaxTree wr) {
      if (type.HasFatPointer) {
        wr.Write(FullName(type.AsNewtype));
        return wr.ForkInParens();
      } else {
        return wr;
      }
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      switch (op) {
        case ResolvedUnaryOp.Cardinality:
          var multiset = expr.Type.NormalizeToAncestorType().AsMultiSetType != null;
          if (!multiset) { wr.Write("len"); }
          TrParenExpr(expr, wr, inLetExprBody, wStmts);
          if (multiset) { wr.Write(".cardinality"); }
          break;
        case ResolvedUnaryOp.BitwiseNot:
          TrParenExpr("~", expr, wr, inLetExprBody, wStmts);
          break;
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("not", expr, wr, inLetExprBody, wStmts);
          break;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
      }
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op,
      Type e0Type, Type e1Type, IOrigin tok, Type resultType,
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
        case BinaryExpr.ResolvedOpcode.And:
          opString = "and";
          break;

        case BinaryExpr.ResolvedOpcode.Or:
          opString = "or";
          break;

        case BinaryExpr.ResolvedOpcode.Imp:
          preOpString = "not ";
          opString = "or";
          break;

        case BinaryExpr.ResolvedOpcode.LeftShift:
          opString = "<<";
          truncateResult = true;
          break;

        case BinaryExpr.ResolvedOpcode.RightShift:
          opString = ">>";
          break;

        case BinaryExpr.ResolvedOpcode.Concat:
          opString = "+";
          break;

        case BinaryExpr.ResolvedOpcode.Add:
          if (resultType.IsCharType && !UnicodeCharEnabled) {
            staticCallString = $"{DafnyRuntimeModule}.plus_char";
          } else {
            opString = "+";
            truncateResult = true;
          }
          break;

        case BinaryExpr.ResolvedOpcode.Sub:
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
        case BinaryExpr.ResolvedOpcode.MapSubtraction:
          if (resultType.IsCharType && !UnicodeCharEnabled) {
            staticCallString = $"{DafnyRuntimeModule}.minus_char";
          } else {
            opString = "-";
            truncateResult = true;
          }
          break;

        case BinaryExpr.ResolvedOpcode.Mul:
          opString = "*";
          truncateResult = true;
          break;

        case BinaryExpr.ResolvedOpcode.Div:
          if (resultType.IsNumericBased(Type.NumericPersuasion.Int) || resultType.NormalizeToAncestorType().IsBitVectorType) {
            staticCallString = $"{DafnyRuntimeModule}.euclidian_division";
          } else {
            opString = "/";
          }
          break;

        case BinaryExpr.ResolvedOpcode.Mod:
          staticCallString = $"{DafnyRuntimeModule}.euclidian_modulus"; break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          opString = "<"; break;

        case BinaryExpr.ResolvedOpcode.Prefix:
          opString = "<="; break;

        case BinaryExpr.ResolvedOpcode.SeqEq:
        case BinaryExpr.ResolvedOpcode.SetEq:
        case BinaryExpr.ResolvedOpcode.MapEq:
        case BinaryExpr.ResolvedOpcode.EqCommon:
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
          opString = "=="; break;

        case BinaryExpr.ResolvedOpcode.NeqCommon:
        case BinaryExpr.ResolvedOpcode.SeqNeq:
        case BinaryExpr.ResolvedOpcode.SetNeq:
        case BinaryExpr.ResolvedOpcode.MapNeq:
        case BinaryExpr.ResolvedOpcode.MultiSetNeq:
          opString = "!="; break;

        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
        case BinaryExpr.ResolvedOpcode.MapMerge:
          opString = "|"; break;

        case BinaryExpr.ResolvedOpcode.InSet:
        case BinaryExpr.ResolvedOpcode.InMultiSet:
        case BinaryExpr.ResolvedOpcode.InSeq:
        case BinaryExpr.ResolvedOpcode.InMap:
          opString = "in"; break;

        case BinaryExpr.ResolvedOpcode.NotInSet:
        case BinaryExpr.ResolvedOpcode.NotInMultiSet:
        case BinaryExpr.ResolvedOpcode.NotInSeq:
        case BinaryExpr.ResolvedOpcode.NotInMap:
          opString = "not in"; break;

        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          callString = "intersection"; break;

        case BinaryExpr.ResolvedOpcode.Disjoint:
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
          callString = "isdisjoint"; break;

        case BinaryExpr.ResolvedOpcode.Subset:
        case BinaryExpr.ResolvedOpcode.MultiSubset:
          callString = "issubset"; break;

        case BinaryExpr.ResolvedOpcode.ProperSubset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
          callString = "ispropersubset"; break;


        default:
          base.CompileBinOp(op, e0Type, e1Type, tok, resultType,
            out opString, out preOpString, out postOpString, out callString, out staticCallString, out reverseArguments,
            out truncateResult, out convertE1_to_int, out coerceE1,
            errorWr);
          break;
      }
    }

    protected override void TrStmtList(IReadOnlyList<Statement> stmts, ConcreteSyntaxTree writer) {
      Contract.Requires(cce.NonNullElements(stmts));
      Contract.Requires(writer != null);
      var listWriter = new ConcreteSyntaxTree();
      base.TrStmtList(stmts, listWriter);
      if (listWriter.Descendants.OfType<LineSegment>().Any()) {
        writer.Append(listWriter);
      } else {
        writer.WriteLine("pass");
      }
    }

    protected override void EmitITE(Expression guard, Expression thn, Expression els, Type resultType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      Contract.Requires(guard != null);
      Contract.Requires(thn != null);
      Contract.Requires(els != null);
      Contract.Requires(wr != null);

      ConcreteSyntaxTree Tree(Expression e) => Expr(e, inLetExprBody, wStmts);

      wr.Format($"({Tree(thn)} if {Tree(guard)} else {Tree(els)})");
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      wr.Write($"{varName} == 0");
    }

    protected override void EmitConversionExpr(Expression fromExpr, Type fromType, Type toType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var (pre, post) = ("", "");
      if (fromType.IsNumericBased(Type.NumericPersuasion.Int) || fromType.NormalizeToAncestorType().IsBitVectorType || fromType.IsBigOrdinalType) {
        if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
          (pre, post) = ($"{DafnyRuntimeModule}.BigRational(", ", 1)");
        } else if (toType.IsCharType) {
          if (UnicodeCharEnabled) {
            (pre, post) = ($"{DafnyRuntimeModule}.CodePoint(chr(", "))");
          } else {
            (pre, post) = ("chr(", ")");
          }
        }
      } else if (fromType.IsCharType) {
        if (toType.IsCharType) {
          // nothing to do
        } else if (toType.IsNumericBased(Type.NumericPersuasion.Int) || toType.NormalizeToAncestorType().IsBitVectorType || toType.IsBigOrdinalType) {
          (pre, post) = ("ord(", ")");
        } else if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
          (pre, post) = ($"{DafnyRuntimeModule}.BigRational(ord(", "), 1)");
        }
      } else if (fromType.IsNumericBased(Type.NumericPersuasion.Real)) {
        if (toType.IsNumericBased(Type.NumericPersuasion.Int) || toType.NormalizeToAncestorType().IsBitVectorType || toType.IsBigOrdinalType) {
          (pre, post) = ("int(", ")");
        } else if (toType.IsCharType) {
          if (UnicodeCharEnabled) {
            (pre, post) = ($"{DafnyRuntimeModule}.CodePoint(chr(floor(", ")))");
          } else {
            (pre, post) = ("chr(floor(", "))");
          }
        }
      }
      wr.Write(pre);
      wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
      wr.Write(post);
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IOrigin tok, ConcreteSyntaxTree wr) {
      if (fromType.IsRefType && !fromType.IsNonNullRefType) {
        Contract.Assert(toType.IsRefType);
        wr = wr.Write($"{localName} is {(toType.IsNonNullRefType ? "not None and" : "None or")} ").ForkInParens();
      }

      if (fromType.IsTraitType && toType.AsNewtype != null) {
        wr.Write($"isinstance({localName}, {FullName(toType.AsNewtype)})");
      } else {
        wr.Write($"isinstance({localName}, {TypeName(toType, wr, tok)})");
      }
    }

    protected override void EmitIsIntegerTest(Expression source, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      EmitExpr(source, false, wr.ForkInParens(), wStmts);
      wr.Write(".is_integer() and ");
    }

    protected override void EmitIsUnicodeScalarValueTest(Expression source, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("_dafny.CodePoint.is_code_point");
      EmitExpr(source, false, wr.ForkInParens(), wStmts);
      wr.Write(" and ");
    }

    protected override void EmitIsInIntegerRange(Expression source, BigInteger lo, BigInteger hi, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      EmitLiteralExpr(wr, new LiteralExpr(source.Origin, lo) { Type = Type.Int });
      wr.Write(" <= ");
      EmitExpr(source, false, wr.ForkInParens(), wStmts);
      wr.Write(" and ");

      EmitExpr(source, false, wr.ForkInParens(), wStmts);
      wr.Write(" < ");
      EmitLiteralExpr(wr, new LiteralExpr(source.Origin, hi) { Type = Type.Int });
      wr.Write(" and ");
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IOrigin tok, List<Expression> elements,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var (open, close) = ct switch {
        SeqType or MultiSetType => ("[", "]"),
        _ => ("{", "}")
      };
      wr.Write(ct is SeqType ? DafnySeqMakerFunction : TypeHelperName(ct));
      wr.Write("(");
      wr.Write(open);
      TrExprList(elements, wr, inLetExprBody, wStmts, typeAt: _ => ct.Arg, parens: false);
      wr.Write(close);
      wr.Write(")");
    }

    private static string TypeHelperName(Type ct) {
      return ct switch {
        SetType => DafnySetClass,
        SeqType => DafnySeqClass,
        MapType => DafnyMapClass,
        MultiSetType => DafnyMultiSetClass,
        _ => throw new NotImplementedException()
      };
    }

    protected override void EmitMapDisplay(MapType mt, IOrigin tok, List<MapDisplayEntry> elements, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write($"{DafnyMapClass}({{");
      var sep = "";
      foreach (var p in elements) {
        wr.Write(sep);
        wr.Append(Expr(p.A, inLetExprBody, wStmts));
        wr.Write(": ");
        wr.Append(Expr(p.B, inLetExprBody, wStmts));
        sep = ", ";
      }
      wr.Write("})");
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
      wr.WriteLine($"{collectionName} = {DafnySetClass}()");
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      wr.WriteLine($"{collectionName} = {DafnyMapClass}()");
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody,
        ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.WriteLine($"{collName} = {collName}.union({DafnySetClass}([{Expr(elmt, inLetExprBody, wStmts)}]))");
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IOrigin tok, string collName, Expression term,
        bool inLetExprBody, ConcreteSyntaxTree wr) {
      var termLeftWriter = new ConcreteSyntaxTree();
      var wStmts = wr.Fork();
      wr.FormatLine($"{collName}[{termLeftWriter}] = {Expr(term, inLetExprBody, wStmts)}");
      return termLeftWriter;
    }

    [CanBeNull]
    protected override Action<ConcreteSyntaxTree> GetSubtypeCondition(string tmpVarName, Type boundVarType, IOrigin tok, ConcreteSyntaxTree wPreconditions) {
      if (!boundVarType.IsRefType) {
        return null;
      }

      var typeTest = boundVarType.IsObject || boundVarType.IsObjectQ
        ? True
        : $"isinstance({tmpVarName}, {TypeName(boundVarType, wPreconditions, tok)})";
      return wr => wr.Write(boundVarType.IsNonNullRefType
        ? $"{tmpVarName} is not None and {typeTest}"
        : $"{tmpVarName} is None or {typeTest}");
    }

    protected override void GetCollectionBuilder_Build(CollectionType ct, IOrigin tok, string collName,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmt) {
      wr.Write(TypeHelperName(ct) + $"({collName})");
    }

    protected override (Type, Action<ConcreteSyntaxTree>) EmitIntegerRange(Type type, Action<ConcreteSyntaxTree> wLo, Action<ConcreteSyntaxTree> wHi) {
      return (new IntType(), (wr) => {
        wr.Write($"{DafnyRuntimeModule}.IntegerRange(");
        wLo(wr);
        wr.Write(", ");
        wHi(wr);
        wr.Write(')');
      }
      );
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("[");
      wr.Append(Expr(e, inLetExprBody, wStmts));
      wr.Write("]");
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      var tryBlock = wr.NewBlockPy("try:");
      TrStmt(body, tryBlock);
      var exceptBlock = wr.NewBlockPy($"except {DafnyRuntimeModule}.HaltException as e:");
      exceptBlock.Write($"{IdProtect(haltMessageVarName)} = ");
      if (UnicodeCharEnabled) {
        exceptBlock.Write($"{DafnySeqMakerFunction}(map({DafnyRuntimeModule}.CodePoint, e.message))");
      } else {
        exceptBlock.Write("e.message");
      }
      exceptBlock.WriteLine();
      TrStmt(recoveryBody, exceptBlock);
    }
  }
}
