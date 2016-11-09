//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;
using System.Text;
using Newtonsoft.Json;

namespace Microsoft.Dafny {

  static class MyExtensions {
    // Convert a NativeType to a Kremlin Constant.width
    public static string KremlinType(this NativeType n) {
      string t = (n.LowerBound.IsZero) ? "UInt" : "SInt";
      return t + ((n.UpperBound.ToByteArray().Length-1) * 8).ToString();
    }
  }

  public class KremlinCompiler : ICompiler {
    public KremlinCompiler() {
  
    }

    List<LocalVariable> varDeclsList; // a list of variable declarations within a Statement list.  Non-null on the first call to TrStmt(), null on the second
    Method enclosingMethod;  // non-null when a method body is being translated
    BoundVar enclosingThis;  // non-null when a class function or method is being translated
    string DafnyDefaultModuleName = "Dafny";
    const string ThisName = "this";


    FreshIdGenerator idGenerator = new FreshIdGenerator();

    JsonTextWriter j;

    Dictionary<Expression, int> uniqueAstNumbers = new Dictionary<Expression, int>();
    int GetUniqueAstNumber(Expression expr) {
      Contract.Requires(expr != null);
      int n;
      if (!uniqueAstNumbers.TryGetValue(expr, out n)) {
        n = uniqueAstNumbers.Count;
        uniqueAstNumbers.Add(expr, n);
      }
      return n;
    }

    public int ErrorCount {
      get {
        return errorCount;
      }
    }
    int errorCount;

    public TextWriter ErrorWriter {
      get {
        return errorWriter;
      }
      set {
        errorWriter = value;
      }
    }
    TextWriter errorWriter = Console.Out;

    void Error(string msg, TextWriter wr, params object[] args) {
      Contract.Requires(msg != null);
      Contract.Requires(args != null);

      string s = string.Format("Compilation error: " + msg, args);
      ErrorWriter.WriteLine(s);
      wr.WriteLine("/* {0} */", s);
      errorCount++;
    }

    void Error(string msg, params object[] args) {
      Contract.Requires(msg != null);
      Contract.Requires(args != null);

      string s = string.Format("Compilation error: " + msg, args);
      ErrorWriter.WriteLine(s);
      j.WriteComment("ERROR: " + s);
      errorCount++;
    }

    static class KremlinAst {
      public const string Version = "19";

      // InputAst.Decl
      public const string DFunction = "DFunction";        // of (calling_convention option * flag list * typ * lident * binder list * expr)
      public const string DTypeAlias = "DTypeAlias";      // of (lident * int * typ) (** Name, number of parameters (De Bruijn), definition. *)
      public const string DGlobal = "DGlobal";            // of (flag list * lident * typ * expr)
      public const string DTypeFlat = "DTypeFlat";        // (lident * int * fields_t)  (** The boolean indicates if the field is mutable *)
      public const string DExternal = "DExternal";        // of (calling_convention option * lident * typ)
      public const string DTypeVariant = "DTypeVariant";  // of (lident * int * branches_t)

      // fields_t = (ident * (typ * bool)) list
      // branches_t = (ident * fields_t) list

      // Common.flag
      public const string Private = "Private";
      public const string NoExtract = "NoExtract";

      // InputAst.typ
      public const string TInt = "TInt";                  // of K.width
      public const string TBuf = "TBuf";                  // of typ
      public const string TUnit = "TUnit";
      public const string TQualified = "TQualified";      // of lident
      public const string TBool = "TBool";
      public const string TAny = "TAny";
      public const string TArrow = "TArrow";              // of (typ * typ)   (** t1 -> t2 *)
      public const string TZ = "TZ";
      public const string TBound = "TBound";              // of int
      public const string TApp = "TApp";                  // of (lident * typ list)

      // InputAst.Expr
      public const string EBound = "EBound";              // of var
      public const string EQualified = "EQualified";      // of lident
      public const string EConstant = "EConstant";        // of K.t
      public const string EUnit = "EUnit";
      public const string EApp = "EApp";                  // of (expr * expr list)
      public const string ELet = "ELet";                  // of (binder * expr * expr)
      public const string EIfThenElse = "EIfThenElse";    // of (expr * expr * expr)
      public const string ESequence = "ESequence";        // of expr list
      public const string EAssign = "EAssign";            // of (expr * expr)   (** left expression can only be a EBound or EOpen *)
      public const string EBufCreate = "EBufCreate";      // of (lifetime * expr * expr)   (** initial value, length *)
      public const string EBufRead = "EBufRead";          // of (expr * expr)   (** e1[e2] *)
      public const string EBufWrite = "EBufWrite";        // of (expr * expr * expr)   (** e1[e2] <- e3 *)
      public const string EBufSub = "EBufSub";            // of (expr * expr)   (** e1 + e2 *)
      public const string EBufBlit = "EBufBlit";          // of (expr * expr * expr * expr * expr)  (** e1, index; e2, index; len *)
      public const string EMatch = "EMatch";              // of (expr * branches)
      public const string EOp = "EOp";                    // of (K.op * K.width)
      public const string ECast = "ECast";                // of (expr * typ)
      public const string EPushFrame = "EPushFrame";
      public const string EPopFrame = "EPopFrame";
      public const string EBool = "EBool";                //  of bool
      public const string EAny = "EAny";                  // (** to indicate that the initial value of a mutable let-binding does not matter *)
      public const string EAbort = "EAbort";              // (** exits the program prematurely *)
      public const string EReturn = "EReturn";            //  of expr
      public const string EFlat = "EFlat";                // of (typ * (ident * expr) list)  (** contains the name of the type we're building *)
      public const string EField = "EField";              // of (typ * expr * ident)         (** contains the name of the type we're selecting from *)
      public const string EWhile = "EWhile";              //  of (expr * expr)
      public const string EBufCreateL = "EBufCreateL";    // of (lifetime * expr list)
      public const string ETuple = "ETuple";              // of expr list
      public const string ECons = "ECons";                // of (typ * ident * expr list)

      // InputAst.pattern
      public const string PUnit = "PUnit";
      public const string PBool = "PBool";                // of bool
      public const string PVar = "PVar";                  // of binder
      public const string PCons = "PCons";                // of (ident * pattern list)
      public const string PTuple = "PTuple";              // of pattern list
      public const string PRecord = "PRecord";            // of (ident * pattern) list

      // Constant.width
      public const string UInt8 = "UInt8";
      public const string UInt16 = "UInt16";
      public const string UInt32 = "UInt32";
      public const string UInt64 = "UInt64";
      public const string Int8 = "Int8";
      public const string Int16 = "Int16";
      public const string Int32 = "Int32";
      public const string Int64 = "Int64";
      public const string Bool = "Bool";

      // Common.calling_convention
      public const string StdCall = "StdCall";
      public const string CDecl = "CDecl";
      public const string FastCall = "FastCall";

      // Common.lifetime
      public const string Eternal = "Eternal";
      public const string Stack = "Stack";
    }


    // "using (WriteArray()) {
    //  ...
    // }"
    // will wrap any generated Json with "[" and "]"
    WriteArrayHelper WriteArray() {
      return new WriteArrayHelper(j);
    }

    class WriteArrayHelper : IDisposable
    {
      JsonTextWriter j = null;

      public WriteArrayHelper(JsonTextWriter j) {
        this.j = j;
        j.WriteStartArray();
      }

      public void Dispose() {
        Dispose(true);
        GC.SuppressFinalize(this);
      }

      protected virtual void Dispose(bool disposing) {
        if (disposing && j != null) {
          j.WriteEndArray();
        }
        j = null;
      }
    }

    // "using (WriteObject()) {
    //  ...
    // }"
    // will wrap any generated Json with "{" and "}"
    WriteObjectHelper WriteObject() {
      return new WriteObjectHelper(j);
    }

    class WriteObjectHelper : IDisposable
    {
      JsonTextWriter j = null;

      public WriteObjectHelper(JsonTextWriter j) {
        this.j = j;
        j.WriteStartObject();
      }

      public void Dispose() {
        Dispose(true);
        GC.SuppressFinalize(this);
      }

      protected virtual void Dispose(bool disposing) {
        if (disposing && j != null) {
          j.WriteEndObject();
        }
        j = null;
      }
    }

    class VariableTracker
    {
      public void Clear() {
        l.Clear();
      }

      public void Push(IVariable var) {
        l.AddFirst(var);
      }

      public void Pop(IVariable var) {
        if (l.First == null) {
          // Mismatch between push and pop
          throw new cce.UnreachableException();
        }
        if (l.First.Value != var) {
          // Mismatch between push and pop
          throw new cce.UnreachableException();
        }
        l.RemoveFirst();
      }

      // To aid debugging
      public void Dump(JsonWriter j) {
        var n = l.First;
        int i = 0;
        j.WriteComment("VariableTracker ========");
        if (n == null) {
          return;
        }
        do {
          j.WriteComment(string.Format(" {0}: {1} ", i, n.Value.DisplayName));
          n = n.Next;
          i++;
        } while (n != null);
      }

      public int GetIndex(IVariable var) {
        // Search the list from front to back, to look for an existing instance
        if (l.First == null) {
          // No variables are present to look up.  Must Add() one first.
          throw new cce.UnreachableException();
        }

        var n = l.First;
        int i = 0;
        do {
          if (n.Value == var) {
            return i;
          }
          n = n.Next;
          i++;
        }  while (n != null);

        // Else the variable hasn't yet been added via a Let statement or function parameter
        throw new cce.UnreachableException();
      }

      // Make a copy of the VariableTracker() and its list.  Variables pointed to by the 
      // list are not copied.
      public VariableTracker Clone() {
        VariableTracker vt = new VariableTracker();
        var n = l.First;
        while (n != null) {
          vt.l.AddLast(n.Value);
          n = n.Next;
        }

        return vt;
      }

      LinkedList<IVariable> l = new LinkedList<IVariable>(); // A doubly-linked list
    }

    VariableTracker VarTracker = new VariableTracker();

    public void Compile(Program program, TextWriter wr) {
      Contract.Requires(program != null);

      // program.Name is the source filename without any path.  Remove the extension
      // and use it as the name of the default module.  In C#, this would have been
      // "_module".  See WriteLident() for the renaming process.
      DafnyDefaultModuleName = System.IO.Path.GetFileNameWithoutExtension(program.Name).Replace('.', '_');

      // Kremlin's JSON input is all JSON arrays, not serialized objects in the usual way.
      //  [6, [
      //      ["FStar_Mul", []],
      //      ["FStar_UInt", [
      //          ["DFunction", [
      //              ["TUnit"], "FStar_UInt_lognot_lemma_2", [{
      //                  "name": "n",
      //                  "typ": ["TQualified", [
      //                      ["Prims"], "pos"
      //                  ]],
      //                 "mut": false,
      //                  "mark": 0
      //              }],
      //              ["EUnit"]
      //          ]]
      //      ]], ...

      j = new JsonTextWriter(wr);
      j.Formatting = Formatting.Indented;
      j.Indentation = 1;
      using (WriteArray()) { // Entire contents is an array - type binary_format
        j.WriteRawValue(KremlinAst.Version); // binary_format = version * file list
        using (WriteArray()) { // start of file list

          // bugbug: generate builtins as needed
          //CompileBuiltIns(program.BuiltIns);

          // Compile modules in order by height (program.Modules is sorted this way but in
          // reverse order). Compile SystemModule last, as it has height -1 and is not in 
          // the .Modules list.
          List<ModuleDefinition> sortedModules = new List<ModuleDefinition>(program.Modules());
          sortedModules.Reverse();

          int previousHeight = sortedModules[0].Height+1;
          foreach (ModuleDefinition m in sortedModules) {
            Contract.Assert(m.Height < previousHeight); // .Modules is sorted
            CompileModule(m, wr);
            previousHeight = m.Height;
          }
          CompileModule(program.BuiltIns.SystemModule, wr);

        } // End of file list
      } // End of entire contents
      j.Close();
    }

    void CompileModule(ModuleDefinition m, TextWriter wr) {
      Contract.Requires(m != null);

      if (m.IsAbstract) {
        // the purpose of an abstract module is to skip compilation
        return;
      }

      string ModuleName = DafnyDefaultModuleName;
      if (!m.IsDefaultModule) {
        var m_prime = m;
        while (DafnyOptions.O.IronDafny && m_prime.ClonedFrom != null) {
          m_prime = m.ClonedFrom;
        }
        ModuleName = m_prime.Name;
      }

      List<TopLevelDecl> topLevelDecls = SortTopLevelDecls(m.TopLevelDecls);

      // A Module is translated as a file:  string * program
      using (WriteArray()) { // start of file
        j.WriteValue(ModuleName);
        using (WriteArray()) { // start of program array
          foreach (TopLevelDecl d in topLevelDecls) {
            CompileTypeLevelDecl(d, wr);
          }
        }
      } // End of file
    }

    // Sort the TopLevelDecls within a module, into dependency order.
    List<TopLevelDecl> SortTopLevelDecls(List<TopLevelDecl> decls) {
      List<Type> referencedTypes = new List<Type>(); // The set of types referenced by the decls
      List<TopLevelDecl> topLevelTypes = new List<TopLevelDecl>(); // TopLevelDecl representing its type

      // First pass:  for each TopLevelDecl, walk it and track the types that
      //              it depends on.  Also track the type produced by the
      //              TopLevelDecl, if any.
      foreach (TopLevelDecl d in decls) {
        SortTopLevelDeclsWorker(d, d, referencedTypes, topLevelTypes);
      }

      // Second pass:  for each type, get its TopLevelDecl, if it has one
      //               add it to the tld list if it isn't already present
      List<TopLevelDecl> ret = new List<TopLevelDecl>();
      foreach (Type t in referencedTypes) {
        if (t is UserDefinedType) {
          var udt = (UserDefinedType)t;
          if (udt.ResolvedClass != null) {
            string TypeName = udt.ResolvedClass.FullName;

            foreach (var tlt in topLevelTypes) {
              if (tlt.FullName == TypeName) {
                if (!ret.Contains(tlt)) {
                  ret.Add(tlt);
                }
                break;
              }
            }
          }
        }
      }

      // Third pass:  add the remaining TopLevelDecls from topLevelTypes, 
      //              representing all types
      foreach (var tlt in topLevelTypes) {
        if (!ret.Contains(tlt)) {
          ret.Add(tlt);
        }
      }

      // Now fill in the remaining TopLevelDecls, for methods and functions, etc.
      foreach (TopLevelDecl d in decls) {
        if (!ret.Contains(d)) {
          ret.Add(d);
        }
      }

      return ret;
    }

    void SortTopLevelDeclsWorker(TopLevelDecl tld, Declaration d, List<Type> referencedTypes, List<TopLevelDecl> topLevelTypes) {
        if (d is NewtypeDecl) {
          var nt = (NewtypeDecl)d;
          referencedTypes.Add(nt.BaseType);
          if (tld != null) {
            topLevelTypes.Add(tld);
          }
        } else if (d is DatatypeDecl) {
          var dt = (DatatypeDecl)d;
          foreach (var ctor in dt.Ctors) {
            foreach (Formal arg in ctor.Formals) {
              if (!arg.IsGhost) {
                referencedTypes.Add(arg.Type);
              }
            }
          }
          if (tld != null) {
            topLevelTypes.Add(tld);
          }
        }
        else if (d is ClassDecl) {
          var c = (ClassDecl)d;
          foreach (var cd in c.InheritedMembers) {
            if (!cd.IsGhost) {
              SortTopLevelDeclsWorker(null, cd, referencedTypes, topLevelTypes);
            }
          }
          foreach (MemberDecl member in c.Members) {
            if (!member.IsGhost) {
              SortTopLevelDeclsWorker(null, member, referencedTypes, topLevelTypes);
            }
          }
          if (tld != null) {
            topLevelTypes.Add(tld);
          }
        }
        else if (d is MemberDecl) {
          var m = (MemberDecl)d;
          if (m is Field) {
            var f = (Field)m;
            referencedTypes.Add(f.Type);
          }
          else if (m is Function) {
            var f = (Function)m;
            foreach (Formal p in f.Formals) {
              referencedTypes.Add(p.Type);
            }
            referencedTypes.Add(f.ResultType);
          }
          else if (m is Method) {
            var meth = (Method)m;
            foreach (Formal p in meth.Ins) {
              if (!p.IsGhost) {
                referencedTypes.Add(p.Type);
              }
            }
            foreach (Formal p in meth.Outs) {
              if (!p.IsGhost) {
                referencedTypes.Add(p.Type);
              }
            }
          }
        }
    }

    void CompileTypeLevelDecl(TopLevelDecl d, TextWriter wr) {
      Contract.Requires(d != null);

      bool compileIt = true;
      if (Attributes.ContainsBool(d.Attributes, "compile", ref compileIt) && !compileIt) {
        return;
      }
      if (d is OpaqueTypeDecl) {
        var at = (OpaqueTypeDecl)d;
        WriteToken(d.tok);
        Error("Opaque type ('{0}') cannot be compiled", wr, at.FullName);
      }
      else if (d is TypeSynonymDecl) {
        // do nothing, just bypass type synonyms in the compiler
      }
      else if (d is NewtypeDecl) {
        var nt = (NewtypeDecl)d;
        WriteToken(d.tok);
        if (nt.CompileName == "uint64" ||
            nt.CompileName == "uint32" ||
            nt.CompileName == "byte") {
          // Skip SHA256 types.s.dfy definitions of native types.  They are unused, but
          // are defined in terms of BigInteger, which Kremlin does not support.
          j.WriteComment("Allowing types.s.dfy definition of " + nt.CompileName);
        }
        using (WriteArray()) {
          j.WriteValue(KremlinAst.DTypeAlias);
          using (WriteArray()) { //  (lident * int * typ)
            WriteLident(nt.FullName);
            j.WriteValue(0); // number of parameters (De Bruijn)
            WriteTypeName(nt.BaseType);
          }
        }
      }
      else if (d is DatatypeDecl) {
        var dt = (DatatypeDecl)d;
        WriteToken(d.tok);
        if (dt.TypeArgs.Count != 0) {
          // system.tuple2<> in sha256 is an example, but unused.
          j.WriteComment("WARNING: DatatypeDecl of parameterized type not supported"); // bugbug: implement.  
        }
        else {
          // Define the type
          if (!CompileDatatypeStruct(dt)) {
            // Generate constructor functions for that type, if it is a struct rather than an enum
            CompileDatatypeConstructors(dt);
          }
        }
      }
      else if (d is IteratorDecl) {
        var iter = (IteratorDecl)d;
        WriteToken(d.tok);
        j.WriteComment("BUGBUG IteratorDecl ignored: " + iter.CompileName); // bugbug: implement
      }
      else if (d is TraitDecl) {
        var trait = (TraitDecl)d;
        WriteToken(d.tok);
        j.WriteComment("BUGBUG TraitDecl ignored: " + trait.CompileName); // bugbug: implement
      }
      else if (d is ClassDecl) {
        var cl = (ClassDecl)d;
        CompileClassMembers(cl);
      }
      else if (d is ModuleDecl) {
        // nop
      }
      else { Contract.Assert(false); }
    }

    void CompileDatatypeConstructors(DatatypeDecl dt) {
      Contract.Requires(dt != null);

      if (dt is CoDatatypeDecl) {
        WriteEAbort("BUGBUG: CoDatatypeDecl not supported"); // bugbug: implement
      }
      // For Kremlin, generate a constructor only:  There are no .NET base 
      // object methods such as Equals() or GetHashCode() so no code-gen is 
      // needed here, to support them.
      //   public Dt_Ctor(arguments) {
      //     Fields = arguments;
      //   }

      UserDefinedType thisType = UserDefinedType.FromTopLevelDecl(dt.tok, dt);
      foreach (DatatypeCtor ctor in dt.Ctors) {

        VarTracker.Clear();
        var pThis = new BoundVar(ctor.tok, ThisName, thisType);

        using (WriteArray()) {
          j.WriteValue(KremlinAst.DFunction);
          using (WriteArray()) { // of (CallingConvention.t option * flag list * typ * lident * binder list * expr)
            WriteDefaultCallingConvention();
            using (WriteArray()) { // flag list.  NoExtract flag can be added here if needed
            }
            WriteTypeName(thisType); // returns type of 'this'
            WriteLident(ctor.FullName);
            using (WriteArray()) { // start of binder list
              WriteFormals(ctor.Formals);
            }
            using (WriteArray()) {
              j.WriteValue(KremlinAst.ESequence);
              // Do not emit EPushFrame/EPopFrame, as we want the allocation
              //  of pThis to be inlined into the calling function.
              using (WriteArray()) {
                // ELet pThis = DefaultValueOfType in ESequence...
                using (WriteArray()) {
                  j.WriteValue(KremlinAst.ELet);
                  using (WriteArray()) { // of (binder * expr * expr)
                    WriteBinder(pThis, ThisName, true);
                    VarTracker.Push(pThis);
                    WriteDefaultValue(thisType);
                    using (WriteArray()) {
                      j.WriteValue(KremlinAst.ESequence);
                      using (WriteArray()) { // of expr list
                        foreach (Formal arg in ctor.Formals) {
                          if (arg.IsGhost) {
                            continue;
                          }
                          // EAssign (EField of (EBufRead this.arg 0)) = EBound of Formal
                          using (WriteArray()) {
                            Formatting old = j.Formatting;
                            j.Formatting = Formatting.None;
                            j.WriteValue(KremlinAst.EAssign);
                            using (WriteArray()) { // of (expr * expr)
                              // First expr:  EField of EBufRead('this',0) to write into
                              using (WriteArray()) {
                                j.WriteValue(KremlinAst.EField);
                                using (WriteArray()) {  // of (typ * expr * ident)
                                  WriteTypeOfLident(pThis.Type); // typ
                                  using (WriteArray()) {
                                    j.WriteValue(KremlinAst.EBufRead);
                                    using (WriteArray()) {
                                      WriteEBound(pThis);
                                      WriteConstant(0u);
                                    }
                                  }
                                  j.WriteValue(arg.Name);
                                }
                              }
                              // Second expr: // EBound of formal
                              WriteEBound(arg);
                            }
                            j.Formatting = old;
                          }
                        }
                        WriteEBound(pThis); // and return the pThis expression from the constructor
                      }
                    }
                    VarTracker.Pop(pThis);
                  }
                }
              }
            }
          }
        }
        enclosingThis = null;
      }
    }

    bool ShouldBeEnum(DatatypeDecl dt) {
      foreach (DatatypeCtor ctor in dt.Ctors) {
        foreach (Formal arg in ctor.Formals) {
          return false;
        }
      }
      // Returns true only if all Ctors have zero formals, ghost or otherwise
      return true;
    }

    // Returns true if the DataTypeDecl was compiled as a DTypeVariant (an 
    // enum), or false if a struct.
    bool CompileDatatypeStruct(DatatypeDecl dt) {
      Contract.Requires(dt != null);

      if (ShouldBeEnum(dt)) {
        WriteToken(dt.tok);
        using (WriteArray()) {
          j.WriteValue(KremlinAst.DTypeVariant); // (lident * int * branches_t)
          using (WriteArray()) {
            WriteLident(dt.FullName);
            j.WriteValue(0); // int type index
            using (WriteArray()) { // branches_t = (ident * fields_t) list
                foreach (DatatypeCtor ctor in dt.Ctors) {
                  using (WriteArray()) {
                  j.WriteValue(ctor.Name);
                  using (WriteArray()) {
                    // No fields
                  }
                }
              }
            }
          }
        }
        return true;
      }
      else {
        foreach (DatatypeCtor ctor in dt.Ctors) {
          WriteToken(ctor.tok);
          using (WriteArray()) {
            j.WriteValue(KremlinAst.DTypeFlat); // of (lident * int * fields_t)
            using (WriteArray()) {
              WriteLident(dt.FullName); // lident
              j.WriteValue(0); // int type index
              using (WriteArray()) { // list
                int i = 0;
                foreach (Formal arg in ctor.Formals) {
                  if (arg.IsGhost) {
                    continue;
                  }
                  Formatting old = j.Formatting;
                  j.Formatting = Formatting.None;
                  using (WriteArray()) { // (ident * (typ * bool))
                    j.WriteValue(FormalName(arg, i));
                    using (WriteArray()) {
                      WriteTypeName(arg.Type); // bugbug: for buffer/array types, how should this specify the length?
                      j.WriteValue(true); // mutable
                    }
                    i++;
                    j.Formatting = old;
                  }
                }
              }
            }
          }
        }
        return false;
      }
    }

    // create a varName that is not a duplicate of formals' name
    string GenVarName(string root, List<Formal> formals) {
      bool finished = false;
      while (!finished) {
        finished = true;
        int i = 0;
        foreach (var arg in formals) {
          if (arg.IsGhost) {
            continue;
          }
          if (root.Equals(FormalName(arg, i))) {
            root += root;
            finished = false;
          }
          i++;
        }
      }
      return root;
    }

    int WriteFormals(List<Formal/*!*/>/*!*/ formals) {
      Contract.Requires(cce.NonNullElements(formals));

      if (enclosingThis != null) {
        WriteBinder(enclosingThis, ThisName, false);
        VarTracker.Push(enclosingThis);
      }

      int i = 0;
      foreach (Formal arg in formals) {
        if (arg.IsGhost) {
          continue;
        }
        string name = FormalName(arg, i);
        WriteBinder(arg, name, false);
        VarTracker.Push(arg);
        i++;
      }

      VarTracker.Dump(j);
      return i;  // the number of formals written
    }

    string FormalName(Formal formal, int i) {
      Contract.Requires(formal != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return formal.HasName ? formal.Name : "_a" + i;
    }

    public bool HasMain(Program program) {
      Method mainMethod = null;
      bool hasMain = false;
      foreach (var module in program.Modules()) {
        if (module.IsAbstract) {
          // the purpose of an abstract module is to skip compilation
          continue;
        }
        foreach (var decl in module.TopLevelDecls) {
          var c = decl as ClassDecl;
          if (c != null) {
            foreach (var member in c.Members) {
              var m = member as Method;
              if (m != null && IsMain(m)) {
                if (mainMethod == null) {
                  mainMethod = m;
                  hasMain = true;
                } else {
                  // more than one main in the program
                  ErrorWriter.WriteLine("More than one method is declared as \"main\"");
                  errorCount++;
                  hasMain = false;
                }
              }
            }
          }
        }
      }
      return hasMain;
    }

    public static bool IsMain(Method m) {
      // In order to be a legal Main() method, the following must be true:
      //    The method takes no parameters
      //    The method is not a ghost method 
      //    The method has no requires clause 
      //    The method has no modifies clause 
      //    If the method is an instance (that is, non-static) method in a class, then the enclosing class must not declare any constructor
      // Or if a method is annotated with {:main} and the above restrictions apply, except it is allowed to take ghost arguments, 
      //    and it is allowed to have preconditions and modifies.  This lets the programmer add some explicit assumptions about the outside world, 
      //    modeled, for example, via ghost parameters.
      if (!m.IsGhost && m.Name == "Main" && m.TypeArgs.Count == 0 && m.Ins.Count == 0 && m.Outs.Count == 0 && m.Req.Count == 0
            && m.Mod.Expressions.Count == 0 && (m.IsStatic || (((ClassDecl)m.EnclosingClass) == null) || !((ClassDecl)m.EnclosingClass).HasConstructor)) {
        return true;
      } else if (Attributes.Contains(m.Attributes, "main") && !m.IsGhost && m.TypeArgs.Count == 0 && m.Outs.Count == 0
            && (m.IsStatic || (((ClassDecl)m.EnclosingClass) == null) || !((ClassDecl)m.EnclosingClass).HasConstructor)) {
        if (m.Ins.Count == 0) {
          return true;
        } else {
          bool isGhost = true;
          foreach (var arg in m.Ins) {
            if (!arg.IsGhost) {
              isGhost = false;
            }
          }
          return isGhost;
        }
      } else {
        return false;
      }
    }

    bool WriteClassStruct(ClassDecl c, bool forCompanionClass) {
      Contract.Requires(c != null);

      // Don't write out a struct with no members, as it isn't valid C
      if (c.InheritedMembers.Count == 0) {
        bool HasNoMembers = true;
        foreach (MemberDecl member in c.Members) {
          if (member is Field) {
            var f = (Field)member;
            if (f.IsGhost || forCompanionClass) {
              // emit nothing
            }
            else {
              HasNoMembers = false;
              break;
            }
          }
        }
        if (HasNoMembers) {
          j.WriteComment("Not writing class struct " + c.FullCompileName + " as it has no non-ghost members");
          return false;
        }
      }

      using (WriteArray()) {
        j.WriteValue(KremlinAst.DTypeFlat); // of (lident * int * fields_t)
        using (WriteArray()) {
          WriteLident(c.FullName);
          j.WriteValue(0); // int type index
          using (WriteArray()) { // list
            foreach (var member in c.InheritedMembers) {
              Contract.Assert(!member.IsGhost && !member.IsStatic);  // only non-ghost instance members should ever be added to .InheritedMembers
              j.WriteComment("Inherited member");
              using (WriteArray()) {
                if (member is Field) {
                  var f = (Field)member;
                  using (WriteArray()) { // (ident * (typ * bool))
                    j.WriteValue(f.Name);
                    using (WriteArray()) {
                      WriteTypeName(f.Type);
                      j.WriteValue(true); // mutable
                    }
                  }
                }
              }
            }

            foreach (MemberDecl member in c.Members) {
              if (member is Field) {
                var f = (Field)member;
                if (f.IsGhost || forCompanionClass) {
                  // emit nothing
                }
                else if (c is TraitDecl) {
                  WriteToken(member.tok);
                  j.WriteComment("BUGBUG TraitDecl not supported: " + f.CompileName); // bugbug: implement
                }
                else {
                  using (WriteArray()) { // (ident * (typ * bool))
                    j.WriteValue(f.Name);
                    using (WriteArray()) {
                      WriteTypeName(f.Type);
                      j.WriteValue(true);
                    }
                  }
                }
              }
            }
          }
        }
      }

      return true;
    }

    // Do what "new TypeName();" would have done in .NET.  See WriteClassStruct()
    // for the code that emits the DTypeFlat.  This function creates an instance
    // of that type.
    void WriteClassAllocation(UserDefinedType udt) {
      var c = (udt.ResolvedClass) as ClassDecl;

      using (WriteArray()) {
        j.WriteValue(KremlinAst.EBufCreateL); // of lifetime * expr list
        using (WriteArray()) {
          using (WriteArray()) {
            j.WriteValue(KremlinAst.Stack);
          }
          using (WriteArray()) {
            using (WriteArray()) {
              j.WriteValue(KremlinAst.EFlat);
              using (WriteArray()) { // (typ * (ident * expr) list)
                WriteTypeOfLident(udt);
                using (WriteArray()) {
                  foreach (var member in c.InheritedMembers) {
                    Contract.Assert(!member.IsGhost && !member.IsStatic);  // only non-ghost instance members should ever be added to .InheritedMembers
                    j.WriteComment("Inherited member");
                    using (WriteArray()) {
                      if (member is Field) {
                        var f = (Field)member;
                        using (WriteArray()) { // (ident * expr)
                          j.WriteValue(f.Name);
                          WriteDefaultValue(f.Type);
                        }
                      }
                    }
                  }

                  foreach (MemberDecl member in c.Members) {
                    if (member is Field) {
                      var f = (Field)member;
                      if (f.IsGhost) {
                        // emit nothing
                      }
                      else if (c is TraitDecl) {
                        WriteToken(member.tok);
                        j.WriteComment("BUGBUG TraitDecl not supported: " + f.CompileName); // bugbug: implement
                      }
                      else {
                        using (WriteArray()) { // (ident * expr)
                          j.WriteValue(f.Name);
                          WriteDefaultValue(f.Type);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }



    void CompileClassMembers(ClassDecl c) {
      Contract.Requires(c != null);

      // For C#, Dafny generates a C# class containing base members, class 
      // fields, methods, and functions all together.
      //
      // For Kremlin, a class will generate a struct (a Kremlin DTypeFlat) 
      // followed by functions (Kremlin DFunction), with explicit "this"
      // parameters.

      bool forCompanionClass = false; // bugbug: implement

      // Generate the DTypeFlat struct representing the class
      if (!WriteClassStruct(c, forCompanionClass)) {
        // No class struct was written because it has no non-ghost members
        foreach (var member in c.InheritedMembers) {
          Contract.Assert(!member.IsGhost && !member.IsStatic);  // only non-ghost instance members should ever be added to .InheritedMembers
        }
        bool HasNoMembers = true;
        foreach (MemberDecl member in c.Members) {
          if (!(member is Field) && !member.IsGhost) {
            HasNoMembers = false;
            break;
          }
        }
        if (HasNoMembers) {
          // Skip the class if it is entirely ghost
          return;
        }
      }
      UserDefinedType thisType = UserDefinedType.FromTopLevelDecl(c.tok, c);

      foreach (var member in c.InheritedMembers) {
        Contract.Assert(!member.IsGhost && !member.IsStatic);  // only non-ghost instance members should ever be added to .InheritedMembers
        using (WriteArray()) {
          if (member is Field) {
            // Do nothing - WriteClassStruct already handled this case
          } else if (member is Function) {
            var f = (Function)member;
            Contract.Assert(f.Body != null);
            WriteToken(member.tok);
            j.WriteComment("BUGBUG Function unsupported: " + f.CompileName); // bugbug: implement
          }
          else if (member is Method) {
            var method = (Method)member;
            Contract.Assert(method.Body != null);
            WriteToken(member.tok);
            j.WriteComment("BUGBUG Method unsupported: " + method.CompileName); // bugbug: implement
          }
          else {
            Contract.Assert(false);  // unexpected member
          }
        }
      }
      foreach (MemberDecl member in c.Members) {
        if (member is Field) {
          // Do nothing - WriteClassStruct already handled this case
        }
        else if (member is Function) {
          var f = (Function)member;
          if (f.Body == null && !(c is TraitDecl && !f.IsStatic)) {
            // A (ghost or non-ghost) function must always have a body, except if it's an instance function in a trait.
            if (forCompanionClass /* || Attributes.Contains(f.Attributes, "axiom") */) {
              // suppress error message (in the case of "forCompanionClass", the non-forCompanionClass call will produce the error message)
            } else {
              // The C# backend ignores functions that are axioms.  But for
              // the Spartan scenario, treat these as extern functions.
              WriteToken(member.tok);
              CompileExternalFunction(f);
            }
          } else if (f.IsGhost) {
            // nothing to compile, but we do check for assumes
            if (f.Body == null) {
              Contract.Assert(c is TraitDecl && !f.IsStatic);
            } else {
              var v = new CheckHasNoAssumes_VisitorJ(this, j);
              v.Visit(f.Body);
            }
          } else if (c is TraitDecl && !forCompanionClass) {
            // include it, unless it's static
            if (!f.IsStatic) {
              WriteToken(member.tok);
              j.WriteComment("BUGBUG TraitDecl in function is unsupported: " + f.FullName); // bugbug: implement
            }
          } else if (forCompanionClass && !f.IsStatic) {
            // companion classes only has static members
          } else {
            WriteToken(member.tok);
            enclosingThis = (f.IsStatic) ? null : new BoundVar(c.tok, ThisName, thisType);
            CompileFunction(f);
            enclosingThis = null;
          }
        } else if (member is Method) {
          var m = (Method)member;
          if (m.Body == null && !(c is TraitDecl && !m.IsStatic)) {
            // A (ghost or non-ghost) method must always have a body, except if it's an instance method in a trait.
            if (forCompanionClass /* || Attributes.Contains(m.Attributes, "axiom") */ ) {
              // suppress error message (in the case of "forCompanionClass", the non-forCompanionClass call will produce the error message)
            } else {
              // The C# backend ignores functions that are axioms.  But for
              // the Spartan scenario, treat these as extern functions.
              WriteToken(member.tok);
              CompileExternalMethod(c, m);
            }
          } else if (m.IsGhost) {
            // nothing to compile, but we do check for assumes
            if (m.Body == null) {
              Contract.Assert(c is TraitDecl && !m.IsStatic);
            } else {
              var v = new CheckHasNoAssumes_VisitorJ(this, j);
              v.Visit(m.Body);
            }
          } else if (c is TraitDecl && !forCompanionClass) {
            // include it, unless it's static
            if (!m.IsStatic) {
              j.WriteComment("BUGBUG TraitDecl not supported: " + m.CompileName); // bugbug: implement
            }
          } else if (forCompanionClass && !m.IsStatic) {
            // companion classes only has static members
          } else {
            WriteToken(member.tok);
            enclosingThis = (m.IsStatic) ? null : new BoundVar(c.tok, ThisName, thisType);
            CompileMethod(c, m);
            enclosingThis = null;
          }
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member
        }
      }
    }

    private void WriteLident(string FullName) {
      string[] names = FullName.Split('.');
      for (int i = 0; i < names.Length; ++i) {
        // Remove '#' prefix.  See DatatypeCtor.FullName in DafnyAst.cs.
        names[i] = names[i].TrimStart('#');
        // See DefaultModuleDecl in DafnyAst.cs for the hard-coded name "_module"
        // And see DefaultClassDecl for the hard-coded name "_default".

        if (names[i] == "_module" || names[i] == "_default") {
          names[i] = DafnyDefaultModuleName;
        }
      }

      using (WriteArray()) {
        using (WriteArray()) {
          if (names.Length == 1) {
            j.WriteValue(DafnyDefaultModuleName);
          }
          else {
            int i = 0;
            if (names.Length > 2 && names[0] == DafnyDefaultModuleName) { 
              i = 1; // Skip the default module name
            }
            for (; i < names.Length - 1; ++i) {
              j.WriteValue(names[i]);
            }
          }
        }
        j.WriteValue(names[names.Length - 1]);
      }
    }

    private void WriteLident(MemberDecl d) {
      WriteLident(d.FullName);
    }

    private void WriteLident(Type t) {
      if (t is UserDefinedType) {
        var udt = (UserDefinedType)t;
        WriteLident(udt.FullName);
      }
      else {
        j.WriteComment("bugbug: WriteLident of unknown type " + t.ToString()); // bugbug: implement
      }
    }

    // WriteType() of a UDT writes out [TBuf[TQualified[["module"]"class"]]] - a pointer to the type
    // This writes out                       TQualified[["module"]"class"]]  - the base type itself
    private void WriteTypeOfLident(Type t) {
      using (WriteArray()) {
        j.WriteValue(KremlinAst.TQualified);
        WriteLident(t);
      }
    }

    // Compile a function with no body
    private void CompileExternalFunction(Function f) {
      Contract.Assert(f != null);
      Contract.Assert(f.Body == null);

      VarTracker.Clear();

      List<Tuple<Type, string>> typeList = new List<Tuple<Type, string>>();
      foreach (Formal p in f.Formals) {
        if (!p.IsGhost) {
          typeList.Add(Tuple.Create(p.Type, p.Name));
        }
      }
      typeList.Add(Tuple.Create(f.ResultType, "returns"));

      WriteExternal(f, typeList);
    }

    bool IsUnsupportedFunction(string Name, Type Result, List<Formal> Formals) {
      if (IsUnsupportedType(Result)) {
        j.WriteComment("Ignoring function " + Name + " due to unsupported return type");
        return true;
      }
      foreach (var f in Formals) {
        if (!f.IsGhost && IsUnsupportedType(f.Type)) {
          j.WriteComment("Ignoring function " + Name + " due to unsupported formal argument type");
          return true;
        }
      }
      return false;
    }

    bool IsUnsupportedMethod(string Name, List<Formal> Outs, List<Formal> Ins) {
      foreach (var f in Outs) {
        if (!f.IsGhost && IsUnsupportedType(f.Type)) {
          j.WriteComment("Ignoring method " + Name + " due to unsupported out type");
          return true;
        }
      }
      foreach (var f in Ins) {
        if (!f.IsGhost && IsUnsupportedType(f.Type)) {
          j.WriteComment("Ignoring method " + Name + " due to unsupported in type");
          return true;
        }
      }
      return false;
    }

    private void CompileFunction(Function f) {
      Contract.Assert(f != null);
      Contract.Assert(f.Body != null);

      VarTracker.Clear();

      if (f.TypeArgs.Count != 0) {
        // Template expansion isn't supported
        j.WriteComment("BUGBUG: Type args not supported:  omitting function " + f.FullCompileName);
        return;
      }
      if (IsUnsupportedFunction(f.Name, f.ResultType, f.Formals)) {
        return;
      }

      using (WriteArray()) {
        j.WriteValue(KremlinAst.DFunction);
        using (WriteArray()) { // of (CallingConvention.t option * flag list * typ * lident * binder list * expr)
          WriteDefaultCallingConvention();
          using (WriteArray()) { // flag list.  NoExtract flag can be added here if needed
          }
          WriteTypeName(f.ResultType); // typ
          WriteLident(f); // lident
          using (WriteArray()) { // start of binder list
            WriteFormals(f.Formals);
          }
          // Don't wrap in EPushFrame/EPopFrame as functions may allocate
          // a return EBuf and we want that to happen in the caller's
          // stack frame.
          CompileReturnBody(f.Body);
        }
      }
    }

    void WriteMethodReturnType(List<Formal> Outs) {
      Contract.Requires(Outs != null);

      int i = 0;
      foreach (Formal arg in Outs) {
        if (arg.IsGhost) {
          continue;
        }
        WriteTypeName(arg.Type);
        i++;
      }
      if (i == 0) {
        WriteTUnit();
      }
    }

    private void WriteExternal(MemberDecl lident, List<Tuple<Type, string>> typeList) {
      if (typeList.Count == 1 && typeList[0].Item1 == null) {
        // The typeList is just TUnit, so there are no inputs and no outputs.
        return;
      }

      using (WriteArray()) {
        j.WriteValue(KremlinAst.DExternal);
        using (WriteArray()) { // of (CallingConvention.t option * lident * typ)
          WriteDefaultCallingConvention();
          WriteLident(lident); // lident

          if (typeList.Count > 1) {
            for (int i = 0; i < typeList.Count - 1; ++i) {
              j.WriteStartArray();
              j.WriteValue(KremlinAst.TArrow);
              j.WriteStartArray(); // of (typ * typ)
              j.WriteComment(typeList[i].Item2);
              WriteTypeName(typeList[i].Item1);
            }
          }
          Type finalType = typeList[typeList.Count - 1].Item1;
          if (finalType == null) {
            WriteTUnit();
          }
          else {
            WriteTypeName(finalType);
          }
          for (int i = 0; i < typeList.Count - 1; ++i) {
            j.WriteEndArray();
            j.WriteEndArray();
          }
        }
      }
    }

    // Compile a method with no body
    private void CompileExternalMethod(ClassDecl c, Method m) {
      Contract.Assert(c != null);
      Contract.Assert(m != null);
      Contract.Assert(m.Body == null);

      if (m.TypeArgs.Count != 0) {
        // Template expansion isn't supported
        j.WriteComment("BUGBUG: Type args not supported:  omitting method " + m.FullCompileName);
        return;
      }

      List<Tuple<Type, string>> typeList = new List<Tuple<Type, string>>();
      if (enclosingThis != null) {
        typeList.Add(Tuple.Create(enclosingThis.Type, ThisName));
      }
      foreach (Formal p in m.Ins) {
        if (!p.IsGhost) {
          typeList.Add(Tuple.Create(p.Type, p.Name));
        }
      }
      bool HasAnOut = false;
      foreach (Formal p in m.Outs) {
        if (!p.IsGhost) {
          typeList.Add(Tuple.Create(p.Type, p.Name));
          HasAnOut = true;
        }
      }
      if (!HasAnOut) {
        typeList.Add(new Tuple<Type, string>(null, ""));
      }

      WriteExternal(m, typeList);
    }

    private void CompileMethod(ClassDecl c, Method m) {
      Contract.Assert(c != null);
      Contract.Assert(m != null);
      Contract.Assert(m.Body != null);

      VarTracker.Clear();

      if (m.TypeArgs.Count != 0) {
        // Template expansion isn't supported
        j.WriteComment("BUGBUG: Type args not supported:  omitting method " + m.FullCompileName);
        return;
      }

      if (IsUnsupportedMethod(m.Name, m.Outs, m.Ins)) {
        return;
      }

      using (WriteArray()) {
        j.WriteValue(KremlinAst.DFunction);
        using (WriteArray()) { // of (CallingConvention.t option * flag list * typ * lident * binder list * expr)
          WriteDefaultCallingConvention();
          using (WriteArray()) { // empty flag list
          }
          WriteMethodReturnType(m.Outs); // typ
          WriteLident(m); // lident
          using (WriteArray()) { // start of binder list
            WriteFormals(m.Ins);
          }
          using (WriteArray()) {
            j.WriteValue(KremlinAst.ESequence);
            using (WriteArray()) {
              List<Formal> Outs = new List<Formal>(m.Outs);
              if (!(m is Constructor)) {
                WriteEPushFrame();
              }
              foreach (Formal p in Outs) { // bugbug: this now needs to be hoisted out and made recursive
                if (!p.IsGhost) {
                  // ELet v in { Stmt 
                  j.WriteStartArray();
                  j.WriteValue(KremlinAst.ELet);
                  j.WriteStartArray();
                  WriteBinder(p, p.Name, true); // lident
                  WriteDefaultValue(p.Type);    // = default
                  VarTracker.Push(p);
                  // "in" is the contents that follow
                  j.WriteStartArray();
                  j.WriteValue(KremlinAst.ESequence);
                  j.WriteStartArray();
                  WriteEUnit();
                }
              }
              if (m.IsTailRecursive) {
                // Note that Dafny conservatively flags functions as possibly-tail-recursive.  This does not acutally
                // indicate the function is tail recursive, or even recursive.
                j.WriteComment("WARNING: IsTailRecursive not supported but the method may not recurse"); // bugbug: implement
              }
              Contract.Assert(enclosingMethod == null);
              enclosingMethod = m;
              TrStmtList(m.Body.Body);
              Contract.Assert(enclosingMethod == m);
              enclosingMethod = null;
              if (!(m is Constructor)) {
                WriteEPopFrame();
              }
              if (m.Outs.Count != 0) {
                var ReturnValue = m.Outs[0];
                WriteEBound(ReturnValue);
              }
              Outs.Reverse();
              foreach (var l in Outs) {
                VarTracker.Pop(l);
                j.WriteEndArray(); // Closing out the expr list in the ESequence
                j.WriteEndArray(); // Closing out the array aboce ESequence
                j.WriteEndArray(); // Closing out the list of binder * expr * expr
                j.WriteEndArray(); // Closing out the array above ELet
              }
            }
          }
        }
      }
    }


    void TrCasePatternOpt(CasePattern pat, Expression rhs, string rhs_string, bool inLetExprBody) {
      Contract.Requires(pat != null);
      Contract.Requires(pat.Var != null || rhs != null);
      WriteEAbort("BUGBUG TrCasePatternOpt");
      // bugbug: implement
    }

    void ReturnExpr(Expression expr, bool inLetExprBody) {
      WriteToken(expr.tok);
      TrExpr(expr, inLetExprBody);
    }

    void WriteEAbort(string msg) {
      using (WriteArray()) {
        j.WriteComment(msg);
        j.WriteValue(KremlinAst.EAbort);
      }
    }

    void WriteEUnit() {
      using (WriteArray()) {
        j.WriteValue(KremlinAst.EUnit);
     }
    }

    void WriteTUnit() {
      using (WriteArray()) {
        j.WriteValue(KremlinAst.TUnit);
     }
    }

    void WriteEPushFrame() {
      using (WriteArray()) {
        j.WriteValue(KremlinAst.EPushFrame);
      }
    }

    void WriteEPopFrame() {
      using (WriteArray()) {
        j.WriteValue(KremlinAst.EPopFrame);
      }
    }

    void WriteEBound(IVariable var) {
      Formatting old = j.Formatting;
      j.Formatting = Formatting.None;
      using (WriteArray()) { // expr
        j.WriteValue(KremlinAst.EBound);
        j.WriteComment(var.Name);
        j.WriteValue(VarTracker.GetIndex(var));
      }
      j.Formatting = old;
    }

    // Emit explicit StdCall, to match Spartan's expectations.
    void WriteDefaultCallingConvention() {
      using (WriteArray()) {
        j.WriteValue(KremlinAst.StdCall);
      }
    }

    void TrExprOpt(Expression expr, bool inLetExprBody) {
      Contract.Requires(expr != null);
      Contract.Requires(j != null);
      if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          for (int i = 0; i < e.LHSs.Count; i++) {
            var lhs = e.LHSs[i];
            if (Contract.Exists(lhs.Vars, bv => !bv.IsGhost)) {
              TrCasePatternOpt(lhs, e.RHSs[i], null, inLetExprBody);
            }            
          }
          TrExprOpt(e.Body, inLetExprBody);
        } else {
          // We haven't optimized the other cases, so fallback to normal compilation
          ReturnExpr(e, inLetExprBody);
        }
      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        using (WriteArray()) { // Start of EIfThenElse
          j.WriteValue(KremlinAst.EIfThenElse); // of (expr * expr * expr)
          using (WriteArray()) {
            TrExpr(e.Test, inLetExprBody);
            TrExprOpt(e.Thn, inLetExprBody);
            TrExprOpt(e.Els, inLetExprBody);
          }
        }
      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        using (WriteArray()) {
          j.WriteValue(KremlinAst.EMatch); // of (expr * branches)
          TrExpr(e.Source, inLetExprBody);
          using (WriteArray()) { // start of branches
            if (e.Cases.Count == 0) {
              // the verifier would have proved we never get here; still, we need some code that will compile
              using (WriteArray()) {
                j.WriteValue(KremlinAst.PUnit);
                WriteEAbort("MatchExpr with no cases"); // bugbug: Dafny emits code to throw a C# exception here
              }
            }
            else {
              int i = 0;
              var sourceType = (UserDefinedType)e.Source.Type.NormalizeExpand();
              foreach (MatchCaseExpr mc in e.Cases) {
                MatchCasePrelude(sourceType, cce.NonNull(mc.Ctor), mc.Arguments, i, e.Cases.Count);
                TrExprOpt(mc.Body, inLetExprBody);
                i++;
              }
            }
          }
        }
      }  else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        TrExprOpt(e.E, inLetExprBody);
      } else {
        // We haven't optimized any other cases, so fallback to normal compilation
        ReturnExpr(expr, inLetExprBody);
      }
    }

    void CompileReturnBody(Expression body) {
      Contract.Requires(body != null);
      body = body.Resolved;
      TrExprOpt(body, false);
    }

    // ----- Type ---------------------------------------------------------------------------------

    NativeType AsNativeType(Type typ) {
      Contract.Requires(typ != null);
      if (typ.AsNewtype != null) {
        return typ.AsNewtype.NativeType;
      }
      else if (typ.IsBitVectorType) {
        return ((BitvectorType)typ).NativeType;
      }
      return null;
    }

    void WriteTypeNames(List<Type/*!*/>/*!*/ types) {
      Contract.Requires(cce.NonNullElements(types));
      Contract.Ensures(Contract.Result<string>() != null);
      foreach (var t in types) {
        WriteTypeName(t);
      }
    }

    void WriteTypeName_Companion(Type type) {
      Contract.Requires(type != null);
      var udt = type as UserDefinedType;
      if (udt != null && udt.ResolvedClass is TraitDecl) {
        j.WriteValue(udt.FullCompanionCompileName);
        if (udt.TypeArgs.Count != 0) {
          if (udt.TypeArgs.Exists(argType => argType is ObjectType)) {
            Error("compilation does not support type 'object' as a type parameter; consider introducing a ghost");
          }
          WriteTypeNames(udt.TypeArgs);
        }
      }
      else {
        WriteTypeName(type);
      }
    }

    // KRemlin extraction does not support some types.  Where possible, references to them are
    // skipped, rather than emitting Kremlin JSON for C extraction that will not execute.
    bool IsUnsupportedType(Type type) {
      var xType = type.NormalizeExpand();
      if (xType is IntType ||
        xType is RealType ||
        xType is BitvectorType ||
        xType is ObjectType ||
        xType is SetType ||
        xType is SeqType ||
        xType is MultiSetType ||
        xType is MapType) {
        return true;
      }
      return false;
    }

    void WriteTypeName(Type type) {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<string>() != null);

      Formatting old = j.Formatting;
      j.Formatting = Formatting.None;

      using (WriteArray()) {
        var xType = type.NormalizeExpand();
        if (xType is TypeProxy) {
          // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
          j.WriteValue(KremlinAst.TUnit);
        }
        else if (xType is BoolType) {
          j.WriteValue(KremlinAst.TBool);
        }
        else if (xType is CharType) {
          // bugbug: is this the right way to express a Dafny char?
          j.WriteValue(KremlinAst.TInt);
          using (WriteArray()) {
            j.WriteValue(KremlinAst.Int8);
          }
        }
        else if (xType is IntType) {
          var it = (IntType)xType;
          // bugbug: A Dafny IntType is an infinite-precision integer.  Add 
          //         runtime support for them as needed.
          j.WriteValue(KremlinAst.TQualified);
          using (WriteArray()) {
            using (WriteArray()) {
              j.WriteValue("Dafny");
            }
            j.WriteValue("BigInt");
          }
        }
        else if (xType is RealType) {
          j.WriteComment("BUGBUG Dafny RealType is unsupported");  // bugbug: implement
        }
        else if (xType is BitvectorType) {
          j.WriteComment("BUGBUG Dafny BitvectorType is unsupported");  // bugbug: implement
        }
        else if (xType.AsNewtype != null) {
          NativeType nativeType = xType.AsNewtype.NativeType;
          if (nativeType != null) {
            j.WriteValue(KremlinAst.TInt);
            using (WriteArray()) {
              j.WriteValue(nativeType.KremlinType());
            }
          }
          else {
            WriteTypeName(xType.AsNewtype.BaseType);
          }
        }
        else if (xType is ObjectType) {
          j.WriteComment("BUGBUG Dafny ObjectType is unsupported"); // bugbug: implement
        }
        else if (xType.IsArrayType) {
          ArrayClassDecl at = xType.AsArrayType;
          Contract.Assert(at != null);  // follows from type.IsArrayType
          Type elType = UserDefinedType.ArrayElementType(xType);
          j.WriteValue(KremlinAst.TBuf);
          WriteTypeName(elType);
          // bugbug: at.Dims is currently ignored
        }
        else if (xType is UserDefinedType) {
          var udt = (UserDefinedType)xType;
          var s = udt.FullName;
          var rc = udt.ResolvedClass;
          if (DafnyOptions.O.IronDafny &&
              !(xType is ArrowType) &&
              rc != null &&
              rc.Module != null &&
              !rc.Module.IsDefaultModule) {
            while (rc.ClonedFrom != null || rc.ExclusiveRefinement != null) {
              if (rc.ClonedFrom != null) {
                rc = (TopLevelDecl)rc.ClonedFrom;
              }
              else {
                Contract.Assert(rc.ExclusiveRefinement != null);
                rc = rc.ExclusiveRefinement;
              }
            }
            s = rc.FullName;
          }
          WriteTypeName_UDT(s, udt.TypeArgs);
        }
        else if (xType is SetType) {
          Type argType = ((SetType)xType).Arg;
          if (argType is ObjectType) {
            Error("compilation of set<object> is not supported; consider introducing a ghost", j);
          }
          j.WriteComment("BUGBUG SetType is unsupported"); // bugbug: implement
        }
        else if (xType is SeqType) {
          Type argType = ((SeqType)xType).Arg;
          if (argType is ObjectType) {
            Error("compilation of seq<object> is not supported; consider introducing a ghost", j);
          }
          j.WriteValue(KremlinAst.TBuf);
          WriteTypeName(argType);
        }
        else if (xType is MultiSetType) {
          Type argType = ((MultiSetType)xType).Arg;
          if (argType is ObjectType) {
            Error("compilation of seq<object> is not supported; consider introducing a ghost", j);
          }
          j.WriteComment("BUGBUG MultiSetType is unsupported"); // bugbug: implement
        }
        else if (xType is MapType) {
          Type domType = ((MapType)xType).Domain;
          Type ranType = ((MapType)xType).Range;
          if (domType is ObjectType || ranType is ObjectType) {
            Error("compilation of map<object, _> or map<_, object> is not supported; consider introducing a ghost", j);
          }
          j.WriteComment("BUGBUG MapType is unsupported"); // bugbug: implement
        }
        else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
        }
      }
      j.Formatting = old;
    }

    void WriteTypeWidth(Type type) {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<string>() != null);

      Formatting old = j.Formatting;
      j.Formatting = Formatting.None;

      using (WriteArray()) {
        var xType = type.NormalizeExpand();
        if (xType is TypeProxy) {
          j.WriteComment("BUGBUG Width of TypeProxy not supported");  // bugbug: implement
          j.WriteValue("0");
        }
        else if (xType is BoolType) {
          j.WriteValue(KremlinAst.Bool);
        }
        else if (xType is CharType) {
          // bugbug: is this the right way to express a Dafny char?
          j.WriteValue(KremlinAst.Int8);
        }
        else if (xType is IntType) {
          var it = (IntType)xType;
          j.WriteComment("BUGBUG Dafny IntType is unsupported");  // bugbug: implement
        }
        else if (xType is RealType) {
          j.WriteComment("BUGBUG Dafny RealType is unsupported");  // bugbug: implement
        }
        else if (xType.AsNewtype != null) {
          NativeType nativeType = xType.AsNewtype.NativeType;
          if (nativeType != null) {
            j.WriteValue(nativeType.KremlinType());
          }
          else {
            WriteTypeWidth(xType.AsNewtype.BaseType);
          }
        }
        else if (xType is ObjectType) {
          j.WriteComment("BUGBUG Dafny ObjectType is unsupported"); // bugbug: implement
        }
        else if (xType.IsArrayType) {
          j.WriteComment("BUGBUG Dafny IsArrayType is unsupported"); // bugbug: implement
        }
        else if (xType is UserDefinedType) {
          j.WriteComment("BUGBUG Dafny UserDefinedType is unsupported"); // bugbug: implement
        }
        else if (xType is SetType) {
          Type argType = ((SetType)xType).Arg;
          if (argType is ObjectType) {
            Error("compilation of set<object> is not supported; consider introducing a ghost", j);
          }
          j.WriteComment("BUGBUG SetType is unsupported"); // bugbug: implement
        }
        else if (xType is SeqType) {
          Type argType = ((SeqType)xType).Arg;
          if (argType is ObjectType) {
            Error("compilation of seq<object> is not supported; consider introducing a ghost", j);
          }
          WriteTypeName(((SeqType)xType).Arg);
        }
        else if (xType is MultiSetType) {
          Type argType = ((MultiSetType)xType).Arg;
          if (argType is ObjectType) {
            Error("compilation of seq<object> is not supported; consider introducing a ghost", j);
          }
          j.WriteComment("BUGBUG MultiSetType is unsupported"); // bugbug: implement
        }
        else if (xType is MapType) {
          Type domType = ((MapType)xType).Domain;
          Type ranType = ((MapType)xType).Range;
          if (domType is ObjectType || ranType is ObjectType) {
            Error("compilation of map<object, _> or map<_, object> is not supported; consider introducing a ghost", j);
          }
          j.WriteComment("BUGBUG MapType is unsupported"); // bugbug: implement
        }
        else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
        }
      }
      j.Formatting = old;
    }


    // This is the inside of a typ, as the caller has already generated the opening '[' and will generate the closing '] afterwards
    void WriteTypeName_UDT(string fullName, List<Type> typeArgs) {
      Contract.Requires(fullName != null);
      Contract.Requires(typeArgs != null);

      j.WriteValue(KremlinAst.TBuf);
      using (WriteArray()) {
        j.WriteValue(KremlinAst.TQualified);
        if (typeArgs.Count != 0) {
          if (typeArgs.Exists(argType => argType is ObjectType)) {
            Error("compilation does not support type 'object' as a type parameter; consider introducing a ghost");
          }
          j.WriteComment("BUGBUG Template types not supported in UDTs"); // bugbug: implement
        }
        WriteLident(fullName);
      }
    }

    // Write out a default value as an expr
    void WriteDefaultValue(Type type) {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var xType = type.NormalizeExpand();
      if (xType is TypeProxy) {
        // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
        WriteEUnit();
      }

      if (xType is BoolType) {
        var old = j.Formatting;
        j.Formatting = Formatting.None;
        using (WriteArray()) {
          j.WriteValue(KremlinAst.EConstant);
          using (WriteArray()) {
            j.WriteValue(KremlinAst.TBool);
            j.WriteValue(false);
          }
        }
        j.Formatting = old;
      }
      else if (xType is CharType) {
        var old = j.Formatting;
        j.Formatting = Formatting.None;
        using (WriteArray()) {
          j.WriteValue(KremlinAst.EConstant);
          using (WriteArray()) {
            j.WriteValue(KremlinAst.TInt);
            j.WriteValue((int)'D');
          }
        }
        j.Formatting = old;
      }
      else if (xType is IntType) {
        var it = (IntType)xType;
        WriteEAbort("BUGBUG Dafny IntType is unsupported");  // bugbug: implement
      }
      else if (xType is RealType) {
        WriteEAbort("BUGBUG Dafny RealType is unsupported");  // bugbug: implement
      }
      else if (xType is BitvectorType) {
        WriteEAbort("BUGBUG Dafny BitvectorType is unsupported");  // bugbug: implement
      }
      else if (xType.AsNewtype != null) {
        if (xType.AsNewtype.NativeType != null) {
          var nativeType = xType.AsNewtype.NativeType;
          var old = j.Formatting;
          j.Formatting = Formatting.None;
          using (WriteArray()) {
            j.WriteValue(KremlinAst.EConstant);
            using (WriteArray()) { // of K.t
              using (WriteArray()) {
                j.WriteValue(nativeType.KremlinType());
              }
              j.WriteValue("0");
            }
          }
          j.Formatting = old;
        }
        else {
          WriteDefaultValue(xType.AsNewtype.BaseType);
        }
      }
      else if (xType.IsArrayType) {
        ArrayClassDecl at = xType.AsArrayType;
        Contract.Assert(at != null);  // follows from type.IsArrayType
        using (WriteArray()) {
          j.WriteValue(KremlinAst.EAny);
        }
      }
      else if (xType.IsRefType) {
        using (WriteArray()) {
          j.WriteValue(KremlinAst.EAny);
        }
      }
      else if (xType.IsDatatype) {
        var udt = (UserDefinedType)xType;
        var s = udt.FullName;
        var rc = udt.ResolvedClass;
        if (DafnyOptions.O.IronDafny &&
            !(xType is ArrowType) &&
            rc != null &&
            rc.Module != null &&
            !rc.Module.IsDefaultModule) {
          while (rc.ClonedFrom != null || rc.ExclusiveRefinement != null) {
            if (rc.ClonedFrom != null) {
              rc = (TopLevelDecl)rc.ClonedFrom;
            }
            else {
              Contract.Assert(rc.ExclusiveRefinement != null);
              rc = rc.ExclusiveRefinement;
            }
          }
          s = rc.FullName;
        }
        using (WriteArray()) {
          if (udt.TypeArgs.Count != 0) {
            WriteEAbort("Udt with TypeArgs is not supported"); // bugbug: implement
          }
          else {
            IndDatatypeDecl dcl = rc as IndDatatypeDecl;
            j.WriteValue(KremlinAst.EBufCreateL);
            using (WriteArray()) { // of (lifetime * expr list)
              using (WriteArray()) {
                j.WriteValue(KremlinAst.Stack);
              }
              using (WriteArray()) {
                using (WriteArray()) {
                  j.WriteValue(KremlinAst.EFlat);
                  using (WriteArray()) { // (typ * list of (ident * expr))
                    WriteTypeOfLident(udt);
                    using (WriteArray()) {
                      int i = 0;
                      foreach (var arg in dcl.DefaultCtor.Formals) {
                        if (arg.IsGhost) {
                          continue;
                        }
                        using (WriteArray()) {
                          j.WriteValue(FormalName(arg, i)); // ident
                          WriteDefaultValue(arg.Type);      // expr
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      else if (xType.IsTypeParameter) {
        WriteEAbort("BUGBUG Dafny TypeParameter is unsupported");  // bugbug: implement
      }
      else if (xType is SetType) {
        WriteEAbort("BUGBUG Dafny SetType is unsupported");  // bugbug: implement
      }
      else if (xType is MultiSetType) {
        WriteEAbort("BUGBUG Dafny MultiSetType is unsupported");  // bugbug: implement
      }
      else if (xType is SeqType) {
        Type argType = ((SeqType)xType).Arg;
        using (WriteArray()) {
          j.WriteValue(KremlinAst.EAny);
        }
      }
      else if (xType is MapType) {
        WriteEAbort("BUGBUG Dafny MapType is unsupported");  // bugbug: implement
      }
      else if (xType is ArrowType) {
        WriteEAbort("BUGBUG Dafny ArrowType is unsupported");  // bugbug: implement
      }
      else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    // ----- Stmt ---------------------------------------------------------------------------------

    public class CheckHasNoAssumes_Visitor : BottomUpVisitor
    {
      readonly KremlinCompiler compiler;
      TextWriter wr;
      public CheckHasNoAssumes_Visitor(KremlinCompiler c, TextWriter wr) {
        Contract.Requires(c != null);
        compiler = c;
        this.wr = wr;
      }
      protected override void VisitOneStmt(Statement stmt) {
        if (stmt is AssumeStmt) {
          compiler.Error("an assume statement cannot be compiled (line {0})", wr, stmt.Tok.line);
        } else if (stmt is AssignSuchThatStmt) {
          var s = (AssignSuchThatStmt)stmt;
          if (s.AssumeToken != null) {
            compiler.Error("an assume statement cannot be compiled (line {0})", wr, s.AssumeToken.line);
          }
        } else if (stmt is ForallStmt) {
          var s = (ForallStmt)stmt;
          if (s.Body == null) {
            compiler.Error("a forall statement without a body cannot be compiled (line {0})", wr, stmt.Tok.line);
          }
        } else if (stmt is WhileStmt) {
          var s = (WhileStmt)stmt;
          if (s.Body == null) {
            compiler.Error("a while statement without a body cannot be compiled (line {0})", wr, stmt.Tok.line);
          }
        }
      }
    }

    public class CheckHasNoAssumes_VisitorJ : BottomUpVisitor
    {
      readonly KremlinCompiler compiler;
      JsonTextWriter j;
      public CheckHasNoAssumes_VisitorJ(KremlinCompiler c, JsonTextWriter j) {
        Contract.Requires(c != null);
        compiler = c;
        this.j = j;
      }
      protected override void VisitOneStmt(Statement stmt) {
        if (stmt is AssumeStmt) {
          compiler.Error("an assume statement cannot be compiled (line {0})", j, stmt.Tok.line);
        }
        else if (stmt is AssignSuchThatStmt) {
          var s = (AssignSuchThatStmt)stmt;
          if (s.AssumeToken != null) {
            compiler.Error("an assume statement cannot be compiled (line {0})", j, s.AssumeToken.line);
          }
        }
        else if (stmt is ForallStmt) {
          var s = (ForallStmt)stmt;
          if (s.Body == null) {
            compiler.Error("a forall statement without a body cannot be compiled (line {0})", j, stmt.Tok.line);
          }
        }
        else if (stmt is WhileStmt) {
          var s = (WhileStmt)stmt;
          if (s.Body == null) {
            compiler.Error("a while statement without a body cannot be compiled (line {0})", j, stmt.Tok.line);
          }
        }
      }
    }

    void TrStmt(Statement stmt) {
      Contract.Requires(stmt != null);
      TextWriter wr = new StringWriter();
      if (stmt.IsGhost) {
        var v = new CheckHasNoAssumes_Visitor(this, wr);
        v.Visit(stmt);
        return;
      }
      if (stmt is PrintStmt) {
        WriteToken(stmt.Tok);
        PrintStmt s = (PrintStmt)stmt;
        using (WriteArray()) {
          j.WriteValue(KremlinAst.EApp);
          j.WriteValue("IO.debug_print_string"); // bugbug: is this the correct way to form the function name?
          using (WriteArray()) {
            foreach (var arg in s.Args) {
              TrExpr(arg, false); // bugbug: each argument needs to be converted to a string and concatenated
            }
          }
        }
      }
      else if (stmt is BreakStmt) {
        WriteToken(stmt.Tok);
        var s = (BreakStmt)stmt;
        WriteEAbort("BUGBUG BreakStmt is unsupported"); // bugbug: implement
      }
      else if (stmt is ProduceStmt) {
        WriteToken(stmt.Tok);
        var s = (ProduceStmt)stmt;
        if (s is YieldStmt) {
          WriteEAbort("BUGBUG ProduceStmt Yield unsupported"); // bugbug: implement.
        }
        else {
          using (WriteArray()) {
            j.WriteValue(KremlinAst.EReturn);
            // Dafny C# generates "return;" because methods are void.  But
            // for Kremlin, if there is one [out] parameter it is translated
            // as a single return value.
            if (enclosingMethod.Outs.Count == 0) {
              WriteEUnit(); // No return value
            }
            else {
              var ReturnValue = enclosingMethod.Outs[0];
              WriteEBound(ReturnValue);
            }
          }
        }
      }
      else if (stmt is UpdateStmt) {
        WriteToken(stmt.Tok);
        var s = (UpdateStmt)stmt;
        var resolved = s.ResolvedStatements;
        if (resolved.Count == 1) {
          TrStmt(resolved[0]);
        }
        else {
          Contract.Assert(s.Lhss.Count == resolved.Count);
          Contract.Assert(s.Rhss.Count == resolved.Count);

          // For each LHSS/RHSS pair, generate:
          //  tmpN = rhsN
          //  ...
          //  lhssN = tmpN
          // so side effects to the LHSS's don't take place until after all 
          // RHSS's have been evaluated.  The complication is that the LHSS
          // may be an EBufWrite to an array element, or an EAssign to
          // a variable.
          // In Kremlin, this is:
          //  let tmp0 = rhs0 in
          //   let tmp1 = rhs1 in
          //    ... in
          //    { assign lhss0 = tmp0;
          //      assign lhss1 = tmp1;
          //      ...
          //    }

          var rhss = new List<IVariable>();
          for (int i = 0; i < resolved.Count; i++) {
            if (!resolved[i].IsGhost) {
              var lhs = s.Lhss[i];
              var rhs = s.Rhss[i];
              if (!(rhs is HavocRhs)) {
                var target = new BoundVar(resolved[i].Tok, idGenerator.FreshId("_rhs"), lhs.Type);
                rhss.Add(target);

                // ELet v in { Stmt 
                j.WriteStartArray();
                j.WriteValue(KremlinAst.ELet);
                j.WriteStartArray();
                WriteBinder(target, target.Name, true); // lident
                TrRhs(target, null, rhs); // expr
                VarTracker.Push(target);
                // "in" is the contents that follow
              }
            }
          }
          using (WriteArray()) {
            j.WriteValue(KremlinAst.ESequence);
            using (WriteArray()) {
              for (int i = 0; i < rhss.Count; i++) {
                TrAssign(s.Lhss[i], rhss[i]);
              }
            }
          }
          rhss.Reverse();
          foreach (var l in rhss) {
            VarTracker.Pop(l);
            j.WriteEndArray(); // Closing out the list of binder * expr * expr
            j.WriteEndArray(); // Closing out the array above ELet
          }
        }
      }
      else if (stmt is AssignStmt) {
        WriteToken(stmt.Tok);
        AssignStmt s = (AssignStmt)stmt;
        Contract.Assert(!(s.Lhs is SeqSelectExpr) || ((SeqSelectExpr)s.Lhs).SelectOne);  // multi-element array assignments are not allowed
        TrRhs(null, s.Lhs, s.Rhs);
      }
      else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        if (s.AssumeToken != null) {
          // Note, a non-ghost AssignSuchThatStmt may contain an assume
          Error("an assume statement cannot be compiled (line {0})", wr, s.AssumeToken.line);
        }
        else if (s.MissingBounds != null) {
          foreach (var bv in s.MissingBounds) {
            Error("this assign-such-that statement is too advanced for the current compiler; Dafny's heuristics cannot find any bound for variable '{0}' (line {1})", wr, bv.Name, s.Tok.line);
          }
        }
        else {
          Contract.Assert(s.Bounds != null);  // follows from s.MissingBounds == null
          WriteToken(stmt.Tok);
          TrAssignSuchThat(
            s.Lhss.ConvertAll(lhs => ((IdentifierExpr)lhs.Resolved).Var),  // the resolver allows only IdentifierExpr left-hand sides
            s.Expr, s.Bounds, s.Tok.line, false);
        }

      }
      else if (stmt is CallStmt) {
        WriteToken(stmt.Tok);
        CallStmt s = (CallStmt)stmt;
        TrCallStmt(s);

      }
      else if (stmt is BlockStmt) {
        WriteToken(stmt.Tok);
        using (WriteArray()) {
          j.WriteValue(KremlinAst.ESequence);
          using (WriteArray()) {
            WriteEUnit(); // in case the statement list is empty
            TrStmtList(((BlockStmt)stmt).Body);
          }
        }
      }
      else if (stmt is IfStmt) {
        WriteToken(stmt.Tok);
        IfStmt s = (IfStmt)stmt;
        if (s.Guard == null) {
          // we can compile the branch of our choice
          if (s.Els == null) {
            // let's compile the "else" branch, since that involves no work
            // (still, let's leave a marker in the source code to indicate that this is what we did)
            j.WriteComment("if (!false) { }");
          }
          else {
            // let's compile the "then" branch
            j.WriteComment("if (true)");
            TrStmt(s.Thn);
          }
        }
        else {
          using (WriteArray()) {
            j.WriteValue(KremlinAst.EIfThenElse);
            using (WriteArray()) {
              TrExpr(s.IsExistentialGuard ? Translator.AlphaRename((ExistsExpr)s.Guard, "eg_d", new Translator(null)) : s.Guard, false);

              // We'd like to do "TrStmt(s.Thn, indent)", except we want the scope of any existential variables to come inside the block
              using (WriteArray()) {
                j.WriteValue(KremlinAst.ESequence);
                using (WriteArray()) {
                  WriteEUnit(); // in case the statement list is empty
                  if (s.IsExistentialGuard) {
                    IntroduceAndAssignBoundVars((ExistsExpr)s.Guard);
                  }
                  TrStmtList(s.Thn.Body);
                }
              }

              using (WriteArray()) {
                j.WriteValue(KremlinAst.ESequence);
                using (WriteArray()) {
                  WriteEUnit(); // in case the statement list is empty
                  if (s.Els != null) {
                    TrStmt(s.Els);
                  }
                }
              }
            }
          }
        }

      }
      else if (stmt is AlternativeStmt) {
        WriteToken(stmt.Tok);
        var s = (AlternativeStmt)stmt;
        WriteEAbort("BUGBUG AlternativeStmt is unsupported"); // bugbug: a cascade of if/else if/else.
      }
      else if (stmt is WhileStmt) {
        WhileStmt s = (WhileStmt)stmt;
        if (s.Body == null) {
          return;
        }
        WriteToken(stmt.Tok);
        if (s.Guard == null) {
          j.WriteComment("while (false) { }");
          WriteEUnit();
        }
        else {
          using (WriteArray()) {
            j.WriteValue(KremlinAst.EWhile);
            using (WriteArray()) {  // of (expr * expr)
              TrExpr(s.Guard, false);
              TrStmt(s.Body);
            }
          }
        }

      }
      else if (stmt is AlternativeLoopStmt) {
        WriteToken(stmt.Tok);
        var s = (AlternativeLoopStmt)stmt;
        WriteEAbort("BUGBUG AlternativeLoopStmt is unsupported"); // bugbug: implement
      }
      else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        if (s.Kind != ForallStmt.ParBodyKind.Assign) {
          // Call and Proof have no side effects, so they can simply be optimized away.
          return;
        }
        else if (s.BoundVars.Count == 0) {
          // the bound variables just spell out a single point, so the forall statement is equivalent to one execution of the body
          WriteToken(stmt.Tok);
          TrStmt(s.Body);
          return;
        }
        var s0 = (AssignStmt)s.S0;
        if (s0.Rhs is HavocRhs) {
          // The forall statement says to havoc a bunch of things.  This can be efficiently compiled
          // into doing nothing.
          return;
        }
        WriteToken(stmt.Tok);
        var rhs = ((ExprRhs)s0.Rhs).Expr;
        WriteEAbort("BUGBUG Forall is unsupported"); // bugbug: implement

      }
      else if (stmt is MatchStmt) {
        WriteToken(stmt.Tok);
        MatchStmt s = (MatchStmt)stmt;
        WriteEAbort("BUGBUG MatchStmt is unsupported"); // bugbug: implement
      }
      else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        foreach (var local in s.Locals) {
          if (!local.IsGhost) {
            // Note that a new local was introduced, and assume the caller
            // will inject an ELet in the correct order, to match the
            // VarTracker state.
            varDeclsList.Add(local);
            VarTracker.Push(local);
          }
        }
        if (s.Update != null) {
          TrStmt(s.Update);
        }
      }
      else if (stmt is LetStmt) {
        WriteToken(stmt.Tok);
        var s = (LetStmt)stmt;
        for (int i = 0; i < s.LHSs.Count; i++) {
          var lhs = s.LHSs[i];
          if (Contract.Exists(lhs.Vars, bv => !bv.IsGhost)) {
            TrCasePatternOpt(lhs, s.RHSs[i], null, false);
          }
        }
      }
      else if (stmt is ModifyStmt) {
        WriteToken(stmt.Tok);
        var s = (ModifyStmt)stmt;
        if (s.Body != null) {
          TrStmt(s.Body);
        }

      }
      else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }
    }

    private void IntroduceAndAssignBoundVars(ExistsExpr exists) {
      Contract.Requires(exists != null);
      Contract.Assume(exists.Bounds != null);  // follows from successful resolution
      Contract.Assert(exists.Range == null);  // follows from invariant of class IfStmt
      foreach (var bv in exists.BoundVars) {
        TrLocalVar(bv, false);
      }
      var ivars = exists.BoundVars.ConvertAll(bv => (IVariable)bv);
      TrAssignSuchThat(ivars, exists.Term, exists.Bounds, exists.tok.line, false);
    }

    private void TrAssignSuchThat(List<IVariable> lhss, Expression constraint, List<ComprehensionExpr.BoundedPool> bounds, int debuginfoLine, bool inLetExprBody) {
      Contract.Requires(lhss != null);
      Contract.Requires(constraint != null);
      Contract.Requires(bounds != null);
      WriteEAbort("TrAssignSuchThat is unsupported"); // bugbug: implement
    }

    // The EBufRead/EBufWrite index expression must be a UInt32 type.  Dafny
    // uses BigInteger, which often resolves to UInt64.  So explicitly cast
    // buffer offsets to UInt32
    private void TrBufferIndexSizeExpr(Expression expr, bool isInLetExprBody) {
      using (WriteArray()) {
        j.WriteValue(KremlinAst.ECast);
        using (WriteArray()) { // of (expr * typ) - cast to UInt32
          TrExpr(expr, isInLetExprBody);
          using (WriteArray()) {
            j.WriteValue(KremlinAst.TInt);
            using (WriteArray()) {
              j.WriteValue(KremlinAst.UInt32);
            }
          }
        }
      }
    }

    void MatchCasePrelude(UserDefinedType sourceType, DatatypeCtor ctor, List<BoundVar/*!*/>/*!*/ arguments, int caseIndex, int caseCount) {
      Contract.Requires(sourceType != null);
      Contract.Requires(ctor != null);
      Contract.Requires(cce.NonNullElements(arguments));

      // bugbug: implement
      WriteEAbort("MatchCasePrelude");
    }

    // Invoked typically as TrRhs(variable, null, RhsExpr)   <- UpdateStmt with multi-assignment
    //                   or TrRhs(null, LhsExpr, RhsExpr)    <- AssignStmt
    void TrRhs(BoundVar target, Expression targetExpr, AssignmentRhs rhs) {
      Contract.Requires((target == null) != (targetExpr == null));
      var tRhs = rhs as TypeRhs;
      if (rhs is HavocRhs) {
        // do nothing
      }
      else {
        using (WriteArray()) {
          j.WriteValue(KremlinAst.ESequence);
          using (WriteArray()) {
            WriteEUnit();

            // For C#, Dafny calls TrExpr(targetExpr), emits "=" then TrAssignmentRhs(rhs),
            // For Kremlin, we may generate EAssign or EBufWrite depending on the 
            // targetExpr type.  The ELet has already been generated by the caller and
            // we are inside an ESequence, about to generate the RHS expression code.
            if (target != null) {
              TrAssignmentRhs(rhs);
            }
            else {
              if (targetExpr is SeqSelectExpr) {
                SeqSelectExpr e = (SeqSelectExpr)targetExpr;
                Contract.Assert(e.Seq.Type != null);
                if (!e.SelectOne) {
                  WriteEAbort("BUGBUG: TrRhs is a SeqSelectExpr with SelectMany"); // bugbug: is this valid Dafny?
                }
                else {
                  using (WriteArray()) {
                    j.WriteValue(KremlinAst.EBufWrite);
                    using (WriteArray()) { // of (expr * expr * expr)
                      TrExpr(e.Seq, false);    // expr1 - the buffer identifier
                      TrBufferIndexSizeExpr(e.E0, false); // expr2 - the buffer offset
                      TrAssignmentRhs(rhs);    // expr3 - the value to write
                    }
                  }
                }
              }
              else if (targetExpr is IdentifierExpr) {
                using (WriteArray()) {
                  j.WriteValue(KremlinAst.EAssign);
                  using (WriteArray()) {
                    var e = (IdentifierExpr)targetExpr;
                    WriteEBound(e.Var);
                    TrAssignmentRhs(rhs);
                  }
                }
              }
              else if (targetExpr is MemberSelectExpr) {
                MemberSelectExpr e = (MemberSelectExpr)targetExpr;
                SpecialField sf = e.Member as SpecialField;
                if (sf != null) {
                  WriteEAbort("BUGBUG MemberSelectExpr TrRhs if SpecialField not supported"); // bugbug: implement
                }
                else {
                  // EAssign of
                  //   EField(lident, EBufRead( EBound(var), 0), FieldName)
                  using (WriteArray()) {
                    j.WriteValue(KremlinAst.EAssign);
                    using (WriteArray()) { // of (expr * expr)

                      // EAssign expr1
                      using (WriteArray()) {
                        j.WriteValue(KremlinAst.EField);
                        using (WriteArray()) { // of (typ * expr * ident)
                          WriteTypeOfLident(e.Obj.Type);
                          using (WriteArray()) {
                            j.WriteValue(KremlinAst.EBufRead);
                            using (WriteArray()) { // of (expr * expr)
                              TrExpr(e.Obj, false); // This will generate an EBound reference to the variable
                              WriteConstant(0u);    // expr2 is the offset (always 0)
                            }
                          }
                          j.WriteValue(e.Member.Name);
                        }
                      }
                      TrAssignmentRhs(rhs); // right-hand-side expression
                    }
                  }
                }
              }
              else {
                WriteEAbort("BUGBUG TrRhs of unsupported targetExpr type " + targetExpr.ToString());
              }
            }
            if (tRhs != null && tRhs.InitCall != null) {
              // We have now generated: var target = Default value;
              // Generate statement:    target.ctor();
              var oldEnclosingThis = enclosingThis;
              if (target != null) {
                j.WriteComment("TrRhs of InitCall to target");
                enclosingThis = target;
                TrCallStmt(tRhs.InitCall); // expr2
              }
              else {
                // targetExpr should be turned into the enclosingThis
                using (WriteArray()) {
                  string nw = idGenerator.FreshId("_nw");
                  enclosingThis = new BoundVar(targetExpr.tok, nw, targetExpr.Type);
                  j.WriteValue(KremlinAst.ELet);
                  using (WriteArray()) { // of (binder * expr * expr)
                    WriteBinder(enclosingThis, nw, true);
                    TrExpr(targetExpr, false);
                    VarTracker.Push(enclosingThis);
                    TrCallStmt(tRhs.InitCall);
                  }
                  VarTracker.Pop(enclosingThis);
                }
              }
              enclosingThis = oldEnclosingThis;
            }
          }
        }
      }
    }

    void TrCallStmt(CallStmt s) {
      Contract.Requires(s != null);
      Contract.Assert(s.Method != null);  // follows from the fact that stmt has been successfully resolved

      if (s.Method == enclosingMethod && enclosingMethod.IsTailRecursive) {
        // compile call as tail-recursive
        j.WriteComment("TrCallStmt tail-recursive calls not supported");
      }
      else {
        // compile call as a regular call
        Contract.Assert(s.Lhs.Count == s.Method.Outs.Count);

        int OutParam = -1;
        for (int i = 0; i < s.Method.Outs.Count; i++) {
          Formal p = s.Method.Outs[i];
          if (!p.IsGhost) {
            if (OutParam != -1) {
              j.WriteComment("Multiple out parameters are unsupported"); // bugbug: implement
            }
            else {
              OutParam = i;
            }
          }
        }

        if (OutParam != -1) {
          // easy - one ELet
          j.WriteStartArray();
          j.WriteValue(KremlinAst.EAssign); // of (expr * expr)
          j.WriteStartArray();
          TrExpr(s.Lhs[OutParam], false);
        }

        using (WriteArray()) {
          j.WriteValue(KremlinAst.EApp);
          using (WriteArray()) { // of (expr * expr list)
            // expr1: Function to call
            using (WriteArray()) {
              var old = j.Formatting;
              j.Formatting = Formatting.None;
              j.WriteValue(KremlinAst.EQualified); // of lident
              // s.Method.IsStatic() would generate a "TypeName.MethodName()" 
              // call in C#.  For Kremlin, the type name is already explicit,
              // so no work to do.
              //
              // For the non-static case, of s.Receiver, this would generate
              // a "receiver.MethodName()" call in C#.  For Kremlin, we pass
              // the receiver as the first argument.
              WriteLident(s.Method);
              j.Formatting = old;
            }
            // expr2: list of arguments
            using (WriteArray()) {
              if (!s.Method.IsStatic) {
                // Pass 'this' as the first argument
                TrExpr(s.Receiver, false);
              }
              for (int i = 0; i < s.Method.Ins.Count; i++) {
                Formal p = s.Method.Ins[i];
                if (!p.IsGhost) {
                  TrExpr(s.Args[i], false);
                }
              }
            }
          }
        }

        if (OutParam != -1) {
          // Complete the EAssign
          j.WriteEndArray();
          j.WriteEndArray();
        }
      }

    }

    /// <summary>
    /// Before calling TrAssignmentRhs(rhs), the caller must have spilled the let variables declared in "rhs".
    /// </summary>
    void TrAssignmentRhs(AssignmentRhs rhs) {
      Contract.Requires(rhs != null);
      Contract.Requires(!(rhs is HavocRhs));
      if (rhs is ExprRhs) {
        ExprRhs e = (ExprRhs)rhs;
        TrExpr(e.Expr, false);

      } else {

        TypeRhs tp = (TypeRhs)rhs;
        if (tp.ArrayDimensions == null) {
          if (tp.EType is UserDefinedType) {
            var udt = tp.EType as UserDefinedType;
            WriteClassAllocation(udt);
          }
          else {
            WriteDefaultValue(tp.EType);
          }
        }
        else {
          if (tp.EType.IsIntegerType || tp.EType.IsTypeParameter) {
            WriteEAbort("BUGBUG: TypeRhs with IntegerType or TypeParameter is unsupported"); // bugbug: implement
          }
          else if (tp.ArrayDimensions.Count == 1) {
            // Dafny: var W := new uint32[64];
            // C#:    new TypeName[ (int)ParenExpr, ... ];
            using (WriteArray()) {
              j.WriteValue(KremlinAst.EBufCreate);
              using (WriteArray()) { // of (lifetime * expr * expr)
                using (WriteArray()) {
                  j.WriteValue(KremlinAst.Stack);
                }
                WriteDefaultValue(tp.EType);
                TrBufferIndexSizeExpr(tp.ArrayDimensions[0], false);
              }
            }
          }
          else {
            WriteEAbort("BUGBUG: TypeRhs with multi-dimensional array is unsupported"); // bugbug: implement
          }
        }

      }
    }

    void TrStmtList(List<Statement/*!*/>/*!*/ stmts) {
      Contract.Requires(cce.NonNullElements(stmts));
      List<LocalVariable> AllDecls = new List<LocalVariable>();

      using (WriteArray()) {
        j.WriteValue(KremlinAst.ESequence);
        using (WriteArray()) {
          WriteEUnit(); // in case the statement list is empty
          foreach (Statement ss in stmts) {
            // JsonTextWriter is forward-only, but after calling TrStmt() we may need
            // to go back and inject new ELet statements to introduce temp variables.
            // So call TrStmt() once to generate code to a throw-away MemoryStream,
            // but remember what temps need to be introduced.  Then introduce them
            // and call TrStmt() once more, to generate the actual Json.
            JsonTextWriter oldj = j;
            VariableTracker oldtracker = VarTracker.Clone();

            StringBuilder sb = new StringBuilder();
            StringWriter sw = new StringWriter(sb);
            JsonTextWriter newj = new JsonTextWriter(sw);
            newj.Formatting = oldj.Formatting;
            newj.Indentation = oldj.Indentation;
            j = newj;

            var oldVarDeclsList = varDeclsList;
            varDeclsList = new List<LocalVariable>();

            TrStmt(ss);

            j = oldj;
            VarTracker = oldtracker;
            var decls = varDeclsList; // Grab the set of just-declared variables generated by the first TrStmt() pass
            varDeclsList = null;      // Switch modes for next TrStmt() pass
            AllDecls.AddRange(decls); // Accumulate the set of all variables this stmt list has generated
            foreach (var l in decls) {
              // ELet v in { Stmt 
              j.WriteStartArray();
              j.WriteValue(KremlinAst.ELet);
              j.WriteStartArray();
              WriteBinder(l, l.Name, true); // lident
              WriteDefaultValue(l.Type);    // = default
              VarTracker.Push(l);
              // "in" is the contents that follow
              j.WriteStartArray();
              j.WriteValue(KremlinAst.ESequence);
              j.WriteStartArray();
              WriteEUnit();
            }

            newj.Close();
            string RawJson = sb.ToString();
            if (RawJson != "") {
              j.WriteRaw(",");
              j.WriteWhitespace("\n");
              j.WriteRaw(RawJson); // Now paste the JSON 
            }

            if (ss.Labels != null) {
              // bugbug: these appear to be used to support "Break" statements.
              j.WriteComment("Labels are unsupported: " + ss.Labels.Data.AssignUniqueId("after_", idGenerator));
            }

            varDeclsList = oldVarDeclsList;
          }

          // Now that all statements in the list have been generated, close out the nested ELets generated above
          AllDecls.Reverse();
          foreach (var l in AllDecls) {
            VarTracker.Pop(l);
            j.WriteEndArray(); // Closing out the expr list in the ESequence
            j.WriteEndArray(); // Closing out the array aboce ESequence
            j.WriteEndArray(); // Closing out the list of binder * expr * expr
            j.WriteEndArray(); // Closing out the array above ELet
          }
        }
      }
    }

    void WriteBinder(IVariable v, string name, bool mutable) {
      Contract.Requires(v != null);
      Contract.Requires(v.IsGhost == false);

      using (WriteObject()) {
        j.WritePropertyName("name");
        j.WriteValue(name);
        j.WritePropertyName("typ");
        WriteTypeName(v.Type);
        j.WritePropertyName("mut");
        j.WriteValue(mutable);
      }
    }

    // Generate:
    //  "Let binder = expr in _;" where the expr initializes the variable to Dafny's default value.
    void TrLocalVar(IVariable v, bool alwaysInitialize) {
      Contract.Requires(v != null);
      if (v.IsGhost) {
        // only emit non-ghosts (we get here only for local variables introduced implicitly by call statements)
        return;
      }

      using (WriteArray()) {
        j.WriteValue(KremlinAst.ELet); // of (binder * expr * expr)  

        using (WriteArray()) {
          // Binder
          WriteBinder(v, v.Name, true);
          // expr1
          WriteDefaultValue(v.Type);
          VarTracker.Push(v);
          // expr2 - the "in" expression
          WriteEUnit();
        }
      }
    }


    // ----- Expression ---------------------------------------------------------------------------


    //["EConstant", [
    //["UInt32"], "value"
    //]],
    void WriteConstant(UInt32 value) {
      Formatting old = j.Formatting;
      j.Formatting = Formatting.None;
      using (WriteArray()) {
        j.WriteValue(KremlinAst.EConstant);
        using (WriteArray()) { // of K.t
          using (WriteArray()) {
            j.WriteValue(KremlinAst.UInt32);
          }
          j.WriteValue(value.ToString());
        }
      }
      j.Formatting = old;
    }

    //["EConstant", [
    //["Int32"], "value"
    //]],
    void WriteConstant(Int32 value) {
      Formatting old = j.Formatting;
      j.Formatting = Formatting.None;
      using (WriteArray()) {
        j.WriteValue(KremlinAst.EConstant);
        using (WriteArray()) { // of K.t
          using (WriteArray()) {
            j.WriteValue(KremlinAst.Int32);
          }
          j.WriteValue(value.ToString());
        }
      }
      j.Formatting = old;
    }

    void TrSeqDisplayElements(List<Expression> expr, Type seqType, bool inLetExprBody) {
      Contract.Requires(expr != null);
      Contract.Requires(seqType != null);

      // ELet tmpVar1 = let tmpVar2 = EBufCreateL (lifetime * list of initializers)  in _ in tmpVar1;
      var tmpVar1 = new BoundVar(expr[0].tok, idGenerator.FreshId("_seq"), seqType);
      using (WriteArray()) {
        j.WriteValue(KremlinAst.ELet);
        using (WriteArray()) { // of (binder * expr * expr)
          WriteBinder(tmpVar1, tmpVar1.Name, false); // binder
          using (WriteArray()) {  // expr1
            j.WriteValue(KremlinAst.EBufCreateL); // of (lifetime * expr list)
            using (WriteArray()) {
              using (WriteArray()) {
                j.WriteValue(KremlinAst.Stack);
              }
              using (WriteArray()) {
                for (int i = 0; i < expr.Count; ++i) {
                  TrExpr(expr[i], inLetExprBody);
                }
              }
            }
          }
          VarTracker.Push(tmpVar1);
          WriteEBound(tmpVar1); // expr2
          VarTracker.Pop(tmpVar1);
        }
      }
    }

    string DtName(DatatypeDecl decl) {
      var d = (TopLevelDecl)decl;
      while (DafnyOptions.O.IronDafny && d.ClonedFrom != null) {
        d = (TopLevelDecl)d.ClonedFrom;
      }
      return d.FullName;
    }

    void TrAssign(Expression lhs, IVariable rhs) {
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);

      lhs = lhs.Resolved;
      if (lhs is IdentifierExpr) {
        var ll = (IdentifierExpr)lhs;
        using (WriteArray()) {
          j.WriteValue(KremlinAst.EAssign);
          using (WriteArray()) { // (expr * expr)
            WriteEBound(ll.Var);
            WriteEBound(rhs);
          }
        }
      }
      else if (lhs is MemberSelectExpr) {
        var ll = (MemberSelectExpr)lhs;
        using (WriteArray()) {
          j.WriteValue(KremlinAst.EAssign);
          using (WriteArray()) { // (expr * expr)
            TrMemberSelectExpr(ll);
            WriteEBound(rhs);
          }
        }
      }
      else if (lhs is SeqSelectExpr) {
        var ll = (SeqSelectExpr)lhs;
        TrSeqSelectExpr(ll, rhs, false); // LHS of a SeqSelect
      }
      else {
        var ll = (MultiSelectExpr)lhs;
      }
    }

    void TrSeqSelectExpr(SeqSelectExpr e, IVariable rhs, bool isInLetExprBody) {
      Contract.Requires(e != null);
      Contract.Assert(e.Seq.Type != null);
      // rhs may be null, meaning the SeqSelect is on the lhs

      string KremlinOp = (rhs == null) ? KremlinAst.EBufRead : KremlinAst.EBufWrite;

      if (e.Seq.Type.IsArrayType) {
        if (e.SelectOne) {
          Contract.Assert(e.E0 != null && e.E1 == null);
          using (WriteArray()) {
            j.WriteValue(KremlinOp);
            using (WriteArray()) {
              TrExpr(e.Seq, isInLetExprBody); // Specify the .Seq array
              TrBufferIndexSizeExpr(e.E0, isInLetExprBody);  // Offset in the array
              if (rhs != null) {
                WriteEBound(rhs);             // Value to write
              }
            }
          }
        }
        else {
          WriteEAbort("BUGBUG Select from array sequence type not supported"); // bugbug: implement
        }
      }
      else if (e.SelectOne) {
        Contract.Assert(e.E0 != null && e.E1 == null);
        using (WriteArray()) {
          j.WriteValue(KremlinOp);
          using (WriteArray()) {
            TrExpr(e.Seq, isInLetExprBody); // Specify the .Seq array
            TrBufferIndexSizeExpr(e.E0, isInLetExprBody);  // Offset in the array
            if (rhs != null) {
              WriteEBound(rhs);             // Value to write
            }
          }
        }
      }
      else {
        WriteEAbort("BUGBUG SeqSelectExpr TrExpr .Take and .Drop not supported yet"); // bugbug: implement
      }
    }

    void TrMemberSelectExpr(MemberSelectExpr e) {
      Contract.Requires(e != null);

      SpecialField sf = e.Member as SpecialField;
      if (sf != null && (sf.PostString != "" || sf.PreString != "")) {
        // A SpecialField with no Pre- or Post- string generates identical
        // code to a non-SpecialField, except for parentheses.  For Kremlin,
        // the code-gen is identical in that case.
        WriteEAbort("BUGBUG MemberSelectExpr TrExpr if SpecialField not supported"); // bugbug: implement
      }
      else {
        using (WriteArray()) {
          // e.Member.Name is the field name
          // e.Obj.Name is the struct name
          j.WriteValue(KremlinAst.EField);
          using (WriteArray()) { // of (typ * expr * ident)
            WriteTypeOfLident(e.Obj.Type);
            using (WriteArray()) {
              j.WriteValue(KremlinAst.EBufRead);
              using (WriteArray()) {
                TrExpr(e.Obj, false); // This will generate an EBound reference to the variable
                WriteConstant(0u);
              }
            }
            j.WriteValue(e.Member.Name);
          }
        }
      }
    }

    /// <summary>
    /// Before calling TrExpr(expr), the caller must have spilled the let variables declared in "expr".
    /// </summary>
    void TrExpr(Expression expr, bool inLetExprBody) {
      Contract.Requires(expr != null);

      if (expr is LiteralExpr) {
        LiteralExpr e = (LiteralExpr)expr;
        if (e is StaticReceiverExpr) {
          // bugbug: Kremlin doesn't support a type name as an expression
          using (WriteArray()) {
            WriteEAbort("BUGBUG TrExpr - type name not supported by Kremlin as an expression");
          }
        }
        else if (e.Value == null) {
          // bugbug: is this correct?
          WriteEUnit();
        }
        else if (e.Value is bool) {
          using (WriteArray()) {
            j.WriteValue(KremlinAst.EBool);
            j.WriteValue((bool)e.Value);
          }
        }
        else if (e is CharLiteralExpr) {
          Formatting old = j.Formatting;
          j.Formatting = Formatting.None;
          using (WriteArray()) {
            j.WriteValue(KremlinAst.EConstant); // of K.t
            using (WriteArray()) { // [type], value
              using (WriteArray()) {
                j.WriteValue("String"); // bugbug: what is the correct Kremlin type for a string?
              }
              j.WriteValue((string)e.Value);
            }
          }
          j.Formatting = old;
        }
        else if (e is StringLiteralExpr) {
          // bugbug: is the correct?  It may need to cast to StringLiteralExpr and check .IsVerbatim
          Formatting old = j.Formatting;
          j.Formatting = Formatting.None;
          using (WriteArray()) {
            j.WriteValue(KremlinAst.EConstant); // of K.t
            using (WriteArray()) { // [type], value
              using (WriteArray()) {
                j.WriteValue("String"); // bugbug: what is the correct Kremlin type for a string?
              }
              j.WriteValue((string)e.Value);
            }
          }
          j.Formatting = old;
        }
        else if (AsNativeType(e.Type) != null) {
          // bugbug: this writes the BitInteger out in decimal.  Is that correct?
          NativeType nt = AsNativeType(e.Type);
          BigInteger bi = (BigInteger)e.Value;
          Formatting old = j.Formatting;
          j.Formatting = Formatting.None;
          using (WriteArray()) {
            j.WriteValue(KremlinAst.EConstant);
            using (WriteArray()) {
              using (WriteArray()) {
                j.WriteValue(nt.KremlinType());
              }
              j.WriteValue(bi.ToString());
            }
          }
          j.Formatting = old;
        }
        else if (e.Value is BigInteger) {
          BigInteger i = (BigInteger)e.Value;
          string KremlinType = KremlinAst.TUnit;
          string Value = "";
          if (new BigInteger(ulong.MinValue) <= i && i <= new BigInteger(ulong.MaxValue)) {
            KremlinType = "UInt64";
            Value = i.ToString();
          }
          else if (new BigInteger(long.MinValue) <= i && i <= new BigInteger(long.MaxValue)) {
            KremlinType = "SInt64";
            Value = i.ToString();
          }
          else {
            j.WriteComment("Unsupported BigInteger value " + i.ToString());
          }

          Formatting old = j.Formatting;
          j.Formatting = Formatting.None;
          using (WriteArray()) {
            j.WriteValue(KremlinAst.EConstant);
            using (WriteArray()) {
              using (WriteArray()) {
                j.WriteValue(KremlinType);
              }
              j.WriteValue(Value);
            }
          }
          j.Formatting = old;
        }
        else if (e.Value is Basetypes.BigDec) {
          WriteEAbort("BUGBUG BigDec TrExpr not supported"); // bugbug: implement
        }
        else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
        }
      }
      else if (expr is ThisExpr) {
        WriteEBound(enclosingThis);
      }
      else if (expr is IdentifierExpr) {
        Formatting old = j.Formatting;
        j.Formatting = Formatting.None;
        var e = (IdentifierExpr)expr;
        if (e.Var is Formal && inLetExprBody && !((Formal)e.Var).InParam) {
          // out param in letExpr body, need to copy it to a temp since
          // letExpr body is translated to an anonymous function that doesn't
          // allow out parameters
          // bugbug: implement
          WriteEAbort("BUGBUG out param in letExpr body unsupported");
        }
        else {
          WriteEBound(e.Var);
        }
        j.Formatting = old;
      }
      else if (expr is SetDisplayExpr) {
        WriteEAbort("BUGBUG SetDisplayExpr TrExpr not supported"); // bugbug: implement
      }
      else if (expr is MultiSetDisplayExpr) {
        WriteEAbort("BUGBUG MultiSetDisplayExpr TrExpr not supported"); // bugbug: implement
      }
      else if (expr is SeqDisplayExpr) {
        var e = (SeqDisplayExpr)expr;
        TrSeqDisplayElements(e.Elements, e.Type, inLetExprBody);
      }
      else if (expr is MapDisplayExpr) {
        WriteEAbort("BUGBUG MapDisplayExpr TrExp not supported"); // bugbug: implement
      }
      else if (expr is MemberSelectExpr) {
        MemberSelectExpr e = (MemberSelectExpr)expr;
        TrMemberSelectExpr(e);
      }
      else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        TrSeqSelectExpr(e, null, inLetExprBody); // RHS of a SeqSelect
      }
      else if (expr is MultiSetFormingExpr) {
        WriteEAbort("BUGBUG MultiSetFormingExpr TrExpr not supported"); // bugbug: implement
      }
      else if (expr is SeqUpdateExpr) {
        WriteEAbort("BUGBUG SeqUpdateExpr TrExpr not supported"); // bugbug: implement
      }
      else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        CompileFunctionCallExpr(e, inLetExprBody);
      }
      else if (expr is ApplyExpr) {
        WriteEAbort("BUGBUG ApplyExpr TrExpr not supported"); // bugbug: implement
      }
      else if (expr is DatatypeValue) {
        // C# code-gen is "new typename(constructor_args)"
        // Kremlin code-gen is "EApp (explicit_constructor_name (args list))
        DatatypeValue dtv = (DatatypeValue)expr;
        Contract.Assert(dtv.Ctor != null);  // since dtv has been successfully resolved
        if (dtv.InferredTypeArgs.Count != 0) {
          WriteEAbort("bugbug: TrExpr of DataTypeValue with InferredTypeArgs is unsupported"); // bugbug: implement
        }
        else if (dtv.IsCoCall) {
          WriteEAbort("bugbug: TrExpr of DataTypeValue of CoCall is unsupported"); // bugbug: implement
        }
        else {
          j.WriteComment("DatatypeValue");
          using (WriteArray()) {
            j.WriteValue(KremlinAst.EApp);
            using (WriteArray()) { // of (expr * expr list)
              // expr1: Function to call
              using (WriteArray()) {
                var old = j.Formatting;
                j.Formatting = Formatting.None;
                j.WriteValue(KremlinAst.EQualified);
                WriteLident(dtv.Ctor.FullName);
                j.Formatting = old;
              }
              // expr2: list of arguments
              using (WriteArray()) {
                for (int i = 0; i < dtv.Arguments.Count; i++) {
                  Formal formal = dtv.Ctor.Formals[i];
                  if (!formal.IsGhost) {
                    TrExpr(dtv.Arguments[i], inLetExprBody);
                  }
                }
              }
            }
          }
        }
      }
      else if (expr is OldExpr) {
        Contract.Assert(false); throw new cce.UnreachableException();  // 'old' is always a ghost (right?)
      }
      else if (expr is UnaryOpExpr) {
        WriteEAbort("BUGBUG UnaryOpExpr TrExpr not supported"); // bugbug: implement
      }
      else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        using (WriteArray()) {
          j.WriteValue(KremlinAst.ECast); // of (expr * typ)
          using (WriteArray()) {
            // e.E is the source, a UnaryExpression
            // e.ToType is the new type, a Type
            TrExpr(e.E, inLetExprBody);
            WriteTypeName(e.ToType);
          }
        }
      }
      else if (expr is BinaryExpr) {
        // EApp of (expr * expr list)
        // EOp of (K.op * K.width)
        //
        // EApp[ [EOp ["Bopname"], ["UInt32"]], expr1, expr2)
        BinaryExpr e = (BinaryExpr)expr;
        using (WriteArray()) {
          j.WriteValue(KremlinAst.EApp); // of (expr * expr list)
          using (WriteArray()) {
            using (WriteArray()) {
              Formatting old = j.Formatting;
              j.Formatting = Formatting.None;
              j.WriteValue(KremlinAst.EOp); // of (K.op * K.width)
              using (WriteArray()) {
                using (WriteArray()) {
                  switch (e.ResolvedOp) {
                    case BinaryExpr.ResolvedOpcode.Add:
                      j.WriteValue("Add"); break;
                    case BinaryExpr.ResolvedOpcode.And:
                      j.WriteValue("And"); break;
                    case BinaryExpr.ResolvedOpcode.Div:
                      j.WriteValue("Div"); break; // bugbug: when to use DivW instead of Div?
                    case BinaryExpr.ResolvedOpcode.EqCommon:
                      j.WriteValue("Eq"); break; // bugbug: Dafny EqCommon rules may not match F*.  It doesn't match C# either.
                    case BinaryExpr.ResolvedOpcode.Ge:
                      j.WriteValue("Ge"); break;
                    case BinaryExpr.ResolvedOpcode.GeChar:
                      j.WriteValue("Ge"); break;
                    case BinaryExpr.ResolvedOpcode.Gt:
                      j.WriteValue("Gt"); break;
                    case BinaryExpr.ResolvedOpcode.GtChar:
                      j.WriteValue("Gt"); break;
                    case BinaryExpr.ResolvedOpcode.Iff:
                      j.WriteValue("Eq"); break; // bugbug: is this correct?
                    case BinaryExpr.ResolvedOpcode.Imp:
                      j.WriteComment("Imp operator not supported"); // bugbug: Dafny generates !(x || y)
                      j.WriteValue("Or"); break;
                    case BinaryExpr.ResolvedOpcode.Le:
                      j.WriteValue("Lte"); break;
                    case BinaryExpr.ResolvedOpcode.LeChar:
                      j.WriteValue("Lte"); break;
                    case BinaryExpr.ResolvedOpcode.Lt:
                      j.WriteValue("Lt"); break;
                    case BinaryExpr.ResolvedOpcode.LtChar:
                      j.WriteValue("Lt"); break;
                    case BinaryExpr.ResolvedOpcode.Mod:
                      j.WriteValue("Mod"); break;
                    case BinaryExpr.ResolvedOpcode.Mul:
                      j.WriteValue("Mult"); break;
                    case BinaryExpr.ResolvedOpcode.NeqCommon:
                      j.WriteValue("Neq"); break;
                    case BinaryExpr.ResolvedOpcode.Or:
                      j.WriteValue("Or"); break;
                    case BinaryExpr.ResolvedOpcode.Sub:
                      j.WriteValue("Sub"); break;
                    case BinaryExpr.ResolvedOpcode.BitwiseAnd:
                    case BinaryExpr.ResolvedOpcode.BitwiseOr:
                    case BinaryExpr.ResolvedOpcode.BitwiseXor:
                    case BinaryExpr.ResolvedOpcode.LeftShift:
                    case BinaryExpr.ResolvedOpcode.RightShift:
                    case BinaryExpr.ResolvedOpcode.SetEq:
                    case BinaryExpr.ResolvedOpcode.MultiSetEq:
                    case BinaryExpr.ResolvedOpcode.SeqEq:
                    case BinaryExpr.ResolvedOpcode.MapEq:
                    case BinaryExpr.ResolvedOpcode.SetNeq:
                    case BinaryExpr.ResolvedOpcode.MultiSetNeq:
                    case BinaryExpr.ResolvedOpcode.SeqNeq:
                    case BinaryExpr.ResolvedOpcode.MapNeq:
                    case BinaryExpr.ResolvedOpcode.ProperSubset:
                    case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
                    case BinaryExpr.ResolvedOpcode.Subset:
                    case BinaryExpr.ResolvedOpcode.MultiSubset:
                    case BinaryExpr.ResolvedOpcode.Superset:
                    case BinaryExpr.ResolvedOpcode.MultiSuperset:
                    case BinaryExpr.ResolvedOpcode.ProperSuperset:
                    case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
                    case BinaryExpr.ResolvedOpcode.Disjoint:
                    case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
                    case BinaryExpr.ResolvedOpcode.MapDisjoint:
                    case BinaryExpr.ResolvedOpcode.InSet:
                    case BinaryExpr.ResolvedOpcode.InMultiSet:
                    case BinaryExpr.ResolvedOpcode.InMap:
                    case BinaryExpr.ResolvedOpcode.NotInSet:
                    case BinaryExpr.ResolvedOpcode.NotInMultiSet:
                    case BinaryExpr.ResolvedOpcode.NotInMap:
                    case BinaryExpr.ResolvedOpcode.Union:
                    case BinaryExpr.ResolvedOpcode.MultiSetUnion:
                    case BinaryExpr.ResolvedOpcode.Intersection:
                    case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
                    case BinaryExpr.ResolvedOpcode.SetDifference:
                    case BinaryExpr.ResolvedOpcode.MultiSetDifference:
                    case BinaryExpr.ResolvedOpcode.ProperPrefix:
                    case BinaryExpr.ResolvedOpcode.Prefix:
                    case BinaryExpr.ResolvedOpcode.Concat:
                    case BinaryExpr.ResolvedOpcode.InSeq:
                    case BinaryExpr.ResolvedOpcode.NotInSeq:
                      j.WriteComment("BUGBUG Operator " + e.ResolvedOp.ToString() + " is not supported"); // bugbug: implement
                      j.WriteValue(e.ResolvedOp.ToString());
                      break;
                    default:
                      System.Diagnostics.Debug.Print(e.ResolvedOp.ToString());
                      Contract.Assert(false); throw new cce.UnreachableException();  // unexpected binary expression
                  }
                }
                WriteTypeWidth(e.E0.Type);
              } // end of EOp
              j.Formatting = old;
            } // end of EOp
            using (WriteArray()) {
              TrExpr(e.E0, inLetExprBody);
              TrExpr(e.E1, inLetExprBody);
            }
          } // end of EApp
        }
      }
      else if (expr is TernaryExpr) {
        Contract.Assume(false);  // currently, none of the ternary expressions is compilable
      }
      else if (expr is LetExpr) {
        WriteEAbort("BUGBUG LetExpr TrExpr not supported"); // bugbug: implement
      }
      else if (expr is MatchExpr) {
        WriteEAbort("BUGBUG MatchExpr TrExpr not supported"); // bugbug: implement
      }
      else if (expr is QuantifierExpr) {
        WriteEAbort("BUGBUG QuantifierExpr TrExpr not supported"); // bugbug: implement
      }
      else if (expr is SetComprehension) {
        WriteEAbort("BUGBUG SetComprehension TrExpr not supported"); // bugbug: implement
      }
      else if (expr is MapComprehension) {
        WriteEAbort("BUGBUG MapComprehension TrExpr not supported"); // bugbug: implement
      }
      else if (expr is LambdaExpr) {
        WriteEAbort("BUGBUG LambdaExpr TrExpr not supported"); // bugbug: implement
      }
      else if (expr is StmtExpr) {
        WriteEAbort("BUGBUG StmtExpr TrExpr not supported"); // bugbug: implement
      }
      else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        TrExpr(e.ResolvedExpression, inLetExprBody);
      }
      else if (expr is NamedExpr) {
        TrExpr(((NamedExpr)expr).Body, inLetExprBody);
      }
      else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }

    int TrCasePattern(CasePattern pat, string rhsString, Type bodyType) {
      Contract.Requires(pat != null);
      Contract.Requires(rhsString != null);

      WriteEAbort("BUGBUG TrCasePattern"); // bugbug: implement

      return 0; // bugbug
    }

    void CompileFunctionCallExpr(FunctionCallExpr e, bool inLetExprBody) {
      Contract.Requires(e != null && e.Function != null);
      Function f = e.Function;

      if (f.TypeArgs.Count != 0) {
        j.WriteComment("BUGBUG CompileFunctionCallExpr support for TypeArgs"); // bugbug: implement
      }

      using (WriteArray()) {
        j.WriteValue(KremlinAst.EApp); // of (expr * expr list)
        using (WriteArray()) {
          // expr1: Function to call
          using (WriteArray()) {
            var old = j.Formatting;
            j.Formatting = Formatting.None;
            j.WriteValue(KremlinAst.EQualified);
            WriteLident(f);
            j.Formatting = old;
          }
          // expr2: list of arguments
          using (WriteArray()) {
            for (int i = 0; i < e.Args.Count; i++) {
              if (!e.Function.Formals[i].IsGhost) {
                TrExpr(e.Args[i], inLetExprBody);
              }
            }
          }
        }
      }
    }

    void WriteToken(Microsoft.Boogie.IToken t) {
      if (t.IsValid) {
        j.WriteComment(string.Format("File:{0} Line:{1} Col:{2}", t.filename, t.line, t.col));
      }
    }
  }
}
