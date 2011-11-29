//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;
using System.Text;

namespace Microsoft.Dafny {
  public class Compiler {
    public Compiler(TextWriter wr) {
      Contract.Requires(wr != null);
      this.wr = wr;
    }

    [ContractInvariantMethod]
    void ObjectInvariant() 
    {
      Contract.Invariant(wr!=null);
    }

    TextWriter wr;
    
    public int ErrorCount;
    void Error(string msg, params object[] args) {Contract.Requires(msg != null);
      string s = string.Format("Compilation error: " + msg, args);
      Console.WriteLine(s);
      wr.WriteLine("/* {0} */", s);
      ErrorCount++;
    }
    
    void ReadRuntimeSystem() {
      string codebase = cce.NonNull( System.IO.Path.GetDirectoryName(cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location)));
      string path = System.IO.Path.Combine(codebase, "DafnyRuntime.cs");
      using (TextReader rd = new StreamReader(new FileStream(path, System.IO.FileMode.Open, System.IO.FileAccess.Read)))
      {
        while (true) {
          string s = rd.ReadLine();
          if (s == null)
            return;
          wr.WriteLine(s);
        }
      }
    }

    readonly int IndentAmount = 2;
    void Indent(int ind) {
      string spaces = "          ";
      for (; spaces.Length < ind; ind -= spaces.Length) {
        wr.Write(spaces);
      }
      wr.Write(spaces.Substring(0, ind));
    }

    public void Compile(Program program) {Contract.Requires(program != null);
      wr.WriteLine("// Dafny program {0} compiled into C#", program.Name);
      wr.WriteLine();
      ReadRuntimeSystem();
      CompileBuiltIns(program.BuiltIns);

      foreach (ModuleDecl m in program.Modules) {
        int indent = 0;
        if (!m.IsDefaultModule) {
          wr.WriteLine("namespace @{0} {{", m.Name);
          indent += IndentAmount;
        }
        foreach (TopLevelDecl d in m.TopLevelDecls) {
          wr.WriteLine();
          if (d is DatatypeDecl) {
            DatatypeDecl dt = (DatatypeDecl)d;
            Indent(indent);
            wr.Write("public abstract class Base_{0}", dt.Name);
            if (dt.TypeArgs.Count != 0) {
              wr.Write("<{0}>", TypeParameters(dt.TypeArgs));
            }
            wr.WriteLine(" { }");
            CompileDatatypeConstructors(dt, indent);
            CompileDatatypeStruct(dt, indent);
          } else {
            ClassDecl cl = (ClassDecl)d;
            Indent(indent);
            wr.Write("public class @{0}", cl.Name);
            if (cl.TypeArgs.Count != 0) {
              wr.Write("<{0}>", TypeParameters(cl.TypeArgs));
            }
            wr.WriteLine(" {");
            CompileClassMembers(cl, indent+IndentAmount);
            Indent(indent);  wr.WriteLine("}");
          }
        }
        if (!m.IsDefaultModule) {
          wr.WriteLine("}} // end of namespace {0}", m.Name);
        }
      }
    }

    void CompileBuiltIns(BuiltIns builtIns) {
      wr.WriteLine("namespace Dafny {");
      Indent(IndentAmount);
      wr.WriteLine("public partial class Helpers {");
      foreach (var decl in builtIns.SystemModule.TopLevelDecls) {
        if (decl is ArrayClassDecl) {
          int dims = ((ArrayClassDecl)decl).Dims;
          // public static T[,] InitNewArray2<T>(BigInteger size0, BigInteger size1) {
          Indent(3 * IndentAmount);
          wr.Write("public static T[");
          RepeatWrite(wr, dims, "", ",");
          wr.Write("] InitNewArray{0}<T>(", dims);
          RepeatWrite(wr, dims, "BigInteger size{0}", ", ");
          wr.WriteLine(") {");
          // int s0 = (int)size0;
          for (int i = 0; i < dims; i++) {
            Indent(4 * IndentAmount);
            wr.WriteLine("int s{0} = (int)size{0};", i);
          }
          // T[,] a = new T[s0, s1];
          Indent(4 * IndentAmount);
          wr.Write("T[");
          RepeatWrite(wr, dims, "", ",");
          wr.Write("] a = new T[");
          RepeatWrite(wr, dims, "s{0}", ",");
          wr.WriteLine("];");
          // BigInteger[,] b = a as BigInteger[,];
          Indent(4 * IndentAmount);
          wr.Write("BigInteger[");
          RepeatWrite(wr, dims, "", ",");
          wr.Write("] b = a as BigInteger[");
          RepeatWrite(wr, dims, "", ",");
          wr.WriteLine("];");
          // if (b != null) {
          Indent(4 * IndentAmount);
          wr.WriteLine("if (b != null) {");
          // BigInteger z = new BigInteger(0);
          Indent(5 * IndentAmount);
          wr.WriteLine("BigInteger z = new BigInteger(0);");
          // for (int i0 = 0; i0 < s0; i0++)
          //   for (int i1 = 0; i1 < s1; i1++)
          for (int i = 0; i < dims; i++) {
            Indent((5+i) * IndentAmount);
            wr.WriteLine("for (int i{0} = 0; i{0} < s{0}; i{0}++)", i);
          }
          // b[i0,i1] = z;
          Indent((5+dims) * IndentAmount);
          wr.Write("b[");
          RepeatWrite(wr, dims, "i{0}", ",");
          wr.WriteLine("] = z;");
          // }
          Indent(4 * IndentAmount);
          wr.WriteLine("}");
          // return a;
          Indent(4 * IndentAmount);
          wr.WriteLine("return a;");
          // }
          Indent(3 * IndentAmount);
          wr.WriteLine("}");  // end of method
        }
      }
      Indent(IndentAmount);
      wr.WriteLine("}");  // end of class Helpers
      wr.WriteLine("}");  // end of namespace
    }

    static void RepeatWrite(TextWriter wr, int times, string template, string separator) {
      Contract.Requires(1 <= times);
      string s = "";
      for (int i = 0; i < times; i++) {
        wr.Write(s);
        wr.Write(template, i);
        s = separator;
      }
    }

    void CompileDatatypeConstructors(DatatypeDecl dt, int indent)
    {Contract.Requires(dt != null);
      foreach (DatatypeCtor ctor in dt.Ctors) {
        // class Dt_Ctor<T,U> : Base_Dt<T> {
        //   Fields;
        //   public Dt_Ctor(arguments) {
        //     Fields = arguments;
        //   }
        // }
        Indent(indent);
        wr.Write("public class {0}", DtCtorName(ctor));
        if (dt.TypeArgs.Count != 0) {
          wr.Write("<");
          if (dt.TypeArgs.Count != 0) {
            wr.Write("{0}", TypeParameters(dt.TypeArgs));
          }
          wr.Write(">");
        }
        wr.Write(" : Base_{0}", dt.Name);
        if (dt.TypeArgs.Count != 0) {
          wr.Write("<{0}>", TypeParameters(dt.TypeArgs));
        }
        wr.WriteLine(" {");
        int ind = indent + IndentAmount;

        int i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            Indent(ind);
            wr.WriteLine("public readonly {0} @{1};", TypeName(arg.Type), FormalName(arg, i));
            i++;
          }
        }

        Indent(ind);
        wr.Write("public {0}(", DtCtorName(ctor));
        WriteFormals("", ctor.Formals);
        wr.WriteLine(") {");
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            Indent(ind + IndentAmount);
            wr.WriteLine("this.@{0} = @{0};", FormalName(arg, i));
            i++;
          }
        }
        Indent(ind);  wr.WriteLine("}");

        Indent(indent);  wr.WriteLine("}");
      }
    }
    
    void CompileDatatypeStruct(DatatypeDecl dt, int indent) {
      Contract.Requires(dt != null);

      // public struct Dt<T> {
      //   Base_Dt<T> d;
      //   public Base_Dt<T> _D {
      //     get { if (d == null) { d = Default; } return d; }
      //   }
      //   public Dt(Base_Dt<T> d) { this.d = d; }
      //   public static Base_Dt<T> Default {
      //     get { return ...; }
      //   }
      //   public override bool Equals(object other) {
      //     return other is Dt<T> && _D.Equals(((Dt<T>)other)._D);
      //   }
      //   public override int GetHashCode() { return _D.GetHashCode(); }
      //
      //   public bool _Ctor0 { get { return _D is Dt_Ctor0; } }
      //   ...
      //
      //   public T0 dtor_Dtor0 { get { return ((DT_Ctor)_D).@Dtor0; } }
      //   ...
      // }
      string DtT = dt.Name;
      if (dt.TypeArgs.Count != 0) {
        DtT += "<" + TypeParameters(dt.TypeArgs) + ">";
      }
      
      Indent(indent);
      wr.WriteLine("public struct @{0} {{", DtT);
      int ind = indent + IndentAmount;
      
      Indent(ind);
      wr.WriteLine("Base_{0} d;", DtT);
      
      Indent(ind);
      wr.WriteLine("public Base_{0} _D {{", DtT);
      Indent(ind + IndentAmount);
      wr.WriteLine("get { if (d == null) { d = Default; } return d; }");
      Indent(ind);  wr.WriteLine("}");
      
      Indent(ind);
      wr.WriteLine("public @{0}(Base_{1} d) {{ this.d = d; }}", dt.Name, DtT);
      
      Indent(ind);
      wr.WriteLine("public static Base_{0} Default {{", DtT);
      Indent(ind + IndentAmount);
      wr.Write("get { return ");
      wr.Write("new {0}", DtCtorName(cce.NonNull(dt.DefaultCtor)));
      if (dt.TypeArgs.Count != 0) {
        wr.Write("<{0}>", TypeParameters(dt.TypeArgs));
      }
      wr.Write("(");
      string sep = "";
      foreach (Formal f in dt.DefaultCtor.Formals) {
        if (!f.IsGhost) {
          wr.Write("{0}{1}", sep, DefaultValue(f.Type));
          sep = ", ";
        }
      }
      wr.Write(")");
      wr.WriteLine("; }");
      Indent(ind);  wr.WriteLine("}");

      Indent(ind);  wr.WriteLine("public override bool Equals(object other) {");
      Indent(ind + IndentAmount);
      wr.WriteLine("return other is @{0} && _D.Equals(((@{0})other)._D);", DtT);
      Indent(ind);  wr.WriteLine("}");

      Indent(ind);
      wr.WriteLine("public override int GetHashCode() { return _D.GetHashCode(); }");

      // query properties
      foreach (var ctor in dt.Ctors) {
        //   public bool _Ctor0 { get { return _D is Dt_Ctor0; } }
        Indent(ind);
        wr.WriteLine("public bool _{0} {{ get {{ return _D is {1}_{0}; }} }}", ctor.Name, DtT);
      }

      // destructors
      foreach (var ctor in dt.Ctors) {
        foreach (var arg in ctor.Formals) {
          if (arg.HasName) {
            //   public T0 @Dtor0 { get { return ((DT_Ctor)_D).@Dtor0; } }
            Indent(ind);
            wr.WriteLine("public {0} dtor_{1} {{ get {{ return (({2}_{3})_D).@{1}; }} }}", TypeName(arg.Type), arg.Name, DtT, ctor.Name);
          }
        }
      }

      Indent(indent);
      wr.WriteLine("}");
    }
    
    int WriteFormals(string sep, List<Formal/*!*/>/*!*/ formals)
    {
      Contract.Requires(sep != null);
      Contract.Requires(cce.NonNullElements(formals));
      int i = 0;
      foreach (Formal arg in formals) {
        if (!arg.IsGhost) {
          string name = FormalName(arg, i);
          wr.Write("{0}{1}{2} @{3}", sep, arg.InParam ? "" : "out ", TypeName(arg.Type), name);
          sep = ", ";
          i++;
        }
      }
      return i;  // the number of formals written
    }
    
    string FormalName(Formal formal, int i) {
      Contract.Requires(formal != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return formal.HasName ? formal.Name : "_a" + i;
    }
    
    string DtCtorName(DatatypeCtor ctor) {
      Contract.Requires(ctor != null);Contract.Ensures(Contract.Result<string>() != null);

      return cce.NonNull(ctor.EnclosingDatatype).Name + "_" + ctor.Name;
    }
        
    void CompileClassMembers(ClassDecl c, int indent)
    {
      Contract.Requires(c != null);
      foreach (MemberDecl member in c.Members) {
        if (member is Field) {
          Field f = (Field)member;
          if (!f.IsGhost) {
            Indent(indent);
            wr.WriteLine("public {0} @{1} = {2};", TypeName(f.Type), f.Name, DefaultValue(f.Type));
          }
          
        } else if (member is Function) {
          Function f = (Function)member;
          if (f.IsGhost) {
            // nothing to compile
          } else if (f.Body == null) {
            Error("Function {0} has no body", f.FullName);
          } else {
            Indent(indent);
            wr.Write("public {0}{1} @{2}", f.IsStatic ? "static " : "", TypeName(f.ResultType), f.Name);
            if (f.TypeArgs.Count != 0) {
              wr.Write("<{0}>", TypeParameters(f.TypeArgs));
            }
            wr.Write("(");
            WriteFormals("", f.Formals);
            wr.WriteLine(") {");
            CompileReturnBody(f.Body, indent);
            Indent(indent);  wr.WriteLine("}");
          }
          
        } else if (member is Method) {
          Method m = (Method)member;
          if (!m.IsGhost) {
            Indent(indent);
            wr.Write("public {0}void @{1}", m.IsStatic ? "static " : "", m.Name);
            if (m.TypeArgs.Count != 0) {
              wr.Write("<{0}>", TypeParameters(m.TypeArgs));
            }
            wr.Write("(");
            int nIns = WriteFormals("", m.Ins);
            WriteFormals(nIns == 0 ? "" : ", ", m.Outs);
            wr.WriteLine(")");
            Indent(indent);  wr.WriteLine("{");
            foreach (Formal p in m.Outs) {
              if (!p.IsGhost) {
                Indent(indent + IndentAmount);
                wr.WriteLine("@{0} = {1};", p.Name, DefaultValue(p.Type));
              }
            }
            if (m.Body == null) {
              Error("Method {0} has no body", m.FullName);
            } else {
              TrStmtList(m.Body.Body, indent);
            }
            Indent(indent);  wr.WriteLine("}");

            // allow the Main method to be an instance method
            if (m.Name == "Main" && m.Ins.Count == 0 && m.Outs.Count == 0) {
              Indent(indent);
              wr.WriteLine("public static void Main(string[] args) {");
              Contract.Assert(m.EnclosingClass == c);
              Indent(indent + IndentAmount);
              wr.Write("@{0} b = new @{0}", c.Name);
              if (c.TypeArgs.Count != 0) {
                // instantiate every parameter, it doesn't particularly matter how
                wr.Write("<");
                string sep = "";
                for (int i = 0; i < c.TypeArgs.Count; i++) {
                  wr.Write("{0}int", sep);
                  sep = ", ";
                }
                wr.Write(">");
              }
              wr.WriteLine("();");
              Indent(indent + IndentAmount);  wr.WriteLine("b.Main();");
              Indent(indent);  wr.WriteLine("}");
            }
          }

        } else if (member is CouplingInvariant) {
          Error("coupling invariants are not supported in compilation");

        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member
        }
      }
    }

    void CompileReturnBody(Expression body, int indent) {
      body = body.Resolved;
      if (body is MatchExpr) {
        MatchExpr me = (MatchExpr)body;
        // Type source = e;
        // if (source._D is Dt_Ctor0) {
        //   FormalType f0 = ((Dt_Ctor0)source._D).a0;
        //   ...
        //   return Body0;
        // } else if (...) {
        //   ...
        // } else if (true) {
        //   ...
        // }

        string source = "_source" + tmpVarCount;
        tmpVarCount++;
        Indent(indent);
        wr.Write("{0} {1} = ", TypeName(cce.NonNull(me.Source.Type)), source);
        TrExpr(me.Source);
        wr.WriteLine(";");

        if (me.Cases.Count == 0) {
          // the verifier would have proved we never get here; still, we need some code that will compile
          Indent(indent);
          wr.WriteLine("throw new System.Exception();");
        } else {
          int i = 0;
          foreach (MatchCaseExpr mc in me.Cases) {
            MatchCasePrelude(source, cce.NonNull(mc.Ctor), mc.Arguments, i, me.Cases.Count, indent + IndentAmount);
            CompileReturnBody(mc.Body, indent + IndentAmount);
            i++;
          }
          Indent(indent); wr.WriteLine("}");
        }

      } else {
        Indent(indent + IndentAmount);
        wr.Write("return ");
        TrExpr(body);
        wr.WriteLine(";");
      }
    }

    // ----- Type ---------------------------------------------------------------------------------
    
    readonly string DafnySetClass = "Dafny.Set";
    readonly string DafnySeqClass = "Dafny.Sequence";
    
    string TypeName(Type type)
    {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<string>() != null);

      while (true) {
        TypeProxy tp = type as TypeProxy;
        if (tp == null) {
          break;
        } else if (tp.T == null) {
          // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
          return "object";
        } else {
          type = tp.T;
        }
      }
      
      if (type is BoolType) {
        return "bool";
      } else if (type is IntType) {
        return "BigInteger";
      } else if (type is ObjectType) {
        return "object";
      } else if (type.IsArrayType) {
        ArrayClassDecl at = type.AsArrayType;
        Contract.Assert(at != null);  // follows from type.IsArrayType
        Type elType = UserDefinedType.ArrayElementType(type);
        string name = TypeName(elType) + "[";
        for (int i = 1; i < at.Dims; i++) {
          name += ",";
        }
        return name + "]";
      } else if (type is UserDefinedType) {
        UserDefinedType udt = (UserDefinedType)type;
        string s = "@" + udt.Name;
        if (udt.TypeArgs.Count != 0) {
          if (Contract.Exists(udt.TypeArgs, argType =>argType is ObjectType)) {
            Error("compilation does not support type 'object' as a type parameter; consider introducing a ghost");
          }
          s += "<" + TypeNames(udt.TypeArgs) + ">";
        }
        return s;
      } else if (type is SetType) {
        Type argType = ((SetType)type).Arg;
        if (argType is ObjectType) {
          Error("compilation of set<object> is not supported; consider introducing a ghost");
        }
        return DafnySetClass + "<" + TypeName(argType) + ">";
      } else if (type is SeqType) {
        Type argType = ((SeqType)type).Arg;
        if (argType is ObjectType) {
          Error("compilation of seq<object> is not supported; consider introducing a ghost");
        }
        return DafnySeqClass + "<" + TypeName(argType) + ">";
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    string/*!*/ TypeNames(List<Type/*!*/>/*!*/ types) {
      Contract.Requires(cce.NonNullElements(types));
      Contract.Ensures(Contract.Result<string>() != null);

      string s = "";
      string sep = "";
      foreach (Type t in types) {
        s += sep + TypeName(t);
        sep = ",";
      }
      return s;
    }
    
    string/*!*/ TypeParameters(List<TypeParameter/*!*/>/*!*/ targs) {
      Contract.Requires(cce.NonNullElements(targs));
      Contract.Ensures(Contract.Result<string>() != null);

      string s = "";
      string sep = "";
      foreach (TypeParameter tp in targs) {
        s += sep + "@" + tp.Name;
        sep = ",";
      }
      return s;
    }
    
    string DefaultValue(Type type)
    {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<string>() != null);

      while (true) {
        TypeProxy tp = type as TypeProxy;
        if (tp == null) {
          break;
        } else if (tp.T == null) {
          // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
          return "null";
        } else {
          type = tp.T;
        }
      }
      
      if (type is BoolType) {
        return "false";
      } else if (type is IntType) {
        return "new BigInteger(0)";
      } else if (type.IsRefType) {
        return "null";
      } else if (type.IsDatatype) {
        UserDefinedType udt = (UserDefinedType)type;
        string s = "@" + udt.Name;
        if (udt.TypeArgs.Count != 0) {
          s += "<" + TypeNames(udt.TypeArgs) + ">";
        }
        return string.Format("new {0}({0}.Default)", s);
      } else if (type.IsTypeParameter) {
        UserDefinedType udt = (UserDefinedType)type;
        return "default(@" + udt.Name + ")";
      } else if (type is SetType) {
        return DafnySetClass + "<" + TypeName(((SetType)type).Arg) + ">.Empty";
      } else if (type is SeqType) {
        return DafnySeqClass + "<" + TypeName(((SeqType)type).Arg) + ">.Empty";
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }
    
    // ----- Stmt ---------------------------------------------------------------------------------
    
    void TrStmt(Statement stmt, int indent)
    {
      Contract.Requires(stmt != null);
      if (stmt.IsGhost) {
        return;
      }
      
      if (stmt is PrintStmt) {
        PrintStmt s = (PrintStmt)stmt;
        foreach (Attributes.Argument arg in s.Args) {
          Indent(indent);
          wr.Write("System.Console.Write(");
          if (arg.S != null) {
            wr.Write("\"{0}\"", arg.S);
          } else {
            Contract.Assert(arg.E != null);
            TrExpr(arg.E);
          }
          wr.WriteLine(");");
        }
      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        Indent(indent);
        wr.WriteLine("goto after_{0};", s.TargetStmt.Labels.UniqueId);
      } else if (stmt is ReturnStmt) {
        var s = (ReturnStmt)stmt;
        if (s.hiddenUpdate != null)
          TrStmt(s.hiddenUpdate, indent);
        Indent(indent); wr.WriteLine("return;");
      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        var resolved = s.ResolvedStatements;
        if (resolved.Count == 1) {
          TrStmt(resolved[0], indent);
        } else {
          // multi-assignment
          Contract.Assert(s.Lhss.Count == resolved.Count);
          Contract.Assert(s.Rhss.Count == resolved.Count);
          var lvalues = new List<string>();
          var rhss = new List<string>();
          for (int i = 0; i < resolved.Count; i++) {
            if (!resolved[i].IsGhost) {
              var lhs = s.Lhss[i];
              var rhs = s.Rhss[i];
              if (!(rhs is HavocRhs)) {
                lvalues.Add(CreateLvalue(lhs, indent));

                string target = "_rhs" + tmpVarCount;
                tmpVarCount++;
                rhss.Add(target);
                TrRhs("var " + target, null, rhs, indent);
              }
            }
          }
          Contract.Assert(lvalues.Count == rhss.Count);
          for (int i = 0; i < lvalues.Count; i++) {
            Indent(indent);
            wr.WriteLine("{0} = {1};", lvalues[i], rhss[i]);
          }
        }

      } else if (stmt is AssignStmt) {
        AssignStmt s = (AssignStmt)stmt;
        if (s.Lhs is SeqSelectExpr && !((SeqSelectExpr)s.Lhs).SelectOne) {
          SeqSelectExpr sel = (SeqSelectExpr)s.Lhs;
          if (!(s.Rhs is HavocRhs)) {
            // Generate the following:
            //   tmpArr = sel.Seq;
            //   tmpLow = sel.E0;  // or 0 if sel.E0==null
            //   tmpHigh = sel.Eq;  // or arr.Length if sel.E1==null
            //   tmpRhs = s.Rhs;
            //   for (int tmpI = tmpLow; tmpI < tmpHigh; tmpI++) {
            //     tmpArr[tmpI] = tmpRhs;
            //   }
            string arr = "_arr" + tmpVarCount;
            string low = "_low" + tmpVarCount;
            string high = "_high" + tmpVarCount;
            string rhs = "_rhs" + tmpVarCount;
            string i = "_i" + tmpVarCount;
            tmpVarCount++;
            Indent(indent); wr.Write("{0} {1} = ", TypeName(cce.NonNull(sel.Seq.Type)), arr); TrExpr(sel.Seq); wr.WriteLine(";");
            Indent(indent); wr.Write("int {0} = ", low);
            if (sel.E0 == null) {
              wr.Write("0");
            } else {
              TrExpr(sel.E0);
            }
            wr.WriteLine(";");
            Indent(indent); wr.Write("int {0} = ", high);
            if (sel.E1 == null) {
              wr.Write("new BigInteger(arr.Length)");
            } else {
              TrExpr(sel.E1);
            }
            wr.WriteLine(";");
            Indent(indent); wr.Write("{0} {1} = ", TypeName(cce.NonNull(sel.Type)), rhs); TrAssignmentRhs(s.Rhs); wr.WriteLine(";");
            Indent(indent);
            wr.WriteLine("for (BigInteger {0} = {1}; {0} < {2}; {0}++) {{", i, low, high);
            Indent(indent + IndentAmount);
            wr.WriteLine("{0}[(int)({1})] = {2};", arr, i, rhs);
            Indent(indent);
            wr.WriteLine(";");
          }

        } else {
          TrRhs(null, s.Lhs, s.Rhs, indent);
        }
        
      } else if (stmt is VarDecl) {
        TrVarDecl((VarDecl)stmt, true, indent);
        
      } else if (stmt is CallStmt) {
        CallStmt s = (CallStmt)stmt;
        TrCallStmt(s, null, indent);
        
      } else if (stmt is BlockStmt) {
        Indent(indent);  wr.WriteLine("{");
        TrStmtList(((BlockStmt)stmt).Body, indent);
        Indent(indent);  wr.WriteLine("}");
        
      } else if (stmt is IfStmt) {
        IfStmt s = (IfStmt)stmt;
        Indent(indent);
        if (s.Guard == null) {
          wr.WriteLine("if (true)");
        } else {
          wr.Write("if (");
          TrExpr(s.Guard);
          wr.WriteLine(")");
        }
        
        TrStmt(s.Thn, indent);
        if (s.Els != null && s.Guard != null) {
          Indent(indent);  wr.WriteLine("else");
          TrStmt(s.Els, indent);
        }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        Indent(indent);
        foreach (var alternative in s.Alternatives) {
          wr.Write("if (");
          TrExpr(alternative.Guard);
          wr.WriteLine(") {");
          TrStmtList(alternative.Body, indent);
          Indent(indent);
          wr.Write("} else ");
        }
        wr.WriteLine("{ /*unreachable alternative*/ }");

      } else if (stmt is WhileStmt) {
        WhileStmt s = (WhileStmt)stmt;
        if (s.Guard == null) {
          Indent(indent);
          wr.WriteLine("while (false) { }");
        } else {
          Indent(indent);
          wr.Write("while (");
          TrExpr(s.Guard);
          wr.WriteLine(")");
          TrStmt(s.Body, indent);
        }

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        if (s.Alternatives.Count != 0) {
          Indent(indent);
          wr.WriteLine("while (true) {");
          int ind = indent + IndentAmount;
          Indent(ind);
          foreach (var alternative in s.Alternatives) {
            wr.Write("if (");
            TrExpr(alternative.Guard);
            wr.WriteLine(") {");
            TrStmtList(alternative.Body, ind);
            Indent(ind);
            wr.Write("} else ");
          }
          wr.WriteLine("{ break; }");
          Indent(indent);
          wr.WriteLine("}");
        }

      } else if (stmt is ForeachStmt) {
        ForeachStmt s = (ForeachStmt)stmt;
        // List<Pair<TType,RhsType>> pendingUpdates = new List<Pair<TType,RhsType>>();
        // foreach (TType x in S) {
        //   if (Range(x)) {
        //     assert/assume ...;
        //     pendingUpdates.Add(new Pair(x,RHS));
        //   }
        // }
        // foreach (Pair<TType,RhsType> p in pendingUpdates) {
        //   p.Car.m = p.Cdr;
        // }
        string pu = "_pendingUpdates" + tmpVarCount;
        string pr = "_pair" + tmpVarCount;
        tmpVarCount++;
        string TType = TypeName(s.BoundVar.Type);
        string RhsType = TypeName(cce.NonNull(s.BodyAssign.Lhs.Type));
        
        Indent(indent);
        wr.WriteLine("List<Pair<{0},{1}>> {2} = new List<Pair<{0},{1}>>();", TType, RhsType, pu);
        
        Indent(indent);
        wr.Write("foreach ({0} @{1} in (", TType, s.BoundVar.Name);
        TrExpr(s.Collection);
        wr.WriteLine(").Elements) {");
        
        Indent(indent + IndentAmount);
        wr.Write("if (");
        TrExpr(s.Range);
        wr.WriteLine(") {");
        
        foreach (PredicateStmt p in s.BodyPrefix) {
          TrStmt(p, indent + 2*IndentAmount);
        }
        Indent(indent + 2*IndentAmount);
        wr.Write("{0}.Add(new Pair<{1},{2}>(@{3}, ", pu, TType, RhsType, s.BoundVar.Name);
        ExprRhs rhsExpr = s.BodyAssign.Rhs as ExprRhs;
        if (rhsExpr != null) {
          TrExpr(rhsExpr.Expr);
        } else {
          wr.Write(DefaultValue(s.BodyAssign.Lhs.Type));
        }
        wr.WriteLine("))");
        
        Indent(indent + IndentAmount);  wr.WriteLine("}");
        Indent(indent);  wr.WriteLine("}");

        Indent(indent);  wr.WriteLine("foreach (Pair<{0},{1}> {2} in {3}) {{", TType, RhsType, pr, pu);
        Indent(indent + IndentAmount);
        FieldSelectExpr fse = (FieldSelectExpr)s.BodyAssign.Lhs;
        wr.WriteLine("{0}.Car.{1} = {0}.Cdr;", pr, fse.FieldName);
        Indent(indent);  wr.WriteLine("}");
        
      } else if (stmt is MatchStmt) {
        MatchStmt s = (MatchStmt)stmt;
        // Type source = e;
        // if (source._D is Dt_Ctor0) {
        //   FormalType f0 = ((Dt_Ctor0)source._D).a0;
        //   ...
        //   Body0;
        // } else if (...) {
        //   ...
        // } else if (true) {
        //   ...
        // }
        if (s.Cases.Count != 0) {
          string source = "_source" + tmpVarCount;
          tmpVarCount++;
          Indent(indent);
          wr.Write("{0} {1} = ", TypeName(cce.NonNull(s.Source.Type)), source);
          TrExpr(s.Source);
          wr.WriteLine(";");

          int i = 0;
          foreach (MatchCaseStmt mc in s.Cases) {
            MatchCasePrelude(source, cce.NonNull(mc.Ctor), mc.Arguments, i, s.Cases.Count, indent);
            TrStmtList(mc.Body, indent);
            i++;
          }
          Indent(indent); wr.WriteLine("}");
        }

      } else if (stmt is ConcreteSyntaxStatement) {
        var s = (ConcreteSyntaxStatement)stmt;
        foreach (var ss in s.ResolvedStatements) {
          TrStmt(ss, indent);
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }
    }

    string CreateLvalue(Expression lhs, int indent) {
      lhs = lhs.Resolved;
      if (lhs is IdentifierExpr) {
        var ll = (IdentifierExpr)lhs;
        return "@" + ll.Var.Name;
      } else if (lhs is FieldSelectExpr) {
        var ll = (FieldSelectExpr)lhs;
        string obj = "_obj" + tmpVarCount;
        tmpVarCount++;
        Indent(indent);
        wr.Write("var {0} = ", obj);
        TrExpr(ll.Obj);
        wr.WriteLine(";");
        return string.Format("{0}.@{1}", obj, ll.Field.Name);
      } else if (lhs is SeqSelectExpr) {
        var ll = (SeqSelectExpr)lhs;
        string arr = "_arr" + tmpVarCount;
        string index = "_index" + tmpVarCount;
        tmpVarCount++;
        Indent(indent);
        wr.Write("var {0} = ", arr);
        TrExpr(ll.Seq);
        wr.WriteLine(";");
        Indent(indent);
        wr.Write("var {0} = ", index);
        TrExpr(ll.E0);
        wr.WriteLine(";");
        return string.Format("{0}[(int){1}]", arr, index);
      } else {
        var ll = (MultiSelectExpr)lhs;
        string arr = "_arr" + tmpVarCount;
        Indent(indent);
        wr.Write("var {0} = ", arr);
        TrExpr(ll.Array);
        wr.WriteLine(";");
        string fullString = arr + "[";
        string sep = "";
        int i = 0;
        foreach (var idx in ll.Indices) {
          string index = "_index" + i + "_" + tmpVarCount;
          Indent(indent);
          wr.Write("var {0} = ", index);
          TrExpr(idx);
          wr.WriteLine(";");
          fullString += sep + "(int)" + index;
          sep = ", ";
          i++;
        }
        tmpVarCount++;
        return fullString + "]";
      }
    }

    void TrRhs(string target, Expression targetExpr, AssignmentRhs rhs, int indent) {
      Contract.Requires((target == null) != (targetExpr == null));
      var tRhs = rhs as TypeRhs;
      if (tRhs != null && tRhs.InitCall != null) {
        string nw = "_nw" + tmpVarCount;
        tmpVarCount++;
        Indent(indent);
        wr.Write("var {0} = ", nw);
        TrAssignmentRhs(rhs);
        wr.WriteLine(";");
        TrCallStmt(tRhs.InitCall, nw, indent);
        Indent(indent);
        if (target != null) {
          wr.Write(target);
        } else {
          TrExpr(targetExpr);
        }
        wr.WriteLine(" = {0};", nw);
      } else if (!(rhs is HavocRhs)) {
        Indent(indent);
        if (target != null) {
          wr.Write(target);
        } else {
          TrExpr(targetExpr);
        }
        wr.Write(" = ", target);
        TrAssignmentRhs(rhs);
        wr.WriteLine(";");
      }
    }

    void TrCallStmt(CallStmt s, string receiverReplacement, int indent) {
      Contract.Requires(s != null);
      Contract.Assert(s.Method != null);  // follows from the fact that stmt has been successfully resolved

      var lvalues = new List<string>();
      foreach (var lhs in s.Lhs) {
        lvalues.Add(CreateLvalue(lhs, indent));
      }
      var outTmps = new List<string>();
      for (int i = 0; i < s.Method.Outs.Count; i++) {
        Formal p = s.Method.Outs[i];
        if (!p.IsGhost) {
          string target = "_out" + tmpVarCount;
          tmpVarCount++;
          outTmps.Add(target);
          Indent(indent);
          wr.WriteLine("{0} {1};", TypeName(s.Lhs[i].Type), target);
        }
      }

      Indent(indent);
      if (receiverReplacement != null) {
        wr.Write("@" + receiverReplacement);
      } else if (s.Method.IsStatic) {
        wr.Write(TypeName(cce.NonNull(s.Receiver.Type)));
      } else {
        TrParenExpr(s.Receiver);
      }
      wr.Write(".@{0}(", s.Method.Name);

      string sep = "";
      for (int i = 0; i < s.Method.Ins.Count; i++) {
        Formal p = s.Method.Ins[i];
        if (!p.IsGhost) {
          wr.Write(sep);
          TrExpr(s.Args[i]);
          sep = ", ";
        }
      }

      foreach (var outTmp in outTmps) {
        wr.Write("{0}out {1}", sep, outTmp);
        sep = ", ";
      }
      wr.WriteLine(");");

      // assign to the actual LHSs
      int j = 0;
      for (int i = 0; i < s.Method.Outs.Count; i++) {
        Formal p = s.Method.Outs[i];
        if (!p.IsGhost) {
          Indent(indent);
          TrExpr(s.Lhs[i]);
          wr.WriteLine(" = {0};", outTmps[j]);
          j++;
        }
      }
      Contract.Assert(j == outTmps.Count);
    }
    
    int tmpVarCount = 0;
    
    void TrAssignmentRhs(AssignmentRhs rhs) {
      Contract.Requires(rhs != null);
      Contract.Requires(!(rhs is HavocRhs));
      if (rhs is ExprRhs) {
        ExprRhs e = (ExprRhs)rhs;
        TrExpr(e.Expr);
        
      } else {
        TypeRhs tp = (TypeRhs)rhs;
        if (tp.ArrayDimensions == null) {
          wr.Write("new {0}()", TypeName(tp.EType));
        } else {
          if (tp.EType is IntType || tp.EType.IsTypeParameter) {
            // Because the default constructor for BigInteger does not generate a valid BigInteger, we have
            // to excplicitly initialize the elements of an integer array.  This is all done in a helper routine.
            wr.Write("Dafny.Helpers.InitNewArray{0}<{1}>", tp.ArrayDimensions.Count, TypeName(tp.EType));
            string prefix = "(";
            foreach (Expression dim in tp.ArrayDimensions) {
              wr.Write(prefix);
              TrExpr(dim);
              prefix = ", ";
            }
            wr.Write(")");
          } else {
            wr.Write("new {0}", TypeName(tp.EType));
            string prefix = "[";
            foreach (Expression dim in tp.ArrayDimensions) {
              wr.Write("{0}(int)", prefix);
              TrExpr(dim);
              prefix = ", ";
            }
            wr.Write("]");
          }
        }
      }
    }
    
    void TrStmtList(List<Statement/*!*/>/*!*/ stmts, int indent) {Contract.Requires(cce.NonNullElements(stmts));
      foreach (Statement ss in stmts) {
        TrStmt(ss, indent + IndentAmount);
        if (ss.Labels != null) {
          Indent(indent);  // labels are not indented as much as the statements
          wr.WriteLine("after_{0}: ;", ss.Labels.UniqueId);
        }
      }
    }

    void TrVarDecl(VarDecl s, bool alwaysInitialize, int indent) {
      Contract.Requires(s != null);
      if (s.IsGhost) {
        // only emit non-ghosts (we get here only for local variables introduced implicitly by call statements)
        return;
      }

      Indent(indent);
      wr.Write("{0} @{1}", TypeName(s.Type), s.Name);
      if (alwaysInitialize) {
        // produce a default value
        wr.WriteLine(" = {0};", DefaultValue(s.Type));
      } else {
        wr.WriteLine(";");
      }
    }

    void MatchCasePrelude(string source, DatatypeCtor ctor, List<BoundVar/*!*/>/*!*/ arguments, int caseIndex, int caseCount, int indent) {
      Contract.Requires(source != null);
      Contract.Requires(ctor != null);
      Contract.Requires(cce.NonNullElements(arguments));
      // if (source._D is Dt_Ctor0) {
      //   FormalType f0 = ((Dt_Ctor0)source._D).a0;
      //   ...
      Indent(indent);
      wr.Write("{0}if (", caseIndex == 0 ? "" : "} else ");
      if (caseIndex == caseCount - 1) {
        wr.Write("true");
      } else {
        wr.Write("{0}._D is {1}", source, DtCtorName(ctor));
      }
      wr.WriteLine(") {");

      int k = 0;  // number of processed non-ghost arguments
      for (int m = 0; m < ctor.Formals.Count; m++) {
        Formal arg = ctor.Formals[m];
        if (!arg.IsGhost) {
          BoundVar bv = arguments[m];
          // FormalType f0 = ((Dt_Ctor0)source._D).a0;
          Indent(indent + IndentAmount);
          wr.WriteLine("{0} @{1} = (({2}){3}._D).@{4};",
            TypeName(bv.Type), bv.Name, DtCtorName(ctor), source, FormalName(arg, k));
          k++;
        }
      }
    }
        
    // ----- Expression ---------------------------------------------------------------------------

    void TrParenExpr(string prefix, Expression expr) {
      Contract.Requires(prefix != null);
      Contract.Requires(expr != null);
      wr.Write(prefix);
      TrParenExpr(expr);
    }

    void TrParenExpr(Expression expr) {
      Contract.Requires(expr != null);
      wr.Write("(");
      TrExpr(expr);
      wr.Write(")");
    }
    
    void TrExprList(List<Expression/*!*/>/*!*/ exprs) {
      Contract.Requires(cce.NonNullElements(exprs));
      wr.Write("(");
      string sep = "";
      foreach (Expression e in exprs) {
        wr.Write(sep);
        TrExpr(e);
        sep = ", ";
      }
      wr.Write(")");
    }

    void TrExpr(Expression expr)
    {
      Contract.Requires(expr != null);
      if (expr is LiteralExpr) {
        LiteralExpr e = (LiteralExpr)expr;
        if (e.Value == null) {
          wr.Write("null");
        } else if (e.Value is bool) {
          wr.Write((bool)e.Value ? "true" : "false");
        } else if (e.Value is BigInteger) {
          BigInteger i = (BigInteger)e.Value;
          if (new BigInteger(int.MinValue) <= i && i <= new BigInteger(int.MaxValue)) {
            wr.Write("new BigInteger({0})", i);
          } else {
            wr.Write("BigInteger.Parse(\"{0}\")", i);
          }
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
        }
        
      } else if (expr is ThisExpr) {
        wr.Write("this");
        
      } else if (expr is IdentifierExpr) {
        IdentifierExpr e = (IdentifierExpr)expr;
        wr.Write("@" + e.Var.Name);
      
      } else if (expr is SetDisplayExpr) {
        SetDisplayExpr e = (SetDisplayExpr)expr;
        Type elType = cce.NonNull((SetType)e.Type).Arg;
        wr.Write("{0}<{1}>.FromElements", DafnySetClass, TypeName(elType));
        TrExprList(e.Elements);
        
      } else if (expr is SeqDisplayExpr) {
        SeqDisplayExpr e = (SeqDisplayExpr)expr;
        Type elType = cce.NonNull((SeqType)e.Type).Arg;
        wr.Write("{0}<{1}>.FromElements", DafnySeqClass, TypeName(elType));
        TrExprList(e.Elements);
      
      } else if (expr is FieldSelectExpr) {
        FieldSelectExpr e = (FieldSelectExpr)expr;
        SpecialField sf = e.Field as SpecialField;
        if (sf != null) {
          wr.Write(sf.PreString);
          TrParenExpr(e.Obj);
          wr.Write(".{0}", sf.CompiledName);
          wr.Write(sf.PostString);
        } else {
          TrParenExpr(e.Obj);
          wr.Write(".@{0}", e.Field.Name);
        }
        
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        TrParenExpr(e.Seq);
        Contract.Assert(e.Seq.Type != null);
        if (e.Seq.Type.IsArrayType) {
          Contract.Assert(e.SelectOne);
          Contract.Assert(e.E0 != null && e.E1 == null);
          wr.Write("[(int)");
          TrParenExpr(e.E0);
          wr.Write("]");
        } else if (e.SelectOne) {
          Contract.Assert(e.E0 != null && e.E1 == null);
          TrParenExpr(".Select", e.E0);
        } else {
          if (e.E1 != null) {
            TrParenExpr(".Take", e.E1);
          }
          if (e.E0 != null) {
            TrParenExpr(".Drop", e.E0);
          }
        }
      
      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;
        TrParenExpr(e.Array);
        string prefix = "[";
        foreach (Expression idx in e.Indices) {
          wr.Write("{0}(int)", prefix);
          TrParenExpr(idx);
          prefix = ", ";
        }
        wr.Write("]");

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        TrParenExpr(e.Seq);
        wr.Write(".Update(");
        TrExpr(e.Index);
        wr.Write(", ");
        TrExpr(e.Value);
        wr.Write(")");
      
      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        Function f = cce.NonNull(e.Function);
        if (f.IsStatic) {
          wr.Write(TypeName(cce.NonNull(e.Receiver.Type)));
        } else {
          TrParenExpr(e.Receiver);
        }
        wr.Write(".@{0}", f.Name);
        wr.Write("(");
        string sep = "";
        for (int i = 0; i < e.Args.Count; i++) {
          if (!e.Function.Formals[i].IsGhost) {
            wr.Write(sep);
            TrExpr(e.Args[i]);
            sep = ", ";
          }
        }
        wr.Write(")");
      
      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        Contract.Assert(dtv.Ctor != null);  // since dtv has been successfully resolved
        wr.Write("new {0}(new {1}", dtv.DatatypeName, DtCtorName(dtv.Ctor));
        if (dtv.InferredTypeArgs.Count != 0) {
          wr.Write("<{0}>", TypeNames(dtv.InferredTypeArgs));
        }
        wr.Write("(");
        string sep = "";
        for (int i = 0; i < dtv.Arguments.Count; i++) {
          Formal formal = dtv.Ctor.Formals[i];
          if (!formal.IsGhost) {
            wr.Write(sep);
            TrExpr(dtv.Arguments[i]);
            sep = ", ";
          }
        }
        wr.Write("))");
          
      } else if (expr is OldExpr) {
        Contract.Assert(false); throw new cce.UnreachableException();  // 'old' is always a ghost (right?)
      
      } else if (expr is FreshExpr) {
        Contract.Assert(false); throw new cce.UnreachableException();  // 'fresh' is always a ghost
      
      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
        switch (e.Op) {
          case UnaryExpr.Opcode.Not:
            wr.Write("!");
            TrParenExpr(e.E);
            break;
          case UnaryExpr.Opcode.SetChoose:
            TrParenExpr(e.E);
            wr.Write(".Choose()");
            break;
          case UnaryExpr.Opcode.SeqLength:
            if (cce.NonNull(e.E.Type).IsArrayType) {
              wr.Write("new BigInteger(");
              TrParenExpr(e.E);
              wr.Write(".Length)");
            } else {
              TrParenExpr(e.E);
              wr.Write(".Length");
            }
            break;
          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
        }
      
      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        string opString = null;
        string preOpString = "";
        string callString = null;
        
        switch (e.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.Iff:
            opString = "==";  break;
          case BinaryExpr.ResolvedOpcode.Imp:
            preOpString = "!";  opString = "||";  break;
          case BinaryExpr.ResolvedOpcode.Or:
            opString = "||";  break;
          case BinaryExpr.ResolvedOpcode.And:
            opString = "&&";  break;
            
          case BinaryExpr.ResolvedOpcode.EqCommon: {
            Type t = cce.NonNull(e.E0.Type);
            if (t.IsDatatype || t.IsTypeParameter) {
              callString = "Equals";
            } else {
              opString = "==";
            }
            break;
          }
          case BinaryExpr.ResolvedOpcode.NeqCommon: {
            Type t = cce.NonNull(e.E0.Type);
            if (t.IsDatatype || t.IsTypeParameter) {
              preOpString = "!";
              callString = "Equals";
            } else {
              opString = "!=";
            }
            break;
          }
            
          case BinaryExpr.ResolvedOpcode.Lt:
            opString = "<";  break;
          case BinaryExpr.ResolvedOpcode.Le:
            opString = "<=";  break;
          case BinaryExpr.ResolvedOpcode.Ge:
            opString = ">=";  break;
          case BinaryExpr.ResolvedOpcode.Gt:
            opString = ">";  break;
          case BinaryExpr.ResolvedOpcode.Add:
            opString = "+";  break;
          case BinaryExpr.ResolvedOpcode.Sub:
            opString = "-";  break;
          case BinaryExpr.ResolvedOpcode.Mul:
            opString = "*";  break;
          case BinaryExpr.ResolvedOpcode.Div:
            wr.Write("Dafny.Helpers.EuclideanDivision(");
            TrParenExpr(e.E0);
            wr.Write(", ");
            TrExpr(e.E1);
            wr.Write(")");
            break;
          case BinaryExpr.ResolvedOpcode.Mod:
            wr.Write("Dafny.Helpers.EuclideanModulus(");
            TrParenExpr(e.E0);
            wr.Write(", ");
            TrExpr(e.E1);
            wr.Write(")");
            break;
          case BinaryExpr.ResolvedOpcode.SetEq:
          case BinaryExpr.ResolvedOpcode.SeqEq:
            callString = "Equals";  break;
          case BinaryExpr.ResolvedOpcode.SetNeq:
          case BinaryExpr.ResolvedOpcode.SeqNeq:
            preOpString = "!";  callString = "Equals";  break;

          case BinaryExpr.ResolvedOpcode.ProperSubset:
            callString = "IsProperSubsetOf";  break;
          case BinaryExpr.ResolvedOpcode.Subset:
            callString = "IsSubsetOf";  break;
          case BinaryExpr.ResolvedOpcode.Superset:
            callString = "IsSupersetOf";  break;
          case BinaryExpr.ResolvedOpcode.ProperSuperset:
            callString = "IsProperSupersetOf";  break;
          case BinaryExpr.ResolvedOpcode.Disjoint:
            callString = "IsDisjointFrom";  break;
          case BinaryExpr.ResolvedOpcode.InSet:
            TrParenExpr(e.E1);
            wr.Write(".Contains(");
            TrExpr(e.E0);
            wr.Write(")");
            break;
          case BinaryExpr.ResolvedOpcode.NotInSet:
            wr.Write("!");
            TrParenExpr(e.E1);
            wr.Write(".Contains(");
            TrExpr(e.E0);
            wr.Write(")");
            break;
          case BinaryExpr.ResolvedOpcode.Union:
            callString = "Union";  break;
          case BinaryExpr.ResolvedOpcode.Intersection:
            callString = "Intersect";  break;
          case BinaryExpr.ResolvedOpcode.SetDifference:
            callString = "Difference";  break;

          case BinaryExpr.ResolvedOpcode.ProperPrefix:
            callString = "IsProperPrefixOf";  break;
          case BinaryExpr.ResolvedOpcode.Prefix:
            callString = "IsPrefixOf";  break;
          case BinaryExpr.ResolvedOpcode.Concat:
            callString = "Concat";  break;
          case BinaryExpr.ResolvedOpcode.InSeq:
            TrParenExpr(e.E1);
            wr.Write(".Contains(");
            TrExpr(e.E0);
            wr.Write(")");
            break;
          case BinaryExpr.ResolvedOpcode.NotInSeq:
            wr.Write("!");
            TrParenExpr(e.E1);
            wr.Write(".Contains(");
            TrExpr(e.E0);
            wr.Write(")");
            break;

          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected binary expression
        }
        if (opString != null) {
          wr.Write(preOpString);
          TrParenExpr(e.E0);
          wr.Write(" {0} ", opString);
          TrParenExpr(e.E1);
        } else if (callString != null) {
          wr.Write(preOpString);
          TrParenExpr(e.E0);
          wr.Write(".{0}(", callString);
          TrExpr(e.E1);
          wr.Write(")");
        }
      
      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        Contract.Assert(e.Bounds != null);  // for non-ghost quantifiers, the resolver would have insisted on finding bounds
        var n = e.BoundVars.Count;
        Contract.Assert(e.Bounds.Count == n);
        for (int i = 0; i < n; i++) {
          var bound = e.Bounds[i];
          var bv = e.BoundVars[i];
          // emit:  Dafny.Helpers.QuantX(boundsInformation, isForall, bv => body)
          if (bound is QuantifierExpr.BoolBoundedPool) {
            wr.Write("Dafny.Helpers.QuantBool(");
          } else if (bound is QuantifierExpr.IntBoundedPool) {
            var b = (QuantifierExpr.IntBoundedPool)bound;
            wr.Write("Dafny.Helpers.QuantInt(");
            TrExpr(b.LowerBound);
            wr.Write(", ");
            TrExpr(b.UpperBound);
            wr.Write(", ");
          } else if (bound is QuantifierExpr.SetBoundedPool) {
            var b = (QuantifierExpr.SetBoundedPool)bound;
            wr.Write("Dafny.Helpers.QuantSet(");
            TrExpr(b.Set);
            wr.Write(", ");
          } else if (bound is QuantifierExpr.SeqBoundedPool) {
            var b = (QuantifierExpr.SeqBoundedPool)bound;
            wr.Write("Dafny.Helpers.QuantSeq(");
            TrExpr(b.Seq);
            wr.Write(", ");
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected BoundedPool type
          }
          wr.Write("{0}, ", expr is ForallExpr ? "true" : "false");
          wr.Write("@{0} => ", bv.Name);
        }
        TrExpr(e.LogicalBody());
        for (int i = 0; i < n; i++) {
          wr.Write(")");
        }

      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        // For "set i,j,k,l | R(i,j,k,l) :: Term(i,j,k,l)" where the term has type "G", emit something like:
        // ((ComprehensionDelegate<G>)delegate() {
        //   var _coll = new List<G>();
        //   foreach (L l in sq.Elements) {
        //     foreach (K k in st.Elements) {
        //       for (BigInteger j = Lo; j < Hi; j++) {
        //         for (bool i in Helper.AllBooleans) {
        //           if (R(i,j,k,l)) {
        //             _coll.Add(Term(i,j,k,l));
        //           }
        //         }
        //       }
        //     }
        //   }
        //   return Dafny.Set<G>.FromCollection(_coll);
        // })()
        Contract.Assert(e.Bounds != null);  // the resolver would have insisted on finding bounds
        var typeName = TypeName(((SetType)e.Type).Arg);
        wr.Write("((Dafny.Helpers.ComprehensionDelegate<{0}>)delegate() {{ ", typeName);
        wr.Write("var _coll = new System.Collections.Generic.List<{0}>(); ", typeName);
        var n = e.BoundVars.Count;
        Contract.Assert(e.Bounds.Count == n);
        for (int i = 0; i < n; i++) {
          var bound = e.Bounds[i];
          var bv = e.BoundVars[i];
          if (bound is QuantifierExpr.BoolBoundedPool) {
            wr.Write("foreach (var @{0} in Dafny.Helpers.AllBooleans) {{ ", bv.Name);
          } else if (bound is QuantifierExpr.IntBoundedPool) {
            var b = (QuantifierExpr.IntBoundedPool)bound;
            wr.Write("for (var @{0} = ", bv.Name);
            TrExpr(b.LowerBound);
            wr.Write("; @{0} < ", bv.Name);
            TrExpr(b.UpperBound);
            wr.Write("; @{0}++) {{ ", bv.Name);
          } else if (bound is QuantifierExpr.SetBoundedPool) {
            var b = (QuantifierExpr.SetBoundedPool)bound;
            wr.Write("foreach (var @{0} in (", bv.Name);
            TrExpr(b.Set);
            wr.Write(").Elements) { ");
          } else if (bound is QuantifierExpr.SeqBoundedPool) {
            var b = (QuantifierExpr.SeqBoundedPool)bound;
            wr.Write("foreach (var @{0} in (", bv.Name);
            TrExpr(b.Seq);
            wr.Write(").Elements) { ");
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected BoundedPool type
          }
        }
        wr.Write("if (");
        TrExpr(e.Range);
        wr.Write(") { _coll.Add(");
        TrExpr(e.Term);
        wr.Write("); }");
        for (int i = 0; i < n; i++) {
          wr.Write("}");
        }
        wr.Write("return Dafny.Set<{0}>.FromCollection(_coll); ", typeName);
        wr.Write("})()");

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        wr.Write("(");
        TrExpr(e.Test);
        wr.Write(") ? (");
        TrExpr(e.Thn);
        wr.Write(") : (");
        TrExpr(e.Els);
        wr.Write(")");

      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        TrExpr(e.ResolvedExpression);

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }
  }
}
