//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Numerics;
using System.IO;
using Microsoft.Contracts;
using Bpl = Microsoft.Boogie;
using System.Text;

namespace Microsoft.Dafny {
  public class Compiler {
    public Compiler(TextWriter! wr) {
      this.wr = wr;
    }

    TextWriter! wr;
    
    public int ErrorCount;
    void Error(string! msg, params object[] args) {
      string s = string.Format("Compilation error: " + msg, args);
      Console.WriteLine(s);
      wr.WriteLine("/* {0} */", s);
      ErrorCount++;
    }
    
    void ReadRuntimeSystem() {
      string! codebase = (!) System.IO.Path.GetDirectoryName((!)System.Reflection.Assembly.GetExecutingAssembly().Location);
      string! path = System.IO.Path.Combine(codebase, "DafnyRuntime.cs");
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

    public void Compile(Program! program) {
      wr.WriteLine("// Dafny program {0} compiled into C#", program.Name);
      wr.WriteLine();
      ReadRuntimeSystem();

      foreach (ModuleDecl m in program.Modules) {
        int indent = 0;
        if (!m.IsDefaultModule) {
          wr.WriteLine("namespace {0} {{", m.Name);
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
            wr.Write("public class {0}", cl.Name);
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

    void CompileDatatypeConstructors(DatatypeDecl! dt, int indent)
    {
      foreach (DatatypeCtor ctor in dt.Ctors) {
        // class Dt_Ctor<T,U> : Base_Dt<T> {
        //   Fields;
        //   public Dt_Ctor(arguments) {
        //     Fields = arguments;
        //   }
        // }
        Indent(indent);
        wr.Write("public class {0}", DtCtorName(ctor));
        if (dt.TypeArgs.Count != 0 || ctor.TypeArgs.Count != 0) {
          wr.Write("<");
          string sep = "";
          if (dt.TypeArgs.Count != 0) {
            wr.Write("{0}", TypeParameters(dt.TypeArgs));
            sep = ",";
          }
          if (ctor.TypeArgs.Count != 0) {
            wr.Write("{0}{1}", sep, TypeParameters(ctor.TypeArgs));
          }
          wr.Write(">");
        }
        wr.Write(" : Base_{0}", dt.Name);
        wr.WriteLine(" {");
        if (dt.TypeArgs.Count != 0) {
          wr.Write("<{0}>", TypeParameters(dt.TypeArgs));
        }
        int ind = indent + IndentAmount;

        int i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            Indent(ind);
            wr.WriteLine("public readonly {0} {1};", TypeName(arg.Type), FormalName(arg, i));
            i++;
          }
        }

        Indent(ind);
        wr.Write("public {0}(", DtCtorName(ctor));
        WriteFormals(ctor.Formals);
        wr.WriteLine(") {");
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            Indent(ind + IndentAmount);
            wr.WriteLine("this.{0} = {0};", FormalName(arg, i));
            i++;
          }
        }
        Indent(ind);  wr.WriteLine("}");

        Indent(indent);  wr.WriteLine("}");
      }
    }
    
    void CompileDatatypeStruct(DatatypeDecl! dt, int indent) {
      // public struct Dt<T> {
      //   Base_Dt<T> d;
      //   public Base_Dt<T> D {
      //     get { if (d == null) { d = Default; } return d; }
      //   }
      //   public Dt(Base_Dt<T> d) { this.d = d; }
      //   public static Base_Dt<T> Default {
      //     get { return ...; }
      //   }
      //   public override bool Equals(object other) {
      //     return other is Dt<T> && D.Equals(((Dt<T>)other).D);
      //   }
      //   public override int GetHashCode() { return D.GetHashCode(); }
      // }
      string DtT = dt.Name;
      if (dt.TypeArgs.Count != 0) {
        DtT += "<" + TypeParameters(dt.TypeArgs) + ">";
      }
      
      Indent(indent);
      wr.WriteLine("public struct {0} {{", DtT);
      int ind = indent + IndentAmount;
      
      Indent(ind);
      wr.WriteLine("Base_{0} d;", DtT);
      
      Indent(ind);
      wr.WriteLine("public Base_{0} D {{", DtT);
      Indent(ind + IndentAmount);
      wr.WriteLine("get { if (d == null) { d = Default; } return d; }");
      Indent(ind);  wr.WriteLine("}");
      
      Indent(ind);
      wr.WriteLine("public {0}(Base_{1} d) {{ this.d = d; }}", dt.Name, DtT);
      
      Indent(ind);
      wr.WriteLine("public static Base_{0} Default {{", DtT);
      Indent(ind + IndentAmount);
      wr.Write("get { return ");
      wr.Write("new {0}", DtCtorName((!)dt.DefaultCtor));
      // todo: type parameters
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
      wr.WriteLine("return other is {0} && D.Equals((({0})other).D);", DtT);
      Indent(ind);  wr.WriteLine("}");

      Indent(ind);
      wr.WriteLine("public override int GetHashCode() { return D.GetHashCode(); }");
      
      Indent(indent);
      wr.WriteLine("}");
    }
    
    void WriteFormals(List<Formal!>! formals)
    {
      int i = 0;
      string sep = "";
      foreach (Formal arg in formals) {
        if (!arg.IsGhost) {
          string name = FormalName(arg, i);
          wr.Write("{0}{1}{2} {3}", sep, arg.InParam ? "" : "out ", TypeName(arg.Type), name);
          sep = ", ";
          i++;
        }
      }
    }
    
    string! FormalName(Formal! formal, int i) {
      return formal.Name.StartsWith("#") ? "a" + i : formal.Name;
    }
    
    string! DtCtorName(DatatypeCtor! ctor) {
      return ((!)ctor.EnclosingDatatype).Name + "_" + ctor.Name;
    }
        
    void CompileClassMembers(ClassDecl! c, int indent)
    {
      foreach (MemberDecl member in c.Members) {
        if (member is Field) {
          Field f = (Field)member;
          if (!f.IsGhost) {
            Indent(indent);
            wr.WriteLine("public {0} {1} = {2};", TypeName(f.Type), f.Name, DefaultValue(f.Type));
          }
          
        } else if (member is Function) {
          Function f = (Function)member;
          if (f.IsGhost) {
            // nothing to compile
          } else if (f.Body == null) {
            Error("Function {0} has no body", f.FullName);
          } else {
            Indent(indent);
            wr.Write("public {0}{1} {2}", f.IsStatic ? "static " : "", TypeName(f.ResultType), f.Name);
            if (f.TypeArgs.Count != 0) {
              wr.Write("<{0}>", TypeParameters(f.TypeArgs));
            }
            wr.Write("(");
            WriteFormals(f.Formals);
            wr.WriteLine(") {");
            if (f.Body is MatchExpr) {
              MatchExpr me = (MatchExpr)f.Body;
              // Type source = e;
              // if (source.D is Dt_Ctor0) {
              //   FormalType f0 = ((Dt_Ctor0)source.D).a0;
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
              wr.Write("{0} {1} = ", TypeName((!)me.Source.Type), source);
              TrExpr(me.Source);
              wr.WriteLine(";");

              int i = 0;
              foreach (MatchCaseExpr mc in me.Cases) {
                MatchCasePrelude(source, (!)mc.Ctor, mc.Arguments, i, me.Cases.Count, indent + IndentAmount);
                
                Indent(indent + 2*IndentAmount);
                wr.Write("return ");
                TrExpr(mc.Body);
                wr.WriteLine(";");
                i++;
              }

              Indent(indent);  wr.WriteLine("}");

            } else {
              Indent(indent + IndentAmount);
              wr.Write("return ");
              TrExpr(f.Body);
              wr.WriteLine(";");
            }
            Indent(indent);  wr.WriteLine("}");
          }
          
        } else if (member is Method) {
          Method m = (Method)member;
          if (!m.IsGhost) {
            Indent(indent);
            wr.Write("public {0}void {1}", m.IsStatic ? "static " : "", m.Name);
            if (m.TypeArgs.Count != 0) {
              wr.Write("<{0}>", TypeParameters(m.TypeArgs));
            }
            wr.Write("(");
            WriteFormals(m.Ins);
            if (m.Ins.Count != 0 && m.Outs.Count != 0) {
              wr.Write(", ");
            }
            WriteFormals(m.Outs);
            wr.WriteLine(")");
            Indent(indent);  wr.WriteLine("{");
            foreach (Formal p in m.Outs) {
              if (!p.IsGhost) {
                Indent(indent + IndentAmount);
                wr.WriteLine("{0} = {1};", p.Name, DefaultValue(p.Type));
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
              ClassDecl cl = (!)m.EnclosingClass;
              Indent(indent + IndentAmount);
              wr.Write("{0} b = new {0}", cl.Name);
              if (cl.TypeArgs.Count != 0) {
                // instantiate every parameter, it doesn't particularly matter how
                wr.Write("<");
                string sep = "";
                for (int i = 0; i < cl.TypeArgs.Count; i++) {
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

        } else {
          assert false;  // unexpected member
        }
      }
    }
    
    // ----- Type ---------------------------------------------------------------------------------
    
    readonly string! DafnySetClass = "Dafny.Set";
    readonly string! DafnySeqClass = "Dafny.Sequence";
    
    string! TypeName(Type! type)
    {
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
        Type elType = UserDefinedType.ArrayElementType(type);
        return TypeName(elType) + "[]";
      } else if (type is UserDefinedType) {
        UserDefinedType udt = (UserDefinedType)type;
        string s = udt.Name;
        if (udt.TypeArgs.Count != 0) {
          if (exists{Type argType in udt.TypeArgs; argType is ObjectType}) {
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
        assert false;  // unexpected type
      }
    }

    string! TypeNames(List<Type!>! types) {
      string s = "";
      string sep = "";
      foreach (Type t in types) {
        s += sep + TypeName(t);
        sep = ",";
      }
      return s;
    }
    
    string! TypeParameters(List<TypeParameter!>! targs) {
      string s = "";
      string sep = "";
      foreach (TypeParameter tp in targs) {
        s += sep + tp.Name;
        sep = ",";
      }
      return s;
    }
    
    string! DefaultValue(Type! type)
    {
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
        string s = udt.Name;
        if (udt.TypeArgs.Count != 0) {
          s += "<" + TypeNames(udt.TypeArgs) + ">";
        }
        return s + ".Default";
      } else if (type.IsTypeParameter) {
        UserDefinedType udt = (UserDefinedType)type;
        return "default(" + udt.Name + ")";
      } else if (type is SetType) {
        return DafnySetClass + "<" + TypeName(((SetType)type).Arg) + ">.Empty";
      } else if (type is SeqType) {
        return DafnySeqClass + "<" + TypeName(((SeqType)type).Arg) + ">.Empty";
      } else {
        assert false;  // unexpected type
      }
    }
    
    // ----- Stmt ---------------------------------------------------------------------------------
    
    void TrStmt(Statement! stmt, int indent)
    {
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
            assert arg.E != null;
            TrExpr(arg.E);
          }
          wr.WriteLine(");");
        }
      } else if (stmt is BreakStmt) {
        BreakStmt s = (BreakStmt)stmt;
        Indent(indent);
        if (s.TargetLabel == null) {
          // use the scoping rules of C#
          wr.WriteLine("break;");
        } else {
          wr.WriteLine("goto after_{0};", s.TargetLabel);
        }
      } else if (stmt is ReturnStmt) {
        Indent(indent);
        wr.WriteLine("return;");
      } else if (stmt is AssignStmt) {
        AssignStmt s = (AssignStmt)stmt;
        if (s.Lhs is SeqSelectExpr && !((SeqSelectExpr)s.Lhs).SelectOne) {
          SeqSelectExpr sel = (SeqSelectExpr)s.Lhs;
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
          Indent(indent);  wr.Write("{0} {1} = ", TypeName((!)sel.Seq.Type), arr);  TrExpr(sel.Seq);  wr.WriteLine(";");
          Indent(indent);  wr.Write("int {0} = ", low);
          if (sel.E0 == null) {
            wr.Write("0");
          } else {
            TrExpr(sel.E0);
          }
          wr.WriteLine(";");
          Indent(indent);  wr.Write("int {0} = ", high);
          if (sel.E1 == null) {
            wr.Write("new BigInteger(arr.Length)");
          } else {
            TrExpr(sel.E1);
          }
          wr.WriteLine(";");
          Indent(indent);  wr.Write("{0} {1} = ", TypeName((!)sel.Type), rhs);  TrAssignmentRhs(s.Rhs);  wr.WriteLine(";");
          Indent(indent);
          wr.WriteLine("for (BigInteger {0} = {1}; {0} < {2}; {0}++) {{", i, low, high);
          Indent(indent + IndentAmount);
          wr.WriteLine("{0}[(int)({1})] = {2};", arr, i, rhs);
          Indent(indent);
          wr.WriteLine(";");

        } else {
          Indent(indent);
          TrExpr(s.Lhs);
          if (!(s.Rhs is HavocRhs)) {
            wr.Write(" = ");
            TrAssignmentRhs(s.Rhs);
          }
          wr.WriteLine(";");
        }
        
      } else if (stmt is VarDecl) {
        TrVarDecl((VarDecl)stmt, true, indent);
        
      } else if (stmt is CallStmt) {
        CallStmt s = (CallStmt)stmt;

        foreach (VarDecl local in s.NewVars) {
          TrVarDecl(local, false, indent);
        }

        assert s.Method != null;  // follows from the fact that stmt has been successfully resolved
        Indent(indent);
        if (s.Method.IsStatic) {
          wr.Write(TypeName((!)s.Receiver.Type));
        } else {
          TrParenExpr(s.Receiver);
        }
        wr.Write(".{0}(", s.Method.Name);

        string sep = "";
        for (int i = 0; i < s.Method.Ins.Count; i++) {
          Formal p = s.Method.Ins[i];
          if (!p.IsGhost) {
            wr.Write(sep);
            TrExpr(s.Args[i]);
            sep = ", ";
          }
        }
        for (int i = 0; i < s.Method.Outs.Count; i++) {
          Formal p = s.Method.Outs[i];
          if (!p.IsGhost) {
            wr.Write("{0}out ", sep);
            TrExpr(s.Lhs[i]);
            sep = ", ";
          }
        }

        wr.WriteLine(");");
        
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
        if (s.Els != null) {
          Indent(indent);  wr.WriteLine("else");
          TrStmt(s.Els, indent);
        }
        
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
        string RhsType = TypeName((!)s.BodyAssign.Lhs.Type);
        
        Indent(indent);
        wr.WriteLine("List<Pair<{0},{1}>> {2} = new List<Pair<{0},{1}>>();", TType, RhsType, pu);
        
        Indent(indent);
        wr.Write("foreach ({0} {1} in (", TType, s.BoundVar.Name);
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
        wr.Write("{0}.Add(new Pair<{1},{2}>({3}, ", pu, TType, RhsType, s.BoundVar.Name);
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
        // if (source.D is Dt_Ctor0) {
        //   FormalType f0 = ((Dt_Ctor0)source.D).a0;
        //   ...
        //   Body0;
        // } else if (...) {
        //   ...
        // } else if (true) {
        //   ...
        // }

        string source = "_source" + tmpVarCount;
        tmpVarCount++;
        Indent(indent);
        wr.Write("{0} {1} = ", TypeName((!)s.Source.Type), source);
        TrExpr(s.Source);
        wr.WriteLine(";");
        
        int i = 0;
        foreach (MatchCaseStmt mc in s.Cases) {
          MatchCasePrelude(source, (!)mc.Ctor, mc.Arguments, i, s.Cases.Count, indent);
          TrStmtList(mc.Body, indent);
          i++;
        }
        Indent(indent);  wr.WriteLine("}");

      } else {
        assert false;  // unexpected statement
      }
    }
    
    int tmpVarCount = 0;
    
    void TrAssignmentRhs(AssignmentRhs! rhs)
      requires !(rhs is HavocRhs);
    {
      if (rhs is ExprRhs) {
        ExprRhs e = (ExprRhs)rhs;
        TrExpr(e.Expr);
        
      } else {
        TypeRhs tp = (TypeRhs)rhs;
        if (tp.ArraySize == null) {
          wr.Write("new {0}()", TypeName(tp.EType));
        } else {
          if (tp.EType is IntType || tp.EType.IsTypeParameter) {
            // Because the default constructor for BigInteger does not generate a valid BigInteger, we have
            // to excplicitly initialize the elements of an integer array.  This is all done in a helper routine.
            wr.Write("Dafny.Helpers.InitNewArray<{0}>(", TypeName(tp.EType));
            TrExpr(tp.ArraySize);
            wr.Write(")");
          } else {
            wr.Write("new {0}[(int)", TypeName(tp.EType));
            TrExpr(tp.ArraySize);
            wr.Write("]");
          }
        }
      }
    }
    
    void TrStmtList(List<Statement!>! stmts, int indent) {
      List<string!> currentLabels = null;
      foreach (Statement ss in stmts) {
        if (ss is LabelStmt) {
          LabelStmt s = (LabelStmt)ss;
          if (currentLabels == null) {
            currentLabels = new List<string!>();
          }
          currentLabels.Add(s.Label);
        } else {
          TrStmt(ss, indent + IndentAmount);
          SpillLabels(currentLabels, indent);
          currentLabels = null;
        }
      }
      SpillLabels(currentLabels, indent);
    }

    void SpillLabels(List<string!> labels, int indent) {
      if (labels != null) {
        foreach (string label in labels) {
          Indent(indent);
          wr.WriteLine("after_{0}: ;", label);
        }
      }
    }

    void TrVarDecl(VarDecl! s, bool alwaysInitialize, int indent) {
      Indent(indent);
      wr.Write("{0} {1}", TypeName(s.Type), s.Name);
      if (s.Rhs != null) {
        wr.Write(" = ");
        TrAssignmentRhs(s.Rhs);
      } else if (alwaysInitialize) {
        // produce a default value
        wr.Write(" = {0}", DefaultValue(s.Type));
      }
      wr.WriteLine(";");
    }

    void MatchCasePrelude(string! source, DatatypeCtor! ctor, List<BoundVar!>! arguments, int caseIndex, int caseCount, int indent) {
      // if (source.D is Dt_Ctor0) {
      //   FormalType f0 = ((Dt_Ctor0)source.D).a0;
      //   ...
      Indent(indent);
      wr.Write("{0}if (", caseIndex == 0 ? "" : "} else ");
      if (caseIndex == caseCount - 1) {
        wr.Write("true");
      } else {
        wr.Write("{0}.D is {1}", source, DtCtorName(ctor));
      }
      wr.WriteLine(") {");

      int k = 0;  // number of processed non-ghost arguments
      for (int m = 0; m < ctor.Formals.Count; m++) {
        Formal arg = ctor.Formals[m];
        if (!arg.IsGhost) {
          BoundVar bv = arguments[m];
          // FormalType f0 = ((Dt_Ctor0)source.D).a0;
          Indent(indent + IndentAmount);
          wr.WriteLine("{0} {1} = (({2}){3}.D).{4};",
            TypeName(bv.Type), bv.Name, DtCtorName(ctor), source, FormalName(arg, k));
          k++;
        }
      }
    }
        
    // ----- Expression ---------------------------------------------------------------------------

    void TrParenExpr(string! prefix, Expression! expr) {
      wr.Write(prefix);
      TrParenExpr(expr);
    }

    void TrParenExpr(Expression! expr) {
      wr.Write("(");
      TrExpr(expr);
      wr.Write(")");
    }
    
    void TrExprList(List<Expression!>! exprs) {
      wr.Write("(");
      string sep = "";
      foreach (Expression e in exprs) {
        wr.Write(sep);
        TrExpr(e);
        sep = ", ";
      }
      wr.Write(")");
    }

    void TrExpr(Expression! expr)
    {
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
          assert false;  // unexpected literal
        }
        
      } else if (expr is ThisExpr) {
        wr.Write("this");
        
      } else if (expr is IdentifierExpr) {
        IdentifierExpr e = (IdentifierExpr)expr;
        wr.Write(((!)e.Var).Name);
      
      } else if (expr is SetDisplayExpr) {
        SetDisplayExpr e = (SetDisplayExpr)expr;
        Type elType = ((SetType!)e.Type).Arg;
        wr.Write("{0}<{1}>.FromElements", DafnySetClass, TypeName(elType));
        TrExprList(e.Elements);
        
      } else if (expr is SeqDisplayExpr) {
        SeqDisplayExpr e = (SeqDisplayExpr)expr;
        Type elType = ((SeqType!)e.Type).Arg;
        wr.Write("{0}<{1}>.FromElements", DafnySeqClass, TypeName(elType));
        TrExprList(e.Elements);
      
      } else if (expr is FieldSelectExpr) {
        FieldSelectExpr e = (FieldSelectExpr)expr;
        TrParenExpr(e.Obj);
        wr.Write(".{0}", e.FieldName);
        
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        TrParenExpr(e.Seq);
        assert e.Seq.Type != null;
        if (e.Seq.Type.IsArrayType) {
          assert e.SelectOne;
          assert e.E0 != null && e.E1 == null;
          wr.Write("[(int)");
          TrParenExpr(e.E0);
          wr.Write("]");
        } else if (e.SelectOne) {
          assert e.E0 != null && e.E1 == null;
          TrParenExpr(".Select", e.E0);
        } else {
          if (e.E1 != null) {
            TrParenExpr(".Take", e.E1);
          }
          if (e.E0 != null) {
            TrParenExpr(".Drop", e.E0);
          }
        }
      
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
        Function f = (!)e.Function;
        if (f.IsStatic) {
          wr.Write(TypeName((!)e.Receiver.Type));
        } else {
          TrParenExpr(e.Receiver);
        }
        wr.Write(".{0}", f.Name);
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
        assert dtv.Ctor != null;  // since dtv has been successfully resolved
        wr.Write("new {0}(new {0}", dtv.DatatypeName, DtCtorName(dtv.Ctor));
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
        assert false;  // 'old' is always a ghost (right?)
      
      } else if (expr is FreshExpr) {
        assert false;  // 'fresh' is always a ghost
      
      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
        switch (e.Op) {
          case UnaryExpr.Opcode.Not:
            wr.Write("!");
            TrParenExpr(e.E);
            break;
          case UnaryExpr.Opcode.SeqLength:
            if (((!)e.E.Type).IsArrayType) {
              wr.Write("new BigInteger(");
              TrParenExpr(e.E);
              wr.Write(".Length)");
            } else {
              TrParenExpr(e.E);
              wr.Write(".Length");
            }
            break;
          default:
            assert false;  // unexpected unary expression
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
            Type t = (!)e.E0.Type;
            if (t.IsDatatype || t.IsTypeParameter) {
              callString = "Equals";
            } else {
              opString = "==";
            }
            break;
          }
          case BinaryExpr.ResolvedOpcode.NeqCommon: {
            Type t = (!)e.E0.Type;
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
            opString = "/";  break;
          case BinaryExpr.ResolvedOpcode.Mod:
            opString = "%";  break;

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
            assert false;  // unexpected binary expression
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
        assert false;  // a quantifier is always a ghost
      
      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        wr.Write("(");
        TrExpr(e.Test);
        wr.Write(") ? (");
        TrExpr(e.Thn);
        wr.Write(") : (");
        TrExpr(e.Els);
        wr.Write(")");
         
      } else {
        assert false;  // unexpected expression
      }
    }
  }
}
