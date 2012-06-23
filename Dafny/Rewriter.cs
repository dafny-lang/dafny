using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny
{
  [ContractClass(typeof(IRewriterContracts))]
  public interface IRewriter
  {
    void PreResolve(ModuleDecl m);
    void PostResolve(ModuleDecl m);
  }
  [ContractClassFor(typeof(IRewriter))]
  abstract class IRewriterContracts : IRewriter
  {
    public void PreResolve(ModuleDecl m) {
      Contract.Requires(m != null);
    }
    public void PostResolve(ModuleDecl m) {
      Contract.Requires(m != null);
    }
  }

  /// <summary>
  /// AutoContracts is an experimental feature that will fill much of the dynamic-frames boilerplate
  /// into a class.  From the user's perspective, what needs to be done is simply:
  ///  - mark the class with {:autocontracts}
  ///  - declare a function (or predicate) called Valid()
  ///  
  /// AutoContracts will then:
  ///
  /// Declare:
  ///    ghost var Repr: set(object);
  ///
  /// For function/predicate Valid(), insert:
  ///    reads this, Repr;
  /// Into body of Valid(), insert (at the beginning of the body):
  ///    this in Repr && null !in Repr
  /// and also insert, for every array-valued field A declared in the class:
  ///    (A != null ==> A in Repr) &&
  /// and for every field F of a class type T where T has a field called Repr, also insert:
  ///    (F != null ==> F in Repr && F.Repr SUBSET Repr && this !in Repr)
  /// Except, if A or F is declared with {:autocontracts false}, then the implication will not
  /// be added.
  ///
  /// For every constructor, add:
  ///    modifies this;
  ///    ensures Valid() && fresh(Repr - {this});
  /// At the end of the body of the constructor, add:
  ///    Repr := {this};
  ///    if (A != null) { Repr := Repr + {A}; }
  ///    if (F != null) { Repr := Repr + {F} + F.Repr; }
  ///
  /// For every method, add:
  ///    requires Valid();
  ///    modifies Repr;
  ///    ensures Valid() && fresh(Repr - old(Repr));
  /// At the end of the body of the method, add:
  ///    if (A != null) { Repr := Repr + {A}; }
  ///    if (F != null) { Repr := Repr + {F} + F.Repr; }
  /// </summary>
  public class AutoContractsRewriter : IRewriter
  {
    public void PreResolve(ModuleDecl m) {
      foreach (var d in m.TopLevelDecls) {
        bool sayYes = true;
        if (d is ClassDecl && Attributes.ContainsBool(d.Attributes, "autocontracts", ref sayYes) && sayYes) {
          ProcessClassPreResolve((ClassDecl)d);
        }
      }
    }

    void ProcessClassPreResolve(ClassDecl cl) {
      // Add:  ghost var Repr: set<object>;
      // ...unless a field with that name is already present
      if (!cl.Members.Exists(member => member is Field && member.Name == "Repr")) {
        Type ty = new SetType(new ObjectType());
        cl.Members.Add(new Field(cl.tok, "Repr", true, ty, null));
      }

      foreach (var member in cl.Members) {
        bool sayYes = true;
        if (Attributes.ContainsBool(member.Attributes, "autocontracts", ref sayYes) && !sayYes) {
          continue;
        }
        var tok = member.tok;
        if (member is Function && member.Name == "Valid" && !member.IsStatic) {
          var valid = (Function)member;
          // reads this;
          valid.Reads.Add(new FrameExpression(new ThisExpr(tok), null));
          // reads Repr;
          valid.Reads.Add(new FrameExpression(new FieldSelectExpr(tok, new ImplicitThisExpr(tok), "Repr"), null));
        } else if (member is Constructor) {
          var ctor = (Constructor)member;
          // modifies this;
          ctor.Mod.Expressions.Add(new FrameExpression(new ImplicitThisExpr(tok), null));
          // ensures Valid();
          ctor.Ens.Insert(0, new MaybeFreeExpression(new FunctionCallExpr(tok, "Valid", new ImplicitThisExpr(tok), tok, new List<Expression>())));
          // ensures fresh(Repr - {this});
          var freshness = new FreshExpr(tok, new BinaryExpr(tok, BinaryExpr.Opcode.Sub,
            new FieldSelectExpr(tok, new ImplicitThisExpr(tok), "Repr"),
            new SetDisplayExpr(tok, new List<Expression>() { new ThisExpr(tok) })));
          ctor.Ens.Insert(1, new MaybeFreeExpression(freshness));
        } else if (member is Method && !member.IsStatic) {
          var m = (Method)member;
          // requires Valid();
          m.Req.Insert(0, new MaybeFreeExpression(new FunctionCallExpr(tok, "Valid", new ImplicitThisExpr(tok), tok, new List<Expression>())));
          // If this is a mutating method, we should also add a modifies clause and a postcondition, but we don't do that if it's
          // a simple query method.  However, we won't know if it's a simple query method until after resolution, so we'll add the
          // rest of the spec then.
        }
      }
    }

    public void PostResolve(ModuleDecl m) {
      foreach (var d in m.TopLevelDecls) {
        bool sayYes = true;
        if (d is ClassDecl && Attributes.ContainsBool(d.Attributes, "autocontracts", ref sayYes) && sayYes) {
          ProcessClassPostResolve((ClassDecl)d);
        }
      }
    }

    void ProcessClassPostResolve(ClassDecl cl) {
      // Find all fields of a reference type, and make a note of whether or not the reference type has a Repr field.
      // Also, find the Repr field and the function Valid in class "cl"
      Field ReprField = null;
      Function Valid = null;
      var subobjects = new List<Tuple<Field, Field>>();
      foreach (var member in cl.Members) {
        var field = member as Field;
        if (field != null) {
          bool sayYes = true;
          if (field.Name == "Repr") {
            ReprField = field;
          } else if (Attributes.ContainsBool(field.Attributes, "autocontracts", ref sayYes) && !sayYes) {
            // ignore this field
          } else if (field.Type is ObjectType) {
            subobjects.Add(new Tuple<Field, Field>(field, null));
          } else if (field.Type.IsRefType) {
            var rcl = (ClassDecl)((UserDefinedType)field.Type).ResolvedClass;
            Field rRepr = null;
            foreach (var memb in rcl.Members) {
              var f = memb as Field;
              if (f != null && f.Name == "Repr") {
                rRepr = f;
                break;
              }
            }
            subobjects.Add(new Tuple<Field, Field>(field, rRepr));
          }
        } else if (member is Function && member.Name == "Valid" && !member.IsStatic) {
          var fn = (Function)member;
          if (fn.Formals.Count == 0 && fn.ResultType is BoolType) {
            Valid = fn;
          }
        }
      }
      Contract.Assert(ReprField != null);  // we expect there to be a "Repr" field, since we added one in PreResolve

      Type ty = new UserDefinedType(cl.tok, cl.Name, cl, new List<Type>());
      var self = new ThisExpr(cl.tok);
      self.Type = ty;
      var implicitSelf = new ImplicitThisExpr(cl.tok);
      implicitSelf.Type = ty;
      var Repr = new FieldSelectExpr(cl.tok, implicitSelf, "Repr");
      Repr.Field = ReprField;
      Repr.Type = ReprField.Type;
      var cNull = new LiteralExpr(cl.tok);
      cNull.Type = new ObjectType();

      foreach (var member in cl.Members) {
        bool sayYes = true;
        if (Attributes.ContainsBool(member.Attributes, "autocontracts", ref sayYes) && !sayYes) {
          continue;
        }
        var tok = member.tok;
        if (member is Function && member.Name == "Valid" && !member.IsStatic) {
          var valid = (Function)member;
          if (valid.IsGhost && valid.ResultType is BoolType) {
            var c0 = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.InSet, self, Repr);  // this in Repr
            var c1 = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.NotInSet, cNull, Repr);  // null !in Repr
            var c = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.And, c0, c1);

            foreach (var ff in subobjects) {
              var F = new FieldSelectExpr(tok, implicitSelf, ff.Item1.Name);
              F.Field = ff.Item1;
              F.Type = ff.Item1.Type;

              c0 = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.NeqCommon, F, cNull);
              c1 = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.InSet, F, Repr);
              if (ff.Item2 == null) {
                // F != null ==> F in Repr  (so, nothing else to do)
              } else {
                // F != null ==> F in Repr && F.Repr <= Repr && this !in F.Repr
                var FRepr = new FieldSelectExpr(tok, F, ff.Item2.Name);
                FRepr.Field = ff.Item2;
                FRepr.Type = ff.Item2.Type;
                var c2 = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.Subset, FRepr, Repr);
                var c3 = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.NotInSet, self, FRepr);
                c1 = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.And, c1, BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.And, c2, c3));
              }
              c = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.And, c, BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.Imp, c0, c1));
            }

            if (valid.Body == null) {
              valid.Body = c;
            } else {
              valid.Body = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.And, c, valid.Body);
            }
          }

        } else if (member is Constructor) {
          var ctor = (Constructor)member;
          if (ctor.Body == null) {
            ctor.Body = new BlockStmt(tok, new List<Statement>());
          }
          // TODO: these assignments should be included on every return path
          var bodyStatements = ((BlockStmt)ctor.Body).Body;
          // Repr := {this};
          var e = new SetDisplayExpr(tok, new List<Expression>() { self });
          e.Type = new SetType(new ObjectType());
          Statement s = new AssignStmt(tok, Repr, new ExprRhs(e));
          s.IsGhost = true;
          bodyStatements.Add(s);

          AddSubobjectReprs(tok, subobjects, bodyStatements, self, implicitSelf, cNull, Repr);

        } else if (member is Method && !member.IsStatic) {
          var m = (Method)member;
          if (Valid != null && !IsSimpleQueryMethod(m)) {
            // modifies Repr;
            m.Mod.Expressions.Add(new FrameExpression(Repr, null));
            // ensures Valid();
            var valid = new FunctionCallExpr(tok, "Valid", implicitSelf, tok, new List<Expression>());
            valid.Function = Valid;
            valid.Type = Type.Bool;
            m.Ens.Insert(0, new MaybeFreeExpression(valid));
            // ensures fresh(Repr - old(Repr));
            var e0 = new OldExpr(tok, Repr);
            e0.Type = Repr.Type;
            var e1 = new BinaryExpr(tok, BinaryExpr.Opcode.Sub, Repr, e0);
            e1.ResolvedOp = BinaryExpr.ResolvedOpcode.SetDifference;
            e1.Type = Repr.Type;
            var freshness = new FreshExpr(tok, e1);
            freshness.Type = Type.Bool;
            m.Ens.Insert(1, new MaybeFreeExpression(freshness));

            if (m.Body == null) {
              m.Body = new BlockStmt(tok, new List<Statement>());
            }
            // TODO: these assignments should be included on every return path
            var bodyStatements = ((BlockStmt)m.Body).Body;
            AddSubobjectReprs(tok, subobjects, bodyStatements, self, implicitSelf, cNull, Repr);
          }
        }
      }
    }

    void AddSubobjectReprs(Boogie.IToken tok, List<Tuple<Field, Field>> subobjects, List<Statement> bodyStatements,
      Expression self, Expression implicitSelf, Expression cNull, Expression Repr) {

      foreach (var ff in subobjects) {
        var F = new FieldSelectExpr(tok, implicitSelf, ff.Item1.Name);
        F.Field = ff.Item1;
        F.Type = ff.Item1.Type;

        Expression e = new SetDisplayExpr(tok, new List<Expression>() { F });
        e.Type = new SetType(new ObjectType());
        var rhs = new BinaryExpr(tok, BinaryExpr.Opcode.Add, Repr, e);
        rhs.ResolvedOp = BinaryExpr.ResolvedOpcode.Union;
        rhs.Type = Repr.Type;
        if (ff.Item2 == null) {
          // Repr := Repr + {F}  (so, nothing else to do)
        } else {
          // Repr := Repr + {F} + F.Repr
          var FRepr = new FieldSelectExpr(tok, F, ff.Item2.Name);
          FRepr.Field = ff.Item2;
          FRepr.Type = ff.Item2.Type;
          rhs = new BinaryExpr(tok, BinaryExpr.Opcode.Add, rhs, FRepr);
          rhs.ResolvedOp = BinaryExpr.ResolvedOpcode.Union;
          rhs.Type = Repr.Type;
        }
        // Repr := Repr + ...;
        Statement s = new AssignStmt(tok, Repr, new ExprRhs(rhs));
        s.IsGhost = true;
        // wrap if statement around s
        e = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.NeqCommon, F, cNull);
        var thn = new BlockStmt(tok, new List<Statement>() { s });
        thn.IsGhost = true;
        s = new IfStmt(tok, e, thn, null);
        s.IsGhost = true;
        // finally, add s to the body
        bodyStatements.Add(s);
      }
    }

    bool IsSimpleQueryMethod(Method m) {
      // A simple query method has out parameters, its body has no effect other than to assign to them,
      // and the postcondition does not explicitly mention the pre-state.
      return m.Outs.Count != 0 && m.Body != null && LocalAssignsOnly(m.Body) &&
        m.Ens.TrueForAll(mfe => !Translator.MentionsOldState(mfe.E));
    }

    bool LocalAssignsOnly(Statement s) {
      Contract.Requires(s != null);
      if (s is AssignStmt) {
        var ss = (AssignStmt)s;
        return ss.Lhs.Resolved is IdentifierExpr;
      } else if (s is ConcreteUpdateStatement) {
        var ss = (ConcreteUpdateStatement)s;
        return ss.Lhss.TrueForAll(e => e.Resolved is IdentifierExpr);
      } else if (s is CallStmt) {
        return false;
      } else {
        foreach (var ss in s.SubStatements) {
          if (!LocalAssignsOnly(ss)) {
            return false;
          }
        }
      }
      return true;
    }

    BinaryExpr BinBoolExpr(Boogie.IToken tok, BinaryExpr.ResolvedOpcode rop, Expression e0, Expression e1) {
      var p = new BinaryExpr(tok, BinaryExpr.ResolvedOp2SyntacticOp(rop), e0, e1);
      p.ResolvedOp = rop;
      p.Type = Type.Bool;
      return p;
    }
  }
}
