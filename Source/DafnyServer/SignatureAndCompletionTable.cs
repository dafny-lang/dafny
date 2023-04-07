// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.Serialization;
using Microsoft.Dafny;
using Type = Microsoft.Dafny.Type;
using Function = Microsoft.Dafny.Function;
using Program = Microsoft.Dafny.Program;

namespace DafnyServer {
  public class LegacySymbolTable {
    private readonly Program _dafnyProgram;
    private readonly List<SymbolInformation> _information = new();

    public LegacySymbolTable(Program dafnyProgram) {
      _dafnyProgram = dafnyProgram;
    }

    public List<SymbolInformation> CalculateSymbols() {
      foreach (var module in _dafnyProgram.Modules()) {
        AddMethods(module, _information);
        AddFields(module, _information);
        AddClasses(module, _information);
      }
      return _information;
    }

    private void AddMethods(ModuleDefinition module, List<SymbolInformation> information) {
      foreach (
          var clbl in
          ModuleDefinition.AllCallables(module.TopLevelDecls).Where(e => e != null && e.Tok.Filename == module.Tok.Filename)) {

        if (clbl is Predicate) {
          var predicate = clbl as Predicate;
          var predicateSymbol = new SymbolInformation {
            Module = predicate.EnclosingClass.EnclosingModuleDefinition.Name,
            Name = predicate.Name,
            ParentClass = predicate.EnclosingClass.Name,
            SymbolType = SymbolInformation.Type.Predicate,
            StartToken = predicate.tok,
            EndToken = predicate.EndToken
          };
          information.Add(predicateSymbol);

        } else if (clbl is Function) {
          var fn = (Function)clbl;
          var functionSymbol = new SymbolInformation {
            Module = fn.EnclosingClass.EnclosingModuleDefinition.Name,
            Name = fn.Name,
            ParentClass = fn.EnclosingClass.Name,
            SymbolType = SymbolInformation.Type.Function,
            StartToken = fn.tok,
            EndColumn = fn.EndToken.col,
            EndLine = fn.EndToken.line,
            EndPosition = fn.EndToken.pos,
            EndToken = fn.EndToken
          };
          information.Add(functionSymbol);
        } else {
          var m = (Method)clbl;
          if (m.Body != null && m.Body.Body != null) {
            information.AddRange(ResolveCallStatements(m.Body.Body));
            information.AddRange(ResolveLocalDefinitions(m.Body.Body, m));
          }
          var methodSymbol = new SymbolInformation {
            Module = m.EnclosingClass.EnclosingModuleDefinition.Name,
            Name = m.Name,
            ParentClass = m.EnclosingClass.Name,
            SymbolType = SymbolInformation.Type.Method,
            StartToken = m.tok,
            Ensures = ParseContracts(m.Ens),
            Requires = ParseContracts(m.Req),
            References =
                  FindMethodReferencesInternal(m.EnclosingClass.EnclosingModuleDefinition.Name + "." + m.EnclosingClass.Name + "." +
                                   m.Name),
            EndColumn = m.EndToken.col,
            EndLine = m.EndToken.line,
            EndPosition = m.EndToken.pos,
            EndToken = m.EndToken
          };
          information.Add(methodSymbol);
        }
      }
    }

    private void AddFields(ModuleDefinition module, List<SymbolInformation> information) {
      foreach (
          var fs in ModuleDefinition.AllFields(module.TopLevelDecls).Where(e => e != null && e.Tok.Filename == module.Tok.Filename)) {

        var fieldSymbol = new SymbolInformation {
          Module = fs.EnclosingClass.EnclosingModuleDefinition.Name,
          Name = fs.Name,
          ParentClass = fs.EnclosingClass.Name,
          SymbolType = SymbolInformation.Type.Field,
          StartToken = fs.tok,
          References = FindFieldReferencesInternal(fs.Name, fs.EnclosingClass.Name, fs.EnclosingClass.EnclosingModuleDefinition.Name)
        };
        if (fs.Type is UserDefinedType) {
          var userType = fs.Type as UserDefinedType;
          fieldSymbol.ReferencedClass = userType.ResolvedClass.SanitizedName;
          fieldSymbol.ReferencedModule = userType.ResolvedClass.EnclosingModuleDefinition.SanitizedName;
        }
        information.Add(fieldSymbol);
      }
    }

    private static void AddClasses(ModuleDefinition module, List<SymbolInformation> information) {
      foreach (var cs in ModuleDefinition.AllClasses(module.TopLevelDecls).Where(cl => cl.Tok.Filename == module.Tok.Filename)) {
        if (cs.EnclosingModuleDefinition != null && cs.tok != null) {
          var classSymbol = new SymbolInformation {
            Module = cs.EnclosingModuleDefinition.Name,
            Name = cs.Name,
            SymbolType = SymbolInformation.Type.Class,
            StartToken = cs.tok,
            EndToken = cs.EndToken
          };
          information.Add(classSymbol);
        }
      }
    }

    private ICollection<string> ParseContracts(IEnumerable<AttributedExpression> contractClauses) {
      var requires = new List<string>();
      foreach (var maybeFreeExpression in contractClauses) {
        requires.Add(Printer.ExprToString(_dafnyProgram.Options, maybeFreeExpression.E));
      }
      return requires;
    }

    private static IEnumerable<SymbolInformation> ResolveLocalDefinitions(IEnumerable<Statement> statements, Method method) {
      var information = new List<SymbolInformation>();

      foreach (var statement in statements) {
        if (statement is VarDeclStmt) {
          var declarations = (VarDeclStmt)statement;
          {
            Type type = null;
            var rightSide = declarations.Update as UpdateStmt;
            if (rightSide != null) {
              var definition = rightSide.Rhss.First();
              var typeDef = definition as TypeRhs;
              if (typeDef != null) {
                type = typeDef.Type;
              }
            }
            if (type != null && type is UserDefinedType) {
              var userType = type as UserDefinedType;
              foreach (var declarationLocal in declarations.Locals) {
                var name = declarationLocal.Name;
                information.Add(new SymbolInformation {
                  Name = name,
                  ParentClass = userType.ResolvedClass.SanitizedName,
                  Module = userType.ResolvedClass.EnclosingModuleDefinition.SanitizedName,
                  SymbolType = SymbolInformation.Type.Definition,
                  StartToken = method.StartToken,
                  EndToken = method.EndToken
                });
              }
            }
          }
        }
        if (statement is UpdateStmt) {
          var updateStatement = statement as UpdateStmt;
          var lefts = updateStatement.Lhss;
          foreach (var expression in lefts) {
            if (expression is AutoGhostIdentifierExpr) {
              var autoGhost = expression as AutoGhostIdentifierExpr;
              information.Add(new SymbolInformation {
                Name = autoGhost.Name,
                ParentClass = autoGhost.Resolved.Type.ToString(),
                SymbolType = SymbolInformation.Type.Definition,
                StartToken = updateStatement.Tok,
                EndToken = updateStatement.EndToken
              });
            }
          }
        }
        if (statement.SubStatements.Any()) {
          information.AddRange(ResolveLocalDefinitions(statement.SubStatements.ToList(), method));
        }
      }
      return information;
    }

    private static IEnumerable<SymbolInformation> ResolveCallStatements(IEnumerable<Statement> statements) {
      var information = new List<SymbolInformation>();

      foreach (var statement in statements) {
        if (statement is CallStmt) {
          ParseCallStatement(statement, information);
        } else if (statement is UpdateStmt) {
          ParseUpdateStatement(statement, information);
        }

        if (statement.SubStatements.Any()) {
          information.AddRange(ResolveCallStatements(statement.SubStatements.ToList()));
        }
      }
      return information;
    }

    private static void ParseCallStatement(Statement statement, List<SymbolInformation> information) {
      var callStmt = (CallStmt)statement;
      {
        if (!(callStmt.Receiver.Type is UserDefinedType)) {
          return;
        }

        var receiver = callStmt.Receiver as NameSegment;
        var userType = (UserDefinedType)callStmt.Receiver.Type;
        var reveiverName = receiver == null ? "" : receiver.Name;
        information.Add(new SymbolInformation {
          Name = callStmt.Method.SanitizedName,
          ParentClass = userType.ResolvedClass.SanitizedName,
          Module = userType.ResolvedClass.EnclosingModuleDefinition.SanitizedName,
          Call = reveiverName + "." + callStmt.MethodSelect.Member,
          SymbolType = SymbolInformation.Type.Call,
          StartToken = callStmt.MethodSelect.tok
        });
      }
    }

    private static void ParseUpdateStatement(Statement statement, List<SymbolInformation> information) {
      var updateStmt = (UpdateStmt)statement;
      var leftSide = updateStmt.Lhss;
      var rightSide = updateStmt.Rhss;
      var leftSideDots = leftSide.OfType<ExprDotName>();
      var rightSideDots = rightSide.OfType<ExprDotName>();
      var allExprDotNames = leftSideDots.Concat(rightSideDots);
      foreach (var exprDotName in allExprDotNames) {
        if (!(exprDotName.Lhs.Type is UserDefinedType)) {
          continue;
        }

        var segment = exprDotName.Lhs as NameSegment;
        var type = (UserDefinedType)exprDotName.Lhs.Type;
        var designator = segment == null ? "" : segment.Name;
        information.Add(new SymbolInformation {
          Name = exprDotName.SuffixName,
          ParentClass = type.ResolvedClass.SanitizedName,
          Module = type.ResolvedClass.EnclosingModuleDefinition.SanitizedName,
          Call = designator + "." + exprDotName.SuffixName,
          SymbolType = SymbolInformation.Type.Call,
          StartToken = exprDotName.tok
        });
      }
    }

    private List<ReferenceInformation> FindFieldReferencesInternal(string fieldName, string className,
        string moduleName) {
      var information = new List<ReferenceInformation>();

      foreach (var module in _dafnyProgram.Modules()) {
        foreach (var clbl in ModuleDefinition.AllCallables(module.TopLevelDecls).Where(e => e.Tok.Filename == module.Tok.Filename)) {
          if (!(clbl is Method)) {
            continue;
          }

          var m = (Method)clbl;
          if (m.Body != null) {
            information.AddRange(ParseBodyForFieldReferences(m.Body.SubStatements, fieldName, className, moduleName));
          }
        }
      }

      return information;
    }
    private List<ReferenceInformation> FindMethodReferencesInternal(string methodToFind) {
      var information = new List<ReferenceInformation>();

      foreach (var module in _dafnyProgram.Modules()) {
        foreach (var clbl in ModuleDefinition.AllCallables(module.TopLevelDecls).Where(e => e.Tok.Filename == module.Tok.Filename)) {
          if (!(clbl is Method)) {
            continue;
          }

          var m = (Method)clbl;
          if (m.Body != null) {
            information.AddRange(ParseBodyForMethodReferences(m.Body.SubStatements, methodToFind, m.Name));
          }
        }
      }
      return information;
    }

    private static ICollection<Expression> GetAllSubExpressions(Expression expression) {
      var expressions = new List<Expression>();
      foreach (var subExpression in expression.SubExpressions) {
        expressions.AddRange(GetAllSubExpressions(subExpression));
      }
      expressions.Add(expression);
      return expressions;
    }

    private static IEnumerable<ReferenceInformation> ParseBodyForFieldReferences(IEnumerable<Statement> block, string fieldName, string className, string moduleName) {
      var information = new List<ReferenceInformation>();
      foreach (var statement in block) {
        if (statement is UpdateStmt) {
          var updateStmt = (UpdateStmt)statement;
          var leftSide = updateStmt.Lhss;
          var rightSide = updateStmt.Rhss;
          var leftSideDots = leftSide.OfType<ExprDotName>();
          var rightSideDots = rightSide.OfType<ExprDotName>();
          var exprDotNames = leftSideDots.Concat(rightSideDots);
          var leftSideNameSegments = leftSide.OfType<NameSegment>();
          var rightSideNameSegments = rightSide.OfType<NameSegment>();
          var nameSegments = leftSideNameSegments.Concat(rightSideNameSegments);
          var allRightSideExpressions = rightSide.SelectMany(e => e.SubExpressions.SelectMany(GetAllSubExpressions));
          var allLeftSideExpressions =
              leftSide.SelectMany(e => e.SubExpressions.SelectMany(GetAllSubExpressions));
          var allExpressions = allRightSideExpressions.Concat(allLeftSideExpressions).ToList();
          var allExprDotNames = exprDotNames.Concat(allExpressions.OfType<ExprDotName>()).Distinct();
          var allNameSegments = nameSegments.Concat(allExpressions.OfType<NameSegment>()).Distinct();

          foreach (var exprDotName in allExprDotNames) {
            if (exprDotName.Lhs.Type is UserDefinedType) {
              var type = (UserDefinedType)exprDotName.Lhs.Type;
              if (fieldName == exprDotName.SuffixName && className == type.ResolvedClass.SanitizedName &&
                  moduleName == type.ResolvedClass.EnclosingModuleDefinition.SanitizedName) {
                information.Add(new ReferenceInformation {
                  MethodName = exprDotName.SuffixName,
                  StartToken = exprDotName.tok,
                  ReferencedName = exprDotName.SuffixName

                });
              }

            }
          }
          foreach (var nameSegment in allNameSegments) {
            if (nameSegment.ResolvedExpression is MemberSelectExpr) {
              var memberAcc = (MemberSelectExpr)nameSegment.ResolvedExpression;
              if (fieldName == memberAcc.MemberName &&
                  className == memberAcc.Member.EnclosingClass.SanitizedName &&
                  moduleName == memberAcc.Member.EnclosingClass.EnclosingModuleDefinition.SanitizedName) {
                information.Add(new ReferenceInformation {
                  MethodName = memberAcc.MemberName,
                  StartToken = memberAcc.tok,
                  ReferencedName = memberAcc.MemberName
                });
              }
            }
          }
        }

        if (statement.SubStatements.Any()) {
          information.AddRange(ParseBodyForFieldReferences(statement.SubStatements, fieldName, className, moduleName));
        }
      }
      return information;
    }

    private List<ReferenceInformation> ParseBodyForMethodReferences(IEnumerable<Statement> block, string methodToFind, string currentMethodName) {
      var information = new List<ReferenceInformation>();
      foreach (var statement in block) {
        if (statement is CallStmt) {
          var callStmt = (CallStmt)statement;
          if (callStmt.Method.FullName == methodToFind) {
            information.Add(new ReferenceInformation {
              StartToken = callStmt.MethodSelect.tok,
              MethodName = currentMethodName,
              ReferencedName = methodToFind.Split('.')[2]
            });
          }
        }
        if (statement.SubStatements.Any()) {
          information.AddRange(ParseBodyForMethodReferences(statement.SubStatements, methodToFind, currentMethodName));
        }
      }
      return information;
    }

    [Serializable]
    [DataContract]
    public class SymbolInformation {
      [DataMember(Name = "Module")]
      public string Module { get; set; }
      [DataMember(Name = "Name")]
      public string Name { get; set; }
      [DataMember(Name = "ParentClass")]
      public string ParentClass { get; set; }
      public Type SymbolType { get; set; }
      [DataMember(Name = "Position")]
      public int? Position { get; set; }
      [DataMember(Name = "Line")]
      public int? Line { get; set; }
      [DataMember(Name = "Column")]
      public int? Column { get; set; }
      [DataMember(Name = "EndPosition")]
      public int? EndPosition { get; set; }
      [DataMember(Name = "EndLine")]
      public int? EndLine { get; set; }
      [DataMember(Name = "EndColumn")]
      public int? EndColumn { get; set; }
      [DataMember(Name = "References")]
      public ICollection<ReferenceInformation> References { get; set; }
      [DataMember(Name = "Requires")]
      public ICollection<string> Requires { get; set; }
      [DataMember(Name = "Ensures")]
      public ICollection<string> Ensures { get; set; }
      [DataMember(Name = "Call")]
      public string Call { get; set; }
      [DataMember(Name = "ReferencedClass")]
      public string ReferencedClass { get; set; }
      [DataMember(Name = "ReferencedModule")]
      public string ReferencedModule { get; set; }
      [DataMember(Name = "SymbolType", Order = 1)]
      private string SymbolTypeString {
        get { return Enum.GetName(typeof(Type), SymbolType); }
        set { SymbolType = (Type)Enum.Parse(typeof(Type), value, true); }
      }

      public IToken StartToken {
        set {
          Line = value.line;
          Position = value.pos;
          Column = value.col;
        }
      }

      public IToken EndToken {
        set {
          EndLine = value.line;
          EndPosition = value.pos;
          EndColumn = value.col;
        }
      }

      public enum Type {
        Class,
        Method,
        Function,
        Field,
        Call,
        Definition,
        Predicate
      }

      public SymbolInformation() {
        References = new List<ReferenceInformation>();
      }
    }

    [Serializable]
    [DataContract]
    public class ReferenceInformation {
      [DataMember(Name = "MethodName")]
      public string MethodName { get; set; }
      [DataMember(Name = "Position")]
      public int? Position { get; set; }
      [DataMember(Name = "Line")]
      public int? Line { get; set; }
      [DataMember(Name = "Column")]
      public int? Column { get; set; }
      [DataMember(Name = "ReferencedName")]
      public string ReferencedName { get; set; }

      public IToken StartToken {
        set {
          Line = value.line;
          Position = value.pos;
          Column = value.col;
        }
      }
    }
  }
}
