using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Runtime.Serialization;
using System.Runtime.Serialization.Json;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny
{
    // FIXME: This should not be duplicated here
    class DafnyConsolePrinter : ConsolePrinter
    {
        public override void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null)
        {
            // Dafny has 0-indexed columns, but Boogie counts from 1
            var realigned_tok = new Token(tok.line, tok.col - 1);
            realigned_tok.kind = tok.kind;
            realigned_tok.pos = tok.pos;
            realigned_tok.val = tok.val;
            realigned_tok.filename = tok.filename;
            base.ReportBplError(realigned_tok, message, error, tw, category);

            if (tok is Dafny.NestedToken)
            {
                var nt = (Dafny.NestedToken)tok;
                ReportBplError(nt.Inner, "Related location", false, tw);
            }
        }
    }

    class DafnyHelper
    {
        private string fname;
        private string source;
        private string[] args;

        private readonly Dafny.ErrorReporter reporter;
        private Dafny.Program dafnyProgram;
        private IEnumerable<Tuple<string, Bpl.Program>> boogiePrograms;

        public DafnyHelper(string[] args, string fname, string source)
        {
            this.args = args;
            this.fname = fname;
            this.source = source;
            this.reporter = new Dafny.ConsoleErrorReporter();
        }

        public bool Verify()
        {
            ServerUtils.ApplyArgs(args, reporter);
            return Parse() && Resolve() && Translate() && Boogie();
        }

        private bool Parse()
        {
            Dafny.ModuleDecl module = new Dafny.LiteralModuleDecl(new Dafny.DefaultModuleDecl(), null);
            Dafny.BuiltIns builtIns = new Dafny.BuiltIns();
            var success =
                (Dafny.Parser.Parse(source, fname, fname, null, module, builtIns, new Dafny.Errors(reporter)) == 0 &&
                 Dafny.Main.ParseIncludes(module, builtIns, new List<string>(), new Dafny.Errors(reporter)) == null);
            if (success)
            {
                dafnyProgram = new Dafny.Program(fname, module, builtIns, reporter);
            }
            return success;
        }

        private bool Resolve()
        {
            var resolver = new Dafny.Resolver(dafnyProgram);
            resolver.ResolveProgram(dafnyProgram);
            return reporter.Count(ErrorLevel.Error) == 0;
        }

        private bool Translate()
        {
            boogiePrograms = Translator.Translate(dafnyProgram, reporter,
                new Translator.TranslatorFlags() { InsertChecksums = true, UniqueIdPrefix = fname });
            // FIXME how are translation errors reported?
            return true;
        }

        private bool BoogieOnce(Bpl.Program boogieProgram)
        {
            if (boogieProgram.Resolve() == 0 && boogieProgram.Typecheck() == 0)
            {
                
                //FIXME ResolveAndTypecheck?
                ExecutionEngine.EliminateDeadVariables(boogieProgram);
                ExecutionEngine.CollectModSets(boogieProgram);
                ExecutionEngine.CoalesceBlocks(boogieProgram);
                ExecutionEngine.Inline(boogieProgram);

                //NOTE: We could capture errors instead of printing them (pass a delegate instead of null)
                switch (
                    ExecutionEngine.InferAndVerify(boogieProgram, new PipelineStatistics(), "ServerProgram", null,
                        DateTime.UtcNow.Ticks.ToString()))
                {
                    case PipelineOutcome.Done:
                    case PipelineOutcome.VerificationCompleted:
                        return true;
                }
            }

            return false;
        }

        private bool Boogie()
        {
            var isVerified = true;
            foreach (var boogieProgram in boogiePrograms)
            {
                isVerified = isVerified && BoogieOnce(boogieProgram.Item2);
            }
            return isVerified;
        }

        public void Symbols()
        {
            ServerUtils.ApplyArgs(args, reporter);
            var information = new List<SymbolInformation>();
            if (Parse() && Resolve())
            {

                    foreach (var module in dafnyProgram.Modules())
                    {
                        foreach (var clbl in ModuleDefinition.AllCallables(module.TopLevelDecls).Where(e => ! (e.Tok is IncludeToken)))
                        {
                            if (clbl is Function)
                            {
                                var fn = (Function)clbl;
                                var functionSymbol = new SymbolInformation
                                {
                                    Module = fn.EnclosingClass.Module.Name,
                                    Name = fn.Name,
                                    ParentClass = fn.EnclosingClass.Name,
                                    SymbolType = SymbolInformation.Type.Function,
                                    Position = fn.tok.pos,
                                    Line = fn.tok.line,
                                    Column = fn.tok.col
                                };
                                information.Add(functionSymbol);
                            }
                            else
                            {
                                var m = (Method)clbl;
                                if (m.Body!= null && m.Body.Body != null)
                                {
                                    information.AddRange(ResolveCallStatements(m.Body.Body));
                                    information.AddRange(ResolveLocalDefinitions(m.Body.Body, m));
                                }
                                var methodSymbol = new SymbolInformation
                                {
                                    Module = m.EnclosingClass.Module.Name,
                                    Name = m.Name,
                                    ParentClass = m.EnclosingClass.Name,
                                    SymbolType = SymbolInformation.Type.Method,
                                    Position = m.tok.pos,
                                    Line = m.tok.line,
                                    Column = m.tok.col,
                                    References = FindMethodReferencesInternal(m.EnclosingClass.Module.Name + "." + m.EnclosingClass.Name + "." + m.Name)
                                };
                                information.Add(methodSymbol);
                            }
                        }

                        foreach (var fs in ModuleDefinition.AllFields(module.TopLevelDecls).Where(e => !(e.tok is IncludeToken)))
                        {
                            var fieldSymbol = new SymbolInformation
                            {
                                Module = fs.EnclosingClass.Module.Name,
                                Name = fs.Name,
                                ParentClass = fs.EnclosingClass.Name,
                                SymbolType = SymbolInformation.Type.Field,
                                Position = fs.tok.pos,
                                Line = fs.tok.line,
                                Column = fs.tok.col,
                                References = FindFieldReferencesInternal(fs.Name, fs.EnclosingClass.Name, fs.EnclosingClass.Module.Name)
                            };
                            information.Add(fieldSymbol);
                        }

                        foreach (var cs in ModuleDefinition.AllClasses(module.TopLevelDecls).Where(e => !(e.tok is IncludeToken)))
                        {
                            if (cs != null && cs.Module != null && cs.tok != null)
                            {
                                var classSymbol = new SymbolInformation
                                {
                                    Module = cs.Module.Name,
                                    Name = cs.Name,
                                    SymbolType = SymbolInformation.Type.Class,
                                    Position = cs.tok.pos,
                                    Line = cs.tok.line,
                                    Column = cs.tok.col,
                                    EndPosition = cs.BodyEndTok.pos,
                                    EndLine = cs.BodyEndTok.line,
                                    EndColumn = cs.BodyEndTok.col
                                };
                                information.Add(classSymbol);
                            }
                        }
                    }
                

            }

            
            var json = ToJson(information);
            Console.WriteLine("SYMBOLS_START " + json + " SYMBOLS_END");
        }

        private static IEnumerable<SymbolInformation> ResolveLocalDefinitions(IEnumerable<Statement> statements, Method method)
        {
            var information = new List<SymbolInformation>();
            try
            {
                foreach (var statement in statements)
                {
                    if (statement is VarDeclStmt)
                    {
                        var declarations = (VarDeclStmt)statement;
                        {
                            Type type = null;
                            var rightSide = declarations.Update as UpdateStmt;
                            if (rightSide != null)
                            {
                                var definition = rightSide.Rhss.First();
                                if (definition != null)
                                {
                                    var typeDef = definition as TypeRhs;
                                    if (typeDef != null)
                                    {
                                        type = typeDef.Type;
                                    }
                                }
                            }
                            if (type != null  && type  is UserDefinedType)
                            {
                                var userType = type as UserDefinedType;
                                foreach (var declarationLocal in declarations.Locals)
                                {
                                    var name = declarationLocal.Name;
                                    information.Add(new SymbolInformation
                                    {
                                        Name = name,
                                        ParentClass = userType.ResolvedClass.CompileName,
                                        Module = userType.ResolvedClass.Module.CompileName,
                                        SymbolType = SymbolInformation.Type.Definition,
                                        Position = method.BodyStartTok.pos,
                                        Line = method.BodyStartTok.line,
                                        Column = method.BodyStartTok.col,
                                        EndColumn = method.BodyEndTok.col,
                                        EndLine = method.BodyEndTok.line,
                                        EndPosition = method.BodyEndTok.pos
                                    });
                                }
                            }
                        }
                    }
                    
                    if (statement.SubStatements.Any())
                    {
                        information.AddRange(ResolveLocalDefinitions(statement.SubStatements.ToList(), method));
                    }
                }
            }
            catch (Exception e)
            {
                Interaction.EOM(Interaction.FAILURE, e.Message + e.StackTrace);
            }
            return information;
        }
        private static IEnumerable<SymbolInformation> ResolveCallStatements(IEnumerable<Statement> statements)
        {
            var information = new List<SymbolInformation>();
            try
            {
                foreach (var statement in statements)
                {
                    if (statement is CallStmt)
                    {
                        var callStmt = (CallStmt)statement;
                        {

                            if (callStmt.Receiver.Type is UserDefinedType)
                            {
                                var receiver = callStmt.Receiver as NameSegment;
                                var userType = callStmt.Receiver.Type as UserDefinedType;
                                var reveiverName = receiver == null ? "" : receiver.Name;
                                information.Add(new SymbolInformation
                                {
                                    Name = callStmt.Method.CompileName,
                                    ParentClass = userType.ResolvedClass.CompileName,
                                    Module = userType.ResolvedClass.Module.CompileName,
                                    Call = reveiverName + "." + callStmt.MethodSelect.Member,
                                    SymbolType = SymbolInformation.Type.Call,
                                    Position = callStmt.MethodSelect.tok.pos,
                                    Line = callStmt.MethodSelect.tok.line,
                                    Column = callStmt.MethodSelect.tok.col
                                });
                            }
                            
                        }
                    } else if (statement is UpdateStmt)
                    {
                        var updateStmt = (UpdateStmt) statement;
                        var leftSide = updateStmt.Lhss;
                        var rightSide = updateStmt.Rhss;
                        var leftSideDots = leftSide.OfType<ExprDotName>();
                        var rightSideDots = rightSide.OfType<ExprDotName>();
                        var allExprDotNames = leftSideDots.Concat(rightSideDots);
                        foreach (var exprDotName in allExprDotNames)
                        {
                            if (exprDotName.Lhs.Type is UserDefinedType)
                            {
                                var segment = exprDotName.Lhs as NameSegment;
                                var type = exprDotName.Lhs.Type as UserDefinedType;
                                var designator = segment == null ? "" : segment.Name;
                                information.Add(new SymbolInformation
                                {
                                    Name = exprDotName.SuffixName,
                                    ParentClass = type.ResolvedClass.CompileName,
                                    Module =  type.ResolvedClass.Module.CompileName,
                                    Call = designator + "." + exprDotName.SuffixName,
                                    SymbolType = SymbolInformation.Type.Call,
                                    Position = exprDotName.tok.pos,
                                    Line = exprDotName.tok.line,
                                    Column = exprDotName.tok.col

                                });
                            }
                        }
                    }
                    if (statement.SubStatements.Any())
                    {
                        information.AddRange(ResolveCallStatements(statement.SubStatements.ToList()));
                    }
                }
            }
            catch (Exception e)
            {
                Interaction.EOM(Interaction.FAILURE, e.Message + e.StackTrace);
            }
            return information;
        }

        public void FindReferences()
        {
            ServerUtils.ApplyArgs(args, reporter);
            string methodToFind = args[0] + "." + args[1] + "." + args[2];
            var information = FindReferences(methodToFind);
            var json = ToJson(information);
            var byteArray = Encoding.UTF8.GetBytes(json);
            var base64 = Convert.ToBase64String(byteArray);
            Console.WriteLine("REFERENCE_START" + base64 + "REFERENCE_END");
        }

        private List<ReferenceInformation> FindReferences(string methodToFind)
        {
            var information = new List<ReferenceInformation>();
            if (Parse() && Resolve())
            {
                try
                {
                    foreach (var module in dafnyProgram.Modules())
                    {
                        foreach (var clbl in ModuleDefinition.AllCallables(module.TopLevelDecls))
                        {
                            if (clbl is Function)
                            {
                                var fn = (Function) clbl;
                            }
                            else
                            {
                                var m = (Method) clbl;
                                var body = m.Body;
                                information.AddRange(ParseBodyForMethodReferences(body.SubStatements, methodToFind, m.Name));
                            }
                        }
                    }
                }
                catch (Exception e)
                {
                    Interaction.EOM(Interaction.FAILURE, e.Message + e.StackTrace);
                }
            }
            return information;
        }

        private List<ReferenceInformation> FindFieldReferencesInternal(string fieldName, string className,
            string moduleName)
        {
            var information = new List<ReferenceInformation>();

            try
            {
                foreach (var module in dafnyProgram.Modules())
                {
                    foreach (var clbl in ModuleDefinition.AllCallables(module.TopLevelDecls).Where(e => !(e.Tok is IncludeToken)))
                    {
                        if (clbl is Function)
                        {
                            var fn = (Function)clbl;
                        }
                        else
                        {
                            var m = (Method)clbl;
                            var body = m.Body;
                            information.AddRange(ParseBodyForFieldReferences(body.SubStatements, fieldName, className, moduleName));
                        }
                    }
                }
            }
            catch (Exception e)
            {
                Interaction.EOM(Interaction.FAILURE, e.Message + e.StackTrace);
            }
            return information;
        }
        private List<ReferenceInformation> FindMethodReferencesInternal(string methodToFind)
        {
            var information = new List<ReferenceInformation>();

                try
                {
                    foreach (var module in dafnyProgram.Modules())
                    {
                        foreach (var clbl in ModuleDefinition.AllCallables(module.TopLevelDecls).Where(e => !(e.Tok is IncludeToken)))
                        {
                            if (clbl is Function)
                            {
                                var fn = (Function)clbl;
                            }
                            else
                            {
                                var m = (Method)clbl;
                                var body = m.Body;
                                information.AddRange(ParseBodyForMethodReferences(body.SubStatements, methodToFind, m.Name));
                            }
                        }
                    }
                }
                catch (Exception e)
                {
                    Interaction.EOM(Interaction.FAILURE, e.Message + e.StackTrace);
                }
            return information;
        }

        public static ICollection<Expression> GetAllSubExpressions(Expression expression)
        {
            var expressions = new List<Expression>();
            foreach (var subExpression in expression.SubExpressions)
            {
                expressions.AddRange(GetAllSubExpressions(subExpression));
            }
            expressions.Add(expression);
            return expressions;
        }
        private static IEnumerable<ReferenceInformation> ParseBodyForFieldReferences(IEnumerable<Statement> block, string fieldName, string className, string moduleName)
        {
            var information = new List<ReferenceInformation>();
            foreach (var statement in block)
            {
                if (statement is UpdateStmt)
                {
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
                    var allMemberSelectExpr = allExpressions.OfType<MemberSelectExpr>().Distinct();
                    foreach (var exprDotName in allExprDotNames)
                    {
                        if (exprDotName.Lhs.Type is UserDefinedType)
                        {
                            var type = exprDotName.Lhs.Type as UserDefinedType;
                            if (fieldName == exprDotName.SuffixName && className == type.ResolvedClass.CompileName &&
                                moduleName == type.ResolvedClass.Module.CompileName)
                            {
                                information.Add(new ReferenceInformation
                                {
                                    MethodName = exprDotName.SuffixName,
                                    Position = exprDotName.tok.pos,
                                    Line = exprDotName.tok.line,
                                    Column = exprDotName.tok.col,
                                    ReferencedName = exprDotName.SuffixName

                                });
                            }
                           
                        }
                    }
                    foreach (var nameSegment in allNameSegments)
                    {
                        if (nameSegment.ResolvedExpression is MemberSelectExpr)
                        {
                            var memberAcc = nameSegment.ResolvedExpression as MemberSelectExpr;
                            if (fieldName == memberAcc.MemberName &&
                                className == memberAcc.Member.EnclosingClass.CompileName &&
                                moduleName == memberAcc.Member.EnclosingClass.Module.CompileName)
                            {
                                information.Add(new ReferenceInformation
                                {
                                    MethodName = memberAcc.MemberName,
                                    Position = memberAcc.tok.pos,
                                    Line = memberAcc.tok.line,
                                    Column = memberAcc.tok.col,
                                    ReferencedName = memberAcc.MemberName
                                });
                            }
                        }
                    }
                }

                if (statement.SubStatements.Any())
                {
                    information.AddRange(ParseBodyForFieldReferences(statement.SubStatements, fieldName, className, moduleName));
                }
            }
            return information;
        }

        private List<ReferenceInformation> ParseBodyForMethodReferences(IEnumerable<Statement> block, string methodToFind, string currentMethodName)
        {
            var information = new List<ReferenceInformation>();
            foreach (var statement in block)
            {
                if (statement is CallStmt)
                {
                    var callStmt = (CallStmt)statement;
                    if (callStmt.Method.FullName == methodToFind)
                    {
                        information.Add(new ReferenceInformation
                        {
                            Position = callStmt.MethodSelect.tok.pos,
                            Line = callStmt.MethodSelect.tok.line,
                            Column = callStmt.MethodSelect.tok.col,
                            MethodName = currentMethodName,
                            ReferencedName = methodToFind.Split('.')[2]
                        });
                    }
                }
                if (statement.SubStatements.Any())
                {
                    information.AddRange(ParseBodyForMethodReferences(statement.SubStatements, methodToFind, currentMethodName));
                }
            }
            return information;
        }

        public void Proofs()
        {
            ServerUtils.ApplyArgs(args, reporter);
            List<ProofInformation> proofs = new List<ProofInformation>();
            if (Parse() && Resolve() && Translate()/* && Boogie()*/)
            {
                Boogie();
                foreach (var boogieProgram in boogiePrograms)
                {
                    object err = "";
                    var name = boogieProgram.Item1;
                    var program = boogieProgram.Item2;
                    foreach (var block in program.Implementations.SelectMany(i => i.Blocks))
                    {
                        var cmds = block.Cmds;
                        if (cmds == null) continue;

                        foreach (var proof in cmds)
                        {
                            var cl = proof.GetType();
                            Console.WriteLine(cl);
                            if (proof is AssertRequiresCmd)
                            {

                                var ar = proof as AssertRequiresCmd;
                                err = ar.ErrorData;
                                proofs.Add(new ProofInformation
                                {
                                    Proof = ar.Expr.ToString(),
                                    Type = ProofInformation.ProofType.AssertRequires
                                });
                            }
                            else if (proof is AssertEnsuresCmd)
                            {
                                var ae = proof as AssertEnsuresCmd;
                                err = ae.ErrorData;
                                proofs.Add(new ProofInformation
                                {
                                    Proof = ae.Expr.ToString(),
                                    Type = ProofInformation.ProofType.AssertEnsures
                                });
                            }
                            else if (proof is LoopInitAssertCmd)
                            {
                                var ai = proof as LoopInitAssertCmd;
                                err = ai.ErrorData;
                                proofs.Add(new ProofInformation
                                {
                                    Proof = ai.Expr.ToString(),
                                    Type = ProofInformation.ProofType.LoopInitAssert
                                });
                            }
                            else if (proof is LoopInvMaintainedAssertCmd)
                            {
                                var am = proof as LoopInvMaintainedAssertCmd;
                                err = am.ErrorData;
                                proofs.Add(new ProofInformation
                                {
                                    Proof = am.Expr.ToString(),
                                    Type = ProofInformation.ProofType.LoopInvMaintainedAssert
                                });
                            }
                            else if (proof is AssertCmd)
                            {
                                var a = proof as AssertCmd;
                                err = a.ErrorData;
                                proofs.Add(new ProofInformation
                                {
                                    Proof = a.Expr.ToString(),
                                    Type = ProofInformation.ProofType.Assert
                                });
                            }
                            else if (proof is AssumeCmd)
                            {
                                var z = proof as AssumeCmd;
                                
                            }
                            else if (proof is AssignCmd)
                            {
                                var x = proof as AssignCmd;
                                
                            }
                            else if (proof is CommentCmd)
                            {
                                var t = proof as CommentCmd;
                            }
                            var u = err;

                        }
                    }
                }
            }

            var json = ToJson(proofs);
            Console.WriteLine("PROOFS_START " + json + " PROOFS_END");
        }

        [Serializable]
        [DataContract]
        internal class SymbolInformation
        {
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
            [DataMember(Name="EndPosition")]
            public int? EndPosition { get; set; }
            [DataMember(Name="EndLine")]
            public int? EndLine { get; set; }
            [DataMember(Name="EndColumn")]
            public int? EndColumn { get; set; }
            [DataMember(Name = "References")]
            public ICollection<ReferenceInformation> References { get; set; }
            [DataMember(Name = "Call")]
            public string Call { get; set; }
            [DataMember(Name = "SymbolType", Order = 1)]
            private string SymbolTypeString
            {
                get { return Enum.GetName(typeof(Type), SymbolType); }
                set { SymbolType = (Type)Enum.Parse(typeof(Type), value, true); }
            }

            internal enum Type
            {
                Class,
                Method,
                Function,
                Field,
                Call,
                Definition
            }

            public SymbolInformation()
            {
                References = new List<ReferenceInformation>();
            }
        }

        [Serializable]
        [DataContract]
        internal class ReferenceInformation
        {
            [DataMember(Name = "MethodName")]
            public string MethodName { get; set; }
            [DataMember(Name = "Position")]
            public int? Position { get; set; }
            [DataMember(Name = "Line")]
            public int? Line { get; set; }
            [DataMember(Name = "Column")]
            public int? Column { get; set; }
            [DataMember(Name="ReferencedName")]
            public string ReferencedName { get; set; }
        }

        [Serializable]
        [DataContract]
        internal class ProofInformation
        {
            [DataMember(Name = "Proof")]
            public string Proof { get; set; }
            public ProofType Type { get; set; }
            [DataMember(Name = "Type", Order = 1)]
            private string TypeString
            {
                get { return Enum.GetName(typeof(ProofType), Type); }
                set { Type = (ProofType)Enum.Parse(typeof(ProofType), value, true); }
            }

            internal enum ProofType
            {
                Assert,
                AssertRequires,
                AssertEnsures,
                LoopInitAssert,
                LoopInvMaintainedAssert
            }
        }


        private static string ToJson<T>(T data)
        {
            DataContractJsonSerializer serializer
                        = new DataContractJsonSerializer(typeof(T));

            using (MemoryStream ms = new MemoryStream())
            {
                serializer.WriteObject(ms, data);
                return Encoding.Default.GetString(ms.ToArray());
            }
        }

    }
}