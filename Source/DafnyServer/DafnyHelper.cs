using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.Remoting;
using System.Text;
using System.Threading.Tasks;
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
                try
                {
                    foreach (var module in dafnyProgram.Modules())
                    {
                        foreach (var clbl in ModuleDefinition.AllCallables(module.TopLevelDecls))
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
                                var methodSymbol = new SymbolInformation
                                {
                                    Module = m.EnclosingClass.Module.Name,
                                    Name = m.Name,
                                    ParentClass = m.EnclosingClass.Name,
                                    SymbolType = SymbolInformation.Type.Method,
                                    Position = m.tok.pos,
                                    Line = m.tok.line,
                                    Column = m.tok.col,
                                };
                                information.Add(methodSymbol);
                            }
                        }

                        foreach (var fs in ModuleDefinition.AllFields(module.TopLevelDecls))
                        {
                            var fieldSymbol = new SymbolInformation
                            {
                                Module = fs.EnclosingClass.Module.Name,
                                Name = fs.Name,
                                ParentClass = fs.EnclosingClass.Name,
                                SymbolType = SymbolInformation.Type.Field,
                                Position = fs.tok.pos,
                                Line = fs.tok.line,
                                Column = fs.tok.col
                            };
                            information.Add(fieldSymbol);
                        }

                        foreach (var cs in ModuleDefinition.AllClasses(module.TopLevelDecls))
                        {
                            var classSymbol = new SymbolInformation
                            {
                                Module = cs.Module.Name,
                                Name = cs.Name,
                                SymbolType = SymbolInformation.Type.Class,
                                Position = cs.tok.pos,
                                Line = cs.tok.line,
                                Column = cs.tok.col
                            };
                            information.Add(classSymbol);
                        }
                    }
                }
                catch (Exception e)
                {
                    throw e;
                }
            }

            
            var json = ToJson(information);
            Console.WriteLine("SYMBOLS_START " + json + " SYMBOLS_END");
        }

        public void FindReferences()
        {
            ServerUtils.ApplyArgs(args, reporter);
            string methodToFind = args[0] + "." + args[1] + "." + args[2];
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
                                var fn = (Function)clbl;
                            }
                            else
                            {
                                var m = (Method)clbl;
                                var body = m.Body;
                                information.AddRange(ParseBody(body.SubStatements, methodToFind, m.Name));
                                int i = 0;
                            }
                        }
                    }
                }
                catch (Exception e)
                {
                    Interaction.EOM(Interaction.FAILURE, e.Message);
                }
            }
            var json = ToJson(information);
            var byteArray = Encoding.UTF8.GetBytes(json);
            var base64 = Convert.ToBase64String(byteArray);
            Console.WriteLine("REFERENCE_START" + base64 + "REFERENCE_END");
        }

        private List<ReferenceInformation> ParseBody(IEnumerable<Statement> block, string methodToFind, string currentMethodName)
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
                            Position = callStmt.Tok.pos,
                            Line = callStmt.Tok.line,
                            Column = callStmt.Tok.col,
                            MethodName = currentMethodName
                        });
                    }
                }
                if (statement.SubStatements.Any())
                {
                    information.AddRange(ParseBody(statement.SubStatements, methodToFind, currentMethodName));
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
                foreach (var boogieProgram in boogiePrograms)
                {
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
                                proofs.Add(new ProofInformation
                                {
                                    Proof = ar.Expr.ToString(),
                                    Type = ProofInformation.ProofType.AssertRequires
                                });
                            }
                            else if (proof is AssertEnsuresCmd)
                            {
                                var ae = proof as AssertEnsuresCmd;
                                proofs.Add(new ProofInformation
                                {
                                    Proof = ae.Expr.ToString(),
                                    Type = ProofInformation.ProofType.AssertEnsures
                                });
                            }
                            else if (proof is LoopInitAssertCmd)
                            {
                                var ai = proof as LoopInitAssertCmd;
                                proofs.Add(new ProofInformation
                                {
                                    Proof = ai.Expr.ToString(),
                                    Type = ProofInformation.ProofType.LoopInitAssert
                                });
                            }
                            else if (proof is LoopInvMaintainedAssertCmd)
                            {
                                var am = proof as LoopInvMaintainedAssertCmd;
                                proofs.Add(new ProofInformation
                                {
                                    Proof = am.Expr.ToString(),
                                    Type = ProofInformation.ProofType.LoopInvMaintainedAssert
                                });
                            }
                            else if (proof is AssertCmd)
                            {
                                var a = proof as AssertCmd;
                                proofs.Add(new ProofInformation
                                {
                                    Proof = a.Expr.ToString(),
                                    Type = ProofInformation.ProofType.Assert
                                });
                            }
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
                Field
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