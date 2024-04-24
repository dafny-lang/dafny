// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
#nullable enable
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;

namespace Microsoft.Dafny {

  public record MessageSourceBasedPhase(MessageSource MessageSource) : IPhase {
    public IPhase? Parent => null;
  }

  public record SingletonPhase(IPhase Parent, object Key) : IPhase;


  /// <summary>
  /// A phase of compilation
  /// 
  /// A phases can have a parent, and so phases form a tree.
  ///
  /// The children of a phase, are the phases that are discovered and completed as phase of that parent.
  /// </summary>
  public interface IPhase {
    IPhase? Parent { get; }
  }

  public enum ErrorLevel {
    Info, Warning, Error
  }

  public enum MessageSource {
    Project, Parser, Cloner, RefinementTransformer, Rewriter, Resolver, Translator, Verifier, Compiler, Documentation, TestGeneration
  }

  public record DafnyRelatedInformation(IToken Token, string Message);
  public record DafnyDiagnostic(IPhase Phase, string ErrorId, IToken Token, string Message,
    MessageSource Source, ErrorLevel Level,
    IReadOnlyList<DafnyRelatedInformation> RelatedInformation);

  public class ErrorReporterSink : ErrorReporter {
    public ErrorReporterSink(DafnyOptions options) : base(options) { }

    protected override bool MessageCore(MessageSource source, ErrorLevel level, string errorId, IToken tok, string msg) {
      return false;
    }

    public override void Error(MessageSource source, string errorId, IToken tok, string msg) {

    }

    public override int Count(ErrorLevel level) {
      return 0;
    }

    public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
      return 0;
    }
  }

  public class ErrorReporterWrapper : BatchErrorReporter {

    private string msgPrefix;
    public readonly ErrorReporter WrappedReporter;

    public ErrorReporterWrapper(ErrorReporter reporter, string msgPrefix) : base(reporter.Options) {
      this.msgPrefix = msgPrefix;
      this.WrappedReporter = reporter;
    }

    protected override bool MessageCore(MessageSource source, ErrorLevel level, string errorId, IToken tok, string msg) {
      if (level == ErrorLevel.Warning) {
        return false;
      }

      base.MessageCore(source, level, errorId, tok, msg);
      return WrappedReporter.Message(source, level, errorId, tok, msgPrefix + msg);
    }
  }
}
