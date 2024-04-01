// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
#nullable enable
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;

namespace Microsoft.Dafny {

  public enum ErrorLevel {
    Info, Warning, Error
  }

  public enum MessageSource {
    Project, Parser, Cloner, RefinementTransformer, Rewriter, Resolver, Translator, Verifier, Compiler, Documentation, TestGeneration, Unknown
  }

  public record DafnyRelatedInformation(IToken Token, string Message);
  public record DafnyDiagnostic(IPhase Phase, string ErrorId, IToken Token, string Message,
    ErrorLevel Level,
    IReadOnlyList<DafnyRelatedInformation> RelatedInformation);

  public class ErrorReporterSink : ErrorReporter {
    public ErrorReporterSink(DafnyOptions options) : base(options) { }

    protected override bool MessageCore(IPhase phase, ErrorLevel level, string errorId, IToken tok, string msg) {
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

    protected override bool MessageCore(IPhase phase, ErrorLevel level, string errorId, IToken tok, string msg) {
      if (level == ErrorLevel.Warning) {
        return false;
      }

      base.MessageCore(phase, level, errorId, tok, msg);
      return WrappedReporter.Message(phase, level, errorId, tok, msgPrefix + msg);
    }
  }
}
