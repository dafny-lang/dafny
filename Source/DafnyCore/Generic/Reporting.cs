// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
#nullable enable
using System.Collections.Generic;
using System.Resources;
using System.Security.AccessControl;

namespace Microsoft.Dafny {

  public enum ErrorLevel {
    Info, Warning, Error
  }

  public enum MessageSource {
    Project, Parser, Cloner, RefinementTransformer, Rewriter, Resolver, Translator, Verifier, Compiler, Documentation, TestGeneration
  }

  public record DafnyRelatedInformation(TokenRange Range, string ErrorId, string FormatMsg, object[] Arguments) {
    public string Message => Arguments.Length == 0 ? FormatMsg : string.Format(FormatMsg, Arguments);
  }

  public class ErrorReporterSink(DafnyOptions options) : ErrorReporter(options) {
    public override bool MessageCore(DafnyDiagnostic dafnyDiagnostic) {
      return false;
    }

    public override void Error(MessageSource source, string errorId, IOrigin tok, string formatMsg, object[] arguments) {
    }

    public override int Count(ErrorLevel level) {
      return 0;
    }

    public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
      return 0;
    }
  }
}
