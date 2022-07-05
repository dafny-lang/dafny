#nullable enable

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Text.Json.Nodes;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

record DiagnosticMessageData(MessageSource source, ErrorLevel level, IToken tok, string? category, string message) {
  private static JsonObject SerializeToken(IToken tok) {
    return new JsonObject {
      ["start"] = new JsonObject {
        ["line"] = tok.line,
        ["character"] = tok.col - 1
      }
    };
  }

  private static int SerializeErrorLevel(ErrorLevel lvl) {
    return lvl switch {
      ErrorLevel.Error => 1,
      ErrorLevel.Warning => 2,
      ErrorLevel.Info => 4,
      _ => throw new ArgumentException()
    };
  }

  private static IEnumerable<JsonNode> SerializeRelatedInformation(IToken tok) {
    while (tok is NestedToken ntok) {
      tok = ntok.Inner;
      yield return new JsonObject {
        ["location"] = SerializeToken(tok),
        ["message"] = "Related location",
      };
    }
  }

  public JsonNode ToJson() {
    return new JsonObject {
      ["range"] = SerializeToken(tok),
      ["severity"] = SerializeErrorLevel(level),
      ["message"] = category == null ? message : $"{category}: {message}",
      ["source"] = source.ToString(),
      ["relatedInformation"] = new JsonArray(SerializeRelatedInformation(tok).ToArray())
    };
  }

  public void WriteJsonTo(TextWriter wr) {
    wr.WriteLine(ToJson().ToJsonString(new JsonSerializerOptions { WriteIndented = false }));
  }
}

public class DafnyJsonConsolePrinter : DafnyConsolePrinter {
  public override void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string? category = null) {
    var level = error ? ErrorLevel.Error : ErrorLevel.Warning;
    new DiagnosticMessageData(MessageSource.Verifier, level, tok, category, message).WriteJsonTo(tw);
  }
}

public class JsonConsoleErrorReporter : BatchErrorReporter {
  public override bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg) {
    if (base.Message(source, level, tok, msg) && (DafnyOptions.O is { PrintTooltips: true } || level != ErrorLevel.Info)) {
      new DiagnosticMessageData(source, level, tok, null, msg).WriteJsonTo(Console.Out);
      return true;
    }

    return false;
  }
}
