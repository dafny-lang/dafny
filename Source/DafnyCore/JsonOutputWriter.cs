#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Threading.Tasks;

namespace Microsoft.Dafny;

class JsonOutputWriter(DafnyOptions options) : IDafnyOutputWriter {

  public void Debug(string message) {
    options.BaseOutputWriter.WriteLine(new JsonObject() {
      ["type"] = "debug",
      ["value"] = message
    }.ToJsonString());
  }

  public void Exception(string message) {
    options.BaseOutputWriter.WriteLine(new JsonObject() {
      ["type"] = "exception",
      ["value"] = message
    }.ToJsonString());
  }

  public Task Status(string message) {
    return WriteMessage(message, "status");
  }

  public Task Code(string message) {
    return WriteMessage(message, "code");
  }

  private Task WriteMessage(string message, string type) {
    return options.BaseOutputWriter.WriteLineAsync(new JsonObject() {
      ["type"] = type,
      ["value"] = message
    }.ToJsonString());
  }

  public TextWriter StatusWriter() {
    return new StringWriterWithDispose(s => WriteMessage(s, "status"));
  }

  public TextWriter ErrorWriter() {
    return new StringWriterWithDispose(s => WriteMessage(s, "error"));
  }

  public void WriteDiagnostic(DafnyDiagnostic dafnyDiagnostic) {
    var data = new DiagnosticMessageData(dafnyDiagnostic.Source, dafnyDiagnostic.Level, dafnyDiagnostic.Range,
      dafnyDiagnostic.Level == ErrorLevel.Error ? "Error" : null, dafnyDiagnostic.Message,
      dafnyDiagnostic.RelatedInformation);
    var jsonString = data.ToJsonMessage(options).ToJsonString(new JsonSerializerOptions { WriteIndented = false });
    options.BaseOutputWriter.WriteLine(jsonString);
  }

  public Task Error(string message) {
    return WriteMessage(message, "error");
  }
}

record DiagnosticMessageData(MessageSource Source, ErrorLevel Level, TokenRange Range, string? Category, string Message,
  IReadOnlyList<DafnyRelatedInformation> Related) {
  private static JsonObject SerializePosition(Boogie.IToken tok, bool includeLength) {
    var addition = includeLength ? tok.val.Length : 0;
    return new JsonObject {
      ["pos"] = tok.pos + addition,
      ["line"] = tok.line,
      ["character"] = tok.col - 1 + addition
    };
  }

  private static JsonObject SerializeRange(TokenRange range) {
    return new JsonObject {
      ["start"] = SerializePosition(range.StartToken, false),
      ["end"] = SerializePosition(range.EndToken, range.InclusiveEnd)
    };
  }

  private static JsonObject SerializeToken(DafnyOptions options, TokenRange range) {
    return new JsonObject {
      ["filename"] = range.StartToken.filename,
      ["filePath"] = TokenExtensions.GetRelativeFilename(options, range.StartToken),
      ["uri"] = range.Uri!.AbsoluteUri,
      ["range"] = SerializeRange(range)
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

  private static string SerializeMessage(string? category, string message) {
    return category == null ? message : $"{category}: {message}";
  }

  private static JsonObject SerializeRelated(DafnyOptions options, TokenRange range, string message) {
    return new JsonObject {
      ["location"] = SerializeToken(options, range),
      ["message"] = message,
    };
  }

  public JsonNode ToJson(DafnyOptions options) {
    var auxRelated = Related.Select<DafnyRelatedInformation, JsonNode>(aux =>
      SerializeRelated(options, aux.Range, aux.Message));
    return new JsonObject {
      ["location"] = SerializeToken(options, Range),
      ["severity"] = SerializeErrorLevel(Level),
      ["message"] = SerializeMessage(Category, Message),
      ["source"] = Source.ToString(),
      ["relatedInformation"] = new JsonArray(auxRelated.ToArray())
    };
  }

  public JsonNode ToJsonMessage(DafnyOptions options) {
    return new JsonObject() {
      ["type"] = "diagnostic",
      ["value"] = ToJson(options)
    };
  }
}