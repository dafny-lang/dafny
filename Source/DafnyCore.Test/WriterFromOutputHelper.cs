#nullable enable
using System.Text;
using Xunit.Abstractions;

namespace DafnyCore.Test;

public class WriterFromOutputHelper(ITestOutputHelper output) : TextWriter {
  private readonly StringBuilder buffer = new();

  public override void Write(string? value) {
    if (value != null) {
      buffer.Append(value);
    }
  }

  public override void Write(char value) {
    buffer.Append(value);
  }

  public override Encoding Encoding => Encoding.Default;

  public override void WriteLine(string? value) {
    try {
      output.WriteLine(buffer + value);
    } catch {
      // ignored because of https://github.com/dafny-lang/dafny/issues/5723
    }
    buffer.Clear();
  }

  public override void WriteLine(string format, params object?[] arg) {
    try {
      output.WriteLine(buffer + format, arg);
    } catch {
      // ignored because of https://github.com/dafny-lang/dafny/issues/5723
    }
    buffer.Clear();
  }

  public override void Flush() {
    try {
      output.WriteLine(buffer.ToString());
    } catch {
      // ignored because of https://github.com/dafny-lang/dafny/issues/5723
    }
    base.Flush();
  }
}