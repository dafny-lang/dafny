// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.IO;
using System.Text;
using Microsoft.Extensions.Primitives;
using Xunit.Abstractions;

namespace DafnyTestGeneration.Test;

public class WriterFromOutputHelper : TextWriter {
  private readonly StringBuilder buffer = new();
  private readonly ITestOutputHelper output;

  public WriterFromOutputHelper(ITestOutputHelper output) {
    this.output = output;
  }

  public override void Write(string value) {
    if (value != null) {
      buffer.Append(value);
    }
  }

  public override void Write(char value) {
    buffer.Append(value);
  }

  public override Encoding Encoding => Encoding.Default;

  public override void WriteLine(string value) {
    output.WriteLine(buffer + value);
    buffer.Clear();
  }

  public override void WriteLine(string format, params object[] arg) {
    output.WriteLine(buffer + format, arg);
    buffer.Clear();
  }

  public override void Flush() {
    output.WriteLine(buffer.ToString());
    base.Flush();
  }
}