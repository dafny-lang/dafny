using System;
using System.IO;
using System.Text;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny;

public class UndisposableTextWriter : TextWriter {
  public UndisposableTextWriter(TextWriter textWriterImplementation) {
    this.textWriterImplementation = textWriterImplementation;
  }

  public override void Close() {
    textWriterImplementation.Close();
  }

  protected override void Dispose(bool disposing) {
    WriteLine("Tried to Dispose the writer at: " + new Exception().StackTrace);
  }

  public override ValueTask DisposeAsync() {
    WriteLine("Tried to DisposeAsync the writer at: " + new Exception().StackTrace);
    return ValueTask.CompletedTask;
  }

  public override void Flush() {
    textWriterImplementation.Flush();
  }

  public override Task FlushAsync() {
    return textWriterImplementation.FlushAsync();
  }

  public override void Write(bool value) {
    textWriterImplementation.Write(value);
  }

  public override void Write(char value) {
    textWriterImplementation.Write(value);
  }

  public override void Write(char[] buffer) {
    textWriterImplementation.Write(buffer);
  }

  public override void Write(char[] buffer, int index, int count) {
    textWriterImplementation.Write(buffer, index, count);
  }

  public override void Write(decimal value) {
    textWriterImplementation.Write(value);
  }

  public override void Write(double value) {
    textWriterImplementation.Write(value);
  }

  public override void Write(int value) {
    textWriterImplementation.Write(value);
  }

  public override void Write(long value) {
    textWriterImplementation.Write(value);
  }

  public override void Write(object value) {
    textWriterImplementation.Write(value);
  }

  public override void Write(ReadOnlySpan<char> buffer) {
    textWriterImplementation.Write(buffer);
  }

  public override void Write(float value) {
    textWriterImplementation.Write(value);
  }

  public override void Write(string value) {
    textWriterImplementation.Write(value);
  }

  public override void Write(string format, object arg0) {
    textWriterImplementation.Write(format, arg0);
  }

  public override void Write(string format, object arg0, object arg1) {
    textWriterImplementation.Write(format, arg0, arg1);
  }

  public override void Write(string format, object arg0, object arg1, object arg2) {
    textWriterImplementation.Write(format, arg0, arg1, arg2);
  }

  public override void Write(string format, params object[] arg) {
    textWriterImplementation.Write(format, arg);
  }

  public override void Write(StringBuilder value) {
    textWriterImplementation.Write(value);
  }

  public override void Write(uint value) {
    textWriterImplementation.Write(value);
  }

  public override void Write(ulong value) {
    textWriterImplementation.Write(value);
  }

  public override Task WriteAsync(char value) {
    return textWriterImplementation.WriteAsync(value);
  }

  public override Task WriteAsync(char[] buffer, int index, int count) {
    return textWriterImplementation.WriteAsync(buffer, index, count);
  }

  public override Task WriteAsync(ReadOnlyMemory<char> buffer, CancellationToken cancellationToken = new CancellationToken()) {
    return textWriterImplementation.WriteAsync(buffer, cancellationToken);
  }

  public override Task WriteAsync(string value) {
    return textWriterImplementation.WriteAsync(value);
  }

  public override Task WriteAsync(StringBuilder value, CancellationToken cancellationToken = new CancellationToken()) {
    return textWriterImplementation.WriteAsync(value, cancellationToken);
  }

  public override void WriteLine() {
    textWriterImplementation.WriteLine();
  }

  public override void WriteLine(bool value) {
    textWriterImplementation.WriteLine(value);
  }

  public override void WriteLine(char value) {
    textWriterImplementation.WriteLine(value);
  }

  public override void WriteLine(char[] buffer) {
    textWriterImplementation.WriteLine(buffer);
  }

  public override void WriteLine(char[] buffer, int index, int count) {
    textWriterImplementation.WriteLine(buffer, index, count);
  }

  public override void WriteLine(decimal value) {
    textWriterImplementation.WriteLine(value);
  }

  public override void WriteLine(double value) {
    textWriterImplementation.WriteLine(value);
  }

  public override void WriteLine(int value) {
    textWriterImplementation.WriteLine(value);
  }

  public override void WriteLine(long value) {
    textWriterImplementation.WriteLine(value);
  }

  public override void WriteLine(object value) {
    textWriterImplementation.WriteLine(value);
  }

  public override void WriteLine(ReadOnlySpan<char> buffer) {
    textWriterImplementation.WriteLine(buffer);
  }

  public override void WriteLine(float value) {
    textWriterImplementation.WriteLine(value);
  }

  public override void WriteLine(string value) {
    textWriterImplementation.WriteLine(value);
  }

  public override void WriteLine(string format, object arg0) {
    textWriterImplementation.WriteLine(format, arg0);
  }

  public override void WriteLine(string format, object arg0, object arg1) {
    textWriterImplementation.WriteLine(format, arg0, arg1);
  }

  public override void WriteLine(string format, object arg0, object arg1, object arg2) {
    textWriterImplementation.WriteLine(format, arg0, arg1, arg2);
  }

  public override void WriteLine(string format, params object[] arg) {
    textWriterImplementation.WriteLine(format, arg);
  }

  public override void WriteLine(StringBuilder value) {
    textWriterImplementation.WriteLine(value);
  }

  public override void WriteLine(uint value) {
    textWriterImplementation.WriteLine(value);
  }

  public override void WriteLine(ulong value) {
    textWriterImplementation.WriteLine(value);
  }

  public override Task WriteLineAsync() {
    return textWriterImplementation.WriteLineAsync();
  }

  public override Task WriteLineAsync(char value) {
    return textWriterImplementation.WriteLineAsync(value);
  }

  public override Task WriteLineAsync(char[] buffer, int index, int count) {
    return textWriterImplementation.WriteLineAsync(buffer, index, count);
  }

  public override Task WriteLineAsync(ReadOnlyMemory<char> buffer, CancellationToken cancellationToken = new CancellationToken()) {
    return textWriterImplementation.WriteLineAsync(buffer, cancellationToken);
  }

  public override Task WriteLineAsync(string value) {
    return textWriterImplementation.WriteLineAsync(value);
  }

  public override Task WriteLineAsync(StringBuilder value, CancellationToken cancellationToken = new CancellationToken()) {
    return textWriterImplementation.WriteLineAsync(value, cancellationToken);
  }

  public override IFormatProvider FormatProvider => textWriterImplementation.FormatProvider;

  public override string NewLine {
    get => textWriterImplementation.NewLine;
    set => textWriterImplementation.NewLine = value;
  }

  private TextWriter textWriterImplementation;
  public override Encoding Encoding => textWriterImplementation.Encoding;



}