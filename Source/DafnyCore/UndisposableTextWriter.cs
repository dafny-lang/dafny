using System;
using System.IO;
using System.Text;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny;

class UndisposableTextWriter : TextWriter {
  public UndisposableTextWriter(TextWriter textWriterImplementation) {
    this.textWriterImplementation = textWriterImplementation;
  }

  public object GetLifetimeService() {
    return textWriterImplementation.GetLifetimeService();
        
  }

  public object InitializeLifetimeService() {
    return textWriterImplementation.InitializeLifetimeService();
  }

  public void Close() {
    textWriterImplementation.Close();
  }

  public void Dispose() {
    WriteLine("Tried to Dispose the writer at: " + new Exception().StackTrace);
  }

  public ValueTask DisposeAsync() {
    WriteLine("Tried to DisposeAsync the writer at: " + new Exception().StackTrace);
  }

  public void Flush() {
    textWriterImplementation.Flush();
  }

  public Task FlushAsync() {
    return textWriterImplementation.FlushAsync();
  }

  public void Write(bool value) {
    textWriterImplementation.Write(value);
  }

  public void Write(char value) {
    textWriterImplementation.Write(value);
  }

  public void Write(char[] buffer) {
    textWriterImplementation.Write(buffer);
  }

  public void Write(char[] buffer, int index, int count) {
    textWriterImplementation.Write(buffer, index, count);
  }

  public void Write(decimal value) {
    textWriterImplementation.Write(value);
  }

  public void Write(double value) {
    textWriterImplementation.Write(value);
  }

  public void Write(int value) {
    textWriterImplementation.Write(value);
  }

  public void Write(long value) {
    textWriterImplementation.Write(value);
  }

  public void Write(object value) {
    textWriterImplementation.Write(value);
  }

  public void Write(ReadOnlySpan<char> buffer) {
    textWriterImplementation.Write(buffer);
  }

  public void Write(float value) {
    textWriterImplementation.Write(value);
  }

  public void Write(string value) {
    textWriterImplementation.Write(value);
  }

  public void Write(string format, object arg0) {
    textWriterImplementation.Write(format, arg0);
  }

  public void Write(string format, object arg0, object arg1) {
    textWriterImplementation.Write(format, arg0, arg1);
  }

  public void Write(string format, object arg0, object arg1, object arg2) {
    textWriterImplementation.Write(format, arg0, arg1, arg2);
  }

  public void Write(string format, params object[] arg) {
    textWriterImplementation.Write(format, arg);
  }

  public void Write(StringBuilder value) {
    textWriterImplementation.Write(value);
  }

  public void Write(uint value) {
    textWriterImplementation.Write(value);
  }

  public void Write(ulong value) {
    textWriterImplementation.Write(value);
  }

  public Task WriteAsync(char value) {
    return textWriterImplementation.WriteAsync(value);
  }

  public Task WriteAsync(char[] buffer) {
    return textWriterImplementation.WriteAsync(buffer);
  }

  public Task WriteAsync(char[] buffer, int index, int count) {
    return textWriterImplementation.WriteAsync(buffer, index, count);
  }

  public Task WriteAsync(ReadOnlyMemory<char> buffer, CancellationToken cancellationToken = new CancellationToken()) {
    return textWriterImplementation.WriteAsync(buffer, cancellationToken);
  }

  public Task WriteAsync(string value) {
    return textWriterImplementation.WriteAsync(value);
  }

  public Task WriteAsync(StringBuilder value, CancellationToken cancellationToken = new CancellationToken()) {
    return textWriterImplementation.WriteAsync(value, cancellationToken);
  }

  public void WriteLine() {
    textWriterImplementation.WriteLine();
  }

  public void WriteLine(bool value) {
    textWriterImplementation.WriteLine(value);
  }

  public void WriteLine(char value) {
    textWriterImplementation.WriteLine(value);
  }

  public void WriteLine(char[] buffer) {
    textWriterImplementation.WriteLine(buffer);
  }

  public void WriteLine(char[] buffer, int index, int count) {
    textWriterImplementation.WriteLine(buffer, index, count);
  }

  public void WriteLine(decimal value) {
    textWriterImplementation.WriteLine(value);
  }

  public void WriteLine(double value) {
    textWriterImplementation.WriteLine(value);
  }

  public void WriteLine(int value) {
    textWriterImplementation.WriteLine(value);
  }

  public void WriteLine(long value) {
    textWriterImplementation.WriteLine(value);
  }

  public void WriteLine(object value) {
    textWriterImplementation.WriteLine(value);
  }

  public void WriteLine(ReadOnlySpan<char> buffer) {
    textWriterImplementation.WriteLine(buffer);
  }

  public void WriteLine(float value) {
    textWriterImplementation.WriteLine(value);
  }

  public void WriteLine(string value) {
    textWriterImplementation.WriteLine(value);
  }

  public void WriteLine(string format, object arg0) {
    textWriterImplementation.WriteLine(format, arg0);
  }

  public void WriteLine(string format, object arg0, object arg1) {
    textWriterImplementation.WriteLine(format, arg0, arg1);
  }

  public void WriteLine(string format, object arg0, object arg1, object arg2) {
    textWriterImplementation.WriteLine(format, arg0, arg1, arg2);
  }

  public void WriteLine(string format, params object[] arg) {
    textWriterImplementation.WriteLine(format, arg);
  }

  public void WriteLine(StringBuilder value) {
    textWriterImplementation.WriteLine(value);
  }

  public void WriteLine(uint value) {
    textWriterImplementation.WriteLine(value);
  }

  public void WriteLine(ulong value) {
    textWriterImplementation.WriteLine(value);
  }

  public Task WriteLineAsync() {
    return textWriterImplementation.WriteLineAsync();
  }

  public Task WriteLineAsync(char value) {
    return textWriterImplementation.WriteLineAsync(value);
  }

  public Task WriteLineAsync(char[] buffer) {
    return textWriterImplementation.WriteLineAsync(buffer);
  }

  public Task WriteLineAsync(char[] buffer, int index, int count) {
    return textWriterImplementation.WriteLineAsync(buffer, index, count);
  }

  public Task WriteLineAsync(ReadOnlyMemory<char> buffer, CancellationToken cancellationToken = new CancellationToken()) {
    return textWriterImplementation.WriteLineAsync(buffer, cancellationToken);
  }

  public Task WriteLineAsync(string value) {
    return textWriterImplementation.WriteLineAsync(value);
  }

  public Task WriteLineAsync(StringBuilder value, CancellationToken cancellationToken = new CancellationToken()) {
    return textWriterImplementation.WriteLineAsync(value, cancellationToken);
  }

  public Encoding Encoding => textWriterImplementation.Encoding;

  public IFormatProvider FormatProvider => textWriterImplementation.FormatProvider;

  public string NewLine {
    get => textWriterImplementation.NewLine;
    set => textWriterImplementation.NewLine = value;
  }

  private TextWriter textWriterImplementation;
  public override Encoding Encoding => textWriterImplementation.Encoding;
      
      
      
}