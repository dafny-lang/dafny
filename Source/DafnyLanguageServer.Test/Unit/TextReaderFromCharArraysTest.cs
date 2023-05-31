using System.Linq;
using Microsoft.Dafny.LanguageServer.Language;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit; 

public class TextReaderFromCharArraysTest {

  [Fact]
  public void EmptyChunks() {
    var fourAs = new[] { 'a', 'a', 'a', 'a' };
    var chunks = new[] { fourAs, new char[] { }, fourAs };
    var reader = new TextReaderFromCharArrays(chunks);
    var end = reader.ReadToEnd();
    Assert.Equal("aaaaaaaa", end);
  }

  [Fact]
  public void ReadMoreThanContent() {
    var abcd = new[] { 'a', 'b', 'c', 'd' };
    var chunks = new[] { abcd, abcd };
    var reader = new TextReaderFromCharArrays(chunks);
    var buffer = new char[1024];
    var readCount = reader.Read(buffer, 0, buffer.Length);
    Assert.Equal(8, readCount);
    Assert.Equal("abcdabcd", new string(buffer.Take(8).ToArray()));
  }

  [Fact]
  public void ReadPerChar() {
    var ab = new[] { 'a', 'b' };
    var chunks = new[] { ab };
    var reader = new TextReaderFromCharArrays(chunks);
    var first = reader.Read();
    var second = reader.Read();
    var third = reader.Read();

    Assert.Equal('a', first);
    Assert.Equal('b', second);
    Assert.Equal(-1, third);
  }
}