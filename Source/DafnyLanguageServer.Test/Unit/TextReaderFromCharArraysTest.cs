using System.Linq;
using Microsoft.Dafny.LanguageServer.Language;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit;

public class TextReaderFromCharArraysTest {

  [Fact]
  public void ReadBlockEmptyMiddle() {
    var fourAs = new[] { 'a', 'a', 'a', 'a' };
    var chunks = new[] { fourAs, [], fourAs };
    var emptyMiddleReader = new TextReaderFromCharArrays(chunks);
    var end = emptyMiddleReader.ReadToEnd();
    Assert.Equal("aaaaaaaa", end);
  }

  [Fact]
  public void ReadPeekEmptyStart() {
    var emptyStart = new[] { [], new[] { 'a', 'b', 'c', 'd' } };
    var emptyStartReader = new TextReaderFromCharArrays(emptyStart);
    var firstPeek = emptyStartReader.Peek();
    var firstRead = emptyStartReader.Read();
    Assert.Equal('a', firstPeek);
    Assert.Equal('a', firstRead);
  }

  [Fact]
  public void ReadEmptyMiddle() {
    var emptyMiddleReader = new TextReaderFromCharArrays(new[] { ['a'], [], new[] { 'b' } });
    var a = emptyMiddleReader.Read();
    var b = emptyMiddleReader.Read();
    Assert.Equal('a', a);
    Assert.Equal('b', b);
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