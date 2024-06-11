using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  public class TextReplacementTest {
    [Fact]
    public void ReplaceSingleLineTextAtStart() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = "function GetIt():int";
      var expected = @"
function GetIt():int {
  1
}".TrimStart();

      var range = new Range((0, 0), (0, 27));
      AssertCorrectBufferUpdate(source, range, change, expected);
    }

    private static void AssertCorrectBufferUpdate(string source, Range range, string change, string expected) {
      var buffer = new TextBuffer(source);

      buffer = buffer.ApplyTextChange(new TextDocumentContentChangeEvent() {
        Range = range,
        RangeLength = range.End.Character,
        Text = change
      });
      Assert.Equal(expected, buffer.Text);
    }

    [Fact]
    public void ReplaceMultiLineTextAtStart() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = @"function Get21(): int
{
  2";

      var range = new Range((0, 0), (1, 2));
      var expected = @"
function Get21(): int
{
  21
}".TrimStart();
      AssertCorrectBufferUpdate(source, range, change, expected);
    }

    [Fact]
    public void ReplaceSingleLineTextAtEnd() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = "/* test */ }";
      var range = new Range((2, 0), (2, 1));
      var expected = @"
function GetConstant(): int {
  1
/* test */ }".TrimStart();
      AssertCorrectBufferUpdate(source, range, change, expected);
    }

    [Fact]
    public void ReplaceMultiLineTextAtEnd() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = @"
23
/* test */ }".TrimStart();
      var range = new Range((1, 2), (2, 1));
      var expected = @"
function GetConstant(): int {
  23
/* test */ }".TrimStart();
      AssertCorrectBufferUpdate(source, range, change, expected);
    }

    [Fact]
    public void ReplaceMultiLineTextInTheMiddle() {
      var source = @"
class Test {
    var x: int;
    var y: int;

    function GetX(): int
        reads this
    {
        this.x
    }

    function GetSum(): int
        reads this
    {
        this.x + this.y
    }

    function GetY(): int
        reads this
    {
        this.y
    }
}".TrimStart();
      var change = @"
method GetXY() returns (x: int, y: int)
    {
        x := this.x;
        y := ".TrimStart();
      var range = new Range((10, 4), (13, 17));
      var expected = @"
class Test {
    var x: int;
    var y: int;

    function GetX(): int
        reads this
    {
        this.x
    }

    method GetXY() returns (x: int, y: int)
    {
        x := this.x;
        y := this.y
    }

    function GetY(): int
        reads this
    {
        this.y
    }
}".TrimStart();
      AssertCorrectBufferUpdate(source, range, change, expected);
    }

    [Fact]
    public void ReplaceSingleLineTextInTheMiddleOfALine() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = "Another";
      var range = new Range((0, 12), (0, 20));
      var expected = @"
function GetAnother(): int {
  1
}".TrimStart();
      AssertCorrectBufferUpdate(source, range, change, expected);
    }

    [Fact]
    public void ReplaceMultiLineTextInTheMiddleOfALine() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = @"It(): string {
  ""test""
}

function Some";
      var range = new Range((0, 9), (0, 20));
      var expected = @"
function It(): string {
  ""test""
}

function Some(): int {
  1
}".TrimStart();
      AssertCorrectBufferUpdate(source, range, change, expected);
    }

    [Fact]
    public void RemoveCompleteDocumentContent() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = "";
      var range = new Range((0, 0), (2, 1));
      var expected = "";
      AssertCorrectBufferUpdate(source, range, change, expected);
    }
  }
}
