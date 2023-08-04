using System.Collections.Generic;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Microsoft.Dafny.LanguageServer.Workspace;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  public class TextInsertionTest {
    [Fact]
    public void InsertTextAtStart() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = @"
function GetConstant2(): int {
  2
}

".TrimStart();
      var range = new Range((0, 0), (0, 0));
      var expected = @"
function GetConstant2(): int {
  2
}

function GetConstant(): int {
  1
}".TrimStart();
      AssertCorrectBufferUpdate(source, range, change, expected);
    }

    [Fact]
    public void InsertTextAtEnd() {
      var source = @"
function GetConstant(): int {
  1
}

".TrimStart();
      var change = @"
function GetConstant2(): int {
  2
}".TrimStart();
      var range = new Range((4, 0), (4, 0));
      var expected = @"
function GetConstant(): int {
  1
}

function GetConstant2(): int {
  2
}".TrimStart();
      AssertCorrectBufferUpdate(source, range, change, expected);
    }

    [Fact]
    public void InsertTextInTheMiddle() {
      var source = @"
function GetConstant(): int {
  1
}

function GetConstant3(): int {
  3
}".TrimStart();
      var change = @"
function GetConstant2(): int {
  2
}

".TrimStart();
      var range = new Range((4, 0), (4, 0));
      var expected = @"
function GetConstant(): int {
  1
}

function GetConstant2(): int {
  2
}

function GetConstant3(): int {
  3
}".TrimStart();
      AssertCorrectBufferUpdate(source, range, change, expected);
    }

    [Fact]
    public void InsertSingleLineTextInTheMiddleOfALine() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = "Another";
      var range = new Range((0, 12), (0, 12));
      var expected = @"
function GetAnotherConstant(): int {
  1
}".TrimStart();
      AssertCorrectBufferUpdate(source, range, change, expected);
    }

    [Fact]
    public void InsertMultiLineTextInTheMiddleOfALine() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = @"It(): string {
  ""test""
}

function Some";
      var range = new Range((0, 12), (0, 12));
      var expected = @"
function GetIt(): string {
  ""test""
}

function SomeConstant(): int {
  1
}".TrimStart();
      AssertCorrectBufferUpdate(source, range, change, expected);
    }

    [Fact]
    public void InsertMultipleInSingleChange() {
      // Note: line breaks are explicitly defined to avoid compatibility issues of \r and \r\n between
      // the change and the verification.
      var source = "function GetConstant(): int { 1 }";
      var ranges = new[] {
        (new Range((0, 0), (0, 0)), @"class Test {
"),
        (new Range((1, 0), (1, 0)), "  "),
        (new Range((1, 35), (1, 35)), @"
"),
        (new Range((2, 0), (2, 0)), "}")
      };
      var expected = @"
class Test {
  function GetConstant(): int { 1 }
}".TrimStart();
      AssertCorrectBufferUpdate(source, ranges, expected);
    }

    private static void AssertCorrectBufferUpdate(string source, Range range, string change, string expected) {
      AssertCorrectBufferUpdate(source, new[] { (range, change) }, expected);
    }

    private static void AssertCorrectBufferUpdate(string source, IEnumerable<(Range Range, string Change)> ranges, string expected) {
      var buffer = new TextBuffer(source);

      foreach (var (range, change) in ranges) {
        buffer = buffer.ApplyTextChange(new TextDocumentContentChangeEvent() {
          Range = range,
          RangeLength = range.End.Character - range.Start.Character,
          Text = change
        });
      }
      Assert.Equal(expected, buffer.Text);
    }
  }
}
