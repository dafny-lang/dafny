#nullable enable
using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text.RegularExpressions;
using JetBrains.Annotations;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using Microsoft.Dafny;
using Xunit;

namespace DafnyPipeline.Test {

  // Simple test cases (FormatterWorksFor with only one argument)
  // consist of removing all the indentation from the program,
  // adding it through the formatter, and checking if we obtain the initial result
  //
  // Advanced test cases consist of passing the program and its expected result after indentation
  //
  // Every test is performed with all three newline styles
  // Every formatted program is formatted again to verify that it stays the same.
  public class DocstringTest {
    enum Newlines {
      LF,
      CR,
      CRLF
    };

    private Newlines currentNewlines;

    [Fact]
    public void DocstringWorksForFunctions() {
      DocstringWorksFor(@"
function Test1(i: int): int
  // Test1 computes an int
  // It takes an int and adds 1 to it
{ i + 1 }

function Test2(i: int): int
  //Test2 computes an int
  //It takes an int and adds 2 to it
{ i + 2 }
// Trailing comment

// Test3 computes an int
// It takes an int and adds 3 to it
function Test3(i: int): int
{ i + 3 }

// TODO: MAke this function recursive and this is not a docstring
function Test4(i: int): int
  // Test4 computes an int
  // It takes an int and adds 4 to it
{ i + 4 }

function Test5(i: int): int
  /* Test5 computes an int
   * It takes an int and adds 5 to it */
{ i + 5 }

function Test6(i: int): int
  /** Test6 computes an int
    * It takes an int and adds 6 to it */
{ i + 6 }

function Test7(i: int): int
  /* Test7 computes an int
  It takes an int and adds 7 to it */
{ i + 7 }

function Test8(i: int): int
  /* Test8 computes an int
     It takes an int and adds 8 to it */
{ i + 8 }

function Test9(i: int): int /*
  Test9 computes an int
  It takes an int and adds 9 to it */
{ i + 9 }

function Test10(i: int): int
  /* Test10 computes an int
      It takes an int and adds 10 to it */
{ i + 1 }

function Test11(i: int): int
  /** Test11 computes an int
    *  It takes an int and adds 11 to it */
{ i + 1 }
", Enumerable.Range(1, 9).Select(i =>
        ($"Test{i}", $"Test{i} computes an int\nIt takes an int and adds {i} to it")
        ).Concat(
        new List<(string, string)>() {
          ($"Test10", $"Test10 computes an int\n It takes an int and adds 10 to it"),
          ($"Test11", $"Test11 computes an int\n It takes an int and adds 11 to it")
        }
        ).ToList());
    }

    protected Node? FindNode(Node? node, Func<Node, bool> nodeFinder) {
      if (node == null) {
        return node;
      }
      if (nodeFinder(node)) {
        return node;
      } else {
        foreach (var childNode in node.PreResolveChildren) {
          if (FindNode(childNode, nodeFinder) is { } found) {
            return found;
          }
        }

        return null;
      }
    }

    protected void DocstringWorksFor(string source, string nodeTokenValue, string expectedDocstring) {
      DocstringWorksFor(source, new List<(string nodeTokenValue, string expectedDocstring)>() {
        (nodeTokenValue, expectedDocstring)
      });
    }

    protected void DocstringWorksFor(string source, List<(string nodeTokenValue, string expectedDocstring)> tests) {
      var options = DafnyOptions.Create();
      BatchErrorReporter reporter = new BatchErrorReporter(options);
      var newlineTypes = Enum.GetValues(typeof(Newlines));
      foreach (Newlines newLinesType in newlineTypes) {
        currentNewlines = newLinesType;
        // This formatting test will remove all the spaces at the beginning of the line
        // and then recompute it. The result should be the same string.
        var programString = AdjustNewlines(source);
        ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDefinition(), null);
        Microsoft.Dafny.Type.ResetScopes();
        BuiltIns builtIns = new BuiltIns(options);
        Parser.Parse(programString, "virtual", "virtual", module, builtIns, reporter);
        var dafnyProgram = new Program("programName", module, builtIns, reporter);
        if (reporter.ErrorCount > 0) {
          var error = reporter.AllMessages[ErrorLevel.Error][0];
          Assert.False(true, $"{error.Message}: line {error.Token.line} col {error.Token.col}");
        }

        foreach (var (nodeTokenValue, expectedDocstring) in tests) {
          var targetNode = FindNode(dafnyProgram, node => node.Tok.val == nodeTokenValue);
          if (targetNode == null) {
            Assert.NotNull(targetNode);
          }

          var docString = targetNode.GetDocString(options);
          Assert.Equal(expectedDocstring, docString);
        }
      }
    }

    private string AdjustNewlines(string programString) {
      return currentNewlines switch {
        Newlines.LF => new Regex("\r?\n").Replace(programString, "\n"),
        Newlines.CR => new Regex("\r?\n").Replace(programString, "\r"),
        _ => new Regex("\r?\n").Replace(programString, "\r\n")
      };
    }
  }
}
