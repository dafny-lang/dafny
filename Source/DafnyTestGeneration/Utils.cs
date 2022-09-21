using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Text;
using Microsoft.Dafny;
using Errors = Microsoft.Dafny.Errors;
using Parser = Microsoft.Dafny.Parser;
using Program = Microsoft.Dafny.Program;

namespace DafnyTestGeneration {

  public static class Utils {

    /// <summary>
    /// Parse a string read (from a certain file) to a Dafny Program
    /// </summary>
    public static Program? Parse(string source, string fileName = "") {
      ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
      var builtIns = new BuiltIns();
      var reporter = new ConsoleErrorReporter();
      var success = Parser.Parse(source, fileName, fileName, null, module, builtIns,
        new Errors(reporter)) == 0 && Microsoft.Dafny.Main.ParseIncludesDepthFirstNotCompiledFirst(module, builtIns,
        new HashSet<string>(), new Errors(reporter)) == null;
      Program? program = null;
      if (success) {
        program = new Program(fileName, module, builtIns, reporter);
      }
      new Resolver(program).ResolveProgram(program);
      return program;
    }

    public static string Stringify(this object root, bool showNullChildren = false) {

      var builder = new StringBuilder();

      void Helper(ImmutableHashSet<object> visited, object? value, int indentation) {
        if (value == null) {
          builder.Append("null");
          return;
        }

        if (value is IEnumerable<object> enumerable) {
          var sep = "";
          builder.Append("[ ");
          var newIndentation = indentation + 2;
          foreach (var child in enumerable) {
            builder.AppendLine(sep);
            builder.Append(new String(' ', newIndentation));
            Helper(visited, child, newIndentation);
            sep = ", ";
          }

          if (sep != "") {
            builder.AppendLine();
            builder.Append(new String(' ', indentation));
          }
          builder.Append("]");

          return;
        }

        if (value is string) {
          builder.Append($"\"{value}\"");
          return;
        }

        var type = value.GetType();
        if (type.Namespace?.StartsWith("System") == true) {
          builder.Append(value);
          return;
        }

        var properties = type.GetProperties();
        if (properties.Any(p => p.PropertyType.IsAssignableTo(typeof(IEnumerable<object>)))) {

          if (visited.Contains(value)) {
            builder.Append("<visited>");
            return;
          }
          var newVisited = visited.Add(value);

          builder.Append(type.Name + " { ");
          var objectSep = "";
          foreach (var property in properties) {
            var child = property.GetValue(value);
            if (!showNullChildren && child == null) {
              continue;
            }
            builder.Append(objectSep);
            builder.Append(property.Name + ": ");
            Helper(newVisited, child, indentation);
            objectSep = ", ";
          }
          builder.Append(" }");
        } else {
          builder.Append(value);
        }
      }

      Helper(ImmutableHashSet.Create<object>(), root, 0);

      return builder.ToString()!;
    }
  }
}
