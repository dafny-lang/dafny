using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny;

public record LegacyUiForOption(Option Option, Action<Boogie.CommandLineParseState, DafnyOptions> Parse,
  string Category, string Name, string Description, string ArgumentName, object DefaultValue) {

  public static string GenerateHelp(string template, IEnumerable<LegacyUiForOption> options, bool oldStyle = false) {
    var regex = new Regex(@"---- ([^-]+) -+\r?\n *\r?\n");
    var categories = regex.Matches(template).ToArray();

    var optionsByCategory = options.GroupBy(option => option.Category).
      ToDictionary(g => g.Key, g => g as IEnumerable<LegacyUiForOption>);

    var output = new StringBuilder();
    var outputIndex = 0;
    for (var index = 0; index < categories.ToArray().Length; index++) {
      var category = categories.ToArray()[index];
      var preCategory = template.Substring(outputIndex, category.Index - outputIndex);
      output.Append(preCategory);
      outputIndex = category.Index + category.Length;
      var categoryName = category.Groups[1].Value;
      output.Append(category.Value);
      var optionsForCategory = optionsByCategory.GetValueOrDefault(categoryName, Enumerable.Empty<LegacyUiForOption>());

      foreach (var option in optionsForCategory.OrderBy(o => o.Name)) {
        var prefix = oldStyle ? "/" : "--";
        var suffix = oldStyle ? ":" : "=";
        var optionHelpHeader = $"  {prefix}{option.Name}{suffix}<{option.ArgumentName ?? "value"}>";
        var linePrefix = "\n      ";
        var optionHelp = optionHelpHeader + linePrefix + string.Join(linePrefix, option.Description.Split("\n")) + "\n";
        output.AppendLine(optionHelp);
      }
    }
    output.Append(template.Substring(outputIndex));

    return output.ToString();
  }
}