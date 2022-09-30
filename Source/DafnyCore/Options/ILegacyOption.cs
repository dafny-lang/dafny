using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny;

public interface ILegacyOption : IOptionSpec {
  string Category { get; }
  string LegacyName { get; }

  public static string GenerateHelp(string template, IEnumerable<ILegacyOption> options, bool oldStyle = false) {
    var regex = new Regex(@"---- ([^-]+) -+\r?\n *\r?\n");
    var categories = regex.Matches(template).ToArray();

    var optionsByCategory = options.GroupBy(option => option.Category).
      ToDictionary(g => g.Key, g => g as IEnumerable<ILegacyOption>);

    var output = new StringBuilder();
    var outputIndex = 0;
    for (var index = 0; index < categories.ToArray().Length; index++) {
      var category = categories.ToArray()[index];
      var preCategory = template.Substring(outputIndex, category.Index - outputIndex);
      output.Append(preCategory);
      outputIndex = category.Index + category.Length;
      var categoryName = category.Groups[1].Value;
      output.Append(category.Value);
      var optionsForCategory = optionsByCategory.GetValueOrDefault(categoryName, Enumerable.Empty<ILegacyOption>());

      foreach (var option in optionsForCategory.OrderBy(o => o.LegacyName)) {
        var prefix = oldStyle ? "/" : "--";
        var suffix = oldStyle ? ":" : "=";
        var optionHelpHeader = $"  {prefix}{option.LegacyName}{suffix}<{option.ArgumentName ?? "value"}>";
        var linePrefix = "\n      ";
        var optionHelp = optionHelpHeader + linePrefix + string.Join(linePrefix, option.Description.Split("\n")) + "\n";
        output.AppendLine(optionHelp);
      }
    }
    output.Append(template.Substring(outputIndex));

    return output.ToString();
  }
}