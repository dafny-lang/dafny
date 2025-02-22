using System.Reflection;

namespace Scripts;

public class ResourceLoader {
  /// <summary>
  /// Gets a string from an embedded resource file
  /// </summary>
  /// <param name="resourceName">Name of the resource file</param>
  /// <returns>Contents of the resource file as a string</returns>
  public static string GetResourceAsString(string resourceName) {
    var assembly = Assembly.GetExecutingAssembly();

    // Get the full name of the resource (including namespace)
    string fullResourceName = assembly.GetManifestResourceNames()
      .FirstOrDefault(name => name.EndsWith(resourceName))!;

    if (fullResourceName == null) {
      throw new FileNotFoundException(
        $"Resource {resourceName} not found. Available resources: " +
        string.Join(", ", assembly.GetManifestResourceNames()));
    }

    using var stream = assembly.GetManifestResourceStream(fullResourceName);
    if (stream == null) {
      throw new InvalidOperationException($"Could not load resource {resourceName}");
    }

    using var reader = new StreamReader(stream);
    return reader.ReadToEnd();
  }
}