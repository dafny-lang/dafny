using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Plugins;

public interface IQuickFixCache {
  Program Program { get; set; }
  string Document { get; set; }
}

/// <summary>
/// Plugins implement one or more QuickFixer to offer "quick code fixes",
/// They should return very quickly, so most of the processing has to be done the first time
/// SetProgram is called with a new program.
/// The best way to implement a QuickFixer is to extend CachedQuickFixer,*
/// which takes care of associating keys to any data structure implementing IQuickFixCache
/// that stores the program, the document, and any information you'd like.
/// </summary>
public abstract class QuickFixer {

  /// <summary>
  /// When the code is parsed, this method is provided both the code and ParsedProgram along with an unique key
  /// This unique keys serves to identity the program and the code both when removing it from any cache with UnsetProrgam,
  /// and when querying the plugin for quick fixes with ``GetQuickFixes`
  /// </summary>
  /// <param name="uniqueKey">The unique key</param>
  /// <param name="program">The program, might not be fully resolved</param>
  /// <param name="code">The textual representation of the program</param>
  /// <param name="cancellationToken">Regularly call cancellationToken.ThrowIfCancellationRequested()
  /// to ensure the plugin does not continue to compute something that won't be useful.</param>
  public abstract void SetProgram(string uniqueKey, Program program, string code, CancellationToken cancellationToken);

  /// <summary>
  /// Optionally remove the unique key (e.g. when the user performs an edit in the program)
  /// It is possible for a uniqueKey to be overriden, so this method might not be called when editing a program.
  /// </summary>
  /// <param name="uniqueKey">The unique key representing the program and the document</param>
  public abstract void UnsetProgram(string uniqueKey);

  /// <summary>
  /// Returns the quick fixes associated to the provided selection, which could be a RangeToken
  /// </summary>
  /// <param name="uniqueKey">The unique key representing the program and the document</param>
  /// <param name="selection">The current selection</param>
  /// <returns>A list of potential quickfixes</returns>
  public abstract QuickFix[] GetQuickFixes(string uniqueKey, IToken selection);
}

/// <summary>
/// Plugin-friendly implementation of QuickFixer that takes care of caching the data you'd compute
/// from a Program and a Document;
/// You only need to implement `GetQuickFixes`
/// </summary>
/// <typeparam name="T"></typeparam>
public abstract class CachedQuickFixer<T> : QuickFixer where T : class, IQuickFixCache {
  private readonly ConditionalWeakTable<string, T> cache;

  protected CachedQuickFixer() {
    cache = new ConditionalWeakTable<string, T>();
  }

  /// <summary>
  /// Compute the cache associated to the given program and document
  /// Regularly call cancellationToken.ThrowIfCancellationRequested() to stop any computation if it becomes obsolete.
  /// </summary>
  /// <param name="program">The program</param>
  /// <param name="document"></param>
  /// <param name="cancellationToken"></param>
  /// <returns></returns>
  public abstract T ComputeCache(Program program, string document, CancellationToken cancellationToken);

  /// <summary>
  /// Given some computed cache on a program and a document, returns an array of `QuickFix`
  /// </summary>
  /// <param name="cachedData">The data as returned by ComputeCache</param>
  /// <param name="selection">The current user selection (selection.val == "" if nothing is selected)</param>
  /// <returns>An array of independent `QuickFix` that each could applied independently on the document</returns>
  protected abstract QuickFix[] GetQuickFixes(T cachedData, IToken selection);

  // Overrides so that you don't need to implement them.
  public override void SetProgram(string uniqueKey, Program resolvedProgram, string resolvedCode, CancellationToken cancellationToken) {
    UnsetProgram(uniqueKey);
    // Make sure the cache is not set if we recompute a program.
    // ComputeCache might take some time, and we don't want GetQuickFixes to return something if it's outdated.
    cache.Add(uniqueKey, ComputeCache(resolvedProgram, resolvedCode, cancellationToken));
  }

  public override void UnsetProgram(string uniqueKey) {
    cache.Remove(uniqueKey);
  }

  public override QuickFix[] GetQuickFixes(string uniqueKey, IToken selection) {
    if (cache.TryGetValue(uniqueKey, out var cachedData)) {
      return GetQuickFixes(cachedData, selection);
    }

    return new QuickFix[] { };
  }
}

public class QuickFix {
  // The title to display in the quickfix interface
  public string Title;
  // Edits are all performed at the same time
  public QuickFixEdit[] Edits;
}

public record QuickFixEdit(IToken token, string insertBefore = "", string insertAfter = "", bool removeToken = false);

