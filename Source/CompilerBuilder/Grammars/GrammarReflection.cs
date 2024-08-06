namespace CompilerBuilder;

interface GrammarPath {
  Grammar Current { get; }
  GrammarPath? Parent { get; }

  IEnumerable<GrammarPath> SelfAndDescendants { get; }
}

class GrammarPathRoot(Grammar root) : GrammarPath {
  public Grammar Current => root;
  public GrammarPath? Parent => null;
  public IEnumerable<GrammarPath> SelfAndDescendants => [this];
}

class GrammarPathChild(GrammarPath parent, Property<Grammar, Grammar> property) : GrammarPath {
  private Grammar? current;
  public Grammar Current => current ??= property.Get(parent.Current);

  public GrammarPath? Parent => parent;
  public IEnumerable<GrammarPath> SelfAndDescendants => throw new NotImplementedException();
}

public record Property<TContainer, TValue>(Func<TContainer, TValue> Get, Action<TContainer, TValue> Set);