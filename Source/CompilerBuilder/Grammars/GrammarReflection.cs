namespace CompilerBuilder;

interface GrammarPath {
  Grammar Current { get; }
  GrammarPath? Parent { get; }
}

class GrammarPathRoot(Grammar root) : GrammarPath {
  public Grammar Current => root;
  public GrammarPath? Parent => null;
}

class GrammarPathChild(GrammarPath parent, Property<Grammar, Grammar> property) : GrammarPath {
  private Grammar? current;
  public Grammar Current => current ??= property.Get(parent.Current);

  public GrammarPath? Parent => parent;
}

interface Property<in TContainer, TValue>
{
  Type ValueType { get; }
  TValue Get(TContainer container);
  void Set(TContainer container, TValue value);
}
