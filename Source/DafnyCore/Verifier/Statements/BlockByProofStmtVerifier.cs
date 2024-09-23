using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;

namespace Microsoft.Dafny;

public class BlockByProofStmtVerifier {
  public static void EmitBoogie(BoogieGenerator generator, BlockByProofStmt block, BoogieStmtListBuilder builder,
    Variables locals, BoogieGenerator.ExpressionTranslator etran, ICodeContext codeContext) {
    var proofBuilder = new BoogieStmtListBuilder(generator, builder.Options, builder.Context);

    generator.CurrentIdGenerator.Push();
    generator.TrStmtList(block.Proof.Body, proofBuilder, locals, etran);
    generator.CurrentIdGenerator.Pop();

    generator.TrStmt(block.Body, proofBuilder, locals, etran);

    generator.PathAsideBlock(block.Tok, proofBuilder, builder);
    generator.TrStmt(block.Body, builder.WithContext(builder.Context with {
      AssertMode = AssertMode.Assume
    }), locals, etran);

  }
}

public class Variables : OrderedDictionary<string, Variable> {
  public Variables() : base(v => v.Name) {
  }

}

public class OrderedDictionary<TKey, TValue> {
  private readonly Dictionary<TKey, TValue> keyToValue = new();
  private readonly List<TKey> keyOrder = new();
  private readonly Func<TValue, TKey> getKey;

  public OrderedDictionary(Func<TValue, TKey> getKey) {
    this.getKey = getKey;
  }
  public IEnumerable<TValue> Values => keyOrder.Select(key => keyToValue[key]);

  public void AddRange(IEnumerable<TValue> values) {
    foreach (var value in values) {
      Add(value);
    }
  }

  public TValue GetOrAdd(TValue value) {
    var key = getKey(value);
    return GetOrCreate(key, () => value);
  }

  public TValue GetOrCreate(TKey key, Func<TValue> createValue) {
    if (keyToValue.TryGetValue(key, out var result)) {
      return result;
    }

    result = createValue();
    keyToValue[key] = result;
    keyOrder.Add(key);
    return result;
  }

  public void Add(TValue value) {
    var key = getKey(value);
    keyOrder.Add(key);
    keyToValue[key] = value;
  }
  
  public TValue GetValueOrDefault(TKey key) {
    return keyToValue.GetValueOrDefault(key);
  }

  public int Count => keyOrder.Count;
}