using System.Collections.Generic;
using System.Linq;

namespace DafnyTests {
  public static class EnumerableUtils {
    /**
     * Source: https://docs.microsoft.com/en-us/archive/blogs/ericlippert/computing-a-cartesian-product-with-linq
     */
    public static IEnumerable<IEnumerable<T>> CartesianProduct<T>(this IEnumerable<IEnumerable<T>> sequences) {
      IEnumerable<IEnumerable<T>> emptyProduct = new[] {Enumerable.Empty<T>()};
      return sequences.Aggregate(
        emptyProduct,
        (accumulator, sequence) =>
          from accseq in accumulator
          from item in sequence
          select accseq.Concat(new[] {item}));
    }
  }
}