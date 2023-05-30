using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks.Dataflow;

namespace Microsoft.Dafny.LanguageServer.Language;

class TextReaderFromCharArrays : TextReader {
  private readonly List<char[]> arrays;
  private int arrayIndex;
  private int elementIndex;

  public TextReaderFromCharArrays(List<char[]> arrays) {
    this.arrays = arrays;
  }

  public string Text {
    get {
      var size = arrays.Sum(a => a.Length);
      var result = new char[size];
      var offset = 0;
      foreach (var array in arrays) {
        Array.Copy(array, 0, result, offset, array.Length);
        offset += array.Length;
      }
      return new string(result);
    }
  }

  public override int Peek() {
    if (arrayIndex == arrays.Count) {
      return -1;
    }
    return arrays[arrayIndex][elementIndex];
  }

  public override int Read() {
    if (arrayIndex == arrays.Count) {
      return -1;
    }

    var array = arrays[arrayIndex];
    if (elementIndex == array.Length) {
      return -1;
    }
    var result = array[elementIndex++];
    if (array.Length == elementIndex) {
      arrayIndex++;
      elementIndex = 0;
    }
    return result;
  }

  public override int Read(char[] buffer, int index, int count) {
    var remainingCount = count;
    while (remainingCount > 0 && arrayIndex < arrays.Count) {
      var currentArray = arrays[arrayIndex];
      var currentRemainder = currentArray.Length - elementIndex;
      var readCount = Math.Min(currentRemainder, remainingCount);
      Array.Copy(currentArray, elementIndex, buffer, index, readCount);
      elementIndex += readCount;
      index += readCount;
      remainingCount -= readCount;
      if (readCount == currentRemainder) {
        arrayIndex++;
        elementIndex = 0;
      }
    }

    return count - remainingCount;
  }
}