// See https://aka.ms/new-console-template for more information

using System.Net.Http.Headers;
using Microsoft.Dafny;

namespace CompilerBuilder;

public interface Printer<T>;
public interface Printer;

class Empty : Printer;

class Verbatim : Printer<string>;

class MapW<T, U>(Printer<T> printer, Func<U, T> map) : Printer<U>;

class Ignore<T>(Printer printer) : Printer<T>;

internal class TextW(string value) : Printer;

internal class ManyW<T>(Printer<T> one) : Printer<List<T>>;
  
internal class NumberW : Printer<int>;

internal class IdentifierW : Printer<string>;

class SequenceW<TContainer>(Printer<TContainer> left, Printer<TContainer> right) : Printer<TContainer>;


public static class PrinterExtensions {
  public static Printer<U> Map<T, U>(this Printer<T> printer, Func<U,T> map) {
    return new MapW<T, U>(printer, map);
  }
}