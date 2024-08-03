// See https://aka.ms/new-console-template for more information

using System.Net.Http.Headers;
using Microsoft.Boogie;
using Microsoft.Dafny;

namespace CompilerBuilder;

public interface Printer<T>: IPrinter;

class RecursiveW<T>(Func<Printer<T>> get) : Printer<T>;

class ChoiceW<T>(Printer<T> first, Printer<T> second): Printer<T>;

class Cast<T, U>(Printer<T> printer) : Printer<U>;

public interface IPrinter;

public interface VoidPrinter : IPrinter;

class Empty : VoidPrinter;

class Verbatim : Printer<string>;

class MapW<T, U>(Printer<T> printer, Func<U, T?> map) : Printer<U>;

class Ignore<T>(VoidPrinter printer) : Printer<T>;

internal class TextW(string value) : VoidPrinter;

internal class ManyW<T>(Printer<T> one) : Printer<List<T>>;
  
internal class NumberW : Printer<int>;

internal class IdentifierW : Printer<string>;

class LeftRight<TContainer>(Printer<TContainer> left, Printer<TContainer> right) : Printer<TContainer>;
class TopBottom<TContainer>(Printer<TContainer> left, Printer<TContainer> right) : Printer<TContainer>;

public static class PrinterExtensions {
  public static Printer<U> Map<T, U>(this Printer<T> printer, Func<U,T?> map) {
    return new MapW<T, U>(printer, map);
  }
}