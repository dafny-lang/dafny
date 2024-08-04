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

class Empty : VoidPrinter {
  public static readonly Empty Instance = new();

  private Empty() { }
}

class Verbatim : Printer<string> {
  public static readonly Printer<string> Instance = new Verbatim();

  private Verbatim() { }
}

class MapW<T, U>(Printer<T> printer, Func<U, T?> map) : Printer<U>;

class IgnoreW<T>(VoidPrinter printer) : Printer<T>;

internal class TextW(string value) : VoidPrinter;

internal class NumberW : Printer<int>;

internal class IdentifierW : Printer<string>;

class SequenceW<TLeft, TRight, T>(Printer<TLeft> left, Printer<TRight> right, 
  Func<T, (TLeft, TRight)?> destruct, Orientation mode) : Printer<T>;

class SkipLeftW<T>(VoidPrinter left, Printer<T> right, Orientation mode) : Printer<T>;

class SkipRightW<T>(Printer<T> left, VoidPrinter right, Orientation mode) : Printer<T>;

public static class PrinterExtensions {
  public static Printer<U> Map<T, U>(this Printer<T> printer, Func<U,T?> map) {
    return new MapW<T, U>(printer, map);
  }
}