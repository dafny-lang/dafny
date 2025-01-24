// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;


/// <summary>
/// The wrapper acts exactly like Model.Func in Boogie except that it skips first N arguments of a function application.
/// This means that the behavior of ModelFuncWrapper is independent of the polymorphism encoding mode in Boogie
/// provided the argsToSkip argument is passed correctly during initialization.
/// 
/// The reason this is a wrapper rather than a subclass is to prevent the use of functionality that might be added to
/// the base class in the future unless it is explicitly supported here and because the creation of Model.Func
/// objects in Boogie is tied to updates to various fields in the Model itself (see MkFunc method)
/// </summary>
class ModelFuncWrapper {

  private readonly Model.Func func;
  private readonly int argsToSkip;

  public ModelFuncWrapper(DafnyModel model, string name, int arity, int argsToSkip) {
    this.argsToSkip = argsToSkip;
    func = model.Model.MkFunc(name, arity + this.argsToSkip);
  }

  public ModelFuncWrapper(Model.Func func, int argsToSkip) {
    this.func = func;
    this.argsToSkip = argsToSkip;
  }

  private ModelFuncTupleWrapper? ConvertFuncTuple(Model.FuncTuple? tuple) {
    return tuple == null ? null : new ModelFuncTupleWrapper(tuple.Result, tuple.Args[argsToSkip..]);
  }

  public ModelFuncTupleWrapper? AppWithResult(Model.Element element) {
    return ConvertFuncTuple(func.AppWithResult(element));
  }

  public IEnumerable<ModelFuncTupleWrapper> AppsWithResult(Model.Element element) {
    return func.AppsWithResult(element).Select(ConvertFuncTuple).OfType<ModelFuncTupleWrapper>();
  }

  public IEnumerable<ModelFuncTupleWrapper> Apps => func.Apps.Select(ConvertFuncTuple).OfType<ModelFuncTupleWrapper>();

  public Model.Element? GetConstant() {
    return func.GetConstant();
  }

  public Model.Element? OptEval(Model.Element? element) {
    if (element == null) {
      return null;
    }
    var app = func.AppWithArg(argsToSkip, element);
    return app?.Result;
  }

  public ModelFuncTupleWrapper? AppWithArg(int index, Model.Element element) {
    return ConvertFuncTuple(func.AppWithArg(argsToSkip + index, element));
  }

  public Model.Element? OptEval(Model.Element? first, Model.Element? second) {
    if (first == null || second == null) {
      return null;
    }
    var apps = func.AppsWithArgs(argsToSkip, first, argsToSkip + 1, second).ToList();
    return !apps.Any() ? null : apps.First().Result;
  }

  public IEnumerable<ModelFuncTupleWrapper> AppsWithArg(int i, Model.Element element) {
    return func.AppsWithArg(i + argsToSkip, element).Select(ConvertFuncTuple).OfType<ModelFuncTupleWrapper>();
  }

  public IEnumerable<ModelFuncTupleWrapper> AppsWithArgs(int i0, Model.Element element0, int i1, Model.Element element1) {
    return func.AppsWithArgs(i0 + argsToSkip, element0, i1 + argsToSkip, element1).Select(ConvertFuncTuple).OfType<ModelFuncTupleWrapper>();
  }

  /// <summary>
  /// Create a new function that merges together the applications of all functions with the given name and arity
  /// at least equal to <param name="arity"></param>
  /// </summary>
  internal static ModelFuncWrapper MergeFunctions(DafnyModel model, List<string> names, int arity) {
    var name = "[" + arity + "]";
    if (model.Model.HasFunc(name)) {
      // Coming up with a new name if the ideal one is reserved
      int id = 0;
      while (model.Model.HasFunc(name + "#" + id)) {
        id++;
      }
      name += "#" + id;
    }
    var result = new ModelFuncWrapper(model, name, arity, 0);
    foreach (var func in model.Model.Functions) {
      if (!names.Contains(func.Name) || func.Arity == null || func.Arity < arity) {
        continue;
      }
      // this removes type arguments when TypeEncodingMethod == Bpl.CoreOptions.TypeEncoding.Arguments
      int offset = func.Arity.Value - arity;
      foreach (var app in func.Apps) {
        result.func.AddApp(app.Result, app.Args[offset..]);
      }
      result.func.Else ??= func.Else;
    }
    return result;
  }

  public class ModelFuncTupleWrapper {

    static readonly Model.Element[] EmptyArgs = [];

    public readonly Model.Element Result;
    public readonly Model.Element[] Args;

    public ModelFuncTupleWrapper(Model.Element res, Model.Element[] args) {
      Args = args ?? EmptyArgs;
      Result = res;
    }
  }
}