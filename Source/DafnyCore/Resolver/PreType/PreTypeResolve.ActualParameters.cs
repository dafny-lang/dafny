//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using ResolutionContext = Microsoft.Dafny.ResolutionContext;

namespace Microsoft.Dafny {
  public partial class PreTypeResolver {
    /// <summary>
    /// Resolve the actual arguments given in "bindings". Then, check that there is exactly one
    /// actual for each formal, and impose assignable constraints.
    /// "typeMap" is applied to the type of each formal.
    /// This method should be called only once. That is, bindings.arguments is required to be null on entry to this method.
    /// </summary>
    internal void ResolveActualParameters(ActualBindings bindings, List<Formal> formals, IOrigin callTok, object context, ResolutionContext opts,
      Dictionary<TypeParameter, PreType> typeMap, Expression/*?*/ receiver) {
      Contract.Requires(bindings != null);
      Contract.Requires(formals != null);
      Contract.Requires(callTok != null);
      Contract.Requires(context is MethodOrConstructor || context is Function || context is DatatypeCtor || context is ArrowType);
      Contract.Requires(typeMap != null);

      string whatKind;
      string name;
      if (context is MethodOrConstructor cMethod) {
        whatKind = cMethod.WhatKind;
        name = $"{whatKind} '{cMethod.Name}'";
      } else if (context is Function cFunction) {
        whatKind = cFunction.WhatKind;
        name = $"{whatKind} '{cFunction.Name}'";
      } else if (context is DatatypeCtor cCtor) {
        whatKind = "datatype constructor";
        name = $"{whatKind} '{cCtor.Name}'";
      } else {
        var arrowPreType = (DPreType)context;
        Contract.Assert(DPreType.IsArrowType(arrowPreType.Decl));
        whatKind = "function application";
        name = $"function type '{arrowPreType}'";
      }

      // If all arguments are passed positionally, use simple error messages that talk about the count of arguments.
      var onlyPositionalArguments = bindings.ArgumentBindings.TrueForAll(binding => binding.FormalParameterName == null);
      var simpleErrorReported = false;
      if (onlyPositionalArguments) {
        var requiredParametersCount = formals.Count(f => f.DefaultValue == null);
        var actualsCounts = bindings.ArgumentBindings.Count;
        if (requiredParametersCount <= actualsCounts && actualsCounts <= formals.Count) {
          // the situation is plausible
        } else if (requiredParametersCount == formals.Count) {
          // this is the common, classical case of no default parameter values; generate a straightforward error message
          ReportError(callTok, $"wrong number of arguments ({name} expects {formals.Count}, got {actualsCounts})");
          simpleErrorReported = true;
        } else if (actualsCounts < requiredParametersCount) {
          ReportError(callTok, $"wrong number of arguments ({name} expects at least {requiredParametersCount}, got {actualsCounts})");
          simpleErrorReported = true;
        } else {
          ReportError(callTok, $"wrong number of arguments ({name} expects at most {formals.Count}, got {actualsCounts})");
          simpleErrorReported = true;
        }
      }

      // resolve given arguments and populate the "namesToActuals" map
      var namesToActuals = new Dictionary<string, ActualBinding>();
      formals.ForEach(f => namesToActuals.Add(f.Name, null)); // a name mapping to "null" says it hasn't been filled in yet
      var stillAcceptingPositionalArguments = true;
      var bindingIndex = 0;
      foreach (var binding in bindings.ArgumentBindings) {
        var arg = binding.Actual;
        // insert the actual into "namesToActuals" under an appropriate name, unless there is an error
        if (binding.FormalParameterName != null) {
          var pname = binding.FormalParameterName.val;
          stillAcceptingPositionalArguments = false;
          if (!namesToActuals.TryGetValue(pname, out var b)) {
            ReportError(binding.FormalParameterName, $"the binding named '{pname}' does not correspond to any formal parameter");
          } else if (b == null) {
            // all is good
            namesToActuals[pname] = binding;
          } else if (b.FormalParameterName == null) {
            ReportError(binding.FormalParameterName, $"the parameter named '{pname}' is already given positionally");
          } else {
            ReportError(binding.FormalParameterName, $"duplicate binding for parameter name '{pname}'");
          }
        } else if (!stillAcceptingPositionalArguments) {
          ReportError(arg.Origin, "a positional argument is not allowed to follow named arguments");
        } else if (bindingIndex < formals.Count) {
          // use the name of formal corresponding to this positional argument, unless the parameter is name-only
          var formal = formals[bindingIndex];
          var pname = formal.Name;
          if (formal.IsNameOnly) {
            ReportError(arg.Origin, $"nameonly parameter '{pname}' must be passed using a name binding; it cannot be passed positionally");
          }
          Contract.Assert(namesToActuals[pname] == null); // we expect this, since we've only filled parameters positionally so far
          namesToActuals[pname] = binding;
        } else {
          // too many positional arguments
          if (onlyPositionalArguments) {
            // error was reported before the "foreach" loop
            Contract.Assert(simpleErrorReported);
          } else if (formals.Count < bindingIndex) {
            // error was reported on a previous iteration of this "foreach" loop
          } else {
            ReportError(callTok, $"wrong number of arguments ({name} expects {formals.Count}, got {bindings.ArgumentBindings.Count})");
          }
        }

        // resolve argument
        ResolveExpression(arg, opts);
        bindingIndex++;
      }

      var actuals = new List<Expression>();
      var formalIndex = 0;
      var substMap = new Dictionary<IVariable, Expression>();
      foreach (var formal in formals) {
        var b = namesToActuals[formal.Name];
        if (b != null) {
          actuals.Add(b.Actual);
          substMap.Add(formal, b.Actual);
          var what = GetLocationInformation(formal,
            bindings.ArgumentBindings.Count, bindings.ArgumentBindings.IndexOf(b),
            whatKind + (context is Method ? " in-parameter" : " parameter"));

          Constraints.AddSubtypeConstraint(
            formal.PreType.Substitute(typeMap), b.Actual.PreType, b.Actual.Origin,
            $"incorrect argument type {what} (expected {{0}}, found {{1}})");
        } else if (formal.DefaultValue != null) {
          // Note, in the following line, "substMap" is passed in, but it hasn't been fully filled in until the
          // end of this foreach loop. Still, that's soon enough, because DefaultValueExpression won't use it
          // until FillInDefaultValueExpressions at the end of Pass 0 of the Resolver.
          var n = new DefaultValueExpressionPreType(callTok, formal, receiver, substMap, typeMap) { PreType = formal.PreType.Substitute(typeMap) };
          resolver.allDefaultValueExpressions.Add(n);
          actuals.Add(n);
          substMap.Add(formal, n);
        } else {
          // parameter has no value
          if (!simpleErrorReported) {
            var formalDescription = whatKind + (context is Method ? " in-parameter" : " parameter");
            var nameWithIndex = formal.HasName && formal is not ImplicitFormal ? "'" + formal.Name + "'" : "";
            if (formals.Count > 1 || nameWithIndex == "") {
              nameWithIndex += nameWithIndex == "" ? "" : " ";
              nameWithIndex += $"at index {formalIndex}";
            }

            var message = $"{formalDescription} {nameWithIndex} requires an argument of type {formal.Type}";
            ReportError(callTok, message);
          }
        }
        formalIndex++;
      }

      bindings.AcceptArgumentExpressionsAsExactParameterList(actuals);
    }

    private static string GetLocationInformation(Formal parameter, int bindingCount, int bindingIndex, string formalDescription) {
      Contract.Requires(parameter != null);
      Contract.Requires(0 <= bindingIndex);
      Contract.Requires(bindingIndex < bindingCount);
      Contract.Requires(formalDescription != null);

      var description = "";
      if (bindingCount > 1) {
        description += $"at index {bindingIndex} ";
      }

      description += $"for {formalDescription}";

      if (parameter.HasName && parameter is not ImplicitFormal) {
        description += $" '{parameter.Name}'";
      }

      return description;
    }
  }
}
