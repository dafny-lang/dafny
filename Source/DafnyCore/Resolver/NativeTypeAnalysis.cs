//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using System.Numerics;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

class NativeTypeAnalysis {
  private readonly ErrorReporter reporter;

  public NativeTypeAnalysis(ErrorReporter reporter) {
    this.reporter = reporter;
  }

  public void FigureOutNativeType(NewtypeDecl dd, DafnyOptions options) {

    // Look at the :nativeType attribute, if any
    var hasNativeTypePreference = ReadAttributesForNativePreferences(dd.Attributes, out var nativeTypeChoices);
    if (hasNativeTypePreference == false) {
      // don't use native type
      return;
    }
    if (hasNativeTypePreference == true && dd.BaseType.NormalizeToAncestorType() is not (IntType or BitvectorType)) {
      reporter.Error(MessageSource.Resolver, dd, ":nativeType can only be used on a newtype based on integers or bitvectors");
      return;
    }

    var detectedRange = "";
    List<(NativeType, bool coversEntireIntegerRange)> possibleNativeTypes = GetPossibleNativeTypes(dd, nativeTypeChoices, ref detectedRange);
    if (possibleNativeTypes == null) {
      // An error occurred while computing "possibleNativeTypes"
      return;
    }

    // Finally, of the big-enough native types, pick the first one that is supported by the selected target compiler.
    foreach (var (nativeT, coversEntireIntegerRange) in possibleNativeTypes) {
      if (options.Backend.SupportedNativeTypes.Contains(nativeT.Name)) {
        // Pick this one!
        dd.NativeType = nativeT;
        if (coversEntireIntegerRange && nativeT.Sel != NativeType.Selection.Number) {
          dd.TargetTypeCoversAllBitPatterns = true;
        }

        // Give an info message saying which type was selected--unless the user requested
        // one particular native type, in which case that must have been the one picked.
        if (nativeTypeChoices is { Count: 1 }) {
          Contract.Assert(dd.NativeType == nativeTypeChoices[0]);
          if (dd.TargetTypeCoversAllBitPatterns) {
            reporter.Info(MessageSource.Resolver, dd.Tok,
              $"newtype {dd.Name} is target-complete for {{:nativeType \"{dd.NativeType.Name}\"}}");
          }
        } else {
          var targetComplete = dd.TargetTypeCoversAllBitPatterns ? "target-complete " : "";
          reporter.Info(MessageSource.Resolver, dd.Tok,
            $"newtype {dd.Name} resolves as {targetComplete}{{:nativeType \"{dd.NativeType.Name}\"}} (detected range: {detectedRange})");
        }

        return;
      }
    }
    // Among the choices available to us, we did not find a native type that is big enough and supported by the compiler.
    if (nativeTypeChoices != null) {
      reporter.Error(MessageSource.Resolver, dd,
        "None of the types given in :nativeType arguments is supported by the current compilation target. Try supplying others.");
    } else if (hasNativeTypePreference == true) {
      reporter.Error(MessageSource.Resolver, dd,
        "Dafny's heuristics cannot find a compatible native type. " +
        "Hint: try writing a newtype constraint of the form 'i: int | lowerBound <= i < upperBound && (...any additional constraints...)'.");
    }
  }

  /// <summary>
  /// Return the native types that are big enough to hold values of for "newtypeDecl". If "nativeTypeChoices" is given, then the
  /// search is restricted to those native types.
  ///
  /// For each native type returned, also indicate if that native type covers the entire integer range of "newtypeDecl".
  /// </summary>
  private List<(NativeType, bool coversEntireIntegerRange)> GetPossibleNativeTypes(NewtypeDecl newtypeDecl,
    [CanBeNull] List<NativeType> nativeTypeChoices, ref string detectedRange) {

    // Figure out the variable and constraint.  Usually, these would be just .Var and .Constraint, but
    // in the case .Var/.Constraint are null, these can be computed from the .BaseType recursively.
    var ddVar = newtypeDecl.Var;
    var ddConstraint = newtypeDecl.Constraint;
    for (var ddWhereConstraintsAre = newtypeDecl; ddVar == null;) {
      ddWhereConstraintsAre = ddWhereConstraintsAre.BaseType.AsNewtype;
      if (ddWhereConstraintsAre == null) {
        break;
      }
      ddVar = ddWhereConstraintsAre.Var;
      ddConstraint = ddWhereConstraintsAre.Constraint;
    }

    var ancestorType = newtypeDecl.BaseType.NormalizeToAncestorType();
    if (ancestorType is BitvectorType bitvectorAncestorType) {
      return FigureOutNativeTypeForBitvectorNewtype(newtypeDecl, bitvectorAncestorType, ddVar == null,
        nativeTypeChoices ?? ModuleResolver.NativeTypes, nativeTypeChoices != null);
    } else if (ancestorType is IntType) {
      return FigureOutNativeTypeForIntegerNewtype(newtypeDecl, ddVar, ddConstraint,
        nativeTypeChoices ?? ModuleResolver.NativeTypes, nativeTypeChoices != null, out detectedRange);
    } else {
      // No native type available
      return new List<(NativeType, bool coversEntireIntegerRange)>();
    }
  }

  /// <summary>
  /// Look at the :nativeType attribute, if any, to determine preferences.
  /// A return of false means: don't use native type. (nativeTypes returns as null)
  /// A return of null means: no preference. (nativeTypes returns as null)
  /// A return of true means: make sure a native type is used. Furthermore,
  ///   * if nativeTypes is null, then no particular preference about which native type is picked
  ///   * if nativeTypes is non-null, then the choices of native types are restricted to those.
  /// </summary>
  bool? ReadAttributesForNativePreferences(Attributes attributes, [CanBeNull] out List<NativeType> nativeTypes) {
    nativeTypes = null;
    var args = Attributes.FindExpressions(attributes, "nativeType");
    if (args == null) {
      // There was no :nativeType attribute
      return null;
    }
    if (args.Count == 0) {
      // {:nativeType}
      return true;
    }
    if (args[0] is LiteralExpr { Value: bool and var boolValue }) {
      return boolValue;
    }

    var choices = new List<NativeType>();
    foreach (var arg in args) {
      if (arg is LiteralExpr { Value: string s }) {
        // Get the NativeType for "s"
        var nativeType = ModuleResolver.NativeTypes.Find(nativeType => nativeType.Name == s);
        if (nativeType == null) {
          reporter.Error(MessageSource.Resolver, arg.Tok, ":nativeType '{0}' not known", s);
          return false;
        }
        choices.Add(nativeType);
      } else {
        reporter.Error(MessageSource.Resolver, arg, "unexpected :nativeType argument");
        return false;
      }
    }
    nativeTypes = choices;
    return true;
  }

  /// <summary>
  /// Returns a list of (n, b) pairs, where "n" is a big enough native type to hold "dd" and "b" says whether or not
  /// all bit patterns of "n" are possible values for "dd".
  /// Returns null if a failure is detected and reported.
  /// </summary>
  [CanBeNull]
  private List<(NativeType, bool coversEntireIntegerRange)> FigureOutNativeTypeForBitvectorNewtype(NewtypeDecl dd,
    BitvectorType bitvectorAncestorType, bool noFurtherConstraints,
    List<NativeType> nativeTypesUnderConsideration, bool reportErrorIfTUCDoesNotFit) {

    var bigEnoughNativeTypes = new List<(NativeType, bool coversEntireIntegerRange)>();
    foreach (var nativeType in nativeTypesUnderConsideration) {
      if (nativeType.Bitwidth != 0 && bitvectorAncestorType.Width <= nativeType.Bitwidth) {
        bigEnoughNativeTypes.Add((nativeType, noFurtherConstraints && bitvectorAncestorType.Width == nativeType.Bitwidth));
      } else if (reportErrorIfTUCDoesNotFit && nativeType.Bitwidth == 0) {
        var hint = "";
        if (nativeType.UnsignedCounterpart() is not null and var unsignedCounterpart) {
          var counterpart = ModuleResolver.NativeTypes.Find(nativeT => nativeT.Sel == unsignedCounterpart);
          Contract.Assert(counterpart != null);
          hint = $" Hint: Try using the unsigned native type '{counterpart.Name}'.";
        }
        reporter.Error(MessageSource.Resolver, dd,
          $"A newtype based on a bitvector type ({bitvectorAncestorType.Name}) cannot use a native type that admits negative values ('{nativeType.Name}').{hint}");
        return null;
      } else if (reportErrorIfTUCDoesNotFit) {
        var hint = noFurtherConstraints ? "" : " Note: constraints of bitvector-based newtypes are not considered when determining native types.";
        reporter.Error(MessageSource.Resolver, dd,
          $"The width of bitvector type {bitvectorAncestorType.Name} cannot fit into native type '{nativeType.Name}'.{hint}");
        return null;
      }
    }

    return bigEnoughNativeTypes;
  }

  /// <summary>
  /// Returns a list of (n, b) pairs, where "n" is a big enough native type to hold "dd" and "b" says whether or not
  /// all bit patterns of "n" are possible values for "dd".
  /// Returns null if a failure is detected and reported.
  /// </summary>
  [CanBeNull]
  private List<(NativeType, bool coversEntireIntegerRange)> FigureOutNativeTypeForIntegerNewtype(NewtypeDecl dd,
    [CanBeNull] BoundVar ddVar, [CanBeNull] Expression ddConstraint,
    List<NativeType> nativeTypesUnderConsideration, bool reportErrorIfTUCDoesNotFit,
    out string detectedRange) {
    Contract.Requires((ddVar == null) == (ddConstraint == null));

    bool constraintConsistsSolelyOfRangeConstraints;
    BigInteger? lowBound = null;
    BigInteger? highBound = null;
    if (ddVar == null) {
      constraintConsistsSolelyOfRangeConstraints = true;
    } else {
      var bounds = ModuleResolver.DiscoverAllBounds_SingleVar(ddVar, ddConstraint, out constraintConsistsSolelyOfRangeConstraints);

      foreach (var bound in bounds) {
        void UpdateBounds(BigInteger? lo, BigInteger? hi) {
          if (lo != null && (lowBound == null || lowBound < lo)) {
            lowBound = lo; // we found a more restrictive lower bound
          }
          if (hi != null && (highBound == null || hi < highBound)) {
            highBound = hi; // we found a more restrictive lower bound
          }
        }

        if (bound is IntBoundedPool range) {
          if (range.LowerBound != null && ConstantFolder.TryFoldInteger(range.LowerBound) is not null and var lo) {
            UpdateBounds(lo, null);
          }
          if (range.UpperBound != null && ConstantFolder.TryFoldInteger(range.UpperBound) is not null and var hi) {
            UpdateBounds(null, hi);
          }
        } else if (bound is ExactBoundedPool exact && ConstantFolder.TryFoldInteger(exact.E) is not null and var value) {
          UpdateBounds(value, value + 1);
        }
      }
    }

    var emptyRange = lowBound != null && highBound != null && highBound <= lowBound;
    detectedRange = lowBound == null || highBound == null ? "" : emptyRange ? "empty" : $"{lowBound} .. {highBound}";

    var bigEnoughNativeTypes = new List<(NativeType, bool coversEntireIntegerRange)>();
    foreach (var nativeT in nativeTypesUnderConsideration) {
      bool lowerOk = emptyRange || (lowBound != null && nativeT.LowerBound <= lowBound);
      bool upperOk = emptyRange || (highBound != null && nativeT.UpperBound >= highBound);
      if (lowerOk && upperOk) {
        var coversAllBitPatterns = constraintConsistsSolelyOfRangeConstraints && lowBound == nativeT.LowerBound && highBound == nativeT.UpperBound;
        bigEnoughNativeTypes.Add((nativeT, coversAllBitPatterns));
      } else if (reportErrorIfTUCDoesNotFit) {
        var hint =
          " Hint: try writing a newtype constraint of the form 'i: int | lowerBound <= i < upperBound && (...any additional constraints...)'.";
        reporter.Error(MessageSource.Resolver, dd,
          $"Dafny's heuristics failed to confirm '{nativeT.Name}' to be a compatible native type.{hint}");
        return null;
      }
    }
    return bigEnoughNativeTypes;
  }

}