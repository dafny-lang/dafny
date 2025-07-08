﻿using System;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.IO;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class SymbolGuesser : ISymbolGuesser {
    private readonly ILogger logger;

    public SymbolGuesser(ILogger<SymbolGuesser> logger) {
      this.logger = logger;
    }

    public bool TryGetSymbolBefore(IdeState state, Uri uri, Position position, CancellationToken cancellationToken, [NotNullWhen(true)] out ILegacySymbol? symbol) {
      (symbol, _) = new Guesser(logger, state, cancellationToken).GetSymbolAndItsTypeBefore(uri, position);
      return symbol != null;
    }

    public bool TryGetTypeBefore(IdeState state, Uri uri, Position position, CancellationToken cancellationToken, [NotNullWhen(true)] out ILegacySymbol? typeSymbol) {
      (_, typeSymbol) = new Guesser(logger, state, cancellationToken).GetSymbolAndItsTypeBefore(uri, position);
      return typeSymbol != null;
    }

    private class Guesser {
      private readonly ILogger logger;
      private readonly IdeState state;
      private readonly CancellationToken cancellationToken;

      public Guesser(ILogger logger, IdeState state, CancellationToken cancellationToken) {
        this.logger = logger;
        this.state = state;
        this.cancellationToken = cancellationToken;
      }

      public (ILegacySymbol? Designator, ILegacySymbol? Type) GetSymbolAndItsTypeBefore(Uri uri, Position requestPosition) {
        var position = GetLinePositionBefore(requestPosition);
        if (position == null) {
          return (null, null);
        }
        var memberAccesses = GetMemberAccessChainEndingAt(uri, position);
        if (memberAccesses.Count == 0) {
          logger.LogDebug("could not resolve the member access chain in front of {Position}", requestPosition);

          if (logger.IsEnabled(LogLevel.Trace)) {
            var program = (Program)state.Program;
            var writer = new StringWriter();
            var printer = new Printer(writer, DafnyOptions.Default);
            printer.PrintProgram(program, true);
            logger.LogTrace($"Program:\n{writer}");
          }
          return (null, null);
        }
        return GetSymbolAndTypeOfLastMember(uri, position, memberAccesses);
      }

      private static Position? GetLinePositionBefore(Position requestPosition) {
        var position = requestPosition;
        if (position.Character < 1) {
          return null;
        }
        return new Position(position.Line, position.Character - 1);
      }

      private (ILegacySymbol? Designator, ILegacySymbol? Type) GetSymbolAndTypeOfLastMember(Uri uri, Position position,
        IReadOnlyList<string> memberAccessChain) {
        var enclosingSymbol = state.SignatureAndCompletionTable.GetEnclosingSymbol(uri, position, cancellationToken);
        ILegacySymbol? currentDesignator = null;
        ILegacySymbol? currentDesignatorType = null;
        for (int currentMemberAccess = 0; currentMemberAccess < memberAccessChain.Count; currentMemberAccess++) {
          cancellationToken.ThrowIfCancellationRequested();
          var currentDesignatorName = memberAccessChain[currentMemberAccess];
          if (currentMemberAccess == 0) {
            if (currentDesignatorName == "this") {
              // This actually the type, but TryGetTypeOf respects the case that the symbol itself is already a type.
              currentDesignator = GetEnclosingType(enclosingSymbol);
            } else {
              currentDesignator = GetAccessedSymbolOfEnclosingScopes(enclosingSymbol, currentDesignatorName);
            }
          } else {
            currentDesignator = FindSymbolWithName(currentDesignatorType!, currentDesignatorName);
          }
          if (currentDesignator == null || !state.SignatureAndCompletionTable.TryGetTypeOf(currentDesignator, out currentDesignatorType)) {
            logger.LogDebug("could not resolve the type of the designator {MemberName} of the member access chain '{Chain}'",
              currentMemberAccess, memberAccessChain);
            return (currentDesignator, null);
          }
        }
        return (currentDesignator, currentDesignatorType);
      }

      private ILegacySymbol? GetAccessedSymbolOfEnclosingScopes(ILegacySymbol scope, string name) {
        cancellationToken.ThrowIfCancellationRequested();
        var symbol = FindSymbolWithName(scope, name);
        if (symbol == null && scope.Scope != null) {
          return GetAccessedSymbolOfEnclosingScopes(scope.Scope, name);
        }
        return symbol;
      }

      private TypeWithMembersSymbolBase? GetEnclosingType(ILegacySymbol scope) {
        cancellationToken.ThrowIfCancellationRequested();
        if (scope is TypeWithMembersSymbolBase typeSymbol) {
          return typeSymbol;
        }
        return scope.Scope == null ? null : GetEnclosingType(scope.Scope);
      }

      private ILegacySymbol? FindSymbolWithName(ILegacySymbol containingSymbol, string name) {
        // TODO The current implementation misses the visibility scope of shadowed variables.
        //      To be more precise, variables of nested blocks that shadow outer variables work
        //      Correct. However, if the shadowing variable of the nested scope was declared
        //      After the actual position, it should return the variable of the outer scope.
        //
        // method Example() {
        //   var x := 1; // X1
        //   {
        //     print x; // Should point to X1, but will currently point to X2.
        //     var x:= 2; // X2
        //   }
        // }
        // TODO This only works as long as Dafny does not support overloading.
        return containingSymbol.Children
          .WithCancellation(cancellationToken)
          .FirstOrDefault(child => child.Name == name);
      }

      private IReadOnlyList<string> GetMemberAccessChainEndingAt(Uri uri, Position position) {
        var node = state.Program.FindNode<Expression>(uri, position.ToDafnyPosition());
        var result = new List<string>();
        while (node is ExprDotName exprDotName) {
          node = exprDotName.Lhs;
          result.Add(exprDotName.SuffixName);
        }

        if (node is NameSegment nameSegment) {
          result.Add(nameSegment.Name);
        }

        if (node is ThisExpr) {
          result.Add("this");
        }

        result.Reverse();
        return result;
      }
    }
  }
}
