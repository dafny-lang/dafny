using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class SymbolGuesser : ISymbolGuesser {
    private readonly ILogger _logger;

    public SymbolGuesser(ILogger<SymbolGuesser> logger) {
      _logger = logger;
    }

    public bool TryGetSymbolBefore(DafnyDocument document, Position position, CancellationToken cancellationToken, [NotNullWhen(true)] out ISymbol? symbol) {
      (symbol, _) = new Guesser(_logger, document, cancellationToken).GetSymbolAndItsTypeBefore(position);
      return symbol != null;
    }

    public bool TryGetTypeBefore(DafnyDocument document, Position position, CancellationToken cancellationToken, [NotNullWhen(true)] out ISymbol? typeSymbol) {
      (_, typeSymbol) = new Guesser(_logger, document, cancellationToken).GetSymbolAndItsTypeBefore(position);
      return typeSymbol != null;
    }

    private class Guesser {
      private readonly ILogger _logger;
      private readonly DafnyDocument _document;
      private readonly CancellationToken _cancellationToken;

      public Guesser(ILogger logger, DafnyDocument document, CancellationToken cancellationToken) {
        _logger = logger;
        _document = document;
        _cancellationToken = cancellationToken;
      }

      public (ISymbol? Designator, ISymbol? Type) GetSymbolAndItsTypeBefore(Position requestPosition) {
        var position = GetLinePositionBefore(requestPosition);
        if(position == null) {
          _logger.LogTrace("the request position {} is at the beginning of the line, no chance to find a symbol there", requestPosition);
          return (null, null);
        }
        var memberAccesses = GetMemberAccessChainEndingAt(position);
        if(memberAccesses.Length == 0) {
          _logger.LogDebug("could not resolve the member access chain in front of of {}", requestPosition);
          return (null, null);
        }
        return GetSymbolAndTypeOfLastMember(position, memberAccesses);
      }

      private Position? GetLinePositionBefore(Position requestPosition) {
        var position = requestPosition;
        if(position.Character < 1) {
          return null;
        }
        return new Position(position.Line, position.Character - 1);
      }

      private (ISymbol? Designator, ISymbol? Type) GetSymbolAndTypeOfLastMember(Position position, string[] memberAccessChain) {
        var enclosingSymbol = _document.SymbolTable.GetEnclosingSymbol(position, _cancellationToken);
        ISymbol? currentDesignator = null;
        ISymbol? currentDesignatorType = null;
        for(int currentMemberAccess = 0; currentMemberAccess < memberAccessChain.Length; currentMemberAccess++) {
          _cancellationToken.ThrowIfCancellationRequested();
          var currentDesignatorName = memberAccessChain[currentMemberAccess];
          if(currentMemberAccess == 0) {
            if(currentDesignatorName == "this") {
              // This actually the type, but TryGetTypeOf respects the case that the symbol itself is already a type.
              currentDesignator = GetEnclosingClass(enclosingSymbol);
            } else {
              currentDesignator = GetAccessedSymbolOfEnclosingScopes(enclosingSymbol, currentDesignatorName);
            }
          } else {
            currentDesignator = FindSymbolWithName(currentDesignatorType!, currentDesignatorName);
          }
          if(currentDesignator == null || !_document.SymbolTable.TryGetTypeOf(currentDesignator, out currentDesignatorType)) {
            _logger.LogDebug("could not resolve the type of the designator {} of the member access chain '{}'", currentMemberAccess, memberAccessChain);
            return (currentDesignator, null);
          }
        }
        return (currentDesignator, currentDesignatorType);
      }

      private ISymbol? GetAccessedSymbolOfEnclosingScopes(ISymbol scope, string name) {
        _cancellationToken.ThrowIfCancellationRequested();
        var symbol = FindSymbolWithName(scope, name);
        if(symbol == null && scope.Scope != null) {
          return GetAccessedSymbolOfEnclosingScopes(scope.Scope, name);
        }
        return symbol;
      }

      private ClassSymbol? GetEnclosingClass(ISymbol scope) {
        _cancellationToken.ThrowIfCancellationRequested();
        if(scope is ClassSymbol classSymbol) {
          return classSymbol;
        }
        return scope.Scope == null ? null : GetEnclosingClass(scope.Scope);
      }

      private ISymbol? FindSymbolWithName(ISymbol containingSymbol, string name) {
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
          .WithCancellation(_cancellationToken)
          .Where(child => child.Name == name)
          .FirstOrDefault();
      }

      private string[] GetMemberAccessChainEndingAt(Position position) {
        var text = _document.Text.Text;
        var absolutePosition = position.ToAbsolutePosition(text, _cancellationToken);
        return new MemberAccessChainResolver(text, absolutePosition, _cancellationToken).ResolveFromBehind().Reverse().ToArray();
      }
    }

    // TODO This is a simple PoC for code suggestion that only works in a regular manner (tokenization).
    //      It should be refined in a context-free parser to generate a mini AST or something suitable that can better represent the actual syntax.
    //      In general, a speculative parser and semantic checker would be suitable to transition an existing semantic model.
    // TODO Instead of "parsing" when a completion was requested, it should be done when transitioning from one semantic model to another speculative one.
    //      This should simplify the completion implementation and unify other actions depending on the (speculative) semantic model.
    // TODO A small refinement might be to ensure that the first character is a nondigit character. However, this is probably not necessary
    //      for this use-case.
    private class MemberAccessChainResolver {
      private readonly string _text;
      private int _position;
      private readonly CancellationToken _cancellationToken;

      private bool IsWhitespace => char.IsWhiteSpace(_text[_position]);
      private bool IsAtNewStatement => _text[_position] == ';' || _text[_position] == '}' || _text[_position] == '{';
      private bool IsMemberAccessOperator => _text[_position] == '.';

      private bool IsIdentifierCharacter {
        get {
          char character = _text[_position];
          return char.IsLetterOrDigit(character)
            || character == '_'
            || character == '\''
            || character == '?';
        }
      }

      public MemberAccessChainResolver(string text, int endPosition, CancellationToken cancellationToken) {
        _text = text;
        _position = endPosition;
        _cancellationToken = cancellationToken;
      }

      public IEnumerable<string> ResolveFromBehind() {
        while(_position >= 0) {
          _cancellationToken.ThrowIfCancellationRequested();
          SkipWhitespaces();
          if(IsAtNewStatement) {
            yield break;
          }
          // TODO method/function invocations and indexers are not supported yet. Maybe just skip to their designator?
          if(IsIdentifierCharacter) {
            yield return ReadIdentifier();
          } else {
            yield break;
          }
          SkipWhitespaces();
          if(IsMemberAccessOperator) {
            _position--;
          } else {
            yield break;
          }
        }
      }

      private void SkipWhitespaces() {
        while(_position >= 0 && IsWhitespace) {
          _cancellationToken.ThrowIfCancellationRequested();
          _position--;
        }
      }

      private string ReadIdentifier() {
        int identifierEnd = _position + 1;
        while(_position >= 0 && IsIdentifierCharacter) {
          _cancellationToken.ThrowIfCancellationRequested();
          _position--;
        }
        return _text[(_position + 1)..identifierEnd];
      }
    }
  }
}
