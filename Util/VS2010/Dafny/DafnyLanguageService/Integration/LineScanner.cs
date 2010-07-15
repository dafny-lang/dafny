using System;
using Microsoft.VisualStudio.Package;
using Irony.Parsing;

namespace Demo
{
    public class LineScanner : IScanner
    {
        private Parser parser;

        public LineScanner(Grammar grammar)
        {
            this.parser = new Parser(grammar);
            this.parser.Context.Mode = ParseMode.VsLineScan;
        }

        public bool ScanTokenAndProvideInfoAboutIt(TokenInfo tokenInfo, ref int state)
        {
            // Reads each token in a source line and performs syntax coloring.  It will continue to
            // be called for the source until false is returned.
            Token token = parser.Scanner.VsReadToken(ref state);

            // !EOL and !EOF
            if (token != null && token.Terminal != Grammar.CurrentGrammar.Eof && token.Category != TokenCategory.Error)
            {
                tokenInfo.StartIndex = token.Location.Position;
                tokenInfo.EndIndex = tokenInfo.StartIndex + token.Length - 1;
                if (token.EditorInfo != null) {
                  tokenInfo.Color = (Microsoft.VisualStudio.Package.TokenColor)token.EditorInfo.Color;
                  tokenInfo.Type = (Microsoft.VisualStudio.Package.TokenType)token.EditorInfo.Type;
                }

                if (token.KeyTerm != null && token.KeyTerm.EditorInfo != null)
                {
                    tokenInfo.Trigger =
                        (Microsoft.VisualStudio.Package.TokenTriggers)token.KeyTerm.EditorInfo.Triggers;
                }
                else
                {
                  if (token.EditorInfo != null) {
                    tokenInfo.Trigger =
                        (Microsoft.VisualStudio.Package.TokenTriggers)token.EditorInfo.Triggers;
                  }
                }

                return true;
            }

            return false;
        }

        public void SetSource(string source, int offset)
        {
            // Stores line of source to be used by ScanTokenAndProvideInfoAboutIt.
            parser.Scanner.VsSetSource(source, offset);
        }
    }
}
