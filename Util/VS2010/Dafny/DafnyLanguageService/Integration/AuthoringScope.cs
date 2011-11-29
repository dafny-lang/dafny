using System;
using System.Collections.Generic;
using Microsoft.VisualStudio;
using Microsoft.VisualStudio.TextManager.Interop;
using Microsoft.VisualStudio.Package;

namespace Demo
{
    public class AuthoringScope : Microsoft.VisualStudio.Package.AuthoringScope
    {
        public AuthoringScope(object parseResult)
        {
            this.parseResult = parseResult;

            // how should this be set?
            this.resolver = new Resolver();
        }

        object parseResult;
        IASTResolver resolver;

        // ParseReason.QuickInfo
        public override string GetDataTipText(int line, int col, out TextSpan span)
        {
            span = new TextSpan();
            return null;
        }

        // ParseReason.CompleteWord
        // ParseReason.DisplayMemberList
        // ParseReason.MemberSelect
        // ParseReason.MemberSelectAndHilightBraces
        public override Microsoft.VisualStudio.Package.Declarations GetDeclarations(IVsTextView view, int line, int col, TokenInfo info, ParseReason reason)
        {
            IList<Declaration> declarations;
            switch (reason)
            {
                case ParseReason.CompleteWord:
                    declarations = resolver.FindCompletions(parseResult, line, col);
                    break;
                case ParseReason.DisplayMemberList:
                case ParseReason.MemberSelect:
                case ParseReason.MemberSelectAndHighlightBraces:
                    declarations = resolver.FindMembers(parseResult, line, col);
                    break;
                default:
                    throw new ArgumentException("reason");
            }

            return new Declarations(declarations);
        }

        // ParseReason.GetMethods
        public override Microsoft.VisualStudio.Package.Methods GetMethods(int line, int col, string name)
        {
            return new Methods(resolver.FindMethods(parseResult, line, col, name));
        }

        // ParseReason.Goto
        public override string Goto(VSConstants.VSStd97CmdID cmd, IVsTextView textView, int line, int col, out TextSpan span)
        {
            span = new TextSpan();
            return null;
        }
    }
}