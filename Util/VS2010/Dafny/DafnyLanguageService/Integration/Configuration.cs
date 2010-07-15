using System;
using System.Collections.Generic;
using Microsoft.VisualStudio.Package;
using Microsoft.VisualStudio.TextManager.Interop;

namespace Demo
{
    public static partial class Configuration
    {
        public static Grammar Grammar = new Grammar();
        static List<Microsoft.VisualStudio.TextManager.Interop.IVsColorableItem> colorableItems = new List<Microsoft.VisualStudio.TextManager.Interop.IVsColorableItem>();

        public static IList<Microsoft.VisualStudio.TextManager.Interop.IVsColorableItem> ColorableItems
        {
            get { return colorableItems; }
        }

        public static TokenColor CreateColor(string name, COLORINDEX foreground, COLORINDEX background)
        {
            return CreateColor(name, foreground, background, false, false);
        }

        public static TokenColor CreateColor(string name, COLORINDEX foreground, COLORINDEX background, bool bold, bool strikethrough)
        {
            colorableItems.Add(new ColorableItem(name, foreground, background, bold, strikethrough));
            return (TokenColor)colorableItems.Count;
        }

        public static void ColorToken(string tokenName, TokenType type, TokenColor color, TokenTriggers trigger)
        {
            definitions[tokenName] = new TokenDefinition(type, color, trigger);
        }

        public static TokenDefinition GetDefinition(string tokenName)
        {
            TokenDefinition result;
            return definitions.TryGetValue(tokenName, out result) ? result : defaultDefinition;
        }

        private static TokenDefinition defaultDefinition = new TokenDefinition(TokenType.Text, TokenColor.Text, TokenTriggers.None);
        private static Dictionary<string, TokenDefinition> definitions = new Dictionary<string, TokenDefinition>();

        public struct TokenDefinition
        {
            public TokenDefinition(TokenType type, TokenColor color, TokenTriggers triggers)
            {
                this.TokenType = type;
                this.TokenColor = color;
                this.TokenTriggers = triggers;
            }

            public TokenType TokenType;
            public TokenColor TokenColor;
            public TokenTriggers TokenTriggers;
        }
    }

    public class ColorableItem : Microsoft.VisualStudio.TextManager.Interop.IVsColorableItem
    {
        private string displayName;
        private COLORINDEX background;
        private COLORINDEX foreground;
        private uint fontFlags = (uint)FONTFLAGS.FF_DEFAULT;

        public ColorableItem(string displayName, COLORINDEX foreground, COLORINDEX background, bool bold, bool strikethrough)
        {
            this.displayName = displayName;
            this.background = background;
            this.foreground = foreground;

            if (bold)
                this.fontFlags = this.fontFlags | (uint)FONTFLAGS.FF_BOLD;
            if (strikethrough)
                this.fontFlags = this.fontFlags | (uint)FONTFLAGS.FF_STRIKETHROUGH;
        }

        #region IVsColorableItem Members
        public int GetDefaultColors(COLORINDEX[] piForeground, COLORINDEX[] piBackground)
        {
            if (null == piForeground)
            {
                throw new ArgumentNullException("piForeground");
            }
            if (0 == piForeground.Length)
            {
                throw new ArgumentOutOfRangeException("piForeground");
            }
            piForeground[0] = foreground;

            if (null == piBackground)
            {
                throw new ArgumentNullException("piBackground");
            }
            if (0 == piBackground.Length)
            {
                throw new ArgumentOutOfRangeException("piBackground");
            }
            piBackground[0] = background;

            return Microsoft.VisualStudio.VSConstants.S_OK;
        }

        public int GetDefaultFontFlags(out uint pdwFontFlags)
        {
            pdwFontFlags = this.fontFlags;
            return Microsoft.VisualStudio.VSConstants.S_OK;
        }

        public int GetDisplayName(out string pbstrName)
        {
            pbstrName = displayName;
            return Microsoft.VisualStudio.VSConstants.S_OK;
        }
        #endregion
    }
}