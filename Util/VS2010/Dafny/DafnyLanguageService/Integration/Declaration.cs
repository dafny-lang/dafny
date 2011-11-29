using System;
using System.Collections.Generic;

namespace Demo
{
    public struct Declaration : IComparable<Declaration>
    {
        public Declaration(string description, string displayText, int glyph, string name)
        {
            this.Description = description;
            this.DisplayText = displayText;
            this.Glyph = glyph;
            this.Name = name;
        }

        public string Description;
        public string DisplayText;
        public int Glyph;
        public string Name;

        #region IComparable<Declaration> Members

        public int CompareTo(Declaration other)
        {
            return DisplayText.CompareTo(other.DisplayText);
        }

        #endregion
    }
}