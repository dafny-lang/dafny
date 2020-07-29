namespace Microsoft.Dafny.LSPServer
{
    class TextDocument
    {
        public string Text { get; set; }

        public TextDocument(string text)
        {
            Text = text;
        }
    }
}
