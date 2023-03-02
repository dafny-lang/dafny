public class GrammarChecker {

    public static void main(String ... args) {
        String grammarFile = args[0];
        String docGrammarFile = args[1];
        String inputGrammar = Files.readAllBytes(grammarFile);

        source(inputGrammar).removeComments()
    }

    public static abstract class CharSupplier {
        Character next();
        boolean more();

        public CharSupplier removeComments() {
            int index = 0;
            Character lookahead = null;
            new CharSupplier() {
                Character next() {
                    r = lookahead;
                    lookahead = null;
                    return r;
                }
                boolean more() {
                    if (lookahead == null) {
                        lookahad = this.
                    }

                }
            }
        }
    }

    public static CharSupplier source(String input) { return new Source(input); }
    public static class Source implements CharSupplier {
        String input;
        int index = 0;
        public Source(String s) {
            input = s;
        }
        public boolean more() { return index < input.length; }

        public Character next() { return input[index++] }
    }

    public static CharSupplier removeComments()
}