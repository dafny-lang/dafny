package DafnyProfiling;

public class CodeCoverage {
    static int[] tallies;
    public static void Setup(int size) {
        tallies = new int[size];
    }
    public static void TearDown() {
        for (int i = 0; i < tallies.length; i++) {
            System.out.println(i + ": " + tallies[i]);
        }
        tallies = null;
    }
    public static boolean Record(int id) {
        tallies[id]++;
        return true;
    }
}
