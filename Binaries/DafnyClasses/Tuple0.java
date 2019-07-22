package dafny;

public class Tuple0{

    public Tuple0() {
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        return true;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        sb.append(")");
        return sb.toString();
    }

    @Override
    public int hashCode() {
        // GetHashCode method (Uses the djb2 algorithm)
        // https://stackoverflow.com/questions/1579721/why-are-5381-and-33-so-important-in-the-djb2-algorithm
        long hash = 5381;
        hash = ((hash << 5) + hash) + 0;
        return (int) hash;
    }
}

