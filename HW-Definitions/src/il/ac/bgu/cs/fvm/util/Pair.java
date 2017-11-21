package il.ac.bgu.cs.fvm.util;

/**
 * A 2-tuple.
 * 
 * @param <FIRST>
 * @param <SECOND>
 */
public class Pair<FIRST, SECOND> {
    
    public final FIRST first;
    public final SECOND second;
    
    public static <X,Y> Pair<X,Y> pair( X x, Y y) {
        return new Pair<>(x,y);
    }
    
    public Pair(FIRST anX, SECOND aY) {
        first = anX;
        second = aY;
    }

    public FIRST getFirst() {
        return first; 
    }

    public SECOND getSecond() { 
        return second;
    }
    
    @Override
    public String toString() {
        return String.format("<%s,%s>", first, second);
    }

    /* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((first == null) ? 0 : first.hashCode());
		result = prime * result + ((second == null) ? 0 : second.hashCode());
		return result;
	}

    /* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (!(obj instanceof Pair))
			return false;
		Pair<?, ?> other = (Pair<?,?>) obj;
		if (first == null) {
			if (other.first != null)
				return false;
		} else if (!first.equals(other.first))
			return false;
		if (second == null) {
			if (other.second != null)
				return false;
		} else if (!second.equals(other.second))
			return false;
		return true;
	}
    
}
