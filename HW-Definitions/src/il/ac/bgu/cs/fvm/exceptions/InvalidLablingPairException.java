package il.ac.bgu.cs.fvm.exceptions;

@SuppressWarnings("serial")
public class InvalidLablingPairException extends FVMException {

	Object s;
	Object p;

	public InvalidLablingPairException(Object s, Object p) {
		super("An attempt to add a label to an invalid state or with an invalid proposition (" + s + "," + p + ")");

		this.s = s;
		this.p = p;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((p == null) ? 0 : p.hashCode());
		result = prime * result + ((s == null) ? 0 : s.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		InvalidLablingPairException other = (InvalidLablingPairException) obj;
		if (p == null) {
			if (other.p != null)
				return false;
		} else if (!p.equals(other.p))
			return false;
		if (s == null) {
			if (other.s != null)
				return false;
		} else if (!s.equals(other.s))
			return false;
		return true;
	}

}
