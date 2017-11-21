package il.ac.bgu.cs.fvm.ltl;

public class TRUE<L> extends LTL<L> {
	@Override
	public int hashCode() {
		return 9876543;
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof TRUE;
	}

	@Override
	public String toString() {
		return "true";
	}
}
