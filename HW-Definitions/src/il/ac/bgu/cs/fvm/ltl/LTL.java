package il.ac.bgu.cs.fvm.ltl;

/**
 * A representation of an LTL formula as a parse tree.
 *
 * @param <L> The type of the atomic propositions.
 */
public abstract class LTL<L> {
	public static <L> And<L> and(LTL<L> l, LTL<L> r) {
		return new And<>(l, r);
	}

	public static <L> LTL<L> until(LTL<L> l, LTL<L> r) {
		return new Until<>(l, r);
	}

	public static <L> LTL<L> not(LTL<L> l) {
		return new Not<>(l);
	}

	public static <L> LTL<L> next(LTL<L> l) {
		return new Next<>(l);
	}

	public static <L> LTL<L> true_() {
		return new TRUE<>();
	}

}
