package il.ac.bgu.cs.fvm.ltl;

public class And<L> extends LTL<L> {
	private LTL<L> left;
	private LTL<L> right;

	public And(LTL<L> left, LTL<L> right) {
		this.setLeft(left);
		this.setRight(right);
	}

	/**
	 * @return the left
	 */
	public LTL<L> getLeft() {
		return left;
	}

	/**
	 * @param left
	 *            the left to set
	 */
	public void setLeft(LTL<L> left) {
		this.left = left;
	}

	/**
	 * @return the right
	 */
	public LTL<L> getRight() {
		return right;
	}

	/**
	 * @param right
	 *            the right to set
	 */
	public void setRight(LTL<L> right) {
		this.right = right;
	}

	@Override
	public String toString() {
		return "(" + left + " /\\ " + right + ")";
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((left == null) ? 0 : left.hashCode());
		result = prime * result + ((right == null) ? 0 : right.hashCode());
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
		if (!(obj instanceof And))
			return false;
		And<?> other = (And<?>) obj;
		if (left == null) {
			if (other.left != null)
				return false;
		} else if (!left.equals(other.left))
			return false;
		if (right == null) {
			if (other.right != null)
				return false;
		} else if (!right.equals(other.right))
			return false;
		return true;
	}
}
