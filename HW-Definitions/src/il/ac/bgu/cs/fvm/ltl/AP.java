package il.ac.bgu.cs.fvm.ltl;

public class AP<L> extends LTL<L> {
	L name;

	public AP(L name) {
		this.name = name;
	}

	@Override
	public String toString() {
		return name.toString();
	}

	/**
	 * @return the name
	 */
	public L getName() {
		return name;
	}

	/**
	 * @param name
	 *            the name to set
	 */
	public void setName(L name) {
		this.name = name;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((name == null) ? 0 : name.hashCode());
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
		if (!(obj instanceof AP))
			return false;
		AP<?> other = (AP<?>) obj;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		return true;
	}
	
	

}
