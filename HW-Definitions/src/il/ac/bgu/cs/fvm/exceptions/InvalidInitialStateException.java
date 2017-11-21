package il.ac.bgu.cs.fvm.exceptions;

@SuppressWarnings("serial")
public class InvalidInitialStateException extends FVMException {
	Object state;

	public InvalidInitialStateException(int line, int col, Object s) {
		super("An asttempt to add an invalid initial state (" + s + ") at " + line + ":" + col);
		state = s;
	}

	public InvalidInitialStateException(Object s) {
		super("An asttempt to add an invalid initial state (" + s + ")");
		this.state = s;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((state == null) ? 0 : state.hashCode());
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
		InvalidInitialStateException other = (InvalidInitialStateException) obj;
		if (state == null) {
			if (other.state != null)
				return false;
		} else if (!state.equals(other.state))
			return false;
		return true;
	}
}
