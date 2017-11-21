package il.ac.bgu.cs.fvm.exceptions;

@SuppressWarnings("serial")
public class ActionNotFoundException extends FVMException {
	Object action;

	public ActionNotFoundException(Object s) {
		super("An asttempt to compute post for an invalid action (" + s + ")");
		this.action = s;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((action == null) ? 0 : action.hashCode());
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
		ActionNotFoundException other = (ActionNotFoundException) obj;
		if (action == null) {
			if (other.action != null)
				return false;
		} else if (!action.equals(other.action))
			return false;
		return true;
	}

}
