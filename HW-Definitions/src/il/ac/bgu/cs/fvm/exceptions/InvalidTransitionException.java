package il.ac.bgu.cs.fvm.exceptions;

import il.ac.bgu.cs.fvm.transitionsystem.Transition;

@SuppressWarnings("serial")
public class InvalidTransitionException extends FVMException {
	Transition<?, ?> transition;

	public InvalidTransitionException(Transition<?, ?> transition) {
		super("An asttempt to add an invalid transition (" + transition + ")");
		this.transition = transition;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((transition == null) ? 0 : transition.hashCode());
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
		InvalidTransitionException other = (InvalidTransitionException) obj;
		if (transition == null) {
			if (other.transition != null)
				return false;
		} else if (!transition.equals(other.transition))
			return false;
		return true;
	}

}
