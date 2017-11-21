package il.ac.bgu.cs.fvm.exceptions;


@SuppressWarnings("serial")
public class DeletionOfAttachedStateException extends FVMException {

	Object state;
	TransitionSystemPart where;

	public DeletionOfAttachedStateException(Object state, TransitionSystemPart where) {
		super("An attempt to delete the state " + state + " that is in use in " + where);

		this.state = state;
		this.where = where;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((state == null) ? 0 : state.hashCode());
		result = prime * result + ((where == null) ? 0 : where.hashCode());
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
		DeletionOfAttachedStateException other = (DeletionOfAttachedStateException) obj;
		if (state == null) {
			if (other.state != null)
				return false;
		} else if (!state.equals(other.state))
			return false;
		if (where != other.where)
			return false;
		return true;
	}

}
