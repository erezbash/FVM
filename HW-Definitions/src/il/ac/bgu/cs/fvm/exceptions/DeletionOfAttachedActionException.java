package il.ac.bgu.cs.fvm.exceptions;

@SuppressWarnings("serial")
public class DeletionOfAttachedActionException extends FVMException {

	Object action;
	TransitionSystemPart where;

	public DeletionOfAttachedActionException(Object action, TransitionSystemPart where) {
		super("An attempt to delete the action " + action + " that is in use in " + where);

		this.action = action;
		this.where = where;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((action == null) ? 0 : action.hashCode());
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
		DeletionOfAttachedActionException other = (DeletionOfAttachedActionException) obj;
		if (action == null) {
			if (other.action != null)
				return false;
		} else if (!action.equals(other.action))
			return false;
		if (where != other.where)
			return false;
		return true;
	}

}
