package il.ac.bgu.cs.fvm.exceptions;

@SuppressWarnings("serial")
public class DeletionOfAttachedAtomicPropositionException extends FVMException {

	Object proposition;
	TransitionSystemPart where;

	public DeletionOfAttachedAtomicPropositionException(Object proposition, TransitionSystemPart where) {
		super("An attempt to delete the proposition " + proposition + " that is in use in " + where);

		this.proposition = proposition;
		this.where = where;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((proposition == null) ? 0 : proposition.hashCode());
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
		DeletionOfAttachedAtomicPropositionException other = (DeletionOfAttachedAtomicPropositionException) obj;
		if (proposition == null) {
			if (other.proposition != null)
				return false;
		} else if (!proposition.equals(other.proposition))
			return false;
		if (where != other.where)
			return false;
		return true;
	}

}
