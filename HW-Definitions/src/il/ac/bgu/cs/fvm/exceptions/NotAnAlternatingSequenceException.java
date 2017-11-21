package il.ac.bgu.cs.fvm.exceptions;

import java.util.List;
import java.util.Objects;


@SuppressWarnings("serial")
public class NotAnAlternatingSequenceException extends FVMException {

	List<?> e;

	public NotAnAlternatingSequenceException(List<?> e) {
		super("An attempt to check an execution with an array that is not an alternating state,action,...,state sequence (" + e + ")");

		this.e = e;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + e.hashCode();
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
		NotAnAlternatingSequenceException other = (NotAnAlternatingSequenceException) obj;
		return Objects.equals(e, other.e);
	}

}
