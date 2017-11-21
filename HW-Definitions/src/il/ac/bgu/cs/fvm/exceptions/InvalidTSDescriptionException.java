package il.ac.bgu.cs.fvm.exceptions;

import java.util.List;

import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystemXmlFormat;

/**
 * Thrown from a {@link TransitionSystemXmlFormat} when it reads a valid XML
 * file containing an invalid description of a {@link TransitionSystem}.
 * 
 */
@SuppressWarnings("serial")
public class InvalidTSDescriptionException extends FVMException {

	List<FVMException> errors;

	public InvalidTSDescriptionException(List<FVMException> errors) {
		super("XML parsing error (" + errors + ")");
		this.errors = errors;
	}

	public List<FVMException> getErrors() {
		return errors;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((errors == null) ? 0 : errors.hashCode());
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
		InvalidTSDescriptionException other = (InvalidTSDescriptionException) obj;
		if (errors == null) {
			if (other.errors != null)
				return false;
		} else if (!errors.equals(other.errors))
			return false;
		return true;
	}

}
