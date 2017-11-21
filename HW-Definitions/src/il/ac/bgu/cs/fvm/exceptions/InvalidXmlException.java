package il.ac.bgu.cs.fvm.exceptions;

import java.util.Objects;

/**
 * A complaint about a single error in an XML file, such as missing attribute or
 * an invalid reference.
 */
@SuppressWarnings("serial")
public class InvalidXmlException extends FVMException {

	private final TransitionSystemPart part;

	public InvalidXmlException(String string, TransitionSystemPart aPart) {
		super(string);
		part = aPart;
	}

	public TransitionSystemPart getPart() {
		return part;
	}

	@Override
	public int hashCode() {
		int hash = 7;
		hash = 59 * hash + Objects.hashCode(this.part);
		return hash;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final InvalidXmlException other = (InvalidXmlException) obj;
		return this.part == other.part;
	}

	@Override
	public String toString() {
		return "InvalidXmlException{" + getMessage() + " (at " + part + ")}";
	}

}
