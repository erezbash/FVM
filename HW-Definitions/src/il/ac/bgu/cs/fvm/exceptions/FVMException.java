package il.ac.bgu.cs.fvm.exceptions;

@SuppressWarnings("serial")
/**
 * Base class for exceptions thrown from the methods in this library.
 */
public class FVMException extends RuntimeException {

	public FVMException(String string) {
		super(string);
	}

}