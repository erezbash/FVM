package il.ac.bgu.cs.fvm.verification;

import java.util.List;

public class VerificationFailed<S> implements VerificationResult<S> {
	List<S> prefix;
	List<S> cycle;

	public List<S> getPrefix() {
		return prefix;
	}

	public void setPrefix(List<S> prefix) {
		this.prefix = prefix;
	}

	public List<S> getCycle() {
		return cycle;
	}

	public void setCycle(List<S> cycle) {
		this.cycle = cycle;
	}

	@Override
	public String toString() {
		String str = "\tPrefix:\n";

		for (S s : prefix) {
			str += "\t\t" + s + "\n";
		}

		str += "\tCycle:\n";

		for (S s : cycle) {
			str += "\t\t" + s + "\n";
		}

		return str;
	}

}