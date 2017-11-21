package il.ac.bgu.cs.fvm.programgraph;

import java.util.Map;
import java.util.Set;

/**
 * Specifies the format and the truth-table of a condition in a program graph.
 */
public interface ConditionDef {
	/**
	 * Evaluate the condition for a given variable evaluation.
	 * 
	 * @param eval
	 *            The values of all the variables.
	 * @param condition
	 *            A string representing the condition to check.
	 * @return {@code true} if the condition is valid for this specification and is met
	 *         for the given variable evaluation.
	 */
	boolean evaluate(Map<String, Object> eval, String condition);

	/*
	 * A generalization of the above method to sets of definitions.
	 */
	static boolean evaluate(Set<ConditionDef> cfs, Map<String, Object> eval, String condition) {
		for (ConditionDef cf : cfs) {
			if (cf.evaluate(eval, condition))
				return true;
		}
		return false;
	}
}
