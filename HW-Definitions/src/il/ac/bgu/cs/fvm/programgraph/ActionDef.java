package il.ac.bgu.cs.fvm.programgraph;

import java.util.Map;
import java.util.Set;

/**
 * Specifies the format and the effect of an action in a {@link ProgramGraph}.
 */
public interface ActionDef {

	/**
	 * Test if the candidate string matches action defined by this object.
	 * 
	 * @param candidate
	 *            A string that we want to check if it matches the action
	 *            specified by this object.
	 * @return {@code true} if the string matches the action.
	 */
	boolean isMatchingAction(Object candidate);

	/**
	 * apply the effect of the action to the variables.
	 * Note: If the returned value is changed, it must be a fresh copy.
     * 
	 * @param eval
	 *            The evaluation of the variables before the action.
	 * @param action
	 *            The action string.
	 * @return An evaluation of the variables after the action.
	 */
	Map<String, Object> effect(Map<String, Object> eval, Object action);

	/*
	 * A generalization of the above method to sets of definitions.
	 */
	static Map<String, Object> effect(Set<ActionDef> ads, Map<String, Object> eval, Object action) {
		for (ActionDef ad : ads) {
			if (ad.isMatchingAction(action))
				return ad.effect(eval, action);
		}
		return eval;
	}

	/*
	 * A generalization of the above method to sets of definitions.
	 */
	static boolean isMatchingAction(Set<ActionDef> ads, Object candidate) {
		return ads.stream().anyMatch(ad -> ad.isMatchingAction(candidate));
	}

}
