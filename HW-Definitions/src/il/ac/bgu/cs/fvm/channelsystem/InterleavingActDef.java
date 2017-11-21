package il.ac.bgu.cs.fvm.channelsystem;

import java.util.Set;

import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

/**
 * An interface for specification of joined actions that interleaved 
 * {@link ProgramGraph}s take together (handshaking).
 */
public interface InterleavingActDef extends ActionDef {

	/**
	 * Test if a given action is a side of an interleaved one. For example, the
	 * action {@code _C!0} cannot be performed alone as it requires, e.g., to be
     * taken simultaneously, so {@code isOneSidedAction(0, "_C!0"} is {@code true}. 
	 * 
	 * @param action The name of the action.
	 * @return {@code true} if the given action cannot be taken alone because it
     *         has to wait for its counterpart.
	 */
	boolean isOneSidedAction(String action);

	/**
	 * An extension of {@link #isOneSidedAction(java.lang.String)} to a set of definition objects.  
	 */
	static boolean isOneSidedAction(Set<InterleavingActDef> ads, String act) {
		return ads.stream().anyMatch(ad -> ad.isOneSidedAction(act));
	}

	/**
     * An extension of {@link ActionDef#isMatchingAction(java.util.Set, java.lang.Object)} to a set of definition objects.  
	 */
	static boolean isMatchingAction(Set<InterleavingActDef> ads, String act) {
		return ads.stream().anyMatch(ad -> ad.isMatchingAction(act));
	}
}
