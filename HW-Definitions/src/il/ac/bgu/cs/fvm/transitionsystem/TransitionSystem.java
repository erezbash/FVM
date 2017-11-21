package il.ac.bgu.cs.fvm.transitionsystem;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import il.ac.bgu.cs.fvm.exceptions.FVMException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;

/**
 * Interface of a transition system, as defined in page 20 of the book.
 * 
 * <strong>Important Note to Students</strong>
 * When implementing this interface, you <em>must</em> implement
 * {@code euqals()} and {@code hashCode()}. The equality tests should match any
 * object whose class implements this interface. This is similar to the fact
 * that a {@link TreeSet} and a {@link HashSet} can be equal, even though they
 * do not have the same concrete class.
 * 
 * @param <STATE>  Type of the states in the system.
 * @param <ACTION> Type of the actions in the system.
 * @param <ATOMIC_PROPOSITION> Type of the atomic propositions in the system.
 */
public interface TransitionSystem<STATE,ACTION,ATOMIC_PROPOSITION> {

	/**
	 * Get the name of the transitions system.
	 * 
	 * @return The name of the transition system.
	 */
	String getName();

	/**
	 * Set the name of the transition system.
	 * 
	 * @param name A new for the transition system.
	 */
	void setName(String name);

	/**
	 * Add an action.
	 * Note: This method must be idempotent.
     * 
	 * @param action A name for the new action.
	 */
	void addAction(ACTION action);

	/**
	 * Add an initial state.
	 * Note: This method must be idempotent.
     * 
	 * @param state A state to add to the set of initial states.
	 * @throws FVMException If the state is not in the set of states.
	 */
	void addInitialState(STATE state) throws FVMException;

	/**
	 * Add a state.
	 * Note: This method must be idempotent.
     * 
	 * @param state A name for the new state.
	 * 
	 */
	void addState(STATE state);

	/**
	 * Add a transition.
	 * Note: This method must be idempotent.
     * 
	 * @param t The transition to add.
	 * @throws FVMException If the states and the actions do not exist.
	 */
	void addTransition(Transition<STATE,ACTION> t) throws FVMException;
    
    /**
     * An internal DSL method making manual addition of transitions easier.
     * Usage:
     * {@code ts.addTransitionFrom(a).action(alpha).to(b);}
     * 
     * <em>NOTE:</em> These methods have default implementation, no need to implement
     * it yourself. But you might want to look at the mechanism, if you're into 
     * internal DSLs.
     * 
     * @param s The starting point of this transition.
     * @return A phase 1 transition builder.
     */
    default TransitionBuilder_1<STATE,ACTION,ATOMIC_PROPOSITION> addTransitionFrom(STATE s) {
        return new TransitionBuilder_1<>(this, s);
    }

	/**
	 * Get the actions.
	 * 
	 * @return A copy of the set of actions.
	 */

	Set<ACTION> getActions();

    /**
	 * Add an atomic proposition. Does nothing if the proposition already
	 * exists.
	 * 
	 * @param p The name of the new atomic proposition.
	 */
	void addAtomicProposition(ATOMIC_PROPOSITION p);
    
	/**
	 * Get the the atomic propositions.
	 * 
	 * @return The set of atomic propositions.
	 */
	Set<ATOMIC_PROPOSITION> getAtomicPropositions();

    /**
	 * Label a state by an atomic proposition. Throws an exception if the label
	 * is not an atomic proposition. Does nothing if the sate is already labeled
	 * by the given proposition.
	 * 
	 * @param s A state
	 * @param l An atomic proposition.
	 * @throws FVMException
	 *             When the label is not an atomic proposition.
	 */
	void addToLabel(STATE s, ATOMIC_PROPOSITION l) throws FVMException;

    /**
     * Returns the label of state {@code s}. Result is never {@code null},
     * but might be an empty set.
     * @param s The state whose label we request.
     * @return {@code s}'s label.
     * @throws StateNotFoundException if {@code s} is not a member of {@code this}' state set.
     */
    Set<ATOMIC_PROPOSITION> getLabel(STATE s);
    
	/**
	 * Get the initial states.
	 * 
	 * @return The set of initial states.
	 */
	Set<STATE> getInitialStates();

	/**
	 * Get the labeling function.
	 * 
	 * @return The set of maps representing the labeling function.
	 */
	Map<STATE, Set<ATOMIC_PROPOSITION>> getLabelingFunction();

	/**
	 * Get the states.
	 * 
	 * @return The set of states.
	 */
	Set<STATE> getStates();

	/**
	 * Get the transitions.
	 * 
	 * @return The set of the transitions.
	 */
	Set<Transition<STATE,ACTION>> getTransitions();

	/**
	 * Remove an action.
	 * 
	 * @param action The name of the action to remove.
	 * @throws FVMException If the action in use by a transition.
	 */
	void removeAction(ACTION action) throws FVMException;

	/**
	 * Remove an atomic proposition.
	 * 
	 * @param p The name of the proposition to remove.
	 * @throws FVMException If the proposition is used as label of a state.
	 */
	void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException;

	/**
	 * Remove a state from the set of initial states.
	 * 
	 * @param state The name of the state to remove.
	 */
	void removeInitialState(STATE state);

	/**
	 * atomic proposition, the method returns without changing anything.
	 * 
	 * @param s A state.
	 * @param l An atomic proposition
	 */
	void removeLabel(STATE s, ATOMIC_PROPOSITION l);

	/**
	 * Remove a state.
	 * 
	 * @param state The name of the state to remove.
	 * @throws FVMException If the state is in use by a transition, is labeled, or is in
	 *                      the set of initial states.
	 */
	void removeState(STATE state) throws FVMException;

	/**
	 * Remove a transition.
	 * 
	 * @param t The transition to remove.
	 */
	void removeTransition(Transition<STATE, ACTION> t);
    
    ////////////////////////////////////////////////////////////////////////////
    /// Convenience default method for less painful system creation.
    
    @SuppressWarnings("unchecked")
	default void addStates( STATE... states ) {
        for ( STATE s : states ) {
            addState(s);
        }
    }
    
    default void addAllStates( STATE states[] ) {
        for ( STATE s : states ) {
            addState(s);
        }
    }
    
    default void addAllStates( Iterable<STATE> states ) {
        for ( STATE s : states ) {
            addState(s);
        }
    }
    
    @SuppressWarnings("unchecked")
    default void addActions( ACTION... actions ) {
        for ( ACTION a : actions ) {
            addAction(a);
        }
    }
    
    default void addAllActions( ACTION actions[] ) {
        for ( ACTION a : actions ) {
            addAction(a);
        }
    }
    
    default void addAllActions( Iterable<ACTION> actions ) {
        for ( ACTION a : actions ) {
            addAction(a);
        }
    }
    
    @SuppressWarnings("unchecked")
    default void addAtomicPropositions( ATOMIC_PROPOSITION... aps ) {
        for ( ATOMIC_PROPOSITION ap : aps ) {
            addAtomicProposition(ap);
        }
    }
    
    default void addAllAtomicPropositions( ATOMIC_PROPOSITION aps[] ) {
        for ( ATOMIC_PROPOSITION ap : aps ) {
            addAtomicProposition(ap);
        }
    }
    
    default void addAllAtomicPropositions( Iterable<ATOMIC_PROPOSITION> aps ) {
        for ( ATOMIC_PROPOSITION ap : aps ) {
            addAtomicProposition(ap);
        }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    /// These are builder classes, supporting the internal DSL approach,
    /// that makes manual building of transition systems less painful.
    
    class TransitionBuilder_1<STATE,ACTION,ATOMIC_PROPOSITION> {
        final TransitionSystem<STATE,ACTION,ATOMIC_PROPOSITION> ts;
        final STATE from;
        
        TransitionBuilder_1(TransitionSystem<STATE,ACTION,ATOMIC_PROPOSITION> aTs, STATE startingPoint ){
            ts = aTs;
            from = startingPoint;
        }
        
        public TransitionBuilder_2<STATE,ACTION,ATOMIC_PROPOSITION> action(ACTION a) {
            return new TransitionBuilder_2<>(this, a);
        }
    }
    
    class TransitionBuilder_2<STATE,ACTION,ATOMIC_PROPOSITION> {
        final TransitionBuilder_1<STATE,ACTION,ATOMIC_PROPOSITION> prev;
        final ACTION action;

        public TransitionBuilder_2(TransitionBuilder_1<STATE, ACTION, ATOMIC_PROPOSITION> prev, ACTION action) {
            this.prev = prev;
            this.action = action;
        }
        
        public void to(STATE to) {
            prev.ts.addTransition( new Transition<>(prev.from, action, to));
        }
    }

}
