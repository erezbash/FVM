package il.ac.bgu.cs.fvm.programgraph;

import java.util.List;
import java.util.Set;

/**
 * A data structure for program graphs.
 *
 * @param <L> Type of the locations.
 * @param <A> Type of the actions.
 */
public interface ProgramGraph<L, A> {

    /**
     * Add an option for the initial value of the variables. The format of the
     * initialization is a list of actions. For example the initialization
     * {@code asList("x := 15", "y:=9")} says that the initial value of x is 15
     * and that the initial value of y is 9.
     * <p>
     * Note that this method can be called several times with different
     * parameters to allow for nondeterministic initialization.
     *
     * @param init A list of initialization actions.
     */
    void addInitalization(List<String> init);

    /**
     * Add an initial state.
     *
     * @param location An initial location
     */
    void addInitialLocation(L location);

    /**
     * Ann a new location (node) to the program graph.
     *
     * @param l The name of the new location.
     */
    void addLocation(L l);

    /**
     * Add a transition to the program graph.
     *
     * @param t A transition to add.
     */
    void addTransition(PGTransition<L,A> t);

    /**
     * @return The set of initialization lists.
     */
    Set<List<String>> getInitalizations();

    /**
     * @return The set of initial locations.
     */
    Set<L> getInitialLocations();

    /**
     * @return The set of locations.
     */
    Set<L> getLocations();

    /**
     * @return The name of the program graph.
     */
    String getName();

    /**
     * @return the transitions
     */
    Set<PGTransition<L, A>> getTransitions();

    /**
     * Removes a location from the program graph.
     *
     * @param l A location to remove.
     */
    void removeLocation(L l);

    /**
     * Remove a transition.
     *
     * @param t A transition to remove.
     */
    void removeTransition(PGTransition<L,A> t);

    /**
     * Set the name of the program graph.
     *
     * @param name The new name.
     */
    void setName(String name);
}
