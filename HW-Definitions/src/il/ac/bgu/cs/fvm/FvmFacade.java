package il.ac.bgu.cs.fvm;

import java.io.InputStream;
import java.util.List;
import java.util.Set;

import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;

import java.util.Map;

/**
 * Interface for the entry point class to the HW in this class. Our
 * client/testing code interfaces with the student solutions through this
 * interface only.
 * <br>
 * More about facade: {@linkplain http://www.vincehuston.org/dp/facade.html}.
 */
public interface FvmFacade {

	/**
	 * Dynamically loads the implementation class, and instantiates it.
	 * 
	 * @return A new object implementing this interface.
	 */
	@SuppressWarnings("unchecked")
	static FvmFacade createInstance() {
		try {
			return ((Class<FvmFacade>) Class.forName("il.ac.bgu.cs.fvm.impl.FvmFacadeImpl")).newInstance();
		} catch (InstantiationException | IllegalAccessException ex) {
			throw new RuntimeException("Cannot instantiate from implementation class: " + ex.getMessage(), ex);
		} catch (ClassNotFoundException ex) {
			throw new RuntimeException("Cannot find implementation class: " + ex.getMessage(), ex);
		}
	}

	/**
	 * Creates a new transition system.
	 * 
	 * @param <S>
	 *            Type of states.
	 * @param <A>
	 *            Type of actions.
	 * @param <P>
	 *            Type of atomic propositions.
	 * @return A new transition system object.
	 */
	<S, A, P> TransitionSystem<S, A, P> createTransitionSystem();

	/**
	 * Checks whether an action is deterministic (as defined in class), in the
	 * context of a given {@link TransitionSystem}.
	 * 
	 * @param <S>
	 *            Type of states.
	 * @param <A>
	 *            Type of actions.
	 * @param <P>
	 *            Type of atomic propositions.
	 * @param ts
	 *            The transition system being tested.
	 * @return {@code true} iff the action is deterministic.
	 */
	<S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts);

	/**
	 * Checks whether an action is ap-deterministic (as defined in class), in
	 * the context of a given {@link TransitionSystem}.
	 * 
	 * @param <S>
	 *            Type of states.
	 * @param <A>
	 *            Type of actions.
	 * @param <P>
	 *            Type of atomic propositions.
	 * @param ts
	 *            The transition system being tested.
	 * @return {@code true} iff the action is ap-deterministic.
	 */
	<S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts);

	/**
	 * Checks whether an alternating sequence is an execution of a
	 * {@link TransitionSystem}, as defined in class.
	 * 
	 * @param <S>
	 *            Type of states.
	 * @param <A>
	 *            Type of actions.
	 * @param <P>
	 *            Type of atomic propositions.
	 * @param ts
	 *            The transition system being tested.
	 * @param e
	 *            The sequence that may or may not be an execution of
	 *            {@code ts}.
	 * @return {@code true} iff {@code e} is an execution of {@code ts}.
	 */
	<S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e);

	/**
	 * Checks whether an alternating sequence is an execution fragment of a
	 * {@link TransitionSystem}, as defined in class.
	 * 
	 * @param <S>
	 *            Type of states.
	 * @param <A>
	 *            Type of actions.
	 * @param <P>
	 *            Type of atomic propositions.
	 * @param ts
	 *            The transition system being tested.
	 * @param e
	 *            The sequence that may or may not be an execution fragment of
	 *            {@code ts}.
	 * @return {@code true} iff {@code e} is an execution fragment of
	 *         {@code ts}.
	 */
	<S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e);

	/**
	 * Checks whether an alternating sequence is an initial execution fragment
	 * of a {@link TransitionSystem}, as defined in class.
	 * 
	 * @param <S>
	 *            Type of states.
	 * @param <A>
	 *            Type of actions.
	 * @param <P>
	 *            Type of atomic propositions.
	 * @param ts
	 *            The transition system being tested.
	 * @param e
	 *            The sequence that may or may not be an initial execution
	 *            fragment of {@code ts}.
	 * @return {@code true} iff {@code e} is an execution fragment of
	 *         {@code ts}.
	 */
	<S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e);

	/**
	 * Checks whether an alternating sequence is a maximal execution fragment of
	 * a {@link TransitionSystem}, as defined in class.
	 * 
	 * @param <S>
	 *            Type of states.
	 * @param <A>
	 *            Type of actions.
	 * @param <P>
	 *            Type of atomic propositions.
	 * @param ts
	 *            The transition system being tested.
	 * @param e
	 *            The sequence that may or may not be a maximal execution
	 *            fragment of {@code ts}.
	 * @return {@code true} iff {@code e} is a maximal fragment of {@code ts}.
	 */
	<S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e);

	/**
	 * Checks whether a state in {@code ts} is terminal.
	 * 
	 * @param <S>
	 *            Type of states.
	 * @param <A>
	 *            Type of actions.
	 * @param ts
	 *            Transition system of {@code s}.
	 * @param s
	 *            The state being tested for terminality.
	 * @return {@code true} iff state {@code s} is terminal in {@code ts}.
	 */
	<S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s);

	/**
	 * @param <S>
	 *            Type of states.
	 * @param ts
	 *            Transition system of {@code s}.
	 * @param s
	 *            A state in {@code ts}.
	 * @return All the states in {@code Post(s)}, in the context of {@code ts}.
	 */
	<S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s);

	/**
	 * @param <S>
	 *            Type of states.
	 * @param ts
	 *            Transition system of {@code s}.
	 * @param c
	 *            States in {@code ts}.
	 * @return All the states in {@code Post(s)} where {@code s} is a member of
	 *         {@code c}, in the context of {@code ts}.
	 */
	<S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c);

	/**
	 * @param <S>
	 *            Type of states.
	 * @param <A>
	 *            Type of actions.
	 * @param ts
	 *            Transition system of {@code s}.
	 * @param s
	 *            A state in {@code ts}.
	 * @param a
	 *            An action.
	 * @return All the states that {@code ts} might transition to from
	 *         {@code s}, when action {@code a} is selected.
	 */
	<S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a);

	/**
	 * @param <S>
	 *            Type of states.
	 * @param <A>
	 *            Type of actions.
	 * @param ts
	 *            Transition system of {@code s}.
	 * @param c
	 *            Set of states in {@code ts}.
	 * @param a
	 *            An action.
	 * @return All the states that {@code ts} might transition to from any state
	 *         in {@code c}, when action {@code a} is selected.
	 */
	<S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a);

	/**
	 * @param <S>
	 *            Type of states.
	 * @param ts
	 *            Transition system of {@code s}.
	 * @param s
	 *            A state in {@code ts}.
	 * @return All the states in {@code Pre(s)}, in the context of {@code ts}.
	 */
	<S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s);

	/**
	 * @param <S>
	 *            Type of states.
	 * @param ts
	 *            Transition system of {@code s}.
	 * @param c
	 *            States in {@code ts}.
	 * @return All the states in {@code Pre(s)} where {@code s} is a member of
	 *         {@code c}, in the context of {@code ts}.
	 */
	<S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c);

	/**
	 * @param <S>
	 *            Type of states.
	 * @param <A>
	 *            Type of actions.
	 * @param ts
	 *            Transition system of {@code s}.
	 * @param s
	 *            A state in {@code ts}.
	 * @param a
	 *            An action.
	 * @return All the states that {@code ts} might transitioned from, when in
	 *         {@code s}, and the last action was {@code a}.
	 */
	<S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a);

	/**
	 * @param <S>
	 *            Type of states.
	 * @param <A>
	 *            Type of actions.
	 * @param ts
	 *            Transition system of {@code s}.
	 * @param c
	 *            Set of states in {@code ts}.
	 * @param a
	 *            An action.
	 * @return All the states that {@code ts} might transitioned from, when in
	 *         any state in {@code c}, and the last action was {@code a}.
	 */
	<S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a);

	/**
	 * Implements the {@code reach(TS)} function.
	 * 
	 * @param <S>
	 *            Type of states.
	 * @param <A>
	 *            Type of actions.
	 * @param ts
	 *            Transition system of {@code s}.
	 * @return All states reachable in {@code ts}.
	 */
	<S, A> Set<S> reach(TransitionSystem<S, A, ?> ts);

	/**
	 * Compute the synchronous product of two transition systems.
	 *
	 * @param <S1>
	 *            Type of states in the first system.
	 * @param <S2>
	 *            Type of states in the first system.
	 * @param <A>
	 *            Type of actions (in both systems).
	 * @param <P>
	 *            Type of atomic propositions (in both systems).
	 * @param ts1
	 *            The first transition system.
	 * @param ts2
	 *            The second transition system.
	 *
	 * @return A transition system that represents the product of the two.
	 */
	<S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
			TransitionSystem<S2, A, P> ts2);

	/**
	 * Compute the synchronous product of two transition systems.
	 *
	 * @param <S1>
	 *            Type of states in the first system.
	 * @param <S2>
	 *            Type of states in the first system.
	 * @param <A>
	 *            Type of actions (in both systems).
	 * @param <P>
	 *            Type of atomic propositions (in both systems).
	 * @param ts1
	 *            The first transition system.
	 * @param ts2
	 *            The second transition system.
	 * @param handShakingActions
	 *            Set of actions both systems perform together.
	 *
	 * @return A transition system that represents the product of the two.
	 */
	<S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
			TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions);

	/**
	 * Creates a new {@link ProgramGraph} object.
	 * 
	 * @param <L>
	 *            Type of locations in the graph.
	 * @param <A>
	 *            Type of actions of the graph.
	 * @return A new program graph instance.
	 */
	<L, A> ProgramGraph<L, A> createProgramGraph();

	/**
	 * Interleaves two program graphs.
	 * 
	 * @param <L1>
	 *            Type of locations in the first graph.
	 * @param <L2>
	 *            Type of locations in the second graph.
	 * @param <A>
	 *            Type of actions in BOTH GRAPHS.
	 * @param pg1
	 *            The first program graph.
	 * @param pg2
	 *            The second program graph.
	 * @return Interleaved program graph.
	 */
	<L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2);

	/**
	 * Creates a {@link TransitionSystem} representing the passed circuit.
	 * 
	 * @param c
	 *            The circuit to translate into a {@link TransitionSystem}.
	 * @return A {@link TransitionSystem} representing {@code c}.
	 */
	TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> 
        transitionSystemFromCircuit(Circuit c);

	/**
	 * Creates a {@link TransitionSystem} from a program graph.
	 * 
	 * @param <L>
	 *            Type of program graph locations.
	 * @param <A>
	 *            Type of program graph actions.
	 * @param pg
	 *            The program graph to be translated into a transition system.
	 * @param actionDefs
	 *            Defines the effect of each action.
	 * @param conditionDefs
	 *            Defines the conditions (guards) of the program graph.
	 * @return A transition system representing {@code pg}.
	 */
	<L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(
			ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs);

	/**
	 * Creates a transition system representing channel system {@code cs}.
	 * 
	 * @param <L>
	 *            Type of locations in the channel system.
	 * @param <A>
	 *            Type of actions in the channel system.
	 * @param cs
	 *            The channel system to be translated into a transition system.
	 * @return A transition system representing {@code cs}.
	 */
	<L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
			ChannelSystem<L, A> cs);

	/**
	 * Creates a transition system from a transition system and an automaton.
	 * 
	 * @param <Sts>
	 *            Type of states in the transition system.
	 * @param <Saut>
	 *            Type of states in the automaton.
	 * @param <A>
	 *            Type of actions in the transition system.
	 * @param <P>
	 *            Type of atomic propositions in the transition system, which is
	 *            also the type of the automaton alphabet.
	 * @param ts
	 *            The transition system.
	 * @param aut
	 *            The automaton.
	 * @return The product of {@code ts} with {@code aut}.
	 */
	<Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> 
        product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut);

	/**
	 * Construct a program graph from nanopromela code.
	 * 
	 * @param filename
	 *            The nanopromela code.
	 * @return A program graph for the given code.
	 * @throws Exception
	 *             If the code is invalid.
	 */
	ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception;

	/**
	 * Construct a program graph from nanopromela code.
	 * 
	 * @param nanopromela
	 *            The nanopromela code.
	 * @return A program graph for the given code.
	 * @throws Exception
	 *             If the code is invalid.
	 */
	ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception;

	/**
	 * Construct a program graph from nanopromela code.
	 * 
	 * @param inputStream
	 *            The nanopromela code.
	 * @return A program graph for the given code.
	 * @throws Exception
	 *             If the code is invalid.
	 */
	ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception;

	/**
	 * Verify that a system satisfies an omega regular property.
	 * 
	 * @param <S>
	 *            Type of states in the transition system.
	 * @param <Saut>
	 *            Type of states in the automaton.
	 * @param <A>
	 *            Type of actions in the transition system.
	 * @param <P>
	 *            Type of atomic propositions in the transition system, which is
	 *            also the type of the automaton alphabet.
	 * @param ts
	 *            The transition system.
	 * @param aut
	 *            A Büchi automaton for the words that do not satisfy the
	 *            property.
	 * @return A VerificationSucceeded object or a VerificationFailed object
	 *         with a counterexample.
	 */
	<S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts,
			Automaton<Saut, P> aut);

	/**
	 * Translation of Linear Temporal Logic (LTL) formula to a Nondeterministic
	 * Büchi Automaton (NBA).
	 * 
     * @param <L>
     *            Type of resultant automaton transition alphabet
	 * @param ltl
	 *            The LTL formula represented as a parse-tree.
	 * @return An automaton A such that L_\omega(A)=Words(ltl)
	 */
	<L> Automaton<?, L> LTL2NBA(LTL<L> ltl);

	/**
	 * A translation of a Generalized Büchi Automaton (GNBA) to a
	 * Nondeterministic Büchi Automaton (NBA).
	 * 
     * @param <L>
     *            Type of resultant automaton transition alphabet
	 * @param mulAut
	 *            An automaton with a set of accepting states (colors).
	 * @return An equivalent automaton with a single set of accepting states.
	 */
	<L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut);

}
