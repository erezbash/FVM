package il.ac.bgu.cs.fvm.automata;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class MultiColorAutomaton<State, L> {

	private Set<State> initial;
	private Map<Integer, Set<State>> accepting;
	private Map<State, Map<Set<L>, Set<State>>> transitions;

	public MultiColorAutomaton() {
		transitions = new HashMap<State, Map<Set<L>, Set<State>>>();
		initial = new HashSet<State>();
		accepting = new HashMap<Integer, Set<State>>();
	}

	public void addState(State s) {
		if (!transitions.containsKey(s))
			transitions.put(s, new HashMap<Set<L>, Set<State>>());
	}

	public void addTransition(State source, Set<L> symbol, State destination) {
		if (!transitions.containsKey(source))
			addState(source);

		if (!transitions.containsKey(destination))
			addState(destination);

		Set<State> set = transitions.get(source).get(symbol);
		if (set == null) {
			set = new HashSet<State>();
			transitions.get(source).put(symbol, set);
		}
		set.add(destination);
	}

	public Set<State> getAcceptingStates(int color) {
		Set<State> acc = accepting.get(color);

		if (acc == null) {
			acc = new HashSet<State>();
			accepting.put(color, acc);
		}

		return acc;
	}

	public Set<State> getInitialStates() {
		return initial;
	}

	public Map<State, Map<Set<L>, Set<State>>> getTransitions() {
		return transitions;
	}

	public Set<State> nextStates(State source, Set<L> symbol) {
		if (!transitions.containsKey(source))
			throw new IllegalArgumentException();
		else
			return transitions.get(source).get(symbol);
	}

	public void setAccepting(State s, int color) {
		Set<State> acc = accepting.get(color);

		if (acc == null) {
			acc = new HashSet<State>();
			accepting.put(color, acc);
		}

		addState(s);
		acc.add(s);
	}

	public void setInitial(State s) {
		addState(s);
		initial.add(s);
	}

	public Set<Integer> getColors() {
		return accepting.keySet();
	}

}
