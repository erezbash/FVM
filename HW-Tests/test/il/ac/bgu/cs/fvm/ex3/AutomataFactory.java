package il.ac.bgu.cs.fvm.ex3;

import java.util.Set;
import java.util.function.Predicate;

import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Util;

// A factory for generating specific types of automata
public class AutomataFactory<P> {
	
	Set<Set<P>> all;
	
	public AutomataFactory(TransitionSystem<?,?,P> ts) {	
		all = Util.powerSet(ts.getAtomicPropositions());
	}

	// An automaton for Always(Eventually phi)
	public Automaton<String, P> alwaysEventuallyAut(Predicate<Set<P>> phi) {
		Automaton<String, P> aut = new Automaton<>();

		all.stream().filter(phi).forEach(l -> aut.addTransition("q0", l, "q1"));
		all.stream().filter(phi).forEach(l -> aut.addTransition("q1", l, "q1"));
		
		all.stream().filter(phi.negate()).forEach(l -> aut.addTransition("q0", l, "q0"));
		all.stream().filter(phi.negate()).forEach(l -> aut.addTransition("q1", l, "q0"));

		aut.setInitial("q1");
		aut.setAccepting("q0");
		return aut;
	}

	// An automaton for Eventually(Always phi)
	public Automaton<String, P> eventuallyAlwaysAut(Predicate<Set<P>> phi) {
		Automaton<String, P> aut = new Automaton<>();

		all.stream().filter(phi.negate()).forEach(l -> aut.addTransition("q0", l, "q0"));
		all.stream().filter(phi).forEach(l -> aut.addTransition("q0", l, "q0"));
		all.stream().filter(phi).forEach(l -> aut.addTransition("q0", l, "q1"));
		all.stream().filter(phi).forEach(l -> aut.addTransition("q1", l, "q1"));

		aut.setInitial("q0");
		aut.setAccepting("q1");
		return aut;
	}

	// An automaton for Eventually(phi1 /\ Next(Always(not phi2)))
	public Automaton<String, P> eventuallyPhi1AndThenAlwaysPhi2Aut(Predicate<Set<P>> phi1, Predicate<Set<P>> phi2) {

		Automaton<String, P> aut = new Automaton<>();

		all.stream().forEach(l -> aut.addTransition("q0", l, "q0"));
		all.stream().filter(phi1).forEach(l -> aut.addTransition("q0", l, "q1"));
		all.stream().filter(phi2).forEach(l -> aut.addTransition("q1", l, "q1"));

		aut.setInitial("q0");
		aut.setAccepting("q1");
		return aut;
	}

	// An automaton for Eventually(phi))
	public Automaton<String, P> eventuallyPhiAut(Predicate<Set<P>> phi) {
		Automaton<String, P> aut = new Automaton<>();

		all.stream().filter(phi.negate()).forEach(l -> aut.addTransition("q0", l, "q0"));
		all.stream().filter(phi).forEach(l -> aut.addTransition("q0", l, "q1"));
		all.stream().forEach(l -> aut.addTransition("q1", l, "q1"));

		aut.setInitial("q0");
		aut.setAccepting("q1");
		return aut;
	}
}