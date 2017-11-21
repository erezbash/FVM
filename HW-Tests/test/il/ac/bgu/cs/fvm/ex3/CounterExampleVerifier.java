package il.ac.bgu.cs.fvm.ex3;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.seq;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationResult;

// A class for verifying that a counter example is valid for a given transition system and a given automaton.
public class CounterExampleVerifier<S, A, P, Saut> {
	FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

	TransitionSystem<S, A, P> ts;
	Automaton<Saut, P> aut;

	Set<List<Saut>> autRuns = new HashSet<>();

	// Constructor
	public CounterExampleVerifier(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
		super();
		this.ts = ts;
		this.aut = aut;
	}

	// Verify that a counter example is an execution that the
	// automaton accepts.
	void verifyCounterExample(VerificationResult<S> vrf) {
		assert vrf instanceof VerificationFailed : "This method is only a utility to avoid verbosity, it is not meant to be invoked when a verification succeeds";
		verifyCounterExample((VerificationFailed<S>) vrf);
	}

	// Verify that a counter example is an execution that the
	// automaton accepts.
	void verifyCounterExample(VerificationFailed<S> vrf) {

		// A counter example must begin with an initial state
		assertTrue(ts.getInitialStates().contains(vrf.getPrefix().get(0)));

		for (Saut sa : aut.getInitialStates()) {
			autRuns.add(seq(sa));
		}

		// The next state in the path
		S ss = null;

		for (S s : vrf.getPrefix()) {

			updateAutRuns(s);

			if (ss != null) {
				// Each state in a counter example must be in the post of its
				// predecessor
				assertTrue(fvmFacadeImpl.post(ts, ss).contains(s));
			}

			ss = s;
		}

		// Start from the last state
		Set<List<Saut>> newAutRuns = new HashSet<>();
		for (List<Saut> r : autRuns) {
			newAutRuns.add(seq(r.get(r.size() - 1)));
		}
		autRuns = newAutRuns;

		for (S s : vrf.getCycle()) {

			updateAutRuns(s);

			if (ss != null) {
				// Each state in a counter example must be in the post of its
				// predecessor
				assertTrue(fvmFacadeImpl.post(ts, ss).contains(s));
			}

			ss = s;
		}

		// The cycle must begin with a state in the post of its last state.
		assertTrue(fvmFacadeImpl.post(ts, ss).contains(vrf.getCycle().get(0)));

		boolean found = false;
		loop: for (List<Saut> r : autRuns) {
			// Check for a cyclic run that contains an accepting state
			List<Saut> rr = r.subList(1, r.size());
			if (aut.nextStates(rr.get(rr.size() - 1), ts.getLabel(vrf.getCycle().get(0))).contains(rr.get(0))) {
				rr.retainAll(aut.getAcceptingStates());
				if (!rr.isEmpty()) {
					found = true;
					break loop;
				}
			}
		}

		// There must be an accepting run of the automaton
		assertTrue(found);

	}

	// Advance the set of runs of the automaton over the word.
	private void updateAutRuns(S s) {
		Set<List<Saut>> newAutRuns = new HashSet<>();
		for (List<Saut> r : autRuns) {

			Set<Saut> nextStates = aut.nextStates(r.get(r.size() - 1), ts.getLabel(s));
			if (nextStates != null) {
				for (Saut sa : nextStates) {
					LinkedList<Saut> rr = new LinkedList<>(r);
					rr.add(sa);
					newAutRuns.add(rr);
				}
			}
		}
		autRuns = newAutRuns;
	}
}