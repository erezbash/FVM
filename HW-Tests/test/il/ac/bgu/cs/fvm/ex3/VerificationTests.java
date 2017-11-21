package il.ac.bgu.cs.fvm.ex3;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.seq;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static org.junit.Assert.assertTrue;

import java.io.InputStream;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.IntStream;

import org.junit.Test;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.examples.PetersonProgramGraphBuilder;
import il.ac.bgu.cs.fvm.examples.SemaphoreBasedMutualExclusionBuilder;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.util.Util;
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;

public class VerificationTests {
	FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

	final static int N = 6;

	@Test
	public void test() throws Exception {
		TransitionSystem<Integer, String, String> ts;
		ts = FvmFacade.createInstance().createTransitionSystem();

		IntStream.range(0, N).forEach(i -> ts.addState(i));

		ts.addAtomicProposition("i<3");
		IntStream.range(0, 3).forEach(i -> ts.addToLabel(i, "i<3"));

		ts.addInitialState(3);

		ts.addAction("dec");
		ts.addAction("inc");

		IntStream.range(0, N).forEach(i -> ts.addTransition(new Transition<>(i, "inc", (i + 1) % N)));
		IntStream.range(0, N).forEach(i -> ts.addTransition(new Transition<>(i, "dec", (i - 1 + N) % N)));

		// Test with an automaton
		{
			Automaton<String, String> aut = new AutomataFactory<>(ts).eventuallyAlwaysAut(a -> a.contains("i<3"));

			VerificationResult<Integer> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);
			assertTrue(vr instanceof VerificationFailed);
			new CounterExampleVerifier<>(ts, aut).verifyCounterExample(vr);
		}

		// Test with another automaton
		{
			Automaton<String, String> aut = new AutomataFactory<>(ts).eventuallyAlwaysAut(a -> !a.contains("i<3"));

			VerificationResult<Integer> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);
			assertTrue(vr instanceof VerificationFailed);
			new CounterExampleVerifier<>(ts, aut).verifyCounterExample(vr);
		}
	}

	@Test
	public void nanopromelaTest() throws Exception {
		try (InputStream in = getClass().getClassLoader().getResourceAsStream("il/ac/bgu/cs/fvm/ex3/tst1.np")) {
			ProgramGraph<String, String> pg = fvmFacadeImpl.programGraphFromNanoPromela(in);
			TransitionSystem<Pair<String, Map<String, Object>>, String, String> ts = fvmFacadeImpl.transitionSystemFromProgramGraph(pg, set(new ParserBasedActDef()), set(new ParserBasedCondDef()));

			Automaton<String, String> aut = new AutomataFactory<>(ts).alwaysEventuallyAut(s -> s.contains("x = 0"));

			VerificationResult<Pair<String, Map<String, Object>>> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);

			assertTrue(vr instanceof VerificationFailed);
			new CounterExampleVerifier<>(ts, aut).verifyCounterExample(vr);

		}
	}

	@Test
	public void peterson() {
		ProgramGraph<String, String> pg1 = PetersonProgramGraphBuilder.build(1);
		ProgramGraph<String, String> pg2 = PetersonProgramGraphBuilder.build(2);

		ProgramGraph<Pair<String, String>, String> pg = fvmFacadeImpl.interleave(pg1, pg2);

		Set<ActionDef> ad = set(new ParserBasedActDef());
		Set<ConditionDef> cd = set(new ParserBasedCondDef());

		TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts;
		ts = fvmFacadeImpl.transitionSystemFromProgramGraph(pg, ad, cd);

		addLabels(ts);

		// Test mutual exclusion
		{
			Automaton<String, String> aut = new AutomataFactory<>(ts).eventuallyPhiAut(a -> a.contains("crit1") && a.contains("crit2"));
			VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);
			assertTrue(vr instanceof VerificationSucceeded);
		}

		// Test a liveness property - that after every state that satisfies
		// wait1 we must eventually have a state that satisfies crit1
		{
			Automaton<String, String> aut = new AutomataFactory<>(ts).eventuallyPhi1AndThenAlwaysPhi2Aut(a -> a.contains("wait1"), a -> !a.contains("crit1"));
			VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);
			assertTrue(vr instanceof VerificationSucceeded);
		}
	}

	@Test
	public void semaphoreBasedMutualExclusion() {
		ProgramGraph<String, String> pg1 = SemaphoreBasedMutualExclusionBuilder.build(1);
		ProgramGraph<String, String> pg2 = SemaphoreBasedMutualExclusionBuilder.build(2);

		ProgramGraph<Pair<String, String>, String> pg = fvmFacadeImpl.interleave(pg1, pg2);

		Set<ActionDef> ad = set(new ParserBasedActDef());
		Set<ConditionDef> cd = set(new ParserBasedCondDef());

		TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts;
		ts = fvmFacadeImpl.transitionSystemFromProgramGraph(pg, ad, cd);

		addLabels(ts);

		// Test mutual exclusion
		{
			Automaton<String, String> aut = new AutomataFactory<>(ts).eventuallyPhiAut(a -> a.contains("crit1") && a.contains("crit2"));
			VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);

			assertTrue(vr instanceof VerificationSucceeded);
		}

		// Test a liveness property - that after every state that satisfies
		// wait1 we must eventually have a state that satisfies crit1
		{
			Automaton<String, String> aut = new AutomataFactory<>(ts).eventuallyPhi1AndThenAlwaysPhi2Aut(a -> a.contains("wait1"), a -> !a.contains("crit1"));
			VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);

			assertTrue(vr instanceof VerificationFailed);
			new CounterExampleVerifier<>(ts, aut).verifyCounterExample(vr);
		}

		// Test the same property with a weak fairness assumptions
		{
			// An automaton for:
			// !(Fair -> P) where Fair is
			// (Eventually(Always(crit1_enabled)) -> Always(Eventually(crit1)))
			// and P is Always(wait1 -> (Next(Eventually(crit1))))
			Automaton<String, String> aut = new Automaton<>();

			Set<Set<String>> all = Util.powerSet(ts.getAtomicPropositions());

			all.stream().forEach(s -> aut.addTransition("q0", s, "q0"));
			all.stream().filter(s -> s.contains("wait1")).forEach(s -> aut.addTransition("q0", s, "q1"));
			all.stream().filter(s -> !s.contains("crit1")).forEach(s -> aut.addTransition("q1", s, "q1"));

			all.stream().filter(s -> !s.contains("crit1") && !s.contains("crit1_enabled")).forEach(s -> aut.addTransition("q1", s, "q2"));
			all.stream().filter(s -> !s.contains("crit1")).forEach(s -> aut.addTransition("q2", s, "q1"));

			aut.setInitial("q0");
			aut.setAccepting("q2");

			VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);

			assertTrue(vr instanceof VerificationFailed);
			new CounterExampleVerifier<>(ts, aut).verifyCounterExample(vr);
		}

		// Test the same property with a strong fairness assumptions
		{
			// An automaton for:
			// !(Fair -> P) where Fair is
			// (Always(Eventually(crit1_enabled)) -> Always(Eventually(crit1)))
			// and P is Always(wait1 -> (Next(Eventually(crit1))))
			Automaton<String, String> aut = new Automaton<>();

			Set<Set<String>> all = Util.powerSet(ts.getAtomicPropositions());

			all.stream().forEach(s -> aut.addTransition("q0", s, "q0"));
			all.stream().filter(s -> s.contains("wait1")).forEach(s -> aut.addTransition("q0", s, "q1"));
			all.stream().filter(s -> !s.contains("wait1") && !s.contains("crit1")).forEach(s -> aut.addTransition("q1", s, "q1"));

			all.stream().filter(s -> !s.contains("crit1") && !s.contains("crit1_enabled")).forEach(s -> aut.addTransition("q1", s, "q2"));
			all.stream().filter(s -> !s.contains("crit1") && !s.contains("crit1_enabled")).forEach(s -> aut.addTransition("q2", s, "q2"));

			aut.setInitial("q0");
			aut.setAccepting("q2");

			VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);

			assertTrue(vr instanceof VerificationSucceeded);
		}

	}

	// Add labels to ts for formulating mutual exclusion properties.
	private void addLabels(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
		ts.getStates().stream().forEach(st -> ts.getAtomicPropositions().stream().forEach(ap -> ts.removeLabel(st, ap)));

		Set<String> aps = new HashSet<>(ts.getAtomicPropositions());
		aps.stream().forEach(ap -> ts.removeAtomicProposition(ap));

		seq("wait1", "wait2", "crit1", "crit2", "crit1_enabled").stream().forEach(s -> ts.addAtomicPropositions(s));

		ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("crit1")).forEach(s -> ts.addToLabel(s, "crit1"));
		ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("wait1")).forEach(s -> ts.addToLabel(s, "wait1"));

		ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("crit2")).forEach(s -> ts.addToLabel(s, "crit2"));
		ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("wait2")).forEach(s -> ts.addToLabel(s, "wait2"));

		Predicate<Pair<Pair<String, String>, ?>> _crit1 = ss -> ss.getFirst().getFirst().equals("crit1");
		ts.getStates().stream().filter(s -> fvmFacadeImpl.post(ts, s).stream().anyMatch(_crit1)).forEach(s -> ts.addToLabel(s, "crit1_enabled"));
	}

}