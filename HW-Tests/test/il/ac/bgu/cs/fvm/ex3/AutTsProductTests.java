package il.ac.bgu.cs.fvm.ex3;

import static il.ac.bgu.cs.fvm.ex3.AutTsProductTests.Actions.Switch;
import static il.ac.bgu.cs.fvm.ex3.AutTsProductTests.AutomatonStates.Q0;
import static il.ac.bgu.cs.fvm.ex3.AutTsProductTests.AutomatonStates.Q1;
import static il.ac.bgu.cs.fvm.ex3.AutTsProductTests.AutomatonStates.Q2;
import static il.ac.bgu.cs.fvm.ex3.AutTsProductTests.Lights.Green;
import static il.ac.bgu.cs.fvm.ex3.AutTsProductTests.Lights.Off;
import static il.ac.bgu.cs.fvm.ex3.AutTsProductTests.Lights.Red;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.transition;
import static org.junit.Assert.assertEquals;

import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.util.codeprinter.TsPrinter;

public class AutTsProductTests {

	public enum Lights {
		Off, Green, Red
	}

	public enum Actions {
		Switch
	}

	public enum AutomatonStates {
		Q0, Q1, Q2
	}

	final TsPrinter tsPrinter = new TsPrinter() {
		{
			setClassPrinter(Actions.class, (obj, tsp, out) -> {
				out.print(obj.name());
			});

			setClassPrinter(Lights.class, (obj, tsp, out) -> {
				out.print(obj.name());
			});

			setClassPrinter(AutomatonStates.class, (obj, tsp, out) -> {
				out.print(obj.name());
			});

		}
	};

	FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

	@SuppressWarnings("unchecked")
	@Test
	public void autTimesTs() {
		TransitionSystem<Lights, Actions, String> ts1 = buildTransitionSystem1();
		TransitionSystem<Lights, Actions, String> ts2 = buildTransitionSystem2();
		Automaton<AutomatonStates, String> aut = buildAutomaton();

		TransitionSystem<Pair<Lights, AutomatonStates>, Actions, AutomatonStates> comb1 = fvmFacadeImpl.product(ts1, aut);

		assertEquals(set(p(Green, Q0), p(Red, Q1), p(Red, Q2), p(Green, Q2), p(Red, Q0)), comb1.getStates());
		assertEquals(set(p(Red, Q1), p(Red, Q0)), comb1.getInitialStates());
		assertEquals(set(Switch), comb1.getActions());
		assertEquals(set(Q2, Q0, Q1), comb1.getAtomicPropositions());
		assertEquals(
				set(transition(p(Green, Q0), Switch, p(Red, Q0)), transition(p(Green, Q0), Switch, p(Red, Q1)), transition(p(Red, Q2), Switch, p(Green, Q2)), transition(p(Green, Q2), Switch, p(Red, Q2)), transition(p(Red, Q1), Switch, p(Green, Q2)), transition(p(Red, Q0), Switch, p(Green, Q0))),
				comb1.getTransitions());
		assertEquals(set(Q0), comb1.getLabel(p(Green, Q0)));
		assertEquals(set(Q1), comb1.getLabel(p(Red, Q1)));
		assertEquals(set(Q2), comb1.getLabel(p(Red, Q2)));
		assertEquals(set(Q2), comb1.getLabel(p(Green, Q2)));
		assertEquals(set(Q0), comb1.getLabel(p(Red, Q0)));

		TransitionSystem<Pair<Lights, AutomatonStates>, Actions, AutomatonStates> ts = fvmFacadeImpl.product(ts2, aut);

		assertEquals(set(p(Green, Q0), p(Off, Q2), p(Off, Q0), p(Red, Q1), p(Red, Q2), p(Green, Q2), p(Red, Q0), p(Off, Q1)), ts.getStates());
		assertEquals(set(p(Red, Q1), p(Red, Q0)), ts.getInitialStates());
		assertEquals(set(Switch), ts.getActions());
		assertEquals(set(Q2, Q0, Q1), ts.getAtomicPropositions());
		assertEquals(set(transition(p(Off, Q1), Switch, p(Red, Q1)), transition(p(Green, Q0), Switch, p(Red, Q1)), transition(p(Off, Q0), Switch, p(Red, Q1)), transition(p(Red, Q2), Switch, p(Green, Q2)), transition(p(Green, Q2), Switch, p(Red, Q2)), transition(p(Red, Q1), Switch, p(Green, Q2)),
				transition(p(Red, Q2), Switch, p(Off, Q2)), transition(p(Red, Q1), Switch, p(Off, Q1)), transition(p(Off, Q2), Switch, p(Red, Q2)), transition(p(Green, Q0), Switch, p(Red, Q0)), transition(p(Red, Q0), Switch, p(Green, Q0)), transition(p(Red, Q0), Switch, p(Off, Q0)),
				transition(p(Off, Q0), Switch, p(Red, Q0)), transition(p(Red, Q0), Switch, p(Off, Q1))), ts.getTransitions());
		assertEquals(set(Q0), ts.getLabel(p(Green, Q0)));
		assertEquals(set(Q2), ts.getLabel(p(Off, Q2)));
		assertEquals(set(Q0), ts.getLabel(p(Off, Q0)));
		assertEquals(set(Q1), ts.getLabel(p(Red, Q1)));
		assertEquals(set(Q2), ts.getLabel(p(Red, Q2)));
		assertEquals(set(Q2), ts.getLabel(p(Green, Q2)));
		assertEquals(set(Q0), ts.getLabel(p(Red, Q0)));
		assertEquals(set(Q1), ts.getLabel(p(Off, Q1)));

	}

	private Automaton<AutomatonStates, String> buildAutomaton() {
		Automaton<AutomatonStates, String> aut = new Automaton<>();

		Set<String> notRedAndNotGreen = set();
		Set<String> redAndNotGreen = set("red");
		Set<String> greenAndNotRed = set("green");
		Set<String> redAndGreen = set("red", "green");

		aut.addTransition(Q0, notRedAndNotGreen, Q0);
		aut.addTransition(Q0, redAndNotGreen, Q0);
		aut.addTransition(Q0, greenAndNotRed, Q0);
		aut.addTransition(Q0, redAndGreen, Q0);

		aut.addTransition(Q0, notRedAndNotGreen, Q1);
		aut.addTransition(Q0, redAndNotGreen, Q1);

		aut.addTransition(Q1, notRedAndNotGreen, Q1);
		aut.addTransition(Q1, redAndNotGreen, Q1);

		aut.addTransition(Q1, greenAndNotRed, Q2);
		aut.addTransition(Q1, redAndGreen, Q2);

		aut.addTransition(Q2, notRedAndNotGreen, Q2);
		aut.addTransition(Q2, redAndNotGreen, Q2);
		aut.addTransition(Q2, greenAndNotRed, Q2);
		aut.addTransition(Q2, redAndGreen, Q2);

		aut.setInitial(Q0);
		aut.setAccepting(Q1);
		return aut;
	}

	private TransitionSystem<Lights, Actions, String> buildTransitionSystem1() {
		TransitionSystem<Lights, Actions, String> ts = fvmFacadeImpl.createTransitionSystem();

		ts.addState(Green);
		ts.addState(Red);

		ts.addInitialState(Red);

		ts.addAction(Actions.Switch);

		ts.addTransitionFrom(Red).action(Switch).to(Green);
		ts.addTransitionFrom(Green).action(Switch).to(Red);

		ts.addAtomicProposition("green");
		ts.addAtomicProposition("red");

		ts.addToLabel(Green, "green");
		ts.addToLabel(Red, "red");
		return ts;
	}

	private TransitionSystem<Lights, Actions, String> buildTransitionSystem2() {
		TransitionSystem<Lights, Actions, String> ts = fvmFacadeImpl.createTransitionSystem();

		ts.addStates(Off, Red, Green);
		ts.addInitialState(Red);
		ts.addAction(Switch);

		ts.addTransitionFrom(Red).action(Switch).to(Green);
		ts.addTransitionFrom(Green).action(Switch).to(Red);
		ts.addTransitionFrom(Red).action(Switch).to(Off);
		ts.addTransitionFrom(Off).action(Switch).to(Red);

		ts.addAtomicProposition("green");
		ts.addAtomicProposition("red");

		ts.addToLabel(Green, "green");
		ts.addToLabel(Red, "red");
		return ts;
	}

}