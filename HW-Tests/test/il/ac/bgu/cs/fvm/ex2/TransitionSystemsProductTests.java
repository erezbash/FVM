package il.ac.bgu.cs.fvm.ex2;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.transition;
import static org.junit.Assert.assertEquals;

import java.util.HashSet;
import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.examples.BookingSystemBuilder;
import il.ac.bgu.cs.fvm.examples.BookingSystemBuilder.AP;
import il.ac.bgu.cs.fvm.examples.BookingSystemBuilder.Action;
import il.ac.bgu.cs.fvm.examples.BookingSystemBuilder.State;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;

public class TransitionSystemsProductTests {

	FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

	@SuppressWarnings("unchecked")
	@Test
	// See page 52, Example 2.9 in the book
	public void booking() {
		TransitionSystem<State, Action, AP> bcr = BookingSystemBuilder.buildBCR();
		TransitionSystem<State, Action, AP> bp = BookingSystemBuilder.buildBP();
		TransitionSystem<State, Action, AP> printer = BookingSystemBuilder.buildPrinter();

		Set<Action> hs1 = new HashSet<>();
		hs1.add(Action.store);
		TransitionSystem<Pair<State, State>, Action, AP> ts1 = fvmFacadeImpl.interleave(bcr, bp, hs1);

		Set<Action> hs2 = new HashSet<>();
		hs1.add(Action.prt_cmd);
		TransitionSystem<Pair<Pair<State, State>, State>, Action, AP> ts = fvmFacadeImpl.interleave(ts1, printer, hs2);

		/*
		 * final TsPrinter tsPrinter = new TsPrinter();
		 * 
		 * tsPrinter.setClassPrinter(Action.class, (obj, tsp, out) -> {
		 * out.print("Action." + obj.name()); });
		 * 
		 * tsPrinter.setClassPrinter(State.class, (obj, tsp, out) -> {
		 * out.print("State." + obj.name()); });
		 * 
		 * tsPrinter.setClassPrinter(AP.class, (obj, tsp, out) -> {
		 * out.print("AP." + obj.name()); });
		 * 
		 * out.println(tsPrinter.getAssertions(ts));
		 */
		assertEquals(set(p(p(State.S1, State.S0), State.S0), p(p(State.S0, State.S0), State.S1), p(p(State.S0, State.S1), State.S1), p(p(State.S1, State.S1), State.S1), p(p(State.S0, State.S1), State.S0), p(p(State.S0, State.S0), State.S0), p(p(State.S1, State.S0), State.S1),
				p(p(State.S1, State.S1), State.S0)), ts.getStates());

		assertEquals(set(p(p(State.S0, State.S0), State.S0)), ts.getInitialStates());

		assertEquals(set(Action.store, Action.scan, Action.print, Action.prt_cmd), ts.getActions());

		assertEquals(set(), ts.getAtomicPropositions());

		assertEquals(set(transition(p(p(State.S0, State.S1), State.S0), Action.prt_cmd, p(p(State.S0, State.S0), State.S0)), transition(p(p(State.S0, State.S1), State.S1), Action.print, p(p(State.S0, State.S1), State.S0)),
				transition(p(p(State.S0, State.S1), State.S0), Action.scan, p(p(State.S1, State.S1), State.S0)), transition(p(p(State.S1, State.S0), State.S0), Action.store, p(p(State.S0, State.S1), State.S0)),
				transition(p(p(State.S0, State.S0), State.S1), Action.scan, p(p(State.S1, State.S0), State.S1)), transition(p(p(State.S0, State.S1), State.S1), Action.prt_cmd, p(p(State.S0, State.S0), State.S1)),
				transition(p(p(State.S1, State.S1), State.S0), Action.prt_cmd, p(p(State.S1, State.S1), State.S1)), transition(p(p(State.S1, State.S0), State.S1), Action.store, p(p(State.S0, State.S1), State.S1)),
				transition(p(p(State.S1, State.S0), State.S1), Action.print, p(p(State.S1, State.S0), State.S0)), transition(p(p(State.S0, State.S1), State.S1), Action.scan, p(p(State.S1, State.S1), State.S1)),
				transition(p(p(State.S0, State.S0), State.S0), Action.prt_cmd, p(p(State.S0, State.S0), State.S1)), transition(p(p(State.S1, State.S1), State.S0), Action.prt_cmd, p(p(State.S1, State.S0), State.S0)),
				transition(p(p(State.S1, State.S1), State.S1), Action.print, p(p(State.S1, State.S1), State.S0)), transition(p(p(State.S1, State.S1), State.S1), Action.prt_cmd, p(p(State.S1, State.S0), State.S1)),
				transition(p(p(State.S0, State.S1), State.S0), Action.prt_cmd, p(p(State.S0, State.S1), State.S1)), transition(p(p(State.S0, State.S0), State.S1), Action.print, p(p(State.S0, State.S0), State.S0)),
				transition(p(p(State.S0, State.S0), State.S0), Action.scan, p(p(State.S1, State.S0), State.S0)), transition(p(p(State.S1, State.S0), State.S0), Action.prt_cmd, p(p(State.S1, State.S0), State.S1))), ts.getTransitions());

		assertEquals(set(), ts.getLabel(p(p(State.S1, State.S0), State.S0)));
		assertEquals(set(), ts.getLabel(p(p(State.S0, State.S0), State.S1)));
		assertEquals(set(), ts.getLabel(p(p(State.S0, State.S1), State.S1)));
		assertEquals(set(), ts.getLabel(p(p(State.S1, State.S1), State.S1)));
		assertEquals(set(), ts.getLabel(p(p(State.S0, State.S1), State.S0)));
		assertEquals(set(), ts.getLabel(p(p(State.S0, State.S0), State.S0)));
		assertEquals(set(), ts.getLabel(p(p(State.S1, State.S0), State.S1)));
		assertEquals(set(), ts.getLabel(p(p(State.S1, State.S1), State.S0)));

	}

	@SuppressWarnings("unchecked")
	@Test // See page 37, Figure 2.4 in the book
	public void trafficLight() {
		TransitionSystem<String, String, String> ts1 = FvmFacade.createInstance().createTransitionSystem();

		ts1.addState("red");
		ts1.addState("green");

		ts1.addInitialState("red");

		ts1.addAction("go1");

		ts1.addAtomicProposition("tl1-is-red");
		ts1.addToLabel("red", "tl1-is-red");

		ts1.addTransition(new Transition<>("red", "go1", "green"));
		ts1.addTransition(new Transition<>("green", "go1", "red"));

		TransitionSystem<String, String, String> ts2 = FvmFacade.createInstance().createTransitionSystem();
		ts2.addState("red");
		ts2.addState("green");

		ts2.addInitialState("red");
		ts2.addAction("go2");

		ts2.addAtomicProposition("tl2-is-red");
		ts2.addToLabel("red", "tl2-is-red");

		ts2.addTransition(new Transition<>("red", "go2", "green"));
		ts2.addTransition(new Transition<>("green", "go2", "red"));

		TransitionSystem<Pair<String, String>, String, String> ts = fvmFacadeImpl.interleave(ts1, ts2);

		assertEquals(set(p("red", "green"), p("green", "green"), p("green", "red"), p("red", "red")), ts.getStates());

		assertEquals(set(p("red", "red")), ts.getInitialStates());

		assertEquals(set("go1", "go2"), ts.getActions());

		assertEquals(set("tl2-is-red", "tl1-is-red"), ts.getAtomicPropositions());

		assertEquals(set(transition(p("green", "green"), "go1", p("red", "green")), transition(p("red", "red"), "go2", p("red", "green")), transition(p("green", "red"), "go2", p("green", "green")), transition(p("green", "red"), "go1", p("red", "red")),
				transition(p("red", "red"), "go1", p("green", "red")), transition(p("red", "green"), "go2", p("red", "red")), transition(p("green", "green"), "go2", p("green", "red")), transition(p("red", "green"), "go1", p("green", "green"))), ts.getTransitions());

		assertEquals(set("tl1-is-red"), ts.getLabel(p("red", "green")));
		assertEquals(set(), ts.getLabel(p("green", "green")));
		assertEquals(set("tl2-is-red"), ts.getLabel(p("green", "red")));
		assertEquals(set("tl2-is-red", "tl1-is-red"), ts.getLabel(p("red", "red")));
	}

	@SuppressWarnings("unchecked")
	@Test
	public void three() {
		TransitionSystem<String, String, String> ts1 = FvmFacade.createInstance().createTransitionSystem();

		ts1.addState("1");
		ts1.addState("2");
		ts1.addInitialState("1");
		ts1.addAction("a");
		ts1.addAction("b");
		ts1.addTransition(new Transition<>("1", "a", "2"));

		TransitionSystem<String, String, String> ts2 = FvmFacade.createInstance().createTransitionSystem();
		ts2.addState("1");
		ts2.addState("2");
		ts2.addState("3");
		ts2.addInitialState("1");
		ts2.addAction("a");
		ts2.addAction("b");
		ts2.addTransition(new Transition<>("1", "b", "2"));
		ts2.addTransition(new Transition<>("2", "a", "3"));

		TransitionSystem<String, String, String> ts3 = FvmFacade.createInstance().createTransitionSystem();
		ts3.addState("1");
		ts3.addState("2");
		ts3.addState("3");
		ts3.addState("4");
		ts3.addState("5");
		ts3.addInitialState("1");
		ts3.addAction("a");
		ts3.addAction("b");
		ts3.addTransition(new Transition<>("1", "a", "2"));
		ts3.addTransition(new Transition<>("2", "b", "3"));
		ts3.addTransition(new Transition<>("2", "b", "4"));
		ts3.addTransition(new Transition<>("2", "b", "5"));

		{
			TransitionSystem<Pair<String, String>, String, String> ts12 = fvmFacadeImpl.interleave(ts1, ts2, set("a"));

			TransitionSystem<Pair<Pair<String, String>, String>, String, String> ts123 = fvmFacadeImpl.interleave(ts12, ts3, set("b"));

			assertEquals(set(p(p("1", "1"), "1"), p(p("1", "1"), "2"), p(p("2", "3"), "5"), p(p("1", "2"), "4"), p(p("1", "2"), "3"), p(p("2", "3"), "4"), p(p("1", "2"), "5"), p(p("2", "3"), "3")), ts123.getStates());
			assertEquals(set(p(p("1", "1"), "1")), ts123.getInitialStates());
			assertEquals(set("a", "b"), ts123.getActions());
			assertEquals(set(), ts123.getAtomicPropositions());
			assertEquals(set(transition(p(p("1", "1"), "1"), "a", p(p("1", "1"), "2")), transition(p(p("1", "2"), "4"), "a", p(p("2", "3"), "4")), transition(p(p("1", "2"), "3"), "a", p(p("2", "3"), "3")), transition(p(p("1", "2"), "5"), "a", p(p("2", "3"), "5")),
					transition(p(p("1", "1"), "2"), "b", p(p("1", "2"), "3")), transition(p(p("1", "1"), "2"), "b", p(p("1", "2"), "4")), transition(p(p("1", "1"), "2"), "b", p(p("1", "2"), "5"))), ts123.getTransitions());
			assertEquals(set(), ts123.getLabel(p(p("1", "1"), "1")));
			assertEquals(set(), ts123.getLabel(p(p("1", "1"), "2")));
			assertEquals(set(), ts123.getLabel(p(p("2", "3"), "5")));
			assertEquals(set(), ts123.getLabel(p(p("1", "2"), "4")));
			assertEquals(set(), ts123.getLabel(p(p("1", "2"), "3")));
			assertEquals(set(), ts123.getLabel(p(p("2", "3"), "4")));
			assertEquals(set(), ts123.getLabel(p(p("1", "2"), "5")));
			assertEquals(set(), ts123.getLabel(p(p("2", "3"), "3")));
		}

		{
			TransitionSystem<Pair<String, String>, String, String> ts23 = fvmFacadeImpl.interleave(ts2, ts3, set("b"));

			TransitionSystem<Pair<String, Pair<String, String>>, String, String> ts123 = fvmFacadeImpl.interleave(ts1, ts23, set("a"));

			assertEquals(set(p("2", p("2", "3")), p("2", p("2", "5")), p("2", p("2", "4")), p("1", p("1", "1")), p("2", p("1", "2"))), ts123.getStates());
			assertEquals(set(p("1", p("1", "1"))), ts123.getInitialStates());
			assertEquals(set("a", "b"), ts123.getActions());
			assertEquals(set(), ts123.getAtomicPropositions());
			assertEquals(set(transition(p("2", p("1", "2")), "b", p("2", p("2", "4"))), transition(p("2", p("1", "2")), "b", p("2", p("2", "5"))), transition(p("1", p("1", "1")), "a", p("2", p("1", "2"))), transition(p("2", p("1", "2")), "b", p("2", p("2", "3")))), ts123.getTransitions());
			assertEquals(set(), ts123.getLabel(p("2", p("2", "3"))));
			assertEquals(set(), ts123.getLabel(p("2", p("2", "5"))));
			assertEquals(set(), ts123.getLabel(p("2", p("2", "4"))));
			assertEquals(set(), ts123.getLabel(p("1", p("1", "1"))));
			assertEquals(set(), ts123.getLabel(p("2", p("1", "2"))));
		}

	}

}
