package il.ac.bgu.cs.fvm.ex3;

import static il.ac.bgu.cs.fvm.ex3.AutomatonTest.State.A;
import static il.ac.bgu.cs.fvm.ex3.AutomatonTest.State.B;
import static il.ac.bgu.cs.fvm.ex3.AutomatonTest.State.C;
import static il.ac.bgu.cs.fvm.ex3.AutomatonTest.State.D;
import static il.ac.bgu.cs.fvm.ex3.AutomatonTest.State.G;
import static il.ac.bgu.cs.fvm.ex3.AutomatonTest.State.H;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static org.junit.Assert.assertEquals;

import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.fvm.automata.Automaton;


public class AutomatonTest {
    
    enum State{
        A,B,C,D,E,F,G,H
    }
    
	@Test
	public void automatonTest() {
		Automaton<State,String> aut = new Automaton<>();

		Set<String> a = set("a");
		Set<String> ab = set("a", "b");
		Set<String> abc = set("a", "b", "c");

		aut.addTransition(A, ab, B);
		aut.addTransition(A, ab, C);
		aut.addTransition(C, ab, D);
		aut.addTransition(D, ab, State.E);
		aut.addTransition(D, abc, G);
		aut.addTransition(G, a, G);
		aut.setInitial(H);
		aut.setInitial(G);

		assertEquals(aut.nextStates(A, a), null);
		assertEquals(aut.nextStates(A, ab), set(B, C));
		assertEquals(aut.nextStates(A, abc), null);

		assertEquals(aut.nextStates(B, a), null);
		assertEquals(aut.nextStates(B, ab), null);
		assertEquals(aut.nextStates(B, abc), null);

		assertEquals(aut.nextStates(C, a), null);
		assertEquals(aut.nextStates(C, ab), set(D));
		assertEquals(aut.nextStates(C, abc), null);

		assertEquals(aut.nextStates(D, a), null);
		assertEquals(aut.nextStates(D, ab), set(State.E));
		assertEquals(aut.nextStates(D, abc), set(G));

		assertEquals(aut.nextStates(State.E, a), null);
		assertEquals(aut.nextStates(State.E, ab), null);
		assertEquals(aut.nextStates(State.E, abc), null);

		assertEquals(aut.nextStates(G, a), set(G));
		assertEquals(aut.nextStates(G, ab), null);
		assertEquals(aut.nextStates(G, abc), null);

		assertEquals(aut.nextStates(H, a), null);
		assertEquals(aut.nextStates(H, ab), null);
		assertEquals(aut.nextStates(H, abc), null);

		assertEquals(aut.getInitialStates(), set(G, H));

	}

}
