package il.ac.bgu.cs.fvm.ex1;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.TSTestUtils;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import org.junit.Before;
import org.junit.Test;

import static il.ac.bgu.cs.fvm.TSTestUtils.States.*;
import static il.ac.bgu.cs.fvm.ex1.OwnTests.States.*;
import static il.ac.bgu.cs.fvm.ex1.OwnTests.AP.*;
import static il.ac.bgu.cs.fvm.ex1.OwnTests.Actions.*;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static org.junit.Assert.*;

public class OwnTests {

    public enum States {S1, S2, S3, S4,S0}

    public enum AP {P, Q, U}

    public enum Actions {A1, A2, A3}

    private FvmFacade sut = null;

    private TransitionSystem<States, Actions, AP> ts;

    @Before
    public void setup() {
        sut = FvmFacade.createInstance();
        ts = sut.createTransitionSystem();

    }


    @Test(timeout = 2000)
    public void testIsAPDeterminstic_true_own() {
        TransitionSystem<States, Actions, AP> ts;
        ts = FvmFacade.createInstance().createTransitionSystem();
        ts.addState(S1);
        ts.addState(S2);
        ts.addState(S3);
        ts.addState(S4);
        ts.addAtomicPropositions(Q, P, U);
        ts.addInitialState(S1);
        ts.addToLabel(S1, Q);

        assertTrue(sut.isAPDeterministic(ts)); //ts with no transitions.

        ts.addAction(A1);
        ts.addTransition(new Transition<>(S1, A1, S2));
        ts.addTransition(new Transition<>(S1, A1, S3));
        ts.addTransition(new Transition<>(S1, A1, S4));

        ts.addToLabel(S2, Q);
        ts.addToLabel(S3, P);

        //S4 is {Q,P}
        ts.addToLabel(S4, Q);
        ts.addToLabel(S4, P);

        assertTrue(sut.isAPDeterministic(ts)); // ts with 3 states that are post of S1 with partial same AP

        //S4 is {U}
        ts.removeLabel(S4, Q);
        ts.removeLabel(S4, P);
        ts.addAtomicPropositions(U);
        ts.addToLabel(S4, U);
        assertTrue(sut.isAPDeterministic(ts)); // ts with 3 states that are post of S1 with different single {d} AP
    }

    @Test(timeout = 2000)
    public void testIsAPDeterminstic_false_own() {
        TransitionSystem<States, Actions, AP> ts;
        ts = FvmFacade.createInstance().createTransitionSystem();
        ts.addState(S1);
        ts.addState(S2);
        ts.addState(S3);
        ts.addState(S4);
        ts.addAtomicPropositions(Q, P, U);
        ts.addInitialState(S1);
        ts.addToLabel(S1, Q);

        ts.addAction(A1);
        ts.addTransition(new Transition<>(S1, A1, S2));
        ts.addTransition(new Transition<>(S1, A1, S3));
        ts.addTransition(new Transition<>(S1, A1, S4));

        ts.addToLabel(S2, Q);
        ts.addToLabel(S3, P);
        ts.addToLabel(S4, P);
        assertFalse(sut.isAPDeterministic(ts)); // ts with 2 states that are post of S with {P} (same AP)

        ts.addToLabel(S3, U);
        ts.addToLabel(S4, U);
        assertFalse(sut.isAPDeterministic(ts)); // ts with 2 states that are post of S with {U,P} (same AP)

        ts.addState(S0);
        ts.addInitialState(S0);
        ts.removeInitialState(S1);
        ts.addTransition(new Transition<>(S0, A1, S1));
        ts.removeLabel(S1, Q);
        ts.removeLabel(S2, Q);
        ts.removeLabel(S3, P);
        ts.removeLabel(S4, P);
        assertFalse(sut.isAPDeterministic(ts)); //ts with no AP
    }


    @Test(timeout = 2000)
    public void postTest_states_empty() throws Exception {
        TransitionSystem<TSTestUtils.States, TSTestUtils.Actions, TSTestUtils.APs> threeState = TSTestUtils.threeStateTS();

        assertEquals(set(), sut.post(threeState, set(e, f, g)));


    }


    @Test(timeout = 2000)
    public void equalityTests() throws Exception {
        ts.addState(S1);
        ts.addState(S2);
        ts.addInitialState(S1);
        ts.addAction(A1);
        ts.addTransition(new Transition<>(S1, A1, S2));
        ts.addAtomicProposition(P);
        ts.addAtomicPropositions(Q, P);
        ts.addToLabel(S1, Q);

        TransitionSystem<States, Actions, AP> otherTs = sut.createTransitionSystem();
        otherTs.addState(S2);
        otherTs.addState(S1);
        otherTs.addInitialState(S1);
        otherTs.addAction(A1);
        otherTs.addAtomicPropositions(Q, P);
        otherTs.addTransition(new Transition<>(S1, A1, S2));
        otherTs.addAtomicProposition(P);
        otherTs.addToLabel(S1, Q);
    }

}