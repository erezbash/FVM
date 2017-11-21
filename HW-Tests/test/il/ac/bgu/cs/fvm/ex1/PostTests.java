package il.ac.bgu.cs.fvm.ex1;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.TSTestUtils;
import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.TSTestUtils.*;
import static il.ac.bgu.cs.fvm.TSTestUtils.Actions.alpha;
import static il.ac.bgu.cs.fvm.TSTestUtils.Actions.beta;
import static il.ac.bgu.cs.fvm.TSTestUtils.States.*;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.*;
import static org.junit.Assert.assertNotEquals;

public class PostTests {

    FvmFacade sut;

    @Before
    public void setup() {
        sut = FvmFacade.createInstance();
    }

    @Test(timeout = 2000)
    public void postTest_states() throws Exception {
        TransitionSystem<States, Actions, APs> threeState = TSTestUtils.threeStateTS();

        assertEquals(set(a, b, c), sut.post(threeState, a));
        assertEquals(set(a), sut.post(threeState, b));
        assertEquals(set(), sut.post(threeState, c));

        TransitionSystem<Integer, String, String> linear5 = TSTestUtils.makeLinearTs(5);
        for (int i = 1; i < 5; i++) {
            assertEquals(set(i + 1), sut.post(linear5, i));
        }
        assertEquals(set(), sut.post(linear5, 5));

        TransitionSystem<String, String, String> branching = TSTestUtils.makeBranchingTs(5, 3);
        assertEquals(set("s3", "s_1_3", "s_2_3", "s_3_3"), sut.post(branching, "s2"));

        assertNotEquals(set("s3x", "s_1_3", "s_2_3", "s_3_3"), sut.post(branching, "s2"));
    }

    @Test(timeout = 2000)
    public void postTest_actions() throws Exception {
        TransitionSystem<States, Actions, APs> threeState = TSTestUtils.threeStateTS();

        assertEquals(set(a, b), sut.post(threeState, a, alpha));
        assertEquals(set(c), sut.post(threeState, a, beta));
        assertEquals(set(), sut.post(threeState, b, beta));
        assertEquals(set(a), sut.post(threeState, b, alpha));
        assertEquals(set(), sut.post(threeState, c, alpha));
        assertEquals(set(), sut.post(threeState, c, beta));

        TransitionSystem<Integer, String, String> linear5 = TSTestUtils.makeLinearTs(5);
        for (int i = 1; i < 5; i++) {
            assertEquals(set(i + 1), sut.post(linear5, i, "a" + i));
            if (i < 4) {
                assertEquals(set(), sut.post(linear5, i, "a" + (i + 1)));
            }
        }
        assertEquals(set(), sut.post(linear5, 5, "a2"));

        TransitionSystem<String, String, String> branching = TSTestUtils.makeBranchingTs(5, 3);
        assertEquals(set("s_1_3", "s_2_3", "s_3_3"), sut.post(branching, "s2", "fork"));
        assertEquals(set("s3"), sut.post(branching, "s2", "a2"));

        TransitionSystem<Integer, String, String> circular = TSTestUtils.makeCircularTs(5);
        assertEquals(set(2), sut.post(circular, 1));
        assertEquals(set(1), sut.post(circular, 5));

        assertNotEquals(set("s3x", "s_1_3", "s_2_3", "s_3_3"), sut.post(branching, "s2"));
    }

    @Test(timeout = 2000)
    public void postTest_actions_sets() throws Exception {
        TransitionSystem<States, Actions, APs> threeState = TSTestUtils.threeStateTS();

        assertEquals(set(a, b), sut.post(threeState, set(a, b, c), alpha));
        assertEquals(set(c), sut.post(threeState, set(a, b, c), beta));
        assertEquals(set(), sut.post(threeState, set(c), alpha));
        assertEquals(set(), sut.post(threeState, set(b, c), beta));
        assertEquals(set(a), sut.post(threeState, set(b, c), alpha));

    }

    @Test(timeout = 2000)
    public void postTest_states_sets() throws Exception {
        TransitionSystem<States, Actions, APs> threeState = TSTestUtils.threeStateTS();

        assertEquals(set(a, b, c), sut.post(threeState, set(a, b, c)));
        assertEquals(set(), sut.post(threeState, set(c)));

        TransitionSystem<Integer, String, String> circular = TSTestUtils.makeCircularTs(5);
        assertEquals(circular.getStates(), sut.post(circular, circular.getStates()));

    }

}
