package il.ac.bgu.cs.fvm.ex1;

import il.ac.bgu.cs.fvm.FvmFacade;
import static il.ac.bgu.cs.fvm.TSTestUtils.makeBranchingTs;
import static il.ac.bgu.cs.fvm.TSTestUtils.makeCircularTs;
import static il.ac.bgu.cs.fvm.TSTestUtils.makeLinearTs;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;

/**
 * Test the transition systems re: execution fragments
 *
 * @author michael
 */
public class Ex1FragmentsTest {

    FvmFacade sut = null;

    @Before
    public void setup() {
        sut = FvmFacade.createInstance();
    }

    @Test(timeout = 2000)
    public void testExecutionFragmentTrue() {
        // corner case: single state.
        assertTrue(sut.isExecutionFragment(makeBranchingTs(5, 2), AlternatingSequence.of("s2")));

        // common cases
        assertTrue(sut.isExecutionFragment(makeLinearTs(5), AlternatingSequence.of(1, "a1", 2, "a2", 3)));
        assertTrue(sut.isExecutionFragment(makeLinearTs(5), AlternatingSequence.of(2, "a2", 3, "a3", 4, "a4", 5)));
        assertTrue(sut.isExecutionFragment(makeBranchingTs(5, 2), AlternatingSequence.of("s2", "a2", "s3", "a3", "s4", "a4", "s5")));
        assertTrue(sut.isExecutionFragment(makeBranchingTs(5, 2), AlternatingSequence.of("s2", "fork", "s_1_3", "a3", "s_1_4", "a4", "s_1_5")));
        assertTrue(sut.isExecutionFragment(makeBranchingTs(5, 2), AlternatingSequence.of("s2", "fork", "s_2_3", "a3", "s_2_4", "a4", "s_2_5")));

    }

    @Test(timeout = 2000)
    public void testExecutionFragmentFalse() {
        assertFalse(sut.isExecutionFragment(makeLinearTs(5), AlternatingSequence.of(2, "a1", 3, "a3", 4, "a4", 5)));
    }

    @Test(expected = StateNotFoundException.class, timeout = 2000)
    public void testInvalidExecutionFragment_state() {
        sut.isExecutionFragment(makeLinearTs(5), AlternatingSequence.of(200, "a1", 3, "a3", 4, "a4", 5));
    }

    @Test(expected = ActionNotFoundException.class, timeout = 2000)
    public void testInvalidExecutionFragment_action() {
        sut.isExecutionFragment(makeLinearTs(5), AlternatingSequence.of(1, "a1000", 3, "a3", 4, "a4", 5));
    }

    @Test(timeout = 2000)
    public void testExecutionTrue() {
        assertTrue(sut.isExecution(makeLinearTs(4), AlternatingSequence.of(1, "a1", 2, "a2", 3, "a3", 4)));
        assertTrue(sut.isExecution(makeBranchingTs(5, 2), AlternatingSequence.of("s1", "a1", "s2", "a2", "s3", "a3", "s4", "a4", "s5")));
        assertTrue(sut.isExecution(makeBranchingTs(5, 2), AlternatingSequence.of("s1", "a1", "s2", "fork", "s_1_3", "a3", "s_1_4", "a4", "s_1_5")));
        assertTrue(sut.isExecution(makeBranchingTs(5, 2), AlternatingSequence.of("s1", "a1", "s2", "fork", "s_2_3", "a3", "s_2_4", "a4", "s_2_5")));
    }

    @Test(timeout = 2000)
    public void testExecutionFalse() {
        assertFalse("not fragment",
                sut.isExecution(makeLinearTs(5), AlternatingSequence.of(1, "a2", 2, "a2", 3)));
        assertFalse("not initial",
                sut.isExecution(makeLinearTs(5), AlternatingSequence.of(3, "a3", 4, "a4", 5)));
        assertFalse("not maximal",
                sut.isExecution(makeLinearTs(5), AlternatingSequence.of(1, "a1", 2, "a2", 3)));
    }

    @Test(timeout = 2000)
    public void testIsInitialExecutionFragment() {
        assertTrue(sut.isInitialExecutionFragment(makeLinearTs(4), AlternatingSequence.of(1)));
        assertTrue(sut.isInitialExecutionFragment(makeLinearTs(4), AlternatingSequence.of(1, "a1", 2)));
        assertTrue(sut.isInitialExecutionFragment(makeBranchingTs(4, 2), AlternatingSequence.of("s1", "a1", "s2")));
        assertTrue(sut.isInitialExecutionFragment(makeBranchingTs(4, 2), AlternatingSequence.of("s1", "fork", "s_1_2")));
    }

    @Test(timeout = 2000)
    public void testIsInitialExecutionFragmentFalse() {
        assertFalse("not initial", sut.isInitialExecutionFragment(makeLinearTs(4), AlternatingSequence.of(2)));
        assertFalse("not a fragment", sut.isInitialExecutionFragment(makeLinearTs(4), AlternatingSequence.of(2, "a1", 2)));

    }

    @Test(timeout = 2000)
    public void testIsMaximalExecutionFragment() {
        assertTrue(sut.isMaximalExecutionFragment(makeLinearTs(5), AlternatingSequence.of(3, "a3", 4, "a4", 5)));
        assertTrue(sut.isMaximalExecutionFragment(makeLinearTs(1), AlternatingSequence.of(1)));
    }

    @Test(timeout = 2000)
    public void testIsMaximalExecutionFragmentFalse() {
        assertFalse("Non-maximal fragment declared maximal",
                sut.isMaximalExecutionFragment(makeLinearTs(20), AlternatingSequence.of(3, "a3", 4, "a4", 5)));
        assertFalse("Single state, non-maximal fragment declared maximal",
                sut.isMaximalExecutionFragment(makeLinearTs(2), AlternatingSequence.of(1)));
    }

    @Test(expected = StateNotFoundException.class, timeout = 2000)
    public void testInvalidExecutionFragment() {
        assertFalse("expecting exception: fragment contains nonexistent states and actions",
                sut.isMaximalExecutionFragment(makeLinearTs(2), AlternatingSequence.of(3, "a3", 4, "a4", 5)));
    }

    @Test(timeout = 2000)
    public void testIsStateTerminal() {
        assertTrue(sut.isStateTerminal(makeLinearTs(3), 3));
    }

    @Test(timeout = 2000)
    public void testIsStateTerminalFalse() {
        assertFalse("s1 is not terminal", sut.isStateTerminal(makeLinearTs(3), 1));
        assertFalse("s3 is not terminal (TS is circular)", sut.isStateTerminal(makeCircularTs(3), 3));
    }

    @Test(expected = StateNotFoundException.class, timeout = 2000)
    public void testIsStateTerminalFalse_corner() {
        assertFalse("s4 is not a state", sut.isStateTerminal(makeLinearTs(3), 4));
    }

}
