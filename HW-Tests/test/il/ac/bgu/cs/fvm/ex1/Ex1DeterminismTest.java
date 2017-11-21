package il.ac.bgu.cs.fvm.ex1;

import il.ac.bgu.cs.fvm.FvmFacade;
import static il.ac.bgu.cs.fvm.TSTestUtils.*;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import org.junit.Before;
import org.junit.Test;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 *
 * @author michael
 */
public class Ex1DeterminismTest {

    FvmFacade sut = null;
    
    @Before
    public void setup() {
        sut = FvmFacade.createInstance();
    }
    
    @Test(timeout = 2000)
    public void testIsActionDeterministic() {
        assertTrue( sut.isActionDeterministic(makeCircularTs(4)) );
        assertTrue( sut.isActionDeterministic(makeLinearTs(1)) );
        assertTrue( sut.isActionDeterministic(makeBranchingTs(5, 1)) );
    }
    
    @Test(timeout = 2000)
    public void testIsActionDeterministicFalse_initial_states() {
        TransitionSystem<Integer,String,String> circularTs = makeCircularTs(4);
        circularTs.addInitialState( 2 );
        assertFalse("TS has more than a single initial state", sut.isActionDeterministic(circularTs) );
        
    }
    
    @Test(timeout = 2000)
    public void testIsActionDeterministicFalse_actions() {
        assertFalse("TS has an indeterministic state", sut.isActionDeterministic(makeBranchingTs(5, 3)) );
        assertFalse("TS has an indeterministic state", sut.isActionDeterministic(makeBranchingTs(5, 2)) );
    }
    
    @Test(timeout = 2000)
    public void testIsAPDeterministic() {
        assertTrue( sut.isAPDeterministic(makeLinearTs(5)) );
        assertTrue( sut.isAPDeterministic(addTagsByStateNames(makeLinearTs(5))) );
    }
    
    @Test(timeout = 2000)
    public void testIsAPDeterministicFalse_initial_states() {
        TransitionSystem<Integer, String, String> circularTs = makeCircularTs(4);
        circularTs.addInitialState( 2 );
        assertFalse("TS has more than a single initial state", sut.isAPDeterministic(circularTs) );
    }
    
    @Test(timeout = 2000)
    public void testIsAPDeterministicFalse_labels_empty() {
        TransitionSystem<Integer, String, String> circularTs = makeCircularTsWithReset(4);
        assertFalse("Each state has more than a single successor with the empty tag", sut.isAPDeterministic(circularTs) );
    }

    @Test(timeout = 2000)
    public void testIsAPDeterministicFalse_labels_same() {
        TransitionSystem<Integer,String, String>  circularTs = makeCircularTsWithReset(4);
        circularTs.addAtomicProposition("same");
        circularTs.addAtomicProposition("sameSame");
        circularTs.getStates().forEach( s->circularTs.addToLabel(s, "same") );
        circularTs.getStates().forEach( s->circularTs.addToLabel(s, "sameSame") );
        assertFalse("Each state has more than a single successor with the empty tag", sut.isAPDeterministic(circularTs) );
    }
}
