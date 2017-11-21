package il.ac.bgu.cs.fvm.ex1;

import il.ac.bgu.cs.fvm.FvmFacade;
import static il.ac.bgu.cs.fvm.TSTestUtils.makeBranchingTs;
import static il.ac.bgu.cs.fvm.TSTestUtils.makeCircularTs;
import static il.ac.bgu.cs.fvm.TSTestUtils.makeCircularTsWithReset;
import static il.ac.bgu.cs.fvm.TSTestUtils.makeLinearTs;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

/**
 *
 * @author michael
 */
public class Ex1ReachTest {

    FvmFacade sut = null;
    
    @Before
    public void setup() {
        sut = FvmFacade.createInstance();
    }

    @Test(timeout = 2000)
    public void testLinearReach() {
        assertEquals( set(1,2,3,4), sut.reach(makeLinearTs(4)) );
    }

    @Test(timeout = 2000)
    public void testBranchReach() {
        TransitionSystem<String, String, String> ts = makeBranchingTs(5, 2);
        assertEquals( ts.getStates(), sut.reach(ts) );
    }
    
    @Test( timeout = 2000 )
    public void testCircular() {
        TransitionSystem<Integer, String, String> ts = makeCircularTs(10);
        assertEquals( ts.getStates(), sut.reach(ts) );
    }
    
    @Test( timeout = 2000 )
    public void testCircularWithReset() {
        TransitionSystem<Integer, String, String> ts = makeCircularTsWithReset(10);
        assertEquals( ts.getStates(), sut.reach(ts) );
    }

    @Test( timeout = 2000 )
    public void testCircularWithResetAndDetached() {
        TransitionSystem<Integer, String, String> ts = makeCircularTsWithReset(5);
       
        ts.addStates(100,101,102,103);
        
        assertEquals( set(1,2,3,4,5), sut.reach(ts) );
        
        ts.addTransitionFrom(100).action("a1").to(101);
        ts.addTransitionFrom(100).action("a1").to(102);
        ts.addTransitionFrom(100).action("a1").to(103);
        ts.addTransitionFrom(103).action("a1").to(102);
        
        assertEquals( set(1,2,3,4,5), sut.reach(ts) );
        
        ts.addTransitionFrom(5).action("a1").to(103);
        assertEquals( set(1,2,3,4,5,102,103), sut.reach(ts) );
    }
}
