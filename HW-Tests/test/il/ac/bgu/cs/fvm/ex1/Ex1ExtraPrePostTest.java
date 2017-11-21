package il.ac.bgu.cs.fvm.ex1;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.TSTestUtils;
import static il.ac.bgu.cs.fvm.TSTestUtils.makeBranchingTs;
import static il.ac.bgu.cs.fvm.TSTestUtils.makeCircularTsWithReset;
import static il.ac.bgu.cs.fvm.TSTestUtils.makeLinearTs;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import org.junit.Before;
import org.junit.Test;
import static org.junit.Assert.assertEquals;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.*;

/**
 * Tests that were not given to the students for EX1.
 * 
 * @author michael
 */
public class Ex1ExtraPrePostTest {
    
    TSTestUtils m = null;
    FvmFacade sut = null;
    
    @Before
    public void setup() {
        sut = FvmFacade.createInstance();
    }
    
    @Test(timeout = 2000)
    public void testActionPostSingleStateNoTransitions() throws Exception {
        TransitionSystem<Integer, String, Integer> ts = sut.createTransitionSystem();
        ts.addState(1);
        ts.addInitialState(1);
        ts.addAction("a1");
        
        assertEquals( set(), sut.post(ts, 1, "a1") );
    }

    @Test(timeout = 2000)
    public void testPostSingleStateNoTransitions() throws Exception {
        TransitionSystem<Integer, String, Integer> ts = sut.createTransitionSystem();
        ts.addState(1);
        ts.addInitialState(1);
        ts.addAction("a1");
        
        assertEquals(set(), sut.post(ts, 1) );
    }

    @Test(timeout = 2000)
    public void testActionPostSingleStateSingleTransition() throws Exception {
        TransitionSystem<Integer, String, Integer> ts = sut.createTransitionSystem();
        ts.addState( 1 );
        ts.addInitialState( 1 );
        ts.addAction("a1");
        
        ts.addTransitionFrom(1).action("a1").to(1);
        
        assertEquals(set(1), sut.post(ts, 1, "a1") );
    }
    
    @Test(timeout = 2000)
    public void testPostSingleStateSingleTransition() throws Exception {
        TransitionSystem<Integer, String, Integer> ts = sut.createTransitionSystem();
        ts.addState(1);
        ts.addInitialState(1);
        ts.addAction("a1");
        
        ts.addTransitionFrom(1).action("a1").to(1);
        
        assertEquals(set(1), sut.post(ts,1) );
    }

    @Test(timeout = 2000)
    public void testPostLinearStart() {
        assertEquals(set(3), sut.post(makeLinearTs(5), 2) );
    }
    
    @Test(timeout = 2000)
    public void testActionPostLinearStart() {
        assertEquals(set(3), sut.post(makeLinearTs(5), 2, "a2") );
    }
    
    @Test(timeout = 2000)
    public void testPostLinearEnd() {
        assertEquals(set(), sut.post(makeLinearTs(5), 5) );
    }
    
    @Test(timeout = 2000)
    public void testActionPostLinearEnd() {
        assertEquals(set(), sut.post(makeLinearTs(5), 5, "a1") );
    }
    
    @Test(timeout = 2000)
    public void testPostMulti() {
        assertEquals(set(3,1), sut.post(makeCircularTsWithReset(5), 2) );
    }
    
    @Test(timeout = 2000)
    public void testActionPostMulti() {
        assertEquals(set(1), sut.post(makeCircularTsWithReset(5), 2, "reset") );
        assertEquals(set(3), sut.post(makeCircularTsWithReset(5), 2, "a2") );
    }
    
    @Test(timeout = 2000)
    public void testIndeterministicActionPost() {
        assertEquals( set("s_1_3", "s_2_3"), sut.post(makeBranchingTs(5, 2), "s2", "fork"));
    }
    
    @Test(timeout = 2000)
    public void testPreNone() {
        assertEquals( set(), sut.pre(makeLinearTs(3), 1) );
    }
    
    @Test(timeout = 2000)
    public void testActionPreNone() {
        assertEquals( set(), sut.pre(makeLinearTs(3), 1, "a1") );
        assertEquals( set(), sut.pre(makeLinearTs(3), 1, "a2") );
    }
    
    @Test(timeout = 2000)
    public void testPreSingle() {
        assertEquals( set(1), sut.pre(makeLinearTs(3), 2) );
    }
    
    @Test(timeout = 2000)
    public void testActionPreSingle() {
        assertEquals( set(1), sut.pre(makeLinearTs(3), 2, "a1") );
        assertEquals( set(),     sut.pre(makeLinearTs(3), 2, "a2") );
    }
}
