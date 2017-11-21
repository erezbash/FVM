package il.ac.bgu.cs.fvm.transitionsystem;

import java.util.Iterator;
import java.util.List;
import static java.util.stream.Collectors.toList;
import java.util.stream.IntStream;
import junit.framework.TestCase;
import org.junit.Test;

/**
 *
 * @author michael
 */
public class AlternatingSequenceTest extends TestCase {
    
    public AlternatingSequenceTest(String testName) {
        super(testName);
    }
    
    @Test
    public void testBasics() {
        AlternatingSequence<String, Integer> sut = AlternatingSequence.of("hello", 1, "world" );
        assertEquals( "hello", sut.head() );
        assertEquals( Integer.valueOf(1), sut.tail().head() );
    }
    
    @Test
    public void testEquals() {
        AlternatingSequence<String, Integer> sut = AlternatingSequence.of("hello", 1, "world" );
        AlternatingSequence<String, Integer> sut2 = AlternatingSequence.of("hello", 1, "world" );
        AlternatingSequence<String, Integer> sut2Pre = AlternatingSequence.of("pre", 0, "hello", 1, "world" );
        
        assertFalse( sut.equals(null) );
        assertFalse( sut.equals(sut2Pre) );
        assertTrue( sut.equals(sut) );
        assertTrue( sut.equals(sut2) );
        assertTrue( sut.equals(sut2Pre.tail().tail()) );
        
    }
    
    @Test(expected=IllegalArgumentException.class)
    public void testCreationIssues_length() {
        try {
            AlternatingSequence.of( 1,2,1,2 );
            fail();
        } catch (IllegalArgumentException iar) {
            // Good, that's what we want;
        }
    }
    
    @Test(expected=IllegalArgumentException.class)
    public void testCreationIssues_type() {
        AlternatingSequence.of( 1,2,1,2,1,2,1,2,1,2,1,2,1,"boom",1 );
    }
    
    @Test
    public void testCreationIssues() {
        AlternatingSequence<Integer, Integer> sut = AlternatingSequence.of( 1,2,3,4,5,6,7,8,9,10,11,12, 13 );
        List<Integer> expected = IntStream.range(1, 14).mapToObj(Integer::valueOf).collect(toList());
        Iterator<Integer> ints = expected.iterator();
        
        while ( ints.hasNext() ) {
            assertEquals( ints.next(), sut.head() );
            sut = sut.tail();
        }
        
        assertTrue( sut.isEmpty() );
        
    }
    
}
