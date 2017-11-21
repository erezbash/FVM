package il.ac.bgu.cs.fvm.transitionsystem;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

/**
 * An alternating sequence of states and actions.
 * When creating instances of this class, consider using the static methods
 * {@code of(...)}, such as {@link #of(java.lang.Object, java.lang.Object, java.lang.Object, java.lang.Object, java.lang.Object).
 * @author michael
 * @param <S> Type of states.
 * @param <A> Type of actions.
 */
public class AlternatingSequence<S,A> {
    
    public static <S,A> AlternatingSequence<S,A> of(S s) {
        return new AlternatingSequence<>(Collections.singletonList(s));
    }
    
    public static <S,A> AlternatingSequence<S,A> of(S s1, A a1, S s2) {
        return new AlternatingSequence<>(Arrays.asList(s1, s2), Collections.singletonList(a1));
    }
    
    public static <S,A> AlternatingSequence<S,A> of(S s1, A a1, S s2, A a2, S s3) {
        return new AlternatingSequence<>(Arrays.asList(s1, s2, s3), Arrays.asList(a1, a2));
    }
    
    public static <S,A> AlternatingSequence<S,A> of(S s1, A a1, S s2, A a2, S s3, A a3, S s4) {
        return new AlternatingSequence<>(Arrays.asList(s1, s2, s3, s4), Arrays.asList(a1, a2, a3));
    }
    
    public static <S,A> AlternatingSequence<S,A> of(S s1, A a1, S s2, A a2, S s3, A a3, S s4, A a4, S s5) {
        return new AlternatingSequence<>(Arrays.asList(s1, s2, s3, s4, s5), Arrays.asList(a1, a2, a3, a4));
    }
    
    @SuppressWarnings("unchecked")
	public static <S,A> AlternatingSequence<S,A> of(S s1, A a1, Object... tail ) {
        List<S> states = new LinkedList<>();
        List<A> actions = new LinkedList<>();
        
        if ( tail.length%2 == 0 ) {
            throw new IllegalArgumentException("Length of tail cannot describe an execution fragment");
        }
        
        states.add(s1);
        actions.add(a1);
        for ( int i=0; i<tail.length-1; i+=2 ) {
            states.add((S) tail[i]);
            actions.add((A) tail[i+1]);
        }
        states.add((S) tail[tail.length-1]);
        return new AlternatingSequence<>(states, actions);
    }
    
    private final List<Object> items;
    
    public AlternatingSequence(List<S> states, List<A> actions ) {
        if ( states.size() != actions.size()+1 ) {
            throw new IllegalArgumentException("List sizes do not match");
        }
        List<Object> itemsBuilder = new ArrayList<>(states.size() + actions.size());
        Iterator<?> sts=states.iterator();
        for ( Iterator<?> acts=actions.iterator(); acts.hasNext(); ) {
            itemsBuilder.add(sts.next());
            itemsBuilder.add(acts.next());
        }
        itemsBuilder.add(sts.next());
        items = Collections.unmodifiableList(itemsBuilder);
    }
    
    private AlternatingSequence( List<Object> items ) {
        this.items = items;
    }
    
    @SuppressWarnings("unchecked")
	public S head() {
        return (S) items.get(0);
    }
    
    public AlternatingSequence<A,S> tail() {
        return new AlternatingSequence<>(items.subList(1, items.size()) );
    }
    
    @SuppressWarnings("unchecked")
    public S last() {
        return (S) items.get(items.size()-1);
    }
    
    public int size() { 
        return items.size();
    }
    
    public boolean isEmpty() {
        return size()==0;
    }

    @Override
    public int hashCode() {
        int hash = 5;
        hash = 67 * hash + Objects.hashCode(this.items);
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final AlternatingSequence<?, ?> other = (AlternatingSequence<?, ?>) obj;
        return Objects.equals(this.items, other.items);
    }

    @Override
    public String toString() {
        return "[AlternatingSequence "+ items + ']';
    }
    
}
