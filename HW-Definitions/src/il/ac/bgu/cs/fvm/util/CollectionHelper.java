package il.ac.bgu.cs.fvm.util;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

/**
 * Some methods to support literal collections.
 *
 */
public class CollectionHelper {

    public static <L,A> PGTransition<L,A> pgtransition(L from, String cond, A action, L to) {
        return new PGTransition<>(from, cond,action, to);
    }

    public static Transition<Object, Object> transition(Object from, Object action, Object to) {
        return new Transition<>(from, action, to);
    }

    /*
    public static <T1,T2> Pair<T1, T2> p(T1 x, T2 y) {
        return new Pair<T1, T2>(x, y);
    }
    */
    
    // The above is better but takes ages to build the project (javac bug?)
    @SuppressWarnings("rawtypes")
	public static <T1,T2> Pair p(T1 x, T2 y) {
        return new Pair<>(x, y);
    }


    @SafeVarargs
	public static  <T> Set<T> set(T... ses) {
        return new HashSet<>(Arrays.asList(ses));
    }

    @SafeVarargs
	public static  <T> List<T> seq(T... ses) {
        return Arrays.asList(ses);
    }

    @SuppressWarnings("unchecked")
	public static <K,V> Map<K,V> map(Pair<K,V>... pairs) {
        return IntStream.range(0, pairs.length)
                .mapToObj(i -> pairs[i])
                .collect(Collectors.toMap(Pair::getFirst, Pair::getSecond));
    }

    public static <K,V> Map<K,V> singeltonMap(K key, V value ) {
        Map<K,V> res = new HashMap<>();
        res.put(key, value);
        return res;
    }
    
    public static  <T1,T2> Stream<Pair<T1,T2>> product(Set<T1> s1, Set<T2> s2) {
        return s1.stream().flatMap(e1 -> s2.stream().map(e2
                -> new Pair<>(e1, e2)));
    }
}
