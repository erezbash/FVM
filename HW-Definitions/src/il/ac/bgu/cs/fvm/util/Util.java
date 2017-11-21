package il.ac.bgu.cs.fvm.util;

import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.ltl.LTL;
import java.util.ArrayList;
import java.util.List;

/**
 * Utility methods for implementation.
 */
public class Util {

	public static <T1, T2> Set<Pair<T1, T2>> getPairs(Set<T1> s1, Set<T2> s2) {
		Stream<Pair<T1, T2>> str = s1.stream().flatMap(e1 -> s2.stream().map(e2 -> new Pair<>(e1, e2))); //
		return str.collect(Collectors.toSet());
	}

	public static <T> Set<Set<T>> powerSet(Set<T> aset) {
		List<T> orderedItems = new ArrayList<>(aset);
		IntStream powerSetMemberIdxs = IntStream.range(0, (int) Math.pow(2, aset.size()));

		Stream<Set<T>> stream = powerSetMemberIdxs.parallel().mapToObj(e -> {
			IntStream range2 = IntStream.range(0, orderedItems.size());
			return range2.filter(i -> (e & (0b1 << i)) != 0).mapToObj(i -> orderedItems.get(i)).collect(Collectors.toSet());
		});

		return stream.collect(Collectors.toSet());
	}

	/**
	 * @param gnba
	 */
	public static <L> void printColoredAutomatonTransitions(MultiColorAutomaton<Set<LTL<L>>, L> gnba) {
		gnba.getTransitions().entrySet().stream()
				.forEach((s1) -> s1.getValue().entrySet().stream().forEach(s2 -> s2.getValue().stream()
						.forEach(s3 -> System.out.println(s1.getKey() + "----" + s2.getKey() + "---->" + s3))));
	}

	/**
	 * @param gnba
	 */
	public static <S,L> void printAutomatonTransitions(Automaton<S, L> nba) {
		nba.getTransitions().entrySet().stream()
				.forEach((s1) -> s1.getValue().entrySet().stream().forEach(s2 -> s2.getValue().stream()
						.forEach(s3 -> System.out.println(s1.getKey() + "----" + s2.getKey() + "---->" + s3))));
	}

}
