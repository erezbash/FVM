package il.ac.bgu.cs.fvm.ex4;

import static il.ac.bgu.cs.fvm.ltl.LTL.and;
import static il.ac.bgu.cs.fvm.ltl.LTL.next;
import static il.ac.bgu.cs.fvm.ltl.LTL.not;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static org.junit.Assert.assertEquals;

import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.ltl.AP;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.util.Pair;

public class LTLTest {

	FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

	@Test
	public void test() {
		AP<String> p = new AP<>("p");

		LTL<String> ltl = and(not(p), next(p));

		Automaton<?, String> aut = fvmFacadeImpl.LTL2NBA(ltl);

		assertEquals(aut, expected());
	}

	Automaton<Pair<Set<String>, Integer>, String> expected() {
		Automaton<Pair<Set<String>, Integer>, String> aut = new Automaton<>();

		Pair<Set<String>, Integer> p_np = new Pair<>(set("!(!p /\\ ()p)", "()p", "p"), 0);
		Pair<Set<String>, Integer> p_notnp = new Pair<>(set("!(!p /\\ ()p)", "!()p", "p"), 0);
		Pair<Set<String>, Integer> notp_np = new Pair<>(set("(!p /\\ ()p)", "!p", "()p"), 0);
		Pair<Set<String>, Integer> notp_notnp = new Pair<>(set("!(!p /\\ ()p)", "!()p", "!p"), 0);

		Set<String> p = set("p");
		Set<String> notp = set();

		aut.addTransition(notp_notnp, notp, notp_np);
		aut.addTransition(notp_notnp, notp, notp_notnp);
		aut.addTransition(p_notnp, p, notp_notnp);
		aut.addTransition(p_notnp, p, notp_np);
		aut.addTransition(notp_np, notp, p_np);
		aut.addTransition(notp_np, notp, p_notnp);
		aut.addTransition(p_np, p, p_np);
		aut.addTransition(p_np, p, p_notnp);

		aut.setInitial(notp_np);

		aut.setAccepting(p_np);
		aut.setAccepting(p_notnp);
		aut.setAccepting(notp_np);
		aut.setAccepting(notp_notnp);

		return aut;

	}

}
