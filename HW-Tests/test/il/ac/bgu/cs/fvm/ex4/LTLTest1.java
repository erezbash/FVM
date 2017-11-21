package il.ac.bgu.cs.fvm.ex4;

import static il.ac.bgu.cs.fvm.ltl.LTL.next;
import static il.ac.bgu.cs.fvm.ltl.LTL.not;
import static il.ac.bgu.cs.fvm.ltl.LTL.until;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static org.junit.Assert.assertEquals;

import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.ltl.AP;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.util.Pair;

public class LTLTest1 {

	FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

	@Test
	public void test() {
		AP<String> p = new AP<>("p");

		LTL<String> ltl = until(not(p), next(p));

		Automaton<?, String> aut = fvmFacadeImpl.LTL2NBA(ltl);

		assertEquals(aut, expected());

	}

	@SuppressWarnings("unchecked")
	Automaton<Pair<String, Integer>, String> expected() {
		Automaton<Pair<String, Integer>, String> aut = new Automaton<>();
		Pair<String, Integer> s1  = p(set( "(!p U ()p)", "!()p", "!p"), 1);
		Pair<String, Integer> s2  = p(set( "(!p U ()p)",  "()p", "!p"), 1);
		Pair<String, Integer> s3  = p(set( "(!p U ()p)",  "()p", "!p"), 0);
		Pair<String, Integer> s4  = p(set( "(!p U ()p)",  "()p",  "p"), 1);
		Pair<String, Integer> s5  = p(set("!(!p U ()p)", "!()p",  "p"), 1);
		Pair<String, Integer> s6  = p(set( "(!p U ()p)",  "()p",  "p"), 0);
		Pair<String, Integer> s7  = p(set("!(!p U ()p)", "!()p",  "p"), 0);
		Pair<String, Integer> s8  = p(set( "(!p U ()p)", "!()p", "!p"), 0);
		Pair<String, Integer> s9  = p(set("!(!p U ()p)", "!()p", "!p"), 0);
		Pair<String, Integer> s10 = p(set("!(!p U ()p)", "!()p", "!p"), 1);

		Set<String> notP = set();
		Set<String> p = set("p");

		aut.addTransition(s1, notP, s1);
		aut.addTransition(s1, notP, s2);
		aut.addTransition(s3, notP, s4);
		aut.addTransition(s3, notP, s5);
		aut.addTransition(s2, notP, s6);
		aut.addTransition(s2, notP, s7);
		aut.addTransition(s4, p, s6);
		aut.addTransition(s4, p, s7);
		aut.addTransition(s8, notP, s1);
		aut.addTransition(s8, notP, s2);
		aut.addTransition(s6, p, s4);
		aut.addTransition(s6, p, s5);
		aut.addTransition(s5, p, s3);
		aut.addTransition(s5, p, s8);
		aut.addTransition(s5, p, s9);
		aut.addTransition(s7, p, s1);
		aut.addTransition(s7, p, s2);
		aut.addTransition(s7, p, s10);
		aut.addTransition(s9, notP, s10);
		aut.addTransition(s10, notP, s9);

		aut.setInitial(s3);
		aut.setInitial(s8);
		aut.setInitial(s6);

		aut.setAccepting(s3);
		aut.setAccepting(s8);
		aut.setAccepting(s6);
		aut.setAccepting(s7);
		aut.setAccepting(s9);

		return aut;
	}

}
