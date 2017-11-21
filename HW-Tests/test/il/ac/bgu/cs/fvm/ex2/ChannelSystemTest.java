package il.ac.bgu.cs.fvm.ex2;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.seq;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.transition;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.List;
import java.util.Map;

import org.junit.Test;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.examples.AlternatingBitProtocolBuilder;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.singeltonMap;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.map;

public class ChannelSystemTest {

	FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

	@SuppressWarnings("unchecked")
	@Test
	public void alternatingBitProtocol() throws Exception {
		TransitionSystem<Pair<List<String>, Map<String, Object>>, String, String> ts = fvmFacadeImpl.transitionSystemFromChannelSystem(AlternatingBitProtocolBuilder.build());

		assertTrue(fvmFacadeImpl.isInitialExecutionFragment(ts, AlternatingSequence.of(p(seq("snd_msg(0)", "off", "wait(0)"), map()), //
				"C!0", //
				p(seq("set_tmr(0)", "off", "wait(0)"), map(p("C", seq(0)))), //
				"_tmr_on!|_tmr_on?", //
				p(seq("wait(0)", "on", "wait(0)"), map(p("C", seq(0)))), //
				"_timeout?|_timeout!", //
				p(seq("snd_msg(0)", "off", "wait(0)"), map(p("C", seq(0)))), //
				"C!0", //
				p(seq("set_tmr(0)", "off", "wait(0)"), map(p("C", seq(0, 0)))), //
				"C?y", //
				p(seq("set_tmr(0)", "off", "pr_msg(0)"), map(p("y", 0), p("C", seq(0)))), //
				"", //
				p(seq("set_tmr(0)", "off", "snd_ack(0)"), map(p("y", 0), p("C", seq(0)))), //
				"D!0", //
				p(seq("set_tmr(0)", "off", "wait(1)"), map(p("y", 0), p("C", seq(0)), p("D", seq(0)))), //
				"C?y", //
				p(seq("set_tmr(0)", "off", "pr_msg(1)"), map(p("y", 0), p("C", seq()), p("D", seq(0)))), //
				"", //
				p(seq("set_tmr(0)", "off", "wait(1)"), map(p("y", 0), p("C", seq()), p("D", seq(0))) //
				))));

	}

	@SuppressWarnings("unchecked")
	@Test
	public void test10() throws Exception {
		ProgramGraph<String, String> pg1 = fvmFacadeImpl.createProgramGraph();

		pg1.addLocation("l1");
		pg1.addLocation("l2");

		pg1.addInitialLocation("l1");

		pg1.addTransition(new PGTransition<>("l1", "true", "C?x", "l2"));
		pg1.addTransition(new PGTransition<>("l2", "x != 0 && size(C)<5", "C!x", "l1"));

		ProgramGraph<String, String> pg2 = fvmFacadeImpl.createProgramGraph();

		pg2.addLocation("l1");
		pg2.addLocation("l2");

		pg2.addInitialLocation("l1");

		pg2.addInitalization(seq("y:=0"));
		pg2.addInitalization(seq("y:=1"));

		pg2.addTransition(new PGTransition<>("l1", "size(C)<5", "C!y", "l2"));
		pg2.addTransition(new PGTransition<>("l2", "true", "C?y", "l1"));

		ChannelSystem<String, String> cs = new ChannelSystem<>(seq(pg1, pg2));

		TransitionSystem<Pair<List<String>, Map<String, Object>>, String, String> ts = fvmFacadeImpl.transitionSystemFromChannelSystem(cs);

		assertEquals(set(
                p(seq("l1", "l2"), map(p("y", 1), p("C", seq(1)))),
                p(seq("l1", "l1"), map(p("y", 0), p("C", seq()))), 
                p(seq("l1", "l1"), map(p("y", 1), p("C", seq()))),
                p(seq("l1", "l2"), map(p("x", 1), p("y", 1), p("C", seq(1)))),
				p(seq("l2", "l2"), map(p("x", 0), p("y", 0), p("C", seq()))), 
                p(seq("l2", "l2"), map(p("x", 1), p("y", 1), p("C", seq()))), 
                p(seq("l1", "l1"), map(p("x", 1), p("y", 1), p("C", seq()))), 
                p(seq("l1", "l1"), map(p("y", 0))), p(seq("l1", "l1"), map(p("y", 1))),
				p(seq("l1", "l2"), map(p("y", 0), p("C", seq(0))))
            ), ts.getStates());
        
		assertEquals(set(p(seq("l1", "l1"), map(p("y", 0))), p(seq("l1", "l1"), map(p("y", 1)))), ts.getInitialStates());
		assertEquals(set("C!x", "C!y", "C?y", "C?x"), ts.getActions());
		assertEquals(set("C = [0]", "C = []", "x = 1", "y = 0", "x = 0", "y = 1", "C = [1]", "l1", "l2"), ts.getAtomicPropositions());
		assertEquals(set(
                transition(p(seq("l1", "l2"), map(p("y", 0), p("C", seq(0)))), "C?y", p(seq("l1", "l1"), map(p("y", 0), p("C", seq())))),
				transition(p(seq("l1", "l2"), map(p("y", 1), p("C", seq(1)))), "C?x", p(seq("l2", "l2"), map(p("x", 1), p("y", 1), p("C", seq())))), 
                transition(p(seq("l1", "l1"), map(p("y", 0))), "C!y", p(seq("l1", "l2"), map(p("y", 0), p("C", seq(0))))),
				transition(p(seq("l1", "l1"), map(p("y", 0), p("C", seq()))), "C!y", p(seq("l1", "l2"), map(p("y", 0), p("C", seq(0))))), 
                transition(p(seq("l1", "l2"), map(p("y", 0), p("C", seq(0)))), "C?x", p(seq("l2", "l2"), map(p("x", 0), p("y", 0), p("C", seq())))),
				transition(p(seq("l1", "l2"), map(p("x", 1), p("y", 1), p("C", seq(1)))), "C?x", p(seq("l2", "l2"), map(p("x", 1), p("y", 1), p("C", seq())))), 
                transition(p(seq("l1", "l2"), map(p("y", 1), p("C", seq(1)))), "C?y", p(seq("l1", "l1"), map(p("y", 1), p("C", seq())))),
				transition(p(seq("l1", "l2"), map(p("x", 1), p("y", 1), p("C", seq(1)))), "C?y", p(seq("l1", "l1"), map(p("x", 1), p("y", 1), p("C", seq())))), 
                transition(p(seq("l1", "l1"), map(p("y", 1))), "C!y", p(seq("l1", "l2"), map(p("y", 1), p("C", seq(1))))),
				transition(p(seq("l1", "l1"), map(p("y", 1), p("C", seq()))), "C!y", p(seq("l1", "l2"), map(p("y", 1), p("C", seq(1))))), 
                transition(p(seq("l1", "l1"), map(p("x", 1), p("y", 1), p("C", seq()))), "C!y", p(seq("l1", "l2"), map(p("x", 1), p("y", 1), p("C", seq(1))))),
				transition(p(seq("l2", "l2"), map(p("x", 1), p("y", 1), p("C", seq()))), "C!x", p(seq("l1", "l2"), map(p("x", 1), p("y", 1), p("C", seq(1)))))), 
               ts.getTransitions());
        
		assertEquals(set("y = 1", "C = [1]", "l1", "l2"), ts.getLabel(p(seq("l1", "l2"), map(p("y", 1), p("C", seq(1))))));
		assertEquals(set("C = []", "y = 0", "l1"), ts.getLabel(p(seq("l1", "l1"), map(p("y", 0), p("C", seq())))));
		assertEquals(set("C = []", "y = 1", "l1"), ts.getLabel(p(seq("l1", "l1"), map(p("y", 1), p("C", seq())))));
		assertEquals(set("x = 1", "y = 1", "C = [1]", "l1", "l2"), ts.getLabel(p(seq("l1", "l2"), map(p("x", 1), p("y", 1), p("C", seq(1))))));
		assertEquals(set("C = []", "y = 0", "x = 0", "l2"), ts.getLabel(p(seq("l2", "l2"), map(p("x", 0), p("y", 0), p("C", seq())))));
		assertEquals(set("C = []", "x = 1", "y = 1", "l2"), ts.getLabel(p(seq("l2", "l2"), map(p("x", 1), p("y", 1), p("C", seq())))));
		assertEquals(set("C = []", "x = 1", "y = 1", "l1"), ts.getLabel(p(seq("l1", "l1"), map(p("x", 1), p("y", 1), p("C", seq())))));
		assertEquals(set("y = 0", "l1"), ts.getLabel(p(seq("l1", "l1"), map(p("y", 0)))));
		assertEquals(set("y = 1", "l1"), ts.getLabel(p(seq("l1", "l1"), map(p("y", 1)))));
		assertEquals(set("C = [0]", "y = 0", "l1", "l2"), ts.getLabel(p(seq("l1", "l2"), map(p("y", 0), p("C", seq(0))))));

	}
}
