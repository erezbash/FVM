package il.ac.bgu.cs.fvm.ex2;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.map;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.transition;
import static java.util.Arrays.asList;
import static org.junit.Assert.assertEquals;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.examples.CollatzProgramGraphBuilder;
import il.ac.bgu.cs.fvm.examples.ExtendedVendingMachineBuilder;
import il.ac.bgu.cs.fvm.examples.HillaryTrumpCounting;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;

public class ProgramGraphTest {

	FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

	@SuppressWarnings("unchecked")
	@Test
	public void debug() throws Exception {
		ProgramGraph<String, String> pg = fvmFacadeImpl.createProgramGraph();

		String l1 = "L1";
		String l2 = "L2";

		pg.addLocation(l1);
		pg.addLocation(l2);

		pg.addInitialLocation(l1);

		Set<ActionDef> effect = new HashSet<>();
		effect.add(new ParserBasedActDef());

		Set<ConditionDef> cond = new HashSet<>();
		cond.add(new ParserBasedCondDef());

		pg.addTransition(new PGTransition<String, String>(l1, "x>z", "x:=(x+y) % 5", l2));
		pg.addTransition(new PGTransition<String, String>(l2, "", "z:=(z-y) % 5", l1));

		pg.addInitalization(asList("x:=1", "y:=2", "z:=0"));

		TransitionSystem<Pair<String, Map<String, Object>>, String, String> ts = fvmFacadeImpl
				.transitionSystemFromProgramGraph(pg, effect, cond);

		assertEquals(set(p("L1", map(p("x", 1), p("y", 2), p("z", 0))), p("L1", map(p("x", 3), p("y", 2), p("z", 3))),
				p("L2", map(p("x", 3), p("y", 2), p("z", 0)))), ts.getStates());

		assertEquals(set(p("L1", map(p("x", 1), p("y", 2), p("z", 0)))), ts.getInitialStates());

		assertEquals(set("x:=(x+y) % 5", "z:=(z-y) % 5"), ts.getActions());

		assertEquals(set("y = 2", "z = 0", "x = 3", "z = 3", "x = 1", "L1", "L2"), ts.getAtomicPropositions());

		
		assertEquals(set(
				transition(p("L1", map(p("x", 1), p("y", 2), p("z", 0))), "x:=(x+y) % 5",
						p("L2", map(p("x", 3), p("y", 2), p("z", 0)))),
				transition(p("L2", map(p("x", 3), p("y", 2), p("z", 0))), "z:=(z-y) % 5",
						p("L1", map(p("x", 3), p("y", 2), p("z", 3))))),
				ts.getTransitions());

		assertEquals(set("y = 2", "z = 0", "x = 1","L1"), ts.getLabel(p("L1", map(p("x", 1), p("y", 2), p("z", 0)))));
		assertEquals(set("y = 2", "x = 3", "z = 3","L1"), ts.getLabel(p("L1", map(p("x", 3), p("y", 2), p("z", 3)))));
		assertEquals(set("y = 2", "z = 0", "x = 3","L2"), ts.getLabel(p("L2", map(p("x", 3), p("y", 2), p("z", 0)))));

	}

	@SuppressWarnings({ "rawtypes", "unchecked" })
	@Test
	public void soda() throws Exception {
		ProgramGraph pg = ExtendedVendingMachineBuilder.build();

		Set<ActionDef> actionDefs = ExtendedVendingMachineBuilder.getActionDefs();
		Set<ConditionDef> conditionDefs = ExtendedVendingMachineBuilder.getConditionDefs();

		TransitionSystem ts = fvmFacadeImpl.transitionSystemFromProgramGraph(pg, actionDefs, conditionDefs);

		assertEquals(set(p("select", map(p("nbeer", 2), p("nsoda", 0))), p("select",map(p("nbeer", 0), p("nsoda", 2))),
						p("select", map(p("nbeer", 1), p("nsoda", 2))), p("select", map(p("nbeer", 0), p("nsoda", 1))),
						p("select", map(p("nbeer", 1), p("nsoda", 1))), p("select", map(p("nbeer", 0), p("nsoda", 0))),
						p("select", map(p("nbeer", 1), p("nsoda", 0))), p("select", map(p("nbeer", 2), p("nsoda", 2))),
						p("select", map(p("nbeer", 2), p("nsoda", 1))), p("start",  map(p("nbeer", 1), p("nsoda", 0))),
						p("start", map(p("nbeer", 1), p("nsoda", 1))), p("start",   map(p("nbeer", 0), p("nsoda", 0))),
						p("start", map(p("nbeer", 2), p("nsoda", 1))), p("start",   map(p("nbeer", 2), p("nsoda", 2))),
						p("start", map(p("nbeer", 1), p("nsoda", 2))), p("start",   map(p("nbeer", 0), p("nsoda", 1))),
						p("start", map(p("nbeer", 2), p("nsoda", 0))), p("start",   map(p("nbeer", 0), p("nsoda", 2)))),
				ts.getStates());

		assertEquals(set(p("start", map(p("nbeer", 2), p("nsoda", 2)))), ts.getInitialStates());

		assertEquals(set("refill", "sget", "ret_coin", "bget", "coin"), ts.getActions());

		assertEquals(
				set("nbeer = 2", "nbeer = 1", "nbeer = 0", "nsoda = 1", "nsoda = 0", "nsoda = 2", "start", "select"),
				ts.getAtomicPropositions());

		assertEquals(set(transition(p("select", map(p("nbeer", 1), p("nsoda", 1))), "bget",
						p("start", map(p("nbeer", 0), p("nsoda", 1)))),
				transition(p("select", map(p("nbeer", 2), p("nsoda", 2))), "bget",
						p("start", map(p("nbeer", 1), p("nsoda", 2)))),
				transition(p("select", map(p("nbeer", 2), p("nsoda", 0))), "bget",
						p("start", map(p("nbeer", 1), p("nsoda", 0)))),
				transition(p("start", map(p("nbeer", 2), p("nsoda", 2))), "coin",
						p("select", map(p("nbeer", 2), p("nsoda", 2)))),
				transition(p("start", map(p("nbeer", 2), p("nsoda", 0))), "coin",
						p("select", map(p("nbeer", 2), p("nsoda", 0)))),
				transition(p("start", map(p("nbeer", 0), p("nsoda", 2))), "coin",
						p("select", map(p("nbeer", 0), p("nsoda", 2)))),
				transition(p("start", map(p("nbeer", 1), p("nsoda", 1))), "coin",
						p("select", map(p("nbeer", 1), p("nsoda", 1)))),
				transition(p("start", map(p("nbeer", 0), p("nsoda", 0))), "coin",
						p("select", map(p("nbeer", 0), p("nsoda", 0)))),
				transition(p("select", map(p("nbeer", 2), p("nsoda", 1))), "sget",
						p("start", map(p("nbeer", 2), p("nsoda", 0)))),
				transition(p("select", map(p("nbeer", 1), p("nsoda", 2))), "sget",
						p("start", map(p("nbeer", 1), p("nsoda", 1)))),
				transition(p("select", map(p("nbeer", 0), p("nsoda", 1))), "sget",
						p("start", map(p("nbeer", 0), p("nsoda", 0)))),
				transition(p("start", map(p("nbeer", 2), p("nsoda", 2))), "refill",
						p("start", map(p("nbeer", 2), p("nsoda", 2)))),
				transition(p("start", map(p("nbeer", 2), p("nsoda", 0))), "refill",
						p("start", map(p("nbeer", 2), p("nsoda", 2)))),
				transition(p("start", map(p("nbeer", 0), p("nsoda", 2))), "refill",
						p("start", map(p("nbeer", 2), p("nsoda", 2)))),
				transition(p("start", map(p("nbeer", 1), p("nsoda", 1))), "refill",
						p("start", map(p("nbeer", 2), p("nsoda", 2)))),
				transition(p("start", map(p("nbeer", 0), p("nsoda", 0))), "refill",
						p("start", map(p("nbeer", 2), p("nsoda", 2)))),
				transition(p("select", map(p("nbeer", 1), p("nsoda", 2))), "bget",
						p("start", map(p("nbeer", 0), p("nsoda", 2)))),
				transition(p("select", map(p("nbeer", 1), p("nsoda", 0))), "bget",
						p("start", map(p("nbeer", 0), p("nsoda", 0)))),
				transition(p("select", map(p("nbeer", 2), p("nsoda", 1))), "bget",
						p("start", map(p("nbeer", 1), p("nsoda", 1)))),
				transition(p("start", map(p("nbeer", 2), p("nsoda", 1))), "coin",
						p("select", map(p("nbeer", 2), p("nsoda", 1)))),
				transition(p("start", map(p("nbeer", 1), p("nsoda", 2))), "coin",
						p("select", map(p("nbeer", 1), p("nsoda", 2)))),
				transition(p("start", map(p("nbeer", 0), p("nsoda", 1))), "coin",
						p("select", map(p("nbeer", 0), p("nsoda", 1)))),
				transition(p("start", map(p("nbeer", 1), p("nsoda", 0))), "coin",
						p("select", map(p("nbeer", 1), p("nsoda", 0)))),
				transition(p("select", map(p("nbeer", 2), p("nsoda", 2))), "sget",
						p("start", map(p("nbeer", 2), p("nsoda", 1)))),
				transition(p("select", map(p("nbeer", 1), p("nsoda", 1))), "sget",
						p("start", map(p("nbeer", 1), p("nsoda", 0)))),
				transition(p("select", map(p("nbeer", 0), p("nsoda", 2))), "sget",
						p("start", map(p("nbeer", 0), p("nsoda", 1)))),
				transition(p("select", map(p("nbeer", 0), p("nsoda", 0))), "ret_coin",
						p("start", map(p("nbeer", 0), p("nsoda", 0)))),
				transition(p("start", map(p("nbeer", 2), p("nsoda", 1))), "refill",
						p("start", map(p("nbeer", 2), p("nsoda", 2)))),
				transition(p("start", map(p("nbeer", 1), p("nsoda", 2))), "refill",
						p("start", map(p("nbeer", 2), p("nsoda", 2)))),
				transition(p("start", map(p("nbeer", 0), p("nsoda", 1))), "refill",
						p("start", map(p("nbeer", 2), p("nsoda", 2)))),
				transition(p("start", map(p("nbeer", 1), p("nsoda", 0))), "refill",
						p("start", map(p("nbeer", 2), p("nsoda", 2))))),
				ts.getTransitions());

		assertEquals(set("nbeer = 2", "nsoda = 0", "select"),
				ts.getLabel(p("select", map(p("nbeer", 2), p("nsoda", 0)))));
		assertEquals(set("nbeer = 0", "nsoda = 2", "select"),
				ts.getLabel(p("select", map(p("nbeer", 0), p("nsoda", 2)))));
		assertEquals(set("nbeer = 1", "nsoda = 2", "select"),
				ts.getLabel(p("select", map(p("nbeer", 1), p("nsoda", 2)))));
		assertEquals(set("nbeer = 0", "nsoda = 1", "select"),
				ts.getLabel(p("select", map(p("nbeer", 0), p("nsoda", 1)))));
		assertEquals(set("nbeer = 1", "nsoda = 1", "select"),
				ts.getLabel(p("select", map(p("nbeer", 1), p("nsoda", 1)))));
		assertEquals(set("nbeer = 0", "nsoda = 0", "select"),
				ts.getLabel(p("select", map(p("nbeer", 0), p("nsoda", 0)))));
		assertEquals(set("nbeer = 1", "nsoda = 0", "select"),
				ts.getLabel(p("select", map(p("nbeer", 1), p("nsoda", 0)))));
		assertEquals(set("nbeer = 2", "nsoda = 2", "select"),
				ts.getLabel(p("select", map(p("nbeer", 2), p("nsoda", 2)))));
		assertEquals(set("nbeer = 2", "nsoda = 1", "select"),
				ts.getLabel(p("select", map(p("nbeer", 2), p("nsoda", 1)))));
		assertEquals(set("nbeer = 1", "nsoda = 0", "start"),
				ts.getLabel(p("start", map(p("nbeer", 1), p("nsoda", 0)))));
		assertEquals(set("nbeer = 1", "nsoda = 1", "start"),
				ts.getLabel(p("start", map(p("nbeer", 1), p("nsoda", 1)))));
		assertEquals(set("nbeer = 0", "nsoda = 0", "start"),
				ts.getLabel(p("start", map(p("nbeer", 0), p("nsoda", 0)))));
		assertEquals(set("nbeer = 2", "nsoda = 1", "start"),
				ts.getLabel(p("start", map(p("nbeer", 2), p("nsoda", 1)))));
		assertEquals(set("nbeer = 2", "nsoda = 2", "start"),
				ts.getLabel(p("start", map(p("nbeer", 2), p("nsoda", 2)))));
		assertEquals(set("nbeer = 1", "nsoda = 2", "start"),
				ts.getLabel(p("start", map(p("nbeer", 1), p("nsoda", 2)))));
		assertEquals(set("nbeer = 0", "nsoda = 1", "start"),
				ts.getLabel(p("start", map(p("nbeer", 0), p("nsoda", 1)))));
		assertEquals(set("nbeer = 2", "nsoda = 0", "start"),
				ts.getLabel(p("start", map(p("nbeer", 2), p("nsoda", 0)))));
		assertEquals(set("nbeer = 0", "nsoda = 2", "start"),
				ts.getLabel(p("start", map(p("nbeer", 0), p("nsoda", 2)))));

	}

	@SuppressWarnings({ "serial", "unchecked", "rawtypes" })
	@Test
	public void collatz() throws Exception {
		ProgramGraph pg = CollatzProgramGraphBuilder.build();

		Set<ActionDef> ad = new HashSet<ActionDef>() {
			{
				add(new ParserBasedActDef());
			}
		};
		Set<ConditionDef> cd = new HashSet<ConditionDef>() {
			{
				add(new ParserBasedCondDef());
			}
		};

		TransitionSystem ts = fvmFacadeImpl.transitionSystemFromProgramGraph(pg, ad, cd);

		assertEquals(set(p("running", map(p("x", 10))), p("finished", map(p("x", 1))), p("running", map(p("x", 8))),
				p("running", map(p("x", 6))), p("running", map(p("x", 5))), p("running", map(p("x", 4))),
				p("running", map(p("x", 3))), p("running", map(p("x", 2))), p("running", map(p("x", 1))),
				p("running", map(p("x", 16)))), ts.getStates());

		assertEquals(set(p("running", map(p("x", 6)))), ts.getInitialStates());

		assertEquals(set("", "x:= (3 * x) + 1", "x:= x / 2"), ts.getActions());

		assertEquals(set("running", "finished", "x = 5", "x = 6", "x = 3", "x = 4", "x = 16", "x = 8", "x = 1", "x = 2", "x = 10"),
				ts.getAtomicPropositions());

		assertEquals(
				set(transition(p("running", map(p("x", 5))), "x:= (3 * x) + 1", p("running", map(p("x", 16)))),
						transition(p("running", map(p("x", 2))), "x:= x / 2", p("running", map(p("x", 1)))),
						transition(p("running", map(p("x", 3))), "x:= (3 * x) + 1", p("running", map(p("x", 10)))),
						transition(p("running", map(p("x", 4))), "x:= x / 2", p("running", map(p("x", 2)))),
						transition(p("running", map(p("x", 6))), "x:= x / 2", p("running", map(p("x", 3)))),
						transition(p("running", map(p("x", 8))), "x:= x / 2", p("running", map(p("x", 4)))),
						transition(p("running", map(p("x", 10))), "x:= x / 2", p("running", map(p("x", 5)))),
						transition(p("running", map(p("x", 1))), "", p("finished", map(p("x", 1)))),
						transition(p("running", map(p("x", 16))), "x:= x / 2", p("running", map(p("x", 8))))),
				ts.getTransitions());

		assertEquals(set("running","x = 10"), ts.getLabel(p("running", map(p("x", 10)))));
		assertEquals(set("finished","x = 1"), ts.getLabel(p("finished", map(p("x", 1)))));
		assertEquals(set("running","x = 8"), ts.getLabel(p("running", map(p("x", 8)))));
		assertEquals(set("running","x = 6"), ts.getLabel(p("running", map(p("x", 6)))));
		assertEquals(set("running","x = 5"), ts.getLabel(p("running", map(p("x", 5)))));
		assertEquals(set("running","x = 4"), ts.getLabel(p("running", map(p("x", 4)))));
		assertEquals(set("running","x = 3"), ts.getLabel(p("running", map(p("x", 3)))));
		assertEquals(set("running","x = 2"), ts.getLabel(p("running", map(p("x", 2)))));
		assertEquals(set("running","x = 1"), ts.getLabel(p("running", map(p("x", 1)))));
		assertEquals(set("running","x = 16"), ts.getLabel(p("running", map(p("x", 16)))));
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	@Test
	public void runningCounter() throws Exception {
		ProgramGraph<String, String> pg = fvmFacadeImpl.createProgramGraph();

		pg.addLocation("S");
		pg.addInitialLocation("S");

		Set<ActionDef> effect = set(new ParserBasedActDef());
		Set<ConditionDef> cond = set(new ParserBasedCondDef());

		pg.addTransition(new PGTransition("S", "x<100", "x:=x+1", "S"));

		pg.addInitalization(asList("x:=1"));

		TransitionSystem ts = fvmFacadeImpl.transitionSystemFromProgramGraph(pg, effect, cond);

		assertEquals(
				// IntStream.range(1, 100).map(i -> p("S", map(p("x",
				// i)))).collect(Collectors.toSet())

				set(p("S", map(p("x", 96))), p("S", map(p("x", 97))), p("S", map(p("x", 98))), p("S", map(p("x", 99))),
						p("S", map(p("x", 100))), p("S", map(p("x", 88))), p("S", map(p("x", 89))),
						p("S", map(p("x", 90))), p("S", map(p("x", 91))), p("S", map(p("x", 92))),
						p("S", map(p("x", 93))), p("S", map(p("x", 94))), p("S", map(p("x", 95))),
						p("S", map(p("x", 80))), p("S", map(p("x", 81))), p("S", map(p("x", 82))),
						p("S", map(p("x", 83))), p("S", map(p("x", 84))), p("S", map(p("x", 85))),
						p("S", map(p("x", 86))), p("S", map(p("x", 87))), p("S", map(p("x", 72))),
						p("S", map(p("x", 73))), p("S", map(p("x", 74))), p("S", map(p("x", 75))),
						p("S", map(p("x", 76))), p("S", map(p("x", 77))), p("S", map(p("x", 78))),
						p("S", map(p("x", 79))), p("S", map(p("x", 64))), p("S", map(p("x", 65))),
						p("S", map(p("x", 66))), p("S", map(p("x", 67))), p("S", map(p("x", 68))),
						p("S", map(p("x", 69))), p("S", map(p("x", 70))), p("S", map(p("x", 71))),
						p("S", map(p("x", 56))), p("S", map(p("x", 57))), p("S", map(p("x", 58))),
						p("S", map(p("x", 59))), p("S", map(p("x", 60))), p("S", map(p("x", 61))),
						p("S", map(p("x", 62))), p("S", map(p("x", 63))), p("S", map(p("x", 48))),
						p("S", map(p("x", 49))), p("S", map(p("x", 50))), p("S", map(p("x", 51))),
						p("S", map(p("x", 52))), p("S", map(p("x", 53))), p("S", map(p("x", 54))),
						p("S", map(p("x", 55))), p("S", map(p("x", 40))), p("S", map(p("x", 41))),
						p("S", map(p("x", 42))), p("S", map(p("x", 43))), p("S", map(p("x", 44))),
						p("S", map(p("x", 45))), p("S", map(p("x", 46))), p("S", map(p("x", 47))),
						p("S", map(p("x", 32))), p("S", map(p("x", 33))), p("S", map(p("x", 34))),
						p("S", map(p("x", 35))), p("S", map(p("x", 36))), p("S", map(p("x", 37))),
						p("S", map(p("x", 38))), p("S", map(p("x", 39))), p("S", map(p("x", 24))),
						p("S", map(p("x", 25))), p("S", map(p("x", 26))), p("S", map(p("x", 27))),
						p("S", map(p("x", 28))), p("S", map(p("x", 29))), p("S", map(p("x", 30))),
						p("S", map(p("x", 31))), p("S", map(p("x", 16))), p("S", map(p("x", 17))),
						p("S", map(p("x", 18))), p("S", map(p("x", 19))), p("S", map(p("x", 20))),
						p("S", map(p("x", 21))), p("S", map(p("x", 22))), p("S", map(p("x", 23))),
						p("S", map(p("x", 8))), p("S", map(p("x", 9))), p("S", map(p("x", 10))),
						p("S", map(p("x", 11))), p("S", map(p("x", 12))), p("S", map(p("x", 13))),
						p("S", map(p("x", 14))), p("S", map(p("x", 15))), p("S", map(p("x", 1))),
						p("S", map(p("x", 2))), p("S", map(p("x", 3))), p("S", map(p("x", 4))), p("S", map(p("x", 5))),
						p("S", map(p("x", 6))), p("S", map(p("x", 7)))),
				ts.getStates());

		assertEquals(set(p("S", map(p("x", 1)))), ts.getInitialStates());
		assertEquals(set("x:=x+1"), ts.getActions());
		assertEquals(set("S","x = 23", "x = 24", "x = 25", "x = 26", "x = 20", "x = 21", "x = 22", "x = 27", "x = 28",
				"x = 29", "x = 100", "x = 92", "x = 93", "x = 94", "x = 95", "x = 90", "x = 91", "x = 12", "x = 13",
				"x = 14", "x = 15", "x = 96", "x = 97", "x = 98", "x = 10", "x = 99", "x = 11", "x = 16", "x = 17",
				"x = 18", "x = 19", "x = 40", "x = 45", "x = 46", "x = 47", "x = 48", "x = 41", "x = 42", "x = 43",
				"x = 44", "x = 49", "x = 34", "x = 35", "x = 36", "x = 37", "x = 30", "x = 31", "x = 32", "x = 33",
				"x = 38", "x = 39", "x = 60", "x = 61", "x = 62", "x = 67", "x = 68", "x = 69", "x = 63", "x = 64",
				"x = 65", "x = 66", "x = 50", "x = 51", "x = 56", "x = 57", "x = 58", "x = 59", "x = 52", "x = 53",
				"x = 54", "x = 55", "x = 5", "x = 81", "x = 6", "x = 82", "x = 83", "x = 3", "x = 84", "x = 4", "x = 9",
				"x = 7", "x = 8", "x = 80", "x = 89", "x = 85", "x = 1", "x = 2", "x = 86", "x = 87", "x = 88",
				"x = 70", "x = 71", "x = 72", "x = 73", "x = 78", "x = 79", "x = 74", "x = 75", "x = 76", "x = 77"),
				ts.getAtomicPropositions());
		assertEquals(set(transition(p("S", map(p("x", 13))), "x:=x+1", p("S", map(p("x", 14)))),
				transition(p("S", map(p("x", 5))), "x:=x+1", p("S", map(p("x", 6)))),
				transition(p("S", map(p("x", 53))), "x:=x+1", p("S", map(p("x", 54)))),
				transition(p("S", map(p("x", 45))), "x:=x+1", p("S", map(p("x", 46)))),
				transition(p("S", map(p("x", 37))), "x:=x+1", p("S", map(p("x", 38)))),
				transition(p("S", map(p("x", 29))), "x:=x+1", p("S", map(p("x", 30)))),
				transition(p("S", map(p("x", 21))), "x:=x+1", p("S", map(p("x", 22)))),
				transition(p("S", map(p("x", 93))), "x:=x+1", p("S", map(p("x", 94)))),
				transition(p("S", map(p("x", 61))), "x:=x+1", p("S", map(p("x", 62)))),
				transition(p("S", map(p("x", 69))), "x:=x+1", p("S", map(p("x", 70)))),
				transition(p("S", map(p("x", 77))), "x:=x+1", p("S", map(p("x", 78)))),
				transition(p("S", map(p("x", 85))), "x:=x+1", p("S", map(p("x", 86)))),
				transition(p("S", map(p("x", 15))), "x:=x+1", p("S", map(p("x", 16)))),
				transition(p("S", map(p("x", 7))), "x:=x+1", p("S", map(p("x", 8)))),
				transition(p("S", map(p("x", 23))), "x:=x+1", p("S", map(p("x", 24)))),
				transition(p("S", map(p("x", 95))), "x:=x+1", p("S", map(p("x", 96)))),
				transition(p("S", map(p("x", 31))), "x:=x+1", p("S", map(p("x", 32)))),
				transition(p("S", map(p("x", 39))), "x:=x+1", p("S", map(p("x", 40)))),
				transition(p("S", map(p("x", 47))), "x:=x+1", p("S", map(p("x", 48)))),
				transition(p("S", map(p("x", 55))), "x:=x+1", p("S", map(p("x", 56)))),
				transition(p("S", map(p("x", 63))), "x:=x+1", p("S", map(p("x", 64)))),
				transition(p("S", map(p("x", 71))), "x:=x+1", p("S", map(p("x", 72)))),
				transition(p("S", map(p("x", 79))), "x:=x+1", p("S", map(p("x", 80)))),
				transition(p("S", map(p("x", 87))), "x:=x+1", p("S", map(p("x", 88)))),
				transition(p("S", map(p("x", 6))), "x:=x+1", p("S", map(p("x", 7)))),
				transition(p("S", map(p("x", 46))), "x:=x+1", p("S", map(p("x", 47)))),
				transition(p("S", map(p("x", 54))), "x:=x+1", p("S", map(p("x", 55)))),
				transition(p("S", map(p("x", 38))), "x:=x+1", p("S", map(p("x", 39)))),
				transition(p("S", map(p("x", 22))), "x:=x+1", p("S", map(p("x", 23)))),
				transition(p("S", map(p("x", 94))), "x:=x+1", p("S", map(p("x", 95)))),
				transition(p("S", map(p("x", 62))), "x:=x+1", p("S", map(p("x", 63)))),
				transition(p("S", map(p("x", 70))), "x:=x+1", p("S", map(p("x", 71)))),
				transition(p("S", map(p("x", 78))), "x:=x+1", p("S", map(p("x", 79)))),
				transition(p("S", map(p("x", 86))), "x:=x+1", p("S", map(p("x", 87)))),
				transition(p("S", map(p("x", 14))), "x:=x+1", p("S", map(p("x", 15)))),
				transition(p("S", map(p("x", 30))), "x:=x+1", p("S", map(p("x", 31)))),
				transition(p("S", map(p("x", 96))), "x:=x+1", p("S", map(p("x", 97)))),
				transition(p("S", map(p("x", 40))), "x:=x+1", p("S", map(p("x", 41)))),
				transition(p("S", map(p("x", 32))), "x:=x+1", p("S", map(p("x", 33)))),
				transition(p("S", map(p("x", 8))), "x:=x+1", p("S", map(p("x", 9)))),
				transition(p("S", map(p("x", 48))), "x:=x+1", p("S", map(p("x", 49)))),
				transition(p("S", map(p("x", 80))), "x:=x+1", p("S", map(p("x", 81)))),
				transition(p("S", map(p("x", 88))), "x:=x+1", p("S", map(p("x", 89)))),
				transition(p("S", map(p("x", 56))), "x:=x+1", p("S", map(p("x", 57)))),
				transition(p("S", map(p("x", 64))), "x:=x+1", p("S", map(p("x", 65)))),
				transition(p("S", map(p("x", 72))), "x:=x+1", p("S", map(p("x", 73)))),
				transition(p("S", map(p("x", 16))), "x:=x+1", p("S", map(p("x", 17)))),
				transition(p("S", map(p("x", 24))), "x:=x+1", p("S", map(p("x", 25)))),
				transition(p("S", map(p("x", 9))), "x:=x+1", p("S", map(p("x", 10)))),
				transition(p("S", map(p("x", 41))), "x:=x+1", p("S", map(p("x", 42)))),
				transition(p("S", map(p("x", 1))), "x:=x+1", p("S", map(p("x", 2)))),
				transition(p("S", map(p("x", 49))), "x:=x+1", p("S", map(p("x", 50)))),
				transition(p("S", map(p("x", 33))), "x:=x+1", p("S", map(p("x", 34)))),
				transition(p("S", map(p("x", 25))), "x:=x+1", p("S", map(p("x", 26)))),
				transition(p("S", map(p("x", 17))), "x:=x+1", p("S", map(p("x", 18)))),
				transition(p("S", map(p("x", 57))), "x:=x+1", p("S", map(p("x", 58)))),
				transition(p("S", map(p("x", 97))), "x:=x+1", p("S", map(p("x", 98)))),
				transition(p("S", map(p("x", 89))), "x:=x+1", p("S", map(p("x", 90)))),
				transition(p("S", map(p("x", 65))), "x:=x+1", p("S", map(p("x", 66)))),
				transition(p("S", map(p("x", 73))), "x:=x+1", p("S", map(p("x", 74)))),
				transition(p("S", map(p("x", 81))), "x:=x+1", p("S", map(p("x", 82)))),
				transition(p("S", map(p("x", 90))), "x:=x+1", p("S", map(p("x", 91)))),
				transition(p("S", map(p("x", 2))), "x:=x+1", p("S", map(p("x", 3)))),
				transition(p("S", map(p("x", 10))), "x:=x+1", p("S", map(p("x", 11)))),
				transition(p("S", map(p("x", 50))), "x:=x+1", p("S", map(p("x", 51)))),
				transition(p("S", map(p("x", 42))), "x:=x+1", p("S", map(p("x", 43)))),
				transition(p("S", map(p("x", 58))), "x:=x+1", p("S", map(p("x", 59)))),
				transition(p("S", map(p("x", 98))), "x:=x+1", p("S", map(p("x", 99)))),
				transition(p("S", map(p("x", 66))), "x:=x+1", p("S", map(p("x", 67)))),
				transition(p("S", map(p("x", 74))), "x:=x+1", p("S", map(p("x", 75)))),
				transition(p("S", map(p("x", 82))), "x:=x+1", p("S", map(p("x", 83)))),
				transition(p("S", map(p("x", 34))), "x:=x+1", p("S", map(p("x", 35)))),
				transition(p("S", map(p("x", 26))), "x:=x+1", p("S", map(p("x", 27)))),
				transition(p("S", map(p("x", 18))), "x:=x+1", p("S", map(p("x", 19)))),
				transition(p("S", map(p("x", 3))), "x:=x+1", p("S", map(p("x", 4)))),
				transition(p("S", map(p("x", 11))), "x:=x+1", p("S", map(p("x", 12)))),
				transition(p("S", map(p("x", 43))), "x:=x+1", p("S", map(p("x", 44)))),
				transition(p("S", map(p("x", 35))), "x:=x+1", p("S", map(p("x", 36)))),
				transition(p("S", map(p("x", 27))), "x:=x+1", p("S", map(p("x", 28)))),
				transition(p("S", map(p("x", 19))), "x:=x+1", p("S", map(p("x", 20)))),
				transition(p("S", map(p("x", 51))), "x:=x+1", p("S", map(p("x", 52)))),
				transition(p("S", map(p("x", 59))), "x:=x+1", p("S", map(p("x", 60)))),
				transition(p("S", map(p("x", 91))), "x:=x+1", p("S", map(p("x", 92)))),
				transition(p("S", map(p("x", 99))), "x:=x+1", p("S", map(p("x", 100)))),
				transition(p("S", map(p("x", 67))), "x:=x+1", p("S", map(p("x", 68)))),
				transition(p("S", map(p("x", 75))), "x:=x+1", p("S", map(p("x", 76)))),
				transition(p("S", map(p("x", 83))), "x:=x+1", p("S", map(p("x", 84)))),
				transition(p("S", map(p("x", 92))), "x:=x+1", p("S", map(p("x", 93)))),
				transition(p("S", map(p("x", 4))), "x:=x+1", p("S", map(p("x", 5)))),
				transition(p("S", map(p("x", 52))), "x:=x+1", p("S", map(p("x", 53)))),
				transition(p("S", map(p("x", 44))), "x:=x+1", p("S", map(p("x", 45)))),
				transition(p("S", map(p("x", 60))), "x:=x+1", p("S", map(p("x", 61)))),
				transition(p("S", map(p("x", 68))), "x:=x+1", p("S", map(p("x", 69)))),
				transition(p("S", map(p("x", 76))), "x:=x+1", p("S", map(p("x", 77)))),
				transition(p("S", map(p("x", 84))), "x:=x+1", p("S", map(p("x", 85)))),
				transition(p("S", map(p("x", 12))), "x:=x+1", p("S", map(p("x", 13)))),
				transition(p("S", map(p("x", 20))), "x:=x+1", p("S", map(p("x", 21)))),
				transition(p("S", map(p("x", 36))), "x:=x+1", p("S", map(p("x", 37)))),
				transition(p("S", map(p("x", 28))), "x:=x+1", p("S", map(p("x", 29))))), ts.getTransitions());
		assertEquals(set("S","x = 96"), ts.getLabel(p("S", map(p("x", 96)))));
		assertEquals(set("S","x = 97"), ts.getLabel(p("S", map(p("x", 97)))));
		assertEquals(set("S","x = 98"), ts.getLabel(p("S", map(p("x", 98)))));
		assertEquals(set("S","x = 99"), ts.getLabel(p("S", map(p("x", 99)))));
		assertEquals(set("S","x = 100"), ts.getLabel(p("S", map(p("x", 100)))));
		assertEquals(set("S","x = 88"), ts.getLabel(p("S", map(p("x", 88)))));
		assertEquals(set("S","x = 89"), ts.getLabel(p("S", map(p("x", 89)))));
		assertEquals(set("S","x = 90"), ts.getLabel(p("S", map(p("x", 90)))));
		assertEquals(set("S","x = 91"), ts.getLabel(p("S", map(p("x", 91)))));
		assertEquals(set("S","x = 92"), ts.getLabel(p("S", map(p("x", 92)))));
		assertEquals(set("S","x = 93"), ts.getLabel(p("S", map(p("x", 93)))));
		assertEquals(set("S","x = 94"), ts.getLabel(p("S", map(p("x", 94)))));
		assertEquals(set("S","x = 95"), ts.getLabel(p("S", map(p("x", 95)))));
		assertEquals(set("S","x = 80"), ts.getLabel(p("S", map(p("x", 80)))));
		assertEquals(set("S","x = 81"), ts.getLabel(p("S", map(p("x", 81)))));
		assertEquals(set("S","x = 82"), ts.getLabel(p("S", map(p("x", 82)))));
		assertEquals(set("S","x = 83"), ts.getLabel(p("S", map(p("x", 83)))));
		assertEquals(set("S","x = 84"), ts.getLabel(p("S", map(p("x", 84)))));
		assertEquals(set("S","x = 85"), ts.getLabel(p("S", map(p("x", 85)))));
		assertEquals(set("S","x = 86"), ts.getLabel(p("S", map(p("x", 86)))));
		assertEquals(set("S","x = 87"), ts.getLabel(p("S", map(p("x", 87)))));
		assertEquals(set("S","x = 72"), ts.getLabel(p("S", map(p("x", 72)))));
		assertEquals(set("S","x = 73"), ts.getLabel(p("S", map(p("x", 73)))));
		assertEquals(set("S","x = 74"), ts.getLabel(p("S", map(p("x", 74)))));
		assertEquals(set("S","x = 75"), ts.getLabel(p("S", map(p("x", 75)))));
		assertEquals(set("S","x = 76"), ts.getLabel(p("S", map(p("x", 76)))));
		assertEquals(set("S","x = 77"), ts.getLabel(p("S", map(p("x", 77)))));
		assertEquals(set("S","x = 78"), ts.getLabel(p("S", map(p("x", 78)))));
		assertEquals(set("S","x = 79"), ts.getLabel(p("S", map(p("x", 79)))));
		assertEquals(set("S","x = 64"), ts.getLabel(p("S", map(p("x", 64)))));
		assertEquals(set("S","x = 65"), ts.getLabel(p("S", map(p("x", 65)))));
		assertEquals(set("S","x = 66"), ts.getLabel(p("S", map(p("x", 66)))));
		assertEquals(set("S","x = 67"), ts.getLabel(p("S", map(p("x", 67)))));
		assertEquals(set("S","x = 68"), ts.getLabel(p("S", map(p("x", 68)))));
		assertEquals(set("S","x = 69"), ts.getLabel(p("S", map(p("x", 69)))));
		assertEquals(set("S","x = 70"), ts.getLabel(p("S", map(p("x", 70)))));
		assertEquals(set("S","x = 71"), ts.getLabel(p("S", map(p("x", 71)))));
		assertEquals(set("S","x = 56"), ts.getLabel(p("S", map(p("x", 56)))));
		assertEquals(set("S","x = 57"), ts.getLabel(p("S", map(p("x", 57)))));
		assertEquals(set("S","x = 58"), ts.getLabel(p("S", map(p("x", 58)))));
		assertEquals(set("S","x = 59"), ts.getLabel(p("S", map(p("x", 59)))));
		assertEquals(set("S","x = 60"), ts.getLabel(p("S", map(p("x", 60)))));
		assertEquals(set("S","x = 61"), ts.getLabel(p("S", map(p("x", 61)))));
		assertEquals(set("S","x = 62"), ts.getLabel(p("S", map(p("x", 62)))));
		assertEquals(set("S","x = 63"), ts.getLabel(p("S", map(p("x", 63)))));
		assertEquals(set("S","x = 48"), ts.getLabel(p("S", map(p("x", 48)))));
		assertEquals(set("S","x = 49"), ts.getLabel(p("S", map(p("x", 49)))));
		assertEquals(set("S","x = 50"), ts.getLabel(p("S", map(p("x", 50)))));
		assertEquals(set("S","x = 51"), ts.getLabel(p("S", map(p("x", 51)))));
		assertEquals(set("S","x = 52"), ts.getLabel(p("S", map(p("x", 52)))));
		assertEquals(set("S","x = 53"), ts.getLabel(p("S", map(p("x", 53)))));
		assertEquals(set("S","x = 54"), ts.getLabel(p("S", map(p("x", 54)))));
		assertEquals(set("S","x = 55"), ts.getLabel(p("S", map(p("x", 55)))));
		assertEquals(set("S","x = 40"), ts.getLabel(p("S", map(p("x", 40)))));
		assertEquals(set("S","x = 41"), ts.getLabel(p("S", map(p("x", 41)))));
		assertEquals(set("S","x = 42"), ts.getLabel(p("S", map(p("x", 42)))));
		assertEquals(set("S","x = 43"), ts.getLabel(p("S", map(p("x", 43)))));
		assertEquals(set("S","x = 44"), ts.getLabel(p("S", map(p("x", 44)))));
		assertEquals(set("S","x = 45"), ts.getLabel(p("S", map(p("x", 45)))));
		assertEquals(set("S","x = 46"), ts.getLabel(p("S", map(p("x", 46)))));
		assertEquals(set("S","x = 47"), ts.getLabel(p("S", map(p("x", 47)))));
		assertEquals(set("S","x = 32"), ts.getLabel(p("S", map(p("x", 32)))));
		assertEquals(set("S","x = 33"), ts.getLabel(p("S", map(p("x", 33)))));
		assertEquals(set("S","x = 34"), ts.getLabel(p("S", map(p("x", 34)))));
		assertEquals(set("S","x = 35"), ts.getLabel(p("S", map(p("x", 35)))));
		assertEquals(set("S","x = 36"), ts.getLabel(p("S", map(p("x", 36)))));
		assertEquals(set("S","x = 37"), ts.getLabel(p("S", map(p("x", 37)))));
		assertEquals(set("S","x = 38"), ts.getLabel(p("S", map(p("x", 38)))));
		assertEquals(set("S","x = 39"), ts.getLabel(p("S", map(p("x", 39)))));
		assertEquals(set("S","x = 24"), ts.getLabel(p("S", map(p("x", 24)))));
		assertEquals(set("S","x = 25"), ts.getLabel(p("S", map(p("x", 25)))));
		assertEquals(set("S","x = 26"), ts.getLabel(p("S", map(p("x", 26)))));
		assertEquals(set("S","x = 27"), ts.getLabel(p("S", map(p("x", 27)))));
		assertEquals(set("S","x = 28"), ts.getLabel(p("S", map(p("x", 28)))));
		assertEquals(set("S","x = 29"), ts.getLabel(p("S", map(p("x", 29)))));
		assertEquals(set("S","x = 30"), ts.getLabel(p("S", map(p("x", 30)))));
		assertEquals(set("S","x = 31"), ts.getLabel(p("S", map(p("x", 31)))));
		assertEquals(set("S","x = 16"), ts.getLabel(p("S", map(p("x", 16)))));
		assertEquals(set("S","x = 17"), ts.getLabel(p("S", map(p("x", 17)))));
		assertEquals(set("S","x = 18"), ts.getLabel(p("S", map(p("x", 18)))));
		assertEquals(set("S","x = 19"), ts.getLabel(p("S", map(p("x", 19)))));
		assertEquals(set("S","x = 20"), ts.getLabel(p("S", map(p("x", 20)))));
		assertEquals(set("S","x = 21"), ts.getLabel(p("S", map(p("x", 21)))));
		assertEquals(set("S","x = 22"), ts.getLabel(p("S", map(p("x", 22)))));
		assertEquals(set("S","x = 23"), ts.getLabel(p("S", map(p("x", 23)))));
		assertEquals(set("S","x = 8"), ts.getLabel(p("S", map(p("x", 8)))));
		assertEquals(set("S","x = 9"), ts.getLabel(p("S", map(p("x", 9)))));
		assertEquals(set("S","x = 10"), ts.getLabel(p("S", map(p("x", 10)))));
		assertEquals(set("S","x = 11"), ts.getLabel(p("S", map(p("x", 11)))));
		assertEquals(set("S","x = 12"), ts.getLabel(p("S", map(p("x", 12)))));
		assertEquals(set("S","x = 13"), ts.getLabel(p("S", map(p("x", 13)))));
		assertEquals(set("S","x = 14"), ts.getLabel(p("S", map(p("x", 14)))));
		assertEquals(set("S","x = 15"), ts.getLabel(p("S", map(p("x", 15)))));
		assertEquals(set("S","x = 1"), ts.getLabel(p("S", map(p("x", 1)))));
		assertEquals(set("S","x = 2"), ts.getLabel(p("S", map(p("x", 2)))));
		assertEquals(set("S","x = 3"), ts.getLabel(p("S", map(p("x", 3)))));
		assertEquals(set("S","x = 4"), ts.getLabel(p("S", map(p("x", 4)))));
		assertEquals(set("S","x = 5"), ts.getLabel(p("S", map(p("x", 5)))));
		assertEquals(set("S","x = 6"), ts.getLabel(p("S", map(p("x", 6)))));
		assertEquals(set("S","x = 7"), ts.getLabel(p("S", map(p("x", 7)))));

	}

	public void electorsCounting() throws Exception {
		ProgramGraph<String, String> pg = HillaryTrumpCounting.buildSmall();
		TransitionSystem<Pair<String, Map<String, Object>>, String, String> ts = fvmFacadeImpl
				.transitionSystemFromProgramGraph(pg, set(new ParserBasedActDef()), set(new ParserBasedCondDef()));

		assertEquals(29705, ts.getStates().size());
		assertEquals(235110, ts.getTransitions().size());
	}

}
