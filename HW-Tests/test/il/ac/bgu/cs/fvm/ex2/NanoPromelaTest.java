package il.ac.bgu.cs.fvm.ex2;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.map;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.pgtransition;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.transition;
import static org.junit.Assert.assertEquals;

import java.io.InputStream;
import java.io.StringBufferInputStream;
import java.util.Map;
import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.examples.VendingmachineInNanopromela;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;

@SuppressWarnings("deprecation")
public class NanoPromelaTest {

	FvmFacade fvmFacadeImpl;

	@Before
	public void setup() {
		fvmFacadeImpl = FvmFacade.createInstance();
	}

	@Test
	public void test1() throws Exception {
		try (InputStream in = getClass().getClassLoader().getResourceAsStream("il/ac/bgu/cs/fvm/nanopromela/tst1.np")) {
			ProgramGraph<String, String> pg = fvmFacadeImpl.programGraphFromNanoPromela(in);

			assertEquals(set("", "do::x<3->x:=x+1od;y:=9",
					"if::a==c->bb:=1::a==b->if::x!=y->do::x<3->x:=x+1odfi;y:=9fi", "y:=9"), pg.getLocations());
			assertEquals(set("if::a==c->bb:=1::a==b->if::x!=y->do::x<3->x:=x+1odfi;y:=9fi"), pg.getInitialLocations());
			assertEquals(set(), pg.getInitalizations());
			assertEquals(
					set(pgtransition("if::a==c->bb:=1::a==b->if::x!=y->do::x<3->x:=x+1odfi;y:=9fi",
							"(a==b) && ((x!=y) && (!((x<3))))", "", "y:=9"), pgtransition("y:=9", "", "y:=9", ""),
							pgtransition("do::x<3->x:=x+1od;y:=9", "(x<3)", "x:=x+1", "do::x<3->x:=x+1od;y:=9"),
							pgtransition("do::x<3->x:=x+1od;y:=9", "!((x<3))", "", "y:=9"),
							pgtransition("if::a==c->bb:=1::a==b->if::x!=y->do::x<3->x:=x+1odfi;y:=9fi", "(a==c)",
									"bb:=1", ""),
							pgtransition("if::a==c->bb:=1::a==b->if::x!=y->do::x<3->x:=x+1odfi;y:=9fi",
									"(a==b) && ((x!=y) && ((x<3)))", "x:=x+1", "do::x<3->x:=x+1od;y:=9")),
					pg.getTransitions());
		}
	}

	@Test
	public void test2() throws Exception {
		try (InputStream in = getClass().getClassLoader().getResourceAsStream("il/ac/bgu/cs/fvm/nanopromela/tst2.np")) {
			ProgramGraph<String, String> pg = fvmFacadeImpl.programGraphFromNanoPromela(in);

			assertEquals(
					set("", "ppp:=2", "do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2",
							"if::x>1->C?x;D!5;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2fi",
							"y:=1;do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2",
							"D!5;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2",
							"do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2",
							"D!r;do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"),
					pg.getLocations());
			assertEquals(set("if::x>1->C?x;D!5;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2fi"),
					pg.getInitialLocations());
			assertEquals(set(), pg.getInitalizations());
			assertEquals(
					set(pgtransition("do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2", "(x>1)", "C?x",
							"y:=1;do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"),
							pgtransition("ppp:=2", "", "ppp:=2", ""),
							pgtransition("do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2", "!((x>1))", "", "ppp:=2"),
							pgtransition("do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2", "(r>3)",
									"r:=1", "D!r;do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"),
							pgtransition("D!r;do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2", "",
									"D!r", "do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"),
							pgtransition("D!5;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2", "", "D!5",
									"do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"),
							pgtransition("if::x>1->C?x;D!5;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2fi", "(x>1)",
									"C?x", "D!5;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"),
							pgtransition("y:=1;do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2", "",
									"y:=1", "do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"),
							pgtransition("do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2",
									"!((r>3))", "", "do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2")),
					pg.getTransitions());

		}
	}

	@Test
	public void test3() throws Exception {
		try (InputStream in = getClass().getClassLoader().getResourceAsStream("il/ac/bgu/cs/fvm/nanopromela/tst3.np")) {
			ProgramGraph<String, String> pg = fvmFacadeImpl.programGraphFromNanoPromela(in);

			assertEquals(set("", "do::x<4->x:=5;x:=6od;x:=7", "x:=6;do::x<4->x:=5;x:=6od;x:=7", "x:=7",
					"if::x<3->do::x<4->x:=5;x:=6od;x:=7fi"), pg.getLocations());
			assertEquals(set("if::x<3->do::x<4->x:=5;x:=6od;x:=7fi"), pg.getInitialLocations());
			assertEquals(set(), pg.getInitalizations());
			assertEquals(set(
					pgtransition("if::x<3->do::x<4->x:=5;x:=6od;x:=7fi", "(x<3) && ((x<4))", "x:=5",
							"x:=6;do::x<4->x:=5;x:=6od;x:=7"),
					pgtransition("x:=7", "", "x:=7", ""),
					pgtransition("do::x<4->x:=5;x:=6od;x:=7", "(x<4)", "x:=5", "x:=6;do::x<4->x:=5;x:=6od;x:=7"),
					pgtransition("do::x<4->x:=5;x:=6od;x:=7", "!((x<4))", "", "x:=7"),
					pgtransition("if::x<3->do::x<4->x:=5;x:=6od;x:=7fi", "(x<3) && (!((x<4)))", "", "x:=7"),
					pgtransition("x:=6;do::x<4->x:=5;x:=6od;x:=7", "", "x:=6", "do::x<4->x:=5;x:=6od;x:=7")),
					pg.getTransitions());

		}
	}

	@SuppressWarnings("unchecked")
	@Test
	public void soda() throws Exception {
		ProgramGraph<String, String> pg = VendingmachineInNanopromela.build();

		assertEquals(
				set("", "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
				pg.getLocations());
		assertEquals(
				set("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
				pg.getInitialLocations());
		assertEquals(set(), pg.getInitalizations());
		assertEquals(
				set(pgtransition(
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"(nbeer>0)", "nbeer:=nbeer-1",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
						pgtransition(
								"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								"(true)", "skip",
								"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
						pgtransition(
								"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								"!((true)||(true))", "", ""),
						pgtransition(
								"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								"(nsoda>0)", "nsoda:=nsoda-1",
								"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
						pgtransition(
								"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								"((nsoda==0)&&(nbeer==0))", "skip",
								"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
						pgtransition(
								"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								"(true)", "atomic{nbeer:=3;nsoda:=3}",
								"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od")),
				pg.getTransitions());

		Set<ActionDef> ad = set(new ParserBasedActDef());
		Set<ConditionDef> cd = set(new ParserBasedCondDef());

		TransitionSystem<Pair<String, Map<String, Object>>, String, String> ts = fvmFacadeImpl
				.transitionSystemFromProgramGraph(pg, ad, cd);

		assertEquals(
				set("", "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
				pg.getLocations());
		assertEquals(
				set("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
				pg.getInitialLocations());
		assertEquals(set(), pg.getInitalizations());
		assertEquals(
				set(pgtransition(
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"(true)", "skip",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
						pgtransition(
								"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								"(nbeer>0)", "nbeer:=nbeer-1",
								"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
						pgtransition(
								"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								"!((true)||(true))", "", ""),
						pgtransition(
								"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								"(nsoda>0)", "nsoda:=nsoda-1",
								"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
						pgtransition(
								"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								"(true)", "atomic{nbeer:=3;nsoda:=3}",
								"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
						pgtransition(
								"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								"((nsoda==0)&&(nbeer==0))", "skip",
								"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od")),
				pg.getTransitions());

		assertEquals(set(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 2), p("nsoda", 3))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map()),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 3), p("nsoda", 0))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 1), p("nsoda", 2))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 0), p("nsoda", 1))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 3), p("nsoda", 1))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 1), p("nsoda", 3))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 2), p("nsoda", 0))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 0), p("nsoda", 2))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 3), p("nsoda", 2))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 2), p("nsoda", 1))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 0), p("nsoda", 3))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 3), p("nsoda", 3))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 2), p("nsoda", 2))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 1), p("nsoda", 0))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 1), p("nsoda", 1))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 0), p("nsoda", 0))),
				p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map()),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 2), p("nsoda", 3))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 3), p("nsoda", 3))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 2), p("nsoda", 2))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 3), p("nsoda", 0))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 1), p("nsoda", 2))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 0), p("nsoda", 1))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 1), p("nsoda", 1))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 0), p("nsoda", 0))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 3), p("nsoda", 2))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 2), p("nsoda", 1))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 0), p("nsoda", 3))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 3), p("nsoda", 1))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 1), p("nsoda", 3))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 2), p("nsoda", 0))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 0), p("nsoda", 2))),
				p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map(p("nbeer", 1), p("nsoda", 0)))),
				ts.getStates());
		assertEquals(
				set(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						map())),
				ts.getInitialStates());
		assertEquals(set("nsoda:=nsoda-1", "skip", "nbeer:=nbeer-1", "atomic{nbeer:=3;nsoda:=3}"), ts.getActions());
		assertEquals(set("nbeer = 3", "nbeer = 2", "nbeer = 1", "nbeer = 0",
				"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
				"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
				"nsoda = 1", "nsoda = 0", "nsoda = 3", "nsoda = 2"), ts.getAtomicPropositions());
		assertEquals(set(transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 3), p("nsoda", 0))),
						"nbeer:=nbeer-1",
						p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 2), p("nsoda", 0)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 2))),
								"nbeer:=nbeer-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 2)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 3))),
								"nbeer:=nbeer-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 3)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 0))),
								"skip",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 0)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 1))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 0))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 1))),
								"nsoda:=nsoda-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 0)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 3))),
								"nsoda:=nsoda-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 2)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 2))),
								"nsoda:=nsoda-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 1)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 2))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 1))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 1)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 3))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 0))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 0)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 2))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 2)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3))),
								"nbeer:=nbeer-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 3)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 1))),
								"nbeer:=nbeer-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 1)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 2))),
								"nbeer:=nbeer-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 2)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 0))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 2))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 1))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 3))),
								"nsoda:=nsoda-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 2)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 2))),
								"nsoda:=nsoda-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 1)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 1))),
								"nsoda:=nsoda-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 0)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 3))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 2))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 2)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 1))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 1)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 3))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 0))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 0)))),
						transition(
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map()),
								"skip",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map())),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 2))),
								"nbeer:=nbeer-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 2)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 0))),
								"nbeer:=nbeer-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 0)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 1))),
								"nbeer:=nbeer-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 1)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 3))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3))),
								"nsoda:=nsoda-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 2)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 1))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 2))),
								"nsoda:=nsoda-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 1)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 0))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 2))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 1))),
								"nsoda:=nsoda-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 0)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 2))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 2)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 1))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 1)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 0))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 0)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 1))),
								"nbeer:=nbeer-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 1)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 3))),
								"nbeer:=nbeer-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map()),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 0))),
								"nbeer:=nbeer-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 0)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 0))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 2))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 1))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 3))),
								"atomic{nbeer:=3;nsoda:=3}",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 3)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 2))),
								"nsoda:=nsoda-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 1)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 1))),
								"nsoda:=nsoda-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 0)))),
						transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 3))),
								"nsoda:=nsoda-1",
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 2)))),
						transition(
								p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map()),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map())),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 3))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 2), p("nsoda", 3)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 0))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 3), p("nsoda", 0)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 2))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 1), p("nsoda", 2)))),
						transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 1))),
								"skip",
								p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
										map(p("nbeer", 0), p("nsoda", 1))))),
				ts.getTransitions());

		assertEquals(set("nbeer = 2",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 3"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 2), p("nsoda", 3)))));
		assertEquals(
				set("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
				ts.getLabel(
						p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map())));
		assertEquals(set("nbeer = 3",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 0"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 3), p("nsoda", 0)))));
		assertEquals(set("nbeer = 1",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 2"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 1), p("nsoda", 2)))));
		assertEquals(set("nbeer = 0",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 1"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 0), p("nsoda", 1)))));
		assertEquals(set("nbeer = 3",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 1"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 3), p("nsoda", 1)))));
		assertEquals(set("nbeer = 1",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 3"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 1), p("nsoda", 3)))));
		assertEquals(set("nbeer = 2",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 0"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 2), p("nsoda", 0)))));
		assertEquals(set("nbeer = 0",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 2"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 0), p("nsoda", 2)))));
		assertEquals(set("nbeer = 3",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 2"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 3), p("nsoda", 2)))));
		assertEquals(set("nbeer = 2",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 1"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 2), p("nsoda", 1)))));
		assertEquals(set("nbeer = 0",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 3"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 0), p("nsoda", 3)))));
		assertEquals(set("nbeer = 3",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 3"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 3), p("nsoda", 3)))));
		assertEquals(set("nbeer = 2",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 2"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 2), p("nsoda", 2)))));
		assertEquals(set("nbeer = 1",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 0"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 1), p("nsoda", 0)))));
		assertEquals(set("nbeer = 1",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 1"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 1), p("nsoda", 1)))));
		assertEquals(set("nbeer = 0",
						"if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 0"),
				ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 0), p("nsoda", 0)))));
		assertEquals(
				set("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
				ts.getLabel(
						p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map())));
		assertEquals(set("nbeer = 2",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 3"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 2), p("nsoda", 3)))));
		assertEquals(set("nbeer = 3",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 3"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 3), p("nsoda", 3)))));
		assertEquals(set("nbeer = 2",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 2"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 2), p("nsoda", 2)))));
		assertEquals(set("nbeer = 3",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 0"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 3), p("nsoda", 0)))));
		assertEquals(set("nbeer = 1",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 2"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 1), p("nsoda", 2)))));
		assertEquals(set("nbeer = 0",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 1"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 0), p("nsoda", 1)))));
		assertEquals(set("nbeer = 1",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 1"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 1), p("nsoda", 1)))));
		assertEquals(set("nbeer = 0",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 0"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 0), p("nsoda", 0)))));
		assertEquals(set("nbeer = 3",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 2"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 3), p("nsoda", 2)))));
		assertEquals(set("nbeer = 2",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 1"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 2), p("nsoda", 1)))));
		assertEquals(set("nbeer = 0",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 3"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 0), p("nsoda", 3)))));
		assertEquals(set("nbeer = 3",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 1"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 3), p("nsoda", 1)))));
		assertEquals(set("nbeer = 1",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 3"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 1), p("nsoda", 3)))));
		assertEquals(set("nbeer = 2",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 0"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 2), p("nsoda", 0)))));
		assertEquals(set("nbeer = 0",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 2"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 0), p("nsoda", 2)))));
		assertEquals(set("nbeer = 1",
						"do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
						"nsoda = 0"),
				ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
								map(p("nbeer", 1), p("nsoda", 0)))));

	}

	@SuppressWarnings({ "unchecked" })
	@Test
	public void test10() throws Exception {
		InputStream in = new StringBufferInputStream("x:=4;\n" + 
				"if :: x>3 -> do  	\n" + 
				"  :: x < 5 -> x:=x+3\n" + 
				"  :: x > 6 -> x:=x-4\n" + 
				"   	od\n" + 
				"fi\n" + 
				"");

		ProgramGraph<String, String> pg = fvmFacadeImpl.programGraphFromNanoPromela(in);

		assertEquals(set("", "do::x<5->x:=x+3::x>6->x:=x-4od", "if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi",
				"x:=4;if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi"), pg.getLocations());
		assertEquals(set("x:=4;if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi"), pg.getInitialLocations());
		assertEquals(set(), pg.getInitalizations());
		assertEquals(set(
				pgtransition("if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", "(x>3) && ((x<5))", "x:=x+3",
						"do::x<5->x:=x+3::x>6->x:=x-4od"),
				pgtransition("do::x<5->x:=x+3::x>6->x:=x-4od", "x>=5 && x<=6", "", ""),
				pgtransition("do::x<5->x:=x+3::x>6->x:=x-4od", "(x<5)", "x:=x+3", "do::x<5->x:=x+3::x>6->x:=x-4od"),
				pgtransition("x:=4;if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", "", "x:=4",
						"if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi"),
				pgtransition("do::x<5->x:=x+3::x>6->x:=x-4od", "(x>6)", "x:=x-4", "do::x<5->x:=x+3::x>6->x:=x-4od"),
				pgtransition("if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", "(x>3) && (!((x<5)||(x>6)))", "", ""),
				pgtransition("if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", "(x>3) && ((x>6))", "x:=x-4",
						"do::x<5->x:=x+3::x>6->x:=x-4od")),
				pg.getTransitions());

		Set<ActionDef> ad = set(new ParserBasedActDef());
		Set<ConditionDef> cd = set(new ParserBasedCondDef());

		TransitionSystem<Pair<String, Map<String, Object>>, String, String> ts = fvmFacadeImpl
				.transitionSystemFromProgramGraph(pg, ad, cd);

		assertEquals(set(p("x:=4;if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", map()), p("", map(p("x", 6))),
				p("do::x<5->x:=x+3::x>6->x:=x-4od", map(p("x", 3))),
				p("do::x<5->x:=x+3::x>6->x:=x-4od", map(p("x", 6))),
				p("do::x<5->x:=x+3::x>6->x:=x-4od", map(p("x", 7))),
				p("if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", map(p("x", 4)))), ts.getStates());
		assertEquals(set(p("x:=4;if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", map())), ts.getInitialStates());
		assertEquals(set("x:=x-4", "", "x:=x+3", "x:=4"), ts.getActions());
		assertEquals(
				set("do::x<5->x:=x+3::x>6->x:=x-4od", "", "x = 6", "x = 3", "x = 4", "x = 7",
						"if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", "x:=4;if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi"),
				ts.getAtomicPropositions());
		assertEquals(
				set(transition(p("x:=4;if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", map()), "x:=4",
						p("if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", map(p("x", 4)))),
						transition(p("do::x<5->x:=x+3::x>6->x:=x-4od", map(p("x", 3))), "x:=x+3",
								p("do::x<5->x:=x+3::x>6->x:=x-4od", map(p("x", 6)))),
						transition(p("if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", map(p("x", 4))), "x:=x+3",
								p("do::x<5->x:=x+3::x>6->x:=x-4od", map(p("x", 7)))),
						transition(p("do::x<5->x:=x+3::x>6->x:=x-4od", map(p("x", 7))), "x:=x-4",
								p("do::x<5->x:=x+3::x>6->x:=x-4od", map(p("x", 3)))),
						transition(p("do::x<5->x:=x+3::x>6->x:=x-4od", map(p("x", 6))), "", p("", map(p("x", 6))))),
				ts.getTransitions());
		assertEquals(set("x:=4;if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi"),
				ts.getLabel(p("x:=4;if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", map())));
		assertEquals(set("", "x = 6"), ts.getLabel(p("", map(p("x", 6)))));
		assertEquals(set("do::x<5->x:=x+3::x>6->x:=x-4od", "x = 3"),
				ts.getLabel(p("do::x<5->x:=x+3::x>6->x:=x-4od", map(p("x", 3)))));
		assertEquals(set("do::x<5->x:=x+3::x>6->x:=x-4od", "x = 6"),
				ts.getLabel(p("do::x<5->x:=x+3::x>6->x:=x-4od", map(p("x", 6)))));
		assertEquals(set("do::x<5->x:=x+3::x>6->x:=x-4od", "x = 7"),
				ts.getLabel(p("do::x<5->x:=x+3::x>6->x:=x-4od", map(p("x", 7)))));
		assertEquals(set("x = 4", "if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi"),
				ts.getLabel(p("if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", map(p("x", 4)))));

	}
	
	
	
	
	

}
