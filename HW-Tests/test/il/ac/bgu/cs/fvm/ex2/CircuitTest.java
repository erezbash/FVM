package il.ac.bgu.cs.fvm.ex2;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.map;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.singeltonMap;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.transition;
import static il.ac.bgu.cs.fvm.util.Pair.pair;
import static java.lang.Boolean.FALSE;
import static java.lang.Boolean.TRUE;
import static junit.framework.TestCase.assertEquals;

import java.util.Map;
import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.examples.ExampleCircuit;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.GraphvizPainter;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.util.codeprinter.TsPrinter;

public class CircuitTest {

    FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

    @SuppressWarnings("unchecked")
	@Test
    public void test1() throws Exception {
        Circuit c = new ExampleCircuit();

        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ts
                = fvmFacadeImpl.transitionSystemFromCircuit(c);
        final Pair<Map<String, Boolean>, Map<String, Boolean>> s00 = p(singeltonMap("x", FALSE), singeltonMap("r", FALSE));
        final Pair<Map<String, Boolean>, Map<String, Boolean>> s10 = p(singeltonMap("x", TRUE), singeltonMap("r", FALSE));
        final Pair<Map<String, Boolean>, Map<String, Boolean>> s01 = p(singeltonMap("x", FALSE), singeltonMap("r", TRUE));
        final Pair<Map<String, Boolean>, Map<String, Boolean>> s11 = p(singeltonMap("x", TRUE), singeltonMap("r", TRUE));

        assertEquals(set(s00, s10, s01, s11), ts.getStates());

        assertEquals(set(s00, s10), ts.getInitialStates());

        assertEquals(set(singeltonMap("x", TRUE), singeltonMap("x", FALSE)), ts.getActions());

        assertEquals(set("r", "x", "y"), ts.getAtomicPropositions());

        assertEquals(set("r", "x", "y"), ts.getLabel(s11));

        assertEquals(set("r"), ts.getLabel(s01));

        assertEquals(set("x"), ts.getLabel(s10));

        assertEquals(set("y"), ts.getLabel(s00));

        assertEquals(set(transition(s00, singeltonMap("x", false), s00),
                transition(s00, singeltonMap("x", true), s10),
                transition(s10, singeltonMap("x", false), s01),
                transition(s10, singeltonMap("x", true), s11),
                transition(s01, singeltonMap("x", false), s01),
                transition(s01, singeltonMap("x", true), s11),
                transition(s11, singeltonMap("x", false), s01),
                transition(s11, singeltonMap("x", true), s11)
        ),
                ts.getTransitions());

    }

    @SuppressWarnings("unchecked")
    @Test
    public void test2() throws Exception {
        Circuit c;

//           +----+
//  x -------|    |
//   1       |    |
//           | OR |---+------------- y
//  x ---+---|    |   |               1
//   2   |   +----+   |
//       |            |
//       |          +-+--+
//       |          | r  |  +----+
//       |          |  1 |--|    |
//       |          +----+  |    |
//       |  +---+           |AND |-- y
//       +--+ r +-----------|    |    2
//          |  2|           +----+
//          +---+
        c = new Circuit() {

            @Override
            public Map<String, Boolean> updateRegisters(Map<String, Boolean> inputs, Map<String, Boolean> registers) {
                return map(
                        pair("r1", (inputs.get("x1") || inputs.get("x2"))),
                        pair("r2", inputs.get("x2"))
                );
            }

            @Override
            public Map<String, Boolean> computeOutputs(Map<String, Boolean> inputs, Map<String, Boolean> registers) {
                return map(p("y1", (inputs.get("x1") || inputs.get("x2"))),
                        p("y2", (registers.get("r1") && registers.get("r2"))));
            }

            @Override
            public Set<String> getInputPortNames() {
                return set("x1", "x2");
            }

            @Override
            public Set<String> getRegisterNames() {
                return set("r1", "r2");
            }

            @Override
            public Set<String> getOutputPortNames() {
                return set("y1", "y2");
            }
        };

        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ts;
        ts = fvmFacadeImpl.transitionSystemFromCircuit(c);

        System.out.println("-------");
        System.out.println("Java code to generate the system");
        System.out.println(new TsPrinter().print(ts));
        System.out.println("-------");
        System.out.println("Graphviz code of the transition system");
        System.out.println("-------");
        System.out.println(GraphvizPainter.circuitPainter().makeDotCode(ts));

        assertEquals(set("r2", "y1", "x1", "y2", "x2", "r1"), ts.getAtomicPropositions());

        assertEquals(
                set(p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", true))), p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", false))),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", false))), p(map(p("x1", false), p("x2", false)), map(p("r2", true), p("r1", true))),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", true), p("r1", true))), p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", true))),
                        p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", false))), p(map(p("x1", true), p("x2", false)), map(p("r2", true), p("r1", true))),
                        p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", true))), p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", true))),
                        p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", false))), p(map(p("x1", false), p("x2", true)), map(p("r2", true), p("r1", true)))),
                ts.getStates());

        assertEquals(
                set(p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", false))),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", false))),
                        p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", false))),
                        p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", false)))),
                ts.getInitialStates());

        assertEquals(set(map(p("x1", false), p("x2", true)), map(p("x1", true), p("x2", false)),
                map(p("x1", false), p("x2", false)), map(p("x1", true), p("x2", true))),
                ts.getActions());

        assertEquals(set(
                transition(p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", false))),
                        map(p("x1", false), p("x2", true)),
                        p(map(p("x1", false), p("x2", true)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", false))),
                        map(p("x1", true), p("x2", false)),
                        p(map(p("x1", true), p("x2", false)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", false))),
                        map(p("x1", false), p("x2", false)),
                        p(map(p("x1", false), p("x2", false)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", false))),
                        map(p("x1", true), p("x2", true)),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", false), p("x2", true)), map(p("r2", true), p("r1", true))),
                        map(p("x1", false), p("x2", true)),
                        p(map(p("x1", false), p("x2", true)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", false), p("x2", true)), map(p("r2", true), p("r1", true))),
                        map(p("x1", true), p("x2", false)),
                        p(map(p("x1", true), p("x2", false)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", false), p("x2", true)), map(p("r2", true), p("r1", true))),
                        map(p("x1", false), p("x2", false)),
                        p(map(p("x1", false), p("x2", false)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", false), p("x2", true)), map(p("r2", true), p("r1", true))),
                        map(p("x1", true), p("x2", true)),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", true))),
                        map(p("x1", false), p("x2", true)),
                        p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", true))),
                        map(p("x1", true), p("x2", false)),
                        p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", true))),
                        map(p("x1", false), p("x2", false)),
                        p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", true))),
                        map(p("x1", true), p("x2", true)),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", true))),
                        map(p("x1", false), p("x2", true)),
                        p(map(p("x1", false), p("x2", true)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", true))),
                        map(p("x1", true), p("x2", false)),
                        p(map(p("x1", true), p("x2", false)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", true))),
                        map(p("x1", false), p("x2", false)),
                        p(map(p("x1", false), p("x2", false)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", true))),
                        map(p("x1", true), p("x2", true)),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", false))),
                        map(p("x1", false), p("x2", true)),
                        p(map(p("x1", false), p("x2", true)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", false))),
                        map(p("x1", true), p("x2", false)),
                        p(map(p("x1", true), p("x2", false)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", false))),
                        map(p("x1", false), p("x2", false)),
                        p(map(p("x1", false), p("x2", false)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", false))),
                        map(p("x1", false), p("x2", true)),
                        p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", false)), map(p("r2", true), p("r1", true))),
                        map(p("x1", false), p("x2", true)),
                        p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", false))),
                        map(p("x1", true), p("x2", false)),
                        p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", true)), map(p("r2", true), p("r1", true))),
                        map(p("x1", false), p("x2", false)),
                        p(map(p("x1", false), p("x2", false)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", false)), map(p("r2", true), p("r1", true))),
                        map(p("x1", true), p("x2", false)),
                        p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", false))),
                        map(p("x1", false), p("x2", false)),
                        p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", false)), map(p("r2", true), p("r1", true))),
                        map(p("x1", false), p("x2", false)),
                        p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", false))),
                        map(p("x1", true), p("x2", true)),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", false)), map(p("r2", true), p("r1", true))),
                        map(p("x1", true), p("x2", true)),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", true)), map(p("r2", true), p("r1", true))),
                        map(p("x1", false), p("x2", true)),
                        p(map(p("x1", false), p("x2", true)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", true)), map(p("r2", true), p("r1", true))),
                        map(p("x1", true), p("x2", false)),
                        p(map(p("x1", true), p("x2", false)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", false))),
                        map(p("x1", true), p("x2", true)),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", true), p("x2", true)), map(p("r2", true), p("r1", true))),
                        map(p("x1", true), p("x2", true)),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", true))),
                        map(p("x1", false), p("x2", true)),
                        p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", false)))),
                transition(p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", true))),
                        map(p("x1", true), p("x2", false)),
                        p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", false)))),
                transition(p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", true))),
                        map(p("x1", false), p("x2", false)),
                        p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", false)))),
                transition(p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", true))),
                        map(p("x1", true), p("x2", true)),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", false)))),
                transition(p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", false))),
                        map(p("x1", true), p("x2", false)),
                        p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", false)))),
                transition(p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", false))),
                        map(p("x1", false), p("x2", true)),
                        p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", false)))),
                transition(p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", false))),
                        map(p("x1", false), p("x2", false)),
                        p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", false)))),
                transition(p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", false))),
                        map(p("x1", true), p("x2", true)),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", false)))),
                transition(p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", true))),
                        map(p("x1", true), p("x2", true)),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", true))),
                        map(p("x1", true), p("x2", false)),
                        p(map(p("x1", true), p("x2", false)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", false), p("x2", false)), map(p("r2", true), p("r1", true))),
                        map(p("x1", false), p("x2", true)),
                        p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", false)))),
                transition(p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", true))),
                        map(p("x1", false), p("x2", false)),
                        p(map(p("x1", false), p("x2", false)), map(p("r2", true), p("r1", true)))),
                transition(p(map(p("x1", false), p("x2", false)), map(p("r2", true), p("r1", true))),
                        map(p("x1", true), p("x2", false)),
                        p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", false)))),
                transition(p(map(p("x1", false), p("x2", false)), map(p("r2", true), p("r1", true))),
                        map(p("x1", false), p("x2", false)),
                        p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", false)))),
                transition(p(map(p("x1", false), p("x2", false)), map(p("r2", true), p("r1", true))),
                        map(p("x1", true), p("x2", true)),
                        p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", false)))),
                transition(p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", true))),
                        map(p("x1", false), p("x2", true)),
                        p(map(p("x1", false), p("x2", true)), map(p("r2", true), p("r1", true))))),
                ts.getTransitions());

        assertEquals(set("y1", "x1", "r1"),
                ts.getLabel(p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", true)))));
        assertEquals(set("y1", "x1", "x2"),
                ts.getLabel(p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", false)))));
        assertEquals(set("r2", "y2", "r1"),
                ts.getLabel(p(map(p("x1", false), p("x2", false)), map(p("r2", true), p("r1", true)))));
        assertEquals(set("r2", "y1", "x1", "y2", "x2", "r1"),
                ts.getLabel(p(map(p("x1", true), p("x2", true)), map(p("r2", true), p("r1", true)))));
        assertEquals(set("y1", "x2", "r1"),
                ts.getLabel(p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", true)))));
        assertEquals(set("y1", "x1"),
                ts.getLabel(p(map(p("x1", true), p("x2", false)), map(p("r2", false), p("r1", false)))));
        assertEquals(set("r2", "y1", "x1", "y2", "r1"),
                ts.getLabel(p(map(p("x1", true), p("x2", false)), map(p("r2", true), p("r1", true)))));
        assertEquals(set("r1"),
                ts.getLabel(p(map(p("x1", false), p("x2", false)), map(p("r2", false), p("r1", true)))));
        assertEquals(set("y1", "x1", "x2", "r1"),
                ts.getLabel(p(map(p("x1", true), p("x2", true)), map(p("r2", false), p("r1", true)))));
        assertEquals(set("y1", "x2"),
                ts.getLabel(p(map(p("x1", false), p("x2", true)), map(p("r2", false), p("r1", false)))));
        assertEquals(set("r2", "y1", "y2", "x2", "r1"),
                ts.getLabel(p(map(p("x1", false), p("x2", true)), map(p("r2", true), p("r1", true)))));

    }

}
