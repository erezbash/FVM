package il.ac.bgu.cs.fvm.transitionsystem;

import il.ac.bgu.cs.fvm.FvmFacade;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.transition;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.util.codeprinter.TsPrinter;
import static org.junit.Assert.assertEquals;

/**
 *
 * @author michael
 */
public class CodePrinterTests {

    enum Action {
        A, B, C, D
    }

    public static void main(String[] args) {
        t3();
    }

    public static void t1() {
        
        TsPrinter prt = new TsPrinter();

        TransitionSystem<String, Integer, String> ts = FvmFacade.createInstance().createTransitionSystem();
        ts.addStates("a", "b", "c", "d");
        ts.addActions(1, 2, 3, 4);
        ts.addAtomicPropositions("x", "y", "z");
        ts.addTransitionFrom("a").action(2).to("d");
        ts.addTransitionFrom("b").action(1).to("c");
        ts.addTransitionFrom("c").action(3).to("b");
        ts.addTransitionFrom("d").action(4).to("a");
        ts.addToLabel("a", "x");
        ts.addToLabel("b", "y");
        ts.addToLabel("c", "z");
        System.out.println(prt.print(ts));
    }

    @SuppressWarnings("unchecked")
	public static void t2() {
        TransitionSystem<Pair<String, Integer>, String, Boolean> ts = FvmFacade.createInstance().createTransitionSystem();

        ts.addState(p("1", 10));
        ts.addState(p("2", 20));
        ts.addState(p("3", 30));
        ts.addState(p("4", 40));
        ts.addActions("a", "b", "c", "d");
        ts.addAtomicProposition(Boolean.TRUE);
        ts.addAtomicProposition(Boolean.FALSE);
        ts.addTransitionFrom(p("1", 10)).action("b").to(p("3", 30));
        ts.addTransitionFrom(p("2", 20)).action("c").to(p("4", 40));
        ts.addTransitionFrom(p("3", 30)).action("d").to(p("1", 10));
        ts.addTransitionFrom(p("4", 40)).action("a").to(p("4", 40));
        ts.addToLabel(p("1", 10), Boolean.TRUE);
        ts.addToLabel(p("1", 10), Boolean.FALSE);
        ts.addToLabel(p("2", 20), Boolean.TRUE);
        ts.addToLabel(p("3", 30), Boolean.TRUE);

        System.out.println(new TsPrinter().print(ts));
    }

    @SuppressWarnings("unchecked")
	public static void t3() {
        TransitionSystem<Pair<String, Integer>, Action, Boolean> ts = FvmFacade.createInstance().createTransitionSystem();

        ts.addState(p("1", 10));
        ts.addState(p("2", 20));
        ts.addState(p("3", 30));
        ts.addState(p("4", 40));
        ts.addInitialState(p("4", 40));
        ts.addAllActions(Action.values());
        ts.addAtomicProposition(Boolean.TRUE);
        ts.addAtomicProposition(Boolean.FALSE);
        ts.addTransitionFrom(p("1", 10)).action(Action.A).to(p("3", 30));
        ts.addTransitionFrom(p("2", 20)).action(Action.B).to(p("4", 40));
        ts.addTransitionFrom(p("3", 30)).action(Action.C).to(p("1", 10));
        ts.addTransitionFrom(p("4", 40)).action(Action.D).to(p("4", 40));
        ts.addTransitionFrom(p("4", 40)).action(Action.A).to(p("4", 40));
        ts.addToLabel(p("1", 10), Boolean.TRUE);
        ts.addToLabel(p("1", 10), Boolean.FALSE);
        ts.addToLabel(p("2", 20), Boolean.TRUE);
        ts.addToLabel(p("3", 30), Boolean.TRUE);

        final TsPrinter tsPrinter = new TsPrinter();
        
        tsPrinter.setClassPrinter(Action.class, (obj, tsp, out) -> {
            out.print("Action.valueOf(\"" + obj.name() + "\")");
        });


        System.out.println(tsPrinter.getAssertions(ts));

        assertEquals(set(p("1", 10), p("4", 40), p("3", 30), p("2", 20)), ts.getStates());
        assertEquals(set(p("4", 40)), ts.getInitialStates());
        assertEquals(set(Action.valueOf("B"), Action.valueOf("D"), Action.valueOf("C"), Action.valueOf("A")), ts.getActions());
        assertEquals(set(false, true), ts.getAtomicPropositions());
        assertEquals(set(transition(p("4", 40), Action.valueOf("A"), p("4", 40)), transition(p("1", 10), Action.valueOf("A"), p("3", 30)), transition(p("4", 40), Action.valueOf("D"), p("4", 40)), transition(p("3", 30), Action.valueOf("C"), p("1", 10)), transition(p("2", 20), Action.valueOf("B"), p("4", 40))
        ), ts.getTransitions());
        assertEquals(set(false, true), ts.getLabel(p("1", 10)));
        assertEquals(set(), ts.getLabel(p("4", 40)));
        assertEquals(set(true), ts.getLabel(p("3", 30)));
        assertEquals(set(true), ts.getLabel(p("2", 20)));
    }

    @SuppressWarnings({ "rawtypes", "unchecked" })
	public void testCode() {
        TransitionSystem ts = FvmFacade.createInstance().createTransitionSystem();
        ts.addStates(p("1", 10), p("4", 40), p("3", 30), p("2", 20));
        ts.addActions(Action.valueOf("B"), Action.valueOf("D"), Action.valueOf("C"), Action.valueOf("A"));
        ts.addAtomicPropositions(false, true);
        ts.addTransitionFrom(p("4", 40)).action(Action.valueOf("A")).to(p("4", 40));
        ts.addTransitionFrom(p("1", 10)).action(Action.valueOf("A")).to(p("3", 30));
        ts.addTransitionFrom(p("4", 40)).action(Action.valueOf("D")).to(p("4", 40));
        ts.addTransitionFrom(p("3", 30)).action(Action.valueOf("C")).to(p("1", 10));
        ts.addTransitionFrom(p("2", 20)).action(Action.valueOf("B")).to(p("4", 40));
        ts.addToLabel(p("1", 10), set(false, true));
        ts.addToLabel(p("3", 30), set(true));
        ts.addToLabel(p("2", 20), set(true));
    }

}
