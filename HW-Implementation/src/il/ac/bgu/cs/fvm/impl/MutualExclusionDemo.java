package il.ac.bgu.cs.fvm.impl;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.seq;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static java.util.Arrays.asList;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.util.Util;
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationResult;

public class MutualExclusionDemo {
    private FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

    public void startDemo() {
        System.out.println("test Properties for peterson algorithm");
        System.out.println("create ProgramGraph for peterson algorithm - pg1");
        ProgramGraph<String, String> pg1 = buildPeterson(1);
        System.out.println("create ProgramGraph for peterson algorithm - pg2");
        ProgramGraph<String, String> pg2 = buildPeterson(2);
        System.out.println("create ProgramGraph interleavePG from interleave pg1 and pg2");
        ProgramGraph<Pair<String, String>, String> interleavePG = fvmFacadeImpl.interleave(pg1, pg2);
        Set<ActionDef> ad = set(new ParserBasedActDef());
        Set<ConditionDef> cd = set(new ParserBasedCondDef());
        System.out.println("create TransitionSystem from interleavePG, ParserBasedActDef and ParserBasedCondDef");
        TransitionSystem ts = fvmFacadeImpl.transitionSystemFromProgramGraph(interleavePG, ad, cd);
        System.out.println("add labels to TransitionSystem");
        addLabelsToTS(ts);
        System.out.println("remove labels from TransitionSystem");
        removeLabels(ts);
        System.out.println("remove atomicProposition from TransitionSystem");
        removeAtomic(ts);
        System.out.println("verify Mutex Property:");
        verifyProperty(ts, createMutexAutomaton(ts), "Mutex");
        System.out.println("verify Starvation Property:");
        verifyProperty(ts, createStarvationAutomaton(ts), "Starvation");
        System.out.println("Summery:");
        System.out.println("peterson algorithm verify Mutex and Starvation this is way we don't need fairness assumption");

    }

    private void verifyProperty(TransitionSystem ts, Automaton aut, String property){
        System.out.println("verify An Omega Regular Property for ts and " + property + " property");
        VerificationResult vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, aut);
        if (vr instanceof VerificationFailed) {
            System.out.println(property + " Verification failed. Error Trace: " + ((VerificationFailed) vr).toString());
        } else {
            System.out.println(property + " Verification passed");
        }
    }

    private void removeAtomic(TransitionSystem ts) {
        Set lst = new HashSet();
        for (Object label : ts.getAtomicPropositions()) {
            if (labels(label)) {
                lst.add(label);
            }
        }
        for (Object atomicProposition : lst) {
            ts.removeAtomicProposition(atomicProposition);
        }
    }

    private void removeLabels(TransitionSystem ts) {
        for (Object state : ts.getStates()) {
            Set lst = new HashSet();
            for (Object label : ts.getLabel(state)) {
                if (labels(label)) {
                    lst.add(label);
                }
            }
            for (Object label : lst) {
                ts.removeLabel(state, label);
            }
        }
    }

    private boolean labels(Object label) {
        boolean ans =
                !(label.equals("crit1 = 0"))
                && !(label.equals("crit1_enabled"))
                && !(label.equals("crit2"))
                && !(label.equals("crit1"))
                && !(label.equals("crit2_enabled"))
                && !(label.equals("b1 = 1"))
                && !(label.equals("b1 = 0"))
                && !(label.equals("b2 = 1"))
                && !(label.equals("b2 = 0"))
                && !(label.equals("x = 1"))
                && !(label.equals("x = 2"));
        return ans;
    }

    private Automaton createMutexAutomaton(
            TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
        System.out.println("create Mutex Automaton");
        Automaton mutexAutomaton = new Automaton<>();
        Set<Set<String>> atomicProp = (Util.powerSet(ts.getAtomicPropositions()));
        Predicate<Set<String>> mutexCheck = (a -> a.contains("crit1") && a.contains("crit2"));

        atomicProp.stream().filter(mutexCheck.negate()).forEach(l -> mutexAutomaton.addTransition("q0", l, "q0"));
        atomicProp.stream().filter(mutexCheck).forEach(l -> mutexAutomaton.addTransition("q0", l, "q1"));
        atomicProp.stream().forEach(l -> mutexAutomaton.addTransition("q1", l, "q1"));

        mutexAutomaton.setInitial("q0");
        mutexAutomaton.setAccepting("q1");
        return mutexAutomaton;
    }

    private Automaton createStarvationAutomaton(
            TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
        System.out.println("create Starvation Automaton");
        Automaton starvationAutomaton = new Automaton<>();
        Set<Set<String>> atomicProp = Util.powerSet(ts.getAtomicPropositions());

        atomicProp.stream().forEach(s -> starvationAutomaton.addTransition("q0", s, "q0"));
        atomicProp.stream().filter(s -> s.contains("wait1")).forEach(s -> starvationAutomaton.addTransition("q0", s, "q1"));
        atomicProp.stream().filter(s -> !s.contains("wait1") && !s.contains("crit1"))
                .forEach(s -> starvationAutomaton.addTransition("q1", s, "q1"));

        Predicate<Set<String>> check = (s -> !s.contains("crit1") && !s.contains("crit1_enabled"));
        atomicProp.stream().filter(check)
                .forEach(s -> starvationAutomaton.addTransition("q1", s, "q2"));
        atomicProp.stream().filter(check)
                .forEach(s -> starvationAutomaton.addTransition("q2", s, "q2"));

        starvationAutomaton.setInitial("q0");
        starvationAutomaton.setAccepting("q2");
        return starvationAutomaton;
    }

    // add labels
    private void addLabelsToTS(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
        seq("wait1", "wait2", "crit1", "crit2", "crit1_enabled").stream().forEach(s -> ts.addAtomicPropositions(s));


        ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("crit2"))
                .forEach(s -> ts.addToLabel(s, "crit2"));
        ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("crit1"))
                .forEach(s -> ts.addToLabel(s, "crit1"));
        Predicate<Pair<Pair<String, String>, ?>> _crit1 = ss -> ss.getFirst().getFirst().equals("crit1");
        Predicate<Pair<Pair<String, String>, ?>> _crit2 = ss -> ss.getFirst().getFirst().equals("crit2");
        ts.getStates().stream().filter(s -> fvmFacadeImpl.post(ts, s).stream().anyMatch(_crit1))
                .forEach(s -> ts.addToLabel(s, "crit1_enabled"));
        ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("wait1"))
                .forEach(s -> ts.addToLabel(s, "wait1"));

        ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("wait2"))
                .forEach(s -> ts.addToLabel(s, "wait2"));


    }

    private ProgramGraph<String, String> buildPeterson(int id) {
        ProgramGraph<String, String> pg = FvmFacade.createInstance().createProgramGraph();

        String noncrit = "noncrit" + id;
        String wait = "wait" + id;
        String crit = "crit" + id;

        pg.addLocation(noncrit);
        pg.addLocation(wait);
        pg.addLocation(crit);

        pg.addInitialLocation(noncrit);

        pg.addTransition(
                new PGTransition<>(noncrit, "true", "atomic{b" + id + ":=1;x:=" + (id == 1 ? 2 : 1) + "}", wait));

        pg.addTransition(new PGTransition<>(wait, "x==" + id + " || b" + (id == 1 ? 2 : 1) + "==0", "", crit));
        pg.addTransition(new PGTransition<>(crit, "true", "b" + id + ":=0", noncrit));

        pg.addInitalization(asList("b" + id + ":=0", "x:=1"));
        pg.addInitalization(asList("b" + id + ":=0", "x:=2"));

        return pg;

    }

    public static void main(String[] args) {
        MutualExclusionDemo petersonAlgoDemo = new MutualExclusionDemo();
        petersonAlgoDemo.startDemo();
    }
}
