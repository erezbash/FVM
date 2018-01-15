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
        ProgramGraph<String, String> pg1 = createPetersonPG(1);
        System.out.println("create ProgramGraph for peterson algorithm - pg2");
        ProgramGraph<String, String> pg2 = createPetersonPG(2);
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
        Set atomicToRemove = new HashSet();
        for (Object l : ts.getAtomicPropositions())
            if (labels(l))
                atomicToRemove.add(l);

        for (Object ap : atomicToRemove)
            ts.removeAtomicProposition(ap);
    }

    private void removeLabels(TransitionSystem ts) {
        for (Object s : ts.getStates()) {
            Set labelsToRemove = new HashSet();
            for (Object l : ts.getLabel(s))
                if (labels(l))
                    labelsToRemove.add(l);

            for (Object label : labelsToRemove)
                ts.removeLabel(s, label);
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
        seq("crit1", "crit2", "crit1_enabled", "wait1", "wait2").stream().forEach(s -> ts.addAtomicPropositions(s));

        ts.getStates().stream()
                .filter(s -> s.getFirst().getFirst().equals("crit1"))
                .forEach(s -> ts.addToLabel(s, "crit1"));
        ts.getStates().stream()
                .filter(s -> s.getFirst().getSecond().equals("crit2"))
                .forEach(s -> ts.addToLabel(s, "crit2"));

        Predicate<Pair<Pair<String, String>, ?>> equalToCrot1 = ss -> ss.getFirst().getFirst().equals("crit1");
        Predicate<Pair<Pair<String, String>, ?>> equalToWait1 = ss -> ss.getFirst().getFirst().equals("wait1");
        Predicate<Pair<Pair<String, String>, ?>> equalToWait2 = ss -> ss.getFirst().getFirst().equals("wait2");

        ts.getStates().stream()
                .filter(s -> fvmFacadeImpl.post(ts, s).stream().anyMatch(equalToCrot1))
                .forEach(s -> ts.addToLabel(s, "crit1_enabled"));
        ts.getStates().stream()
                .filter(equalToWait1)
                .forEach(s -> ts.addToLabel(s, "wait1"));
        ts.getStates().stream()
                .filter(equalToWait2)
                .forEach(s -> ts.addToLabel(s, "wait2"));
    }

    private ProgramGraph<String, String> createPetersonPG(int id) {
        ProgramGraph<String, String> pg = fvmFacadeImpl.createProgramGraph();

        String noncritState = "noncrit" + id;
        pg.addLocation(noncritState);
        pg.addInitialLocation(noncritState);

        String waitState = "wait" + id;
        pg.addLocation(waitState);

        String critState = "crit" + id;
        pg.addLocation(critState);

        pg.addTransition(
                new PGTransition<>(
                        critState, "true", "b" + id + ":=0", noncritState));
        pg.addTransition(
                new PGTransition<>(
                        noncritState, "true", "atomic{b" + id + ":=1;x:=" + (id == 1 ? 2 : 1) + "}", waitState));
        pg.addTransition(
                new PGTransition<>(
                        waitState, "x==" + id + " || b" + (id == 1 ? 2 : 1) + "==0", "", critState));

        pg.addInitalization(asList("b" + id + ":=0", "x:=2"));
        pg.addInitalization(asList("b" + id + ":=0", "x:=1"));

        return pg;
    }

    public static void main(String[] args) {
        MutualExclusionDemo petersonAlgoDemo = new MutualExclusionDemo();
        petersonAlgoDemo.startDemo();
    }
}
