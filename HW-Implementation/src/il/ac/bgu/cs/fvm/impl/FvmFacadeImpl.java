package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.channelsystem.InterleavingActDef;
import il.ac.bgu.cs.fvm.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.OptionContext;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.fvm.programgraph.*;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;

import java.io.InputStream;
import java.util.*;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.*;
import static il.ac.bgu.cs.fvm.util.Pair.pair;
import static java.lang.Boolean.FALSE;
import static java.lang.Boolean.TRUE;
import static java.util.stream.Collectors.toList;
import static java.util.stream.Collectors.toMap;
import static java.util.stream.Collectors.toSet;

/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {


    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {
        return new TransitionSystemImpl();
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        Set<Transition<S, A>> transitions = ts.getTransitions();
        return transitions
                .stream()
                .map(transition -> new Transition(transition.getFrom(), transition.getAction(), null))
                .collect(toSet())
                .size() == transitions.size() && ts.getInitialStates().size() <= 1;
    }

    @Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        return getFromToLabelsStream(ts).collect(toSet()).size() ==
                getFromToLabelsStream(ts).collect(Collectors.toList()).size() &&
                ts.getInitialStates().size() <= 1;
    }

    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isInitialExecutionFragment(ts, e) && isStateTerminal(ts, e.last());
    }

    @Override
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (e.size() == 1) {
            S head = e.head();
            Validator.validateState(head, ts.getStates());
            return ts.getStates().stream().anyMatch(head::equals);
        } else {
            return ts.getTransitions().containsAll(alternatingSequence(e, ts));
        }
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isExecutionFragment(ts, e) && ts.getInitialStates().contains(e.head());
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isExecutionFragment(ts, e) && isStateTerminal(ts, e.last());
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        Validator.validateState(s, ts.getStates());
        return post(ts, s).size() == 0;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        return getStateFilterBy(ts, transition -> transition.getFrom().equals(s), Transition::getTo);
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> ret = set();
        c.stream()
                .map(state -> post(ts, state))
                .forEach(ret::addAll);
        return ret;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        return getStateFilterBy(ts, transition -> transition.getFrom().equals(s) && transition.getAction().equals(a), Transition::getTo);
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> ret = set();
        c.stream()
                .map(state -> post(ts, state, a))
                .forEach(ret::addAll);
        return ret;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        return getStateFilterBy(ts, transition -> transition.getTo().equals(s), Transition::getFrom);
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> ret = set();
        c.stream()
                .map(state -> pre(ts, state))
                .forEach(ret::addAll);
        return ret;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        return getStateFilterBy(ts, transition -> transition.getTo().equals(s) && transition.getAction().equals(a), Transition::getFrom);
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> ret = set();
        c.stream()
                .map(state -> pre(ts, state, a))
                .forEach(ret::addAll);
        return ret;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> states;
        Set<S> afterPost = ts.getInitialStates();
        do {
            states = new HashSet<>(afterPost);
            afterPost = post(ts, states);
            afterPost.addAll(states);
        } while (states.size() != afterPost.size());
        return afterPost;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        return interleaveWithHandShaking(ts1, ts2, set());
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        return interleaveWithHandShaking(ts1, ts2, handShakingActions);
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraphImpl();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> pg = createProgramGraph();
        pg1.getLocations().forEach(l1 -> pg2.getLocations().forEach(l2 -> pg.addLocation(p(l1, l2))));
        pg1.getInitialLocations().forEach(l1 -> pg2.getInitialLocations().forEach(l2 -> pg.addInitialLocation(p(l1, l2))));
        if (pg1.getInitalizations().isEmpty()) pg2.getInitalizations().forEach(pg::addInitalization);
        if (pg2.getInitalizations().isEmpty()) pg1.getInitalizations().forEach(pg::addInitalization);
        pg1.getInitalizations().forEach(i1 -> pg2.getInitalizations().forEach(i2 -> pg.addInitalization(Stream.concat(i1.stream(), i2.stream()).collect(toList()))));

        pg1.getTransitions().forEach(transition -> {
            List<Pair> leftSide =
                    pg.getLocations().stream().filter(state -> state.first.equals(transition.getFrom())).collect(toList());
            List<Pair> rightSide =
                    pg.getLocations().stream().filter(state -> state.first.equals(transition.getTo())).collect(toList());
            leftSide
                    .forEach(leftState ->
                            pg.addTransition(
                                    pgtransition(leftState, transition.getCondition(), transition.getAction(), rightSide.stream().filter(s -> s.second.equals(leftState.second)).findFirst().get())));
        });
        pg2.getTransitions().forEach(transition -> {
            List<Pair> leftSide =
                    pg.getLocations().stream().filter(state -> state.second.equals(transition.getFrom())).collect(toList());
            List<Pair> rightSide =
                    pg.getLocations().stream().filter(state -> state.second.equals(transition.getTo())).collect(toList());
            leftSide
                    .forEach(leftState ->
                            pg.addTransition(
                                    pgtransition(leftState, transition.getCondition(), transition.getAction(), rightSide.stream().filter(s -> s.first.equals(leftState.first)).findFirst().get())));
        });
        return pg;
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object>
                ts = createTransitionSystem();

        List<List<Pair<String, Boolean>>> rPairs = new ArrayList<>();
        List<List<Pair<String, Boolean>>> iPairs = new ArrayList<>();
        List<List<Pair<String, Boolean>>> finalRPairs = rPairs;
        List<List<Pair<String, Boolean>>> finalIPairs = iPairs;
        c.getRegisterNames().forEach(r -> {
            List<Pair<String, Boolean>> x = new ArrayList<>();
            x.add(pair(r, FALSE));
            x.add(pair(r, TRUE));
            finalRPairs.add(x);
        });
        c.getInputPortNames().forEach(r -> {
            List<Pair<String, Boolean>> x = new ArrayList<>();
            x.add(pair(r, FALSE));
            x.add(pair(r, TRUE));
            finalIPairs.add(x);
        });
        List<List<List<Pair<String, Boolean>>>> all = new ArrayList<>();
        rPairs = cartesianProduct(rPairs);
        iPairs = cartesianProduct(iPairs);
        all.add(rPairs);
        all.add(iPairs);
        all = cartesianProduct(all);
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> set = all
                .stream()
                .map(x ->
                        pair(
                                x.get(1).stream().collect(toMap(Pair::getFirst, Pair::getSecond)),
                                x.get(0).stream().collect(toMap(Pair::getFirst, Pair::getSecond)))).collect(toSet());
        set.forEach(ts::addStates);
        set.stream().filter(t -> t.second.values().stream().noneMatch(z -> z)).forEach(ts::addInitialState);
        set.stream().map(x -> x.first).forEach(ts::addAction);
        set(c.getInputPortNames(), c.getRegisterNames(), c.getOutputPortNames()).stream()
                .flatMap(Collection::stream)
                .forEach(ts::addAtomicProposition);

        ts.getStates().forEach(state -> {
            state.first.forEach((k, v) -> {
                if (v) ts.addToLabel(state, k);
            });
            state.second.forEach((k, v) -> {
                if (v) ts.addToLabel(state, k);
            });
            c.computeOutputs(state.first, state.second).forEach((k, v) -> {
                if (v) ts.addToLabel(state, k);
            });
            ts.getActions().forEach(action -> {
                Pair<Map<String, Boolean>, Map<String, Boolean>> to =
                        ts.getStates()
                                .stream()
                                .filter(x -> x.first.equals(action) && x.second.equals(c.updateRegisters(state.first, state.second)))
                                .findFirst()
                                .get();
                ts.addTransition(
                        new Transition<>(
                                state,
                                action,
                                to));
            });
        });

        return clearUnReachAble(ts);
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts = createTransitionSystem();

        programInitStates(pg, actionDefs, ts);

        ts.getInitialStates().forEach(state -> getPairConsumer(pg, ts, actionDefs, conditionDefs, state));
        ts.getStates().forEach(state -> {
            state.second.forEach((key, value) -> {
                String p = key + " = " + value;
                ts.addAtomicProposition(p);
                ts.addToLabel(state, p);
            });
            ts.addAtomicProposition(state.first.toString());
            ts.addToLabel(state, state.first.toString());
        });
        return ts;
    }

    private <L, A> void programInitStates(
            ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts) {
        pg.getInitialLocations().forEach(location -> {
            pg.getInitalizations().forEach(list -> {
                AtomicReference<Map<String, Object>> variables = new AtomicReference<>(map());
                list.forEach(cond -> variables.set(ActionDef.effect(actionDefs, variables.get(), cond)));
                ts.addState(p(location, variables.get()));
                ts.addInitialState(p(location, variables.get()));
            });
            if(pg.getInitalizations().isEmpty()){
                ts.addState(p(location, map()));
                ts.addInitialState(p(location, map()));
            }
        });
    }

    private <L, A> void getPairConsumer(
            ProgramGraph<L, A> pg,
            TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts,
            Set<ActionDef> actionDefs,
            Set<ConditionDef> conditionDefs,
            Pair<L, Map<String, Object>> state) {
        pg
                .getTransitions()
                .stream()
                .filter(t -> t.getFrom().equals(state.first) && ConditionDef.evaluate(conditionDefs, state.second, t.getCondition()))
                .forEach(transition -> {
                    Pair p = p(transition.getTo(), ActionDef.effect(actionDefs, state.second, transition.getAction()));
                    ts.addActions(transition.getAction());
                    if (!ts.getStates().contains(p)) {
                        ts.addState(p);
                        ts.addTransition(new Transition<>(state, transition.getAction(), p));
                        getPairConsumer(pg, ts, actionDefs, conditionDefs, p);
                    }
                    ts.addTransition(new Transition<>(state, transition.getAction(), p));
                });
    }


    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ret = createTransitionSystem();
        List<List<String>> initializations = new ArrayList<>();
        cartesianProduct(cs.getProgramGraphs()
                .stream()
                .map(ProgramGraph::getInitalizations)
                .map(ArrayList::new)
                .filter(l -> !l.isEmpty())
                .collect(toList())).forEach(initializations::addAll);
        List<List<L>> initialLocations = cartesianProduct(cs.getProgramGraphs()
                .stream()
                .map(ProgramGraph::getInitialLocations)
                .map(ArrayList::new).collect(toList()));
        Set<Map<String, Object>> initialsActions = generateInitialActions(initializations);
        Queue<Pair<List<L>, Map<String, Object>>> reach = new LinkedList();
        initialLocations.stream().flatMap(l -> initialsActions.stream().map(a -> new Pair<>(l, a))).collect(toSet()).forEach(state -> {
            ret.addState(state);
            ret.addInitialState(state);
            reach.add(state);
            addAtomicAndLabel(ret, state);
        });
        while (!reach.isEmpty()) {
            Pair<List<L>, Map<String, Object>> from = reach.poll();
            Map<Integer, List<PGTransition<L, A>>> simultaneous_actions = new HashMap<>();
            cs.getProgramGraphs().forEach(current_pg -> {
                current_pg.getTransitions()
                        .stream()
                        .filter(transition ->
                                transition.getFrom().equals(from.getFirst().get(cs.getProgramGraphs().indexOf(current_pg))) && ConditionDef.evaluate(conditionDefs(), from.second, transition.getCondition()))
                        .forEach(transition -> {
                        if (!new ParserBasedInterleavingActDef().isOneSidedAction(transition.getAction().toString())) {
                            List<L> new_location = new ArrayList<>(from.first);
                            new_location.set(cs.getProgramGraphs().indexOf(current_pg), transition.getTo());
                            Map<String, Object> newEval = ActionDef.effect(actionDefs(), from.second, transition.getAction());
                            if (newEval != null) {
                                if (!ret.getStates().contains(p(new_location, newEval))) {
                                    reach.add(p(new_location, newEval));
                                    ret.addState(p(new_location, newEval));
                                }
                                ret.addAction(transition.getAction());
                                ret.addTransition(new Transition<>(from, transition.getAction(), p(new_location, newEval)));
                                addAtomicAndLabel(ret, p(new_location, newEval));
                            }
                        } else {
                            ArrayList<PGTransition<L, A>> value = new ArrayList<>();
                            value.add(transition);
                            simultaneous_actions.merge(cs.getProgramGraphs().indexOf(current_pg), value, ((p, x) -> {
                                p.addAll(x);
                                return p;
                            }));
                        }
                });
                cartesianProduct(
                        simultaneous_actions.entrySet().stream().map(e -> e.getValue().stream().map(transition -> new Pair<>(e.getKey(), transition)).collect(toList())).collect(toList())
                ).forEach(complexTransition -> {
                    StringBuilder action = new StringBuilder();
                    List<L> newLocation = new ArrayList<>(from.first);
                    List<A> actions = new ArrayList<>();
                    complexTransition.forEach(pair -> {
                        if (action.length() != 0) {
                            action.append("|");
                        }
                        action.append(pair.second.getAction());
                        actions.add(pair.second.getAction());
                        newLocation.set(pair.first, pair.second.getTo());
                    });
                    if (!new ParserBasedInterleavingActDef().isOneSidedAction(actions.toString()) && complexTransition.size() > 1) {
                        Map<String, Object> newEval = ActionDef.effect(emptyQAction(), from.second, action.toString());
                        if (newEval != null) {
                            if (!ret.getStates().contains(p(newLocation, newEval))) {
                                reach.add(p(newLocation, newEval));
                                ret.addState(p(newLocation, newEval));
                            }
                            ret.addAction((A) action.toString());
                            ret.addTransition(new Transition<Pair<List<L>, Map<String, Object>>, A>(from, (A) action.toString(), p(newLocation, newEval)));
                            addAtomicAndLabel(ret, p(newLocation, newEval));
                        }
                    }
                });
            });
        }


        return ret;
    }

    private <L, A> void addAtomicAndLabel(TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ret, Pair<List<L>, Map<String, Object>> newState) {
        newState.first.stream().map(Object::toString).forEach(l -> {
            ret.addAtomicProposition(l);
            ret.addToLabel(newState, l);
        });
        newState.second.forEach((k, v) -> {
            ret.addAtomicProposition(k + " = " + v);
            ret.addToLabel(newState, k + " = " + v);
        });
    }

    private Set<Map<String, Object>> generateInitialActions(List<List<String>> initializations) {
        Set<Map<String, Object>> ret = new HashSet<>();
        for (List<String> initialization : initializations) {
            Map<String, Object> eval = new HashMap<>();
            for (String action : initialization) {
                eval = ActionDef.effect(actionDefs(), eval, action);
            }
            ret.add(eval);
        }
        if (ret.size() == 0) {
            ret.add(new HashMap<>());
        }
        return ret;
    }

    private Set<ConditionDef> conditionDefs() {
        ConditionDef conditionDef = new ParserBasedCondDef();
        Set<ConditionDef> conditionDefs = new HashSet<>();
        conditionDefs.add(conditionDef);
        return conditionDefs;
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        StmtContext root = NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);

        return pgFromRoot(root);
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        StmtContext root = NanoPromelaFileReader.parseNanoPromelaStream(inputStream);

        return pgFromRoot(root);
    }

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement verifyAnOmegaRegularProperty
    }

    @Override
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement LTL2NBA
    }

    @Override
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement GNBA2NBA
    }

    private <S, A> Set<S> getStateFilterBy(TransitionSystem<S, A, ?> ts,
                                           Predicate<Transition<S, A>> transitionPredicate,
                                           Function<Transition<S, A>, S> collect
    ) {
        return ts
                .getTransitions()
                .stream()
                .filter(transitionPredicate)
                .map(collect)
                .collect(toSet());
    }

    private <T> List<List<T>> cartesianProduct(List<List<T>> lists) {
        List<List<T>> resultLists = new ArrayList<>();
        if (lists.size() == 0) {
            resultLists.add(new ArrayList<>());
            return resultLists;
        } else {
            List<T> firstList = lists.get(0);
            List<List<T>> remainingLists = cartesianProduct(lists.subList(1, lists.size()));
            for (T condition : firstList) {
                for (List<T> remainingList : remainingLists) {
                    ArrayList<T> resultList = new ArrayList<>();
                    resultList.add(condition);
                    resultList.addAll(remainingList);
                    resultLists.add(resultList);
                }
            }
        }
        return resultLists;
    }

    private <S, A, P> Stream<FromToLabels> getFromToLabelsStream(TransitionSystem<S, A, P> ts) {
        return ts.getTransitions()
                .stream()
                .map(transition -> new FromToLabels(transition.getFrom(), ts.getLabel(transition.getTo())));
    }

    private <S, A, P> TransitionSystem<S, A, P> clearUnReachAble(TransitionSystem<S, A, P> ts) {
        TransitionSystem<S, A, P> ts2 = createTransitionSystem();
        reach(ts).forEach(ts2::addState);
        ts.getAtomicPropositions().forEach(ts2::addAtomicProposition);
        ts.getInitialStates().forEach(ts2::addInitialState);
        ts.getActions().forEach(ts2::addAction);
        ts2.getStates().forEach(state -> ts.getLabel(state).forEach(label -> ts2.addToLabel(state, label)));
        ts.getTransitions().stream().filter(transition -> ts2.getStates().contains(transition.getFrom()) && ts2.getStates().contains(transition.getTo())).forEach(ts2::addTransition);
        return ts2;
    }

    private <S1, S2, A, P> void interleaveStates(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, TransitionSystem<Pair<S1, S2>, A, P> ts, Set<A> handShakingActions) {
        ts1.getTransitions().stream().filter(t -> !handShakingActions.contains(t.getAction())).forEach(transition -> {
            List<Pair<S1, S2>> leftSide =
                    ts.getStates().stream().filter(state -> state.first.equals(transition.getFrom())).collect(toList());
            List<Pair<S1, S2>> rightSide =
                    ts.getStates().stream().filter(state -> state.first.equals(transition.getTo())).collect(toList());
            leftSide
                    .forEach(leftState ->
                            ts.addTransition(new Transition(leftState, transition.getAction(), rightSide.stream().filter(s -> s.second.equals(leftState.second)).findFirst().get())));
        });
        ts2.getTransitions().stream().filter(t -> !handShakingActions.contains(t.getAction())).forEach(transition -> {
            List<Pair<S1, S2>> leftSide =
                    ts.getStates().stream().filter(state -> state.second.equals(transition.getFrom())).collect(toList());
            List<Pair<S1, S2>> rightSide =
                    ts.getStates().stream().filter(state -> state.second.equals(transition.getTo())).collect(toList());
            leftSide
                    .forEach(leftState ->
                            ts.addTransition(new Transition(leftState, transition.getAction(), rightSide.stream().filter(s -> s.first.equals(leftState.first)).findFirst().get())));
        });
        handShakingActions.forEach(action -> {
            ts1.getTransitions().stream().filter(t1 -> action.equals(t1.getAction())).forEach(t1 -> {
                ts2.getTransitions().stream().filter(t2 -> action.equals(t2.getAction())).forEach(t2 -> {
                    ts.addTransition(new Transition<>(p(t1.getFrom(), t2.getFrom()), action, p(t1.getTo(), t2.getTo())));
                });
            });
        });
    }

    private <S, A, P> Set<Transition<S, A>> alternatingSequence(AlternatingSequence<S, A> e, TransitionSystem<S, A, P> ts) {
        Set<Transition<S, A>> alternatingSequence = set();
        while (e.size() != 1) {
            Transition transition = new Transition(e.head(), e.tail().head(), e.tail().tail().head());
            Validator.validateTransition(transition, ts.getActions(), ts.getStates());
            alternatingSequence.add(transition);
            e = e.tail().tail();
        }
        return alternatingSequence;
    }

    private <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleaveWithHandShaking(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        TransitionSystem<Pair<S1, S2>, A, P> ts = createTransitionSystem();

        ts1.getStates().forEach(ts1State -> ts2.getStates().forEach(ts2State -> ts.addState(p(ts1State, ts2State))));
        ts1.getInitialStates().forEach(ts1State -> ts2.getInitialStates().forEach(ts2State -> ts.addInitialState(p(ts1State, ts2State))));
        ts1.getActions().forEach(ts::addAction);
        ts2.getActions().forEach(ts::addAction);
        ts1.getAtomicPropositions().forEach(ts::addAtomicProposition);
        ts2.getAtomicPropositions().forEach(ts::addAtomicProposition);
        interleaveStates(ts1, ts2, ts, handShakingActions);
        ts.getStates().forEach(state -> {
            ts1.getLabel(state.first).forEach(label -> ts.addToLabel(state, label));
            ts2.getLabel(state.second).forEach(label -> ts.addToLabel(state, label));
        });
        return clearUnReachAble(ts);
    }

    private Set<ActionDef> actionDefs() {
        Set<ActionDef> actionDefs = new HashSet<>();
        InterleavingActDef actionDef = new ParserBasedInterleavingActDef();
        actionDefs.add(new ParserBasedActDef());
        actionDefs.add(actionDef);
        return actionDefs;
    }

    private Set<ActionDef> emptyQAction() {
        Set<ActionDef> complexActionDefSet = new HashSet<>();
        complexActionDefSet.add(new ParserBasedInterleavingActDef());
        return complexActionDefSet;
    }


    private ProgramGraph<String, String> pgFromRoot(StmtContext root)
    {

        ProgramGraph<String, String> pg = createProgramGraph();

        HashSet<String> loc = new HashSet<>();
        loc = sub(root, loc, pg);

        loc.forEach(pg::addLocation);
        pg.addInitialLocation(root.getText());
        pg.getLocations().forEach(pg::removeLocation);
        reachableOnly(pg).forEach(pg::addLocation);
        removeWasteTrans(pg);
        return pg;

    }

    private HashSet<String> sub(StmtContext root, HashSet<String> loc, ProgramGraph<String, String> pg)
    {

        if (root.assstmt() != null || root.chanreadstmt() != null || root.chanwritestmt() != null ||
                root.atomicstmt() != null || root.skipstmt() != null)
        {
            loc.add("");
            loc.add(root.getText());

            if (root.assstmt() != null || root.chanreadstmt() != null || root.chanwritestmt() != null)
            {
                PGTransition<String, String> t = new PGTransition<String, String>(root.getText(), "", root.getText(), "");
                pg.addTransition(t);
            } else if (root.atomicstmt() != null)
            {

                PGTransition<String, String> t = new PGTransition<String, String>(root.getText(), "", root.getText(), "");
                pg.addTransition(t);
            } else if (root.skipstmt() != null)
            {
                PGTransition<String, String> t = new PGTransition<String, String>(root.getText(), "", "skip", "");
                pg.addTransition(t);
            }
        } else if (root.ifstmt() != null)
        {
//			System.out.println(root.);
            loc.add(root.getText());

            List<OptionContext> options = root.ifstmt().option();

            for (OptionContext option : options)
            {
                HashSet<String> emptyLoc = new HashSet<String>();
                loc.addAll(sub(option.stmt(), emptyLoc, pg));
            }

            Set<PGTransition<String, String>> transitions = pg.getTransitions(); //trans so far

            for (OptionContext option : options)
            {
                String fromToCheck = option.stmt().getText();

                for (PGTransition<String, String> trans : transitions)
                {
                    if (trans.getFrom().equals(fromToCheck))
                    {
                        PGTransition<String, String> t;
                        if (!(trans.getCondition().equals("")))
                        {
                            t = new PGTransition<String, String>(root.getText(), "(" + option.boolexpr().getText() + ") && (" + trans.getCondition() + ")", trans.getAction(), trans.getTo());
                        } else
                        {
                            t = new PGTransition<String, String>(root.getText(), "(" + option.boolexpr().getText() + ")", trans.getAction(), trans.getTo());
                        }
                        pg.addTransition(t);
                    }
                }
            }

        } else if (root.dostmt() != null)
        {
            loc.add(root.getText());
            loc.add("");

            List<OptionContext> options = root.dostmt().option();
            for (OptionContext option : options)
            { //need to check if .stmt() is needed
                HashSet<String> emptyLoc = new HashSet<String>();
                HashSet<String> temp = sub(option.stmt(), emptyLoc, pg);
                temp.remove("");

                String loopStmtWithSpaces = addSpaces(root.getText());
                for (String str : temp)
                {
                    loc.add(str + ";" + root.getText());

                    String strWithSpaces = addSpaces(str);
                    String s = strWithSpaces + " ; " + loopStmtWithSpaces;
                    StmtContext secondRoot = NanoPromelaFileReader.pareseNanoPromelaString(s);

                    addAdditionalTransactions(secondRoot, pg);
                }
            }
            //first cond
            String allRules = "(";
            for (OptionContext option : options)
            {
                allRules = allRules + option.boolexpr().getText() + ")||(";
            }
            allRules = allRules.substring(0, allRules.length() - 3);
            PGTransition<String, String> t = new PGTransition<String, String>(root.getText(), "!(" + allRules + ")", "", "");
            pg.addTransition(t);

            //second cond

            for (OptionContext option : options)
            {
                String fromToCheck = option.stmt().getText();

                pg.getTransitions().stream().map(trans -> {
                    if (trans.getFrom().equals(fromToCheck) && trans.getTo().equals(""))
                    {
                        PGTransition<String, String> t2;
                        if (!(trans.getCondition().equals("")))
                        {
                            t2 = new PGTransition<String, String>(root.getText(), "(" + option.boolexpr().getText() + ") && (" + trans.getCondition() + ")", trans.getAction(), root.getText());
                        } else
                        {
                            t2 = new PGTransition<String, String>(root.getText(), "(" + option.boolexpr().getText() + ")", trans.getAction(), root.getText());
                        }
                        return t2;
                    } else if (trans.getFrom().equals(fromToCheck) && !(trans.getTo().equals("")))
                    {
                        PGTransition<String, String> t2;
                        if (!(trans.getCondition().equals("")))
                        {
                            t2 = new PGTransition<String, String>(root.getText(), "(" + option.boolexpr().getText() + ") && (" + trans.getCondition() + ")", trans.getAction(), trans.getTo() + ";" + root.getText());
                        } else
                        {
                            t2 = new PGTransition<String, String>(root.getText(), "(" + option.boolexpr().getText() + ")", trans.getAction(), trans.getTo() + ";" + root.getText());
                        }
                        return t2;
                    } else return null;
                }).filter(Objects::nonNull).forEach(pg::addTransition);
            }

        } else
        { // ;
            HashSet<String> emptyLoc1 = new HashSet<String>();
            loc.addAll(sub(root.stmt(1), emptyLoc1, pg));

            HashSet<String> emptyLoc0 = new HashSet<String>();
            HashSet<String> temp = sub(root.stmt(0), emptyLoc0, pg);
            temp.remove("");
            String secondStmtWithSpaces = addSpaces(root.stmt(1).getText());

            for (String str : temp)
            {

                loc.add(str + ";" + root.stmt(1).getText());

                String strWithSpaces = addSpaces(str);
                String s = strWithSpaces + " ; " + secondStmtWithSpaces;
                StmtContext secondRoot = NanoPromelaFileReader.pareseNanoPromelaString(s);

                addAdditionalTransactions(secondRoot, pg);

            }
            addAdditionalTransactions(root, pg);
        }

        return loc;
    }

    private HashSet<String> reachableOnly(ProgramGraph<String, String> pg)
    {
        Set<String> initialLocs = pg.getInitialLocations();

        HashSet<String> toReturn = new HashSet<String>();

        for (String loc : initialLocs)
        {
            toReturn.add(loc);
            toReturn.addAll(reachableOnly(pg, toReturn, loc));
        }

        return toReturn;
    }

    private Set<String> reachableOnly(ProgramGraph<String, String> pg, Set<String> toReturn, String loc)
    {
        Set<PGTransition<String, String>> transitions = pg.getTransitions();

        boolean flag = false;

        for (PGTransition<String, String> trans : transitions)
        {
            if (trans.getFrom().equals(loc))
            {
                flag = true;
                if (!toReturn.contains(trans.getTo()))
                {
                    toReturn.add(trans.getTo());
                    reachableOnly(pg, toReturn, trans.getTo());
                }
            }
        }
        if (!flag)
        {
            return toReturn;
        }
        return toReturn;
    }


    private String addSpaces(String str)
    {
        str = str.replace("nsoda", "sagivmapgavker");
        str = str.replace("fi", " fi");
        str = str.replace("if", "if ");
        str = str.replace("od", " od");
        str = str.replace("do", "do ");
        str = str.replace("::", ":: ");


        str = str.replace("->", " -> ");
        str = str.replace("skip", " skip");
        str = str.replace("atomic", "atomic ");
        str = str.replace("sagivmapgavker", "nsoda");
        return str;
    }


    private void addAdditionalTransactions(StmtContext secondRoot, ProgramGraph<String, String> pg) {
        pg.getTransitions().stream().map(trans -> {
            String toCheck = secondRoot.stmt(0).getText();
            if (trans.getFrom().equals(toCheck) && trans.getTo().equals(""))
            {
                        return new PGTransition<>(secondRoot.getText(), trans.getCondition(), trans.getAction(), secondRoot.stmt(1).getText());
            } else if (trans.getFrom().equals(toCheck) && !(trans.getTo().equals("")))
            {
                        return new PGTransition<>(secondRoot.getText(), trans.getCondition(), trans.getAction(), trans.getTo() + ";" + secondRoot.stmt(1).getText());
            } else return null;
        }).filter(Objects::nonNull).forEach(pg::addTransition);
    }

    private void removeWasteTrans(ProgramGraph<String, String> pg)
    {
        Set<String> locations = pg.getLocations();

        for (PGTransition<String, String> trans : pg.getTransitions())
        {
            if (!locations.contains(trans.getFrom()) || !locations.contains(trans.getTo())) {
                pg.removeTransition(trans);
            }
        }

    }
}
