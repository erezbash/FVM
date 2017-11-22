package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static il.ac.bgu.cs.fvm.exceptions.TransitionSystemPart.ATOMIC_PROPOSITIONS;
import static il.ac.bgu.cs.fvm.exceptions.TransitionSystemPart.INITIAL_STATES;
import static il.ac.bgu.cs.fvm.exceptions.TransitionSystemPart.TRANSITIONS;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;

public class TransitionSystemImpl<STATE, ACTION, ATOMIC_PROPOSITION> implements TransitionSystem<STATE, ACTION, ATOMIC_PROPOSITION> {

    private String name;
    private Set<STATE> states = set();
    private Set<ACTION> actions = set();
    private Set<STATE> initialStates = set();
    private Set<ATOMIC_PROPOSITION> atomicPropositions = set();
    private Set<Transition<STATE, ACTION>> transitions = set();
    private Map<STATE, Set<ATOMIC_PROPOSITION>> propositionHashMap = new HashMap<>();

    @Override
    public String getName() {
        return name;
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void addAction(ACTION action) {
        actions.add(action);
    }

    @Override
    public void addInitialState(STATE state) throws FVMException {
        Validator.validateState(state, states, new InvalidInitialStateException(""));
        initialStates.add(state);
    }

    @Override
    public void addState(STATE state) {
        states.add(state);
    }

    @Override
    public void addTransition(Transition<STATE, ACTION> t) throws FVMException {
        Validator.validateTransition(t, actions, states, new InvalidTransitionException(t));
        transitions.add(t);
    }

    @Override
    public Set<ACTION> getActions() {
        return new HashSet<>(actions);
    }

    @Override
    public void addAtomicProposition(ATOMIC_PROPOSITION p) {
        atomicPropositions.add(p);
    }

    @Override
    public Set<ATOMIC_PROPOSITION> getAtomicPropositions() {
        return new HashSet<>(atomicPropositions);
    }

    @Override
    public void addToLabel(STATE s, ATOMIC_PROPOSITION l) throws FVMException {
        validateAtomicProposition(s, l);
        Set<ATOMIC_PROPOSITION> propositions = set();
        propositions.add(l);
        propositionHashMap.merge(s, propositions, ((p, x) -> {
            p.addAll(x);
            return p;
        }));
    }

    private void validateAtomicProposition(STATE s, ATOMIC_PROPOSITION l) {
        validateState(s);
        if (atomicPropositions.stream().noneMatch(l::equals))
            throw new InvalidLablingPairException(s, l);
    }

    @Override
    public Set<ATOMIC_PROPOSITION> getLabel(STATE s) {
        Validator.validateState(s, states);
        return propositionHashMap.getOrDefault(s, set());
    }

    @Override
    public Set<STATE> getInitialStates() {
        return new HashSet<>(initialStates);
    }

    @Override
    public Map<STATE, Set<ATOMIC_PROPOSITION>> getLabelingFunction() {
        return new HashMap<>(propositionHashMap);
    }

    @Override
    public Set<STATE> getStates() {
        return new HashSet<>(states);
    }

    @Override
    public Set<Transition<STATE, ACTION>> getTransitions() {
        return new HashSet<>(transitions);
    }

    @Override
    public void removeAction(ACTION action) throws FVMException {
        if (transitions.stream().anyMatch(transition -> transition.getAction().equals(action))) {
            throw new DeletionOfAttachedActionException(action, TRANSITIONS);
        } else {
            actions.remove(action);
        }
    }

    @Override
    public void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException {
        Set<ATOMIC_PROPOSITION> propositions = set();
        propositionHashMap.values().forEach(propositions::addAll);
        if (propositions.contains(p))
            throw new DeletionOfAttachedAtomicPropositionException(p, ATOMIC_PROPOSITIONS);
        else
            atomicPropositions.remove(p);

    }

    @Override
    public void removeInitialState(STATE state) {
        initialStates.remove(state);
    }

    @Override
    public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
        Set<ATOMIC_PROPOSITION> propositions = propositionHashMap.getOrDefault(s, set());
        propositions.remove(l);
        propositionHashMap.merge(s, propositions, ((p, x) -> {
            p.addAll(x);
            return p;
        }));
        if (propositionHashMap.getOrDefault(s, set()).size() == 0)
            propositionHashMap.remove(s);
    }

    @Override
    public void removeState(STATE state) throws FVMException {
        if (cantRemoveState(state))
            throw new DeletionOfAttachedStateException(state, INITIAL_STATES);
        else
            states.remove(state);
    }

    private boolean cantRemoveState(STATE state) {
        return initialStates.contains(state) ||
                transitions.stream().anyMatch(transition -> transition.getTo().equals(state) || transition.getFrom().equals(state)) ||
                propositionHashMap.containsKey(state);
    }

    @Override
    public void removeTransition(Transition<STATE, ACTION> t) {
        transitions.remove(t);
    }

    private void validateState(STATE state) {
        if (states.stream().noneMatch(state::equals)) {
            throw new InvalidInitialStateException("Validate STATE Fail " + state);
        }
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof TransitionSystemImpl)) return false;

        TransitionSystemImpl<?, ?, ?> that = (TransitionSystemImpl<?, ?, ?>) o;

        if (getName() != null ? !getName().equals(that.getName()) : that.getName() != null) return false;
        if (!getStates().equals(that.getStates())) return false;
        if (!getActions().equals(that.getActions())) return false;
        if (!getInitialStates().equals(that.getInitialStates())) return false;
        if (!getAtomicPropositions().equals(that.getAtomicPropositions())) return false;
        if (!getTransitions().equals(that.getTransitions())) return false;
        return propositionHashMap.equals(that.propositionHashMap);
    }

    @Override
    public int hashCode() {
        int result = getName() != null ? getName().hashCode() : 0;
        result = 31 * result + getStates().hashCode();
        result = 31 * result + getActions().hashCode();
        result = 31 * result + getInitialStates().hashCode();
        result = 31 * result + getAtomicPropositions().hashCode();
        result = 31 * result + getTransitions().hashCode();
        result = 31 * result + propositionHashMap.hashCode();
        return result;
    }
}