package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.FVMException;
import il.ac.bgu.cs.fvm.exceptions.InvalidTransitionException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;

import java.util.Set;

class Validator {

    static <STATE, ACTION> void validateTransition(Transition<STATE, ACTION> t, Set<ACTION> actions, Set<STATE> states, FVMException exception) {
        validateState(t.getTo(), states, exception);
        validateState(t.getFrom(), states, exception);
        validateAction(t.getAction(), actions, exception);
    }

    static <STATE, ACTION> void validateTransition(Transition<STATE, ACTION> t, Set<ACTION> actions, Set<STATE> states) {
        validateState(t.getTo(), states);
        validateState(t.getFrom(), states);
        validateAction(t.getAction(), actions);
    }

    private static <ACTION> void validateAction(ACTION action, Set<ACTION> actions) {
        if(actions.stream().noneMatch(action::equals))
            throw new ActionNotFoundException("Validate ACTION Fail " + action);
    }

    private static <ACTION> void validateAction(ACTION action, Set<ACTION> actions, FVMException exception) {
        if(actions.stream().noneMatch(action::equals))
            throw exception;
    }

    static<STATE> void validateState(STATE state, Set<STATE> states, FVMException exception) {
        if(states.stream().noneMatch(state::equals)) {
            throw exception;
        }
    }

    static<STATE> void validateState(STATE state, Set<STATE> states) {
        if(states.stream().noneMatch(state::equals)) {
            throw new StateNotFoundException("");
        }
    }
}
