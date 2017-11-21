package il.ac.bgu.cs.fvm.examples;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

// Figure 2.12 in the book
public class MutualExclusionUsingArbiter {
    public enum TsState { NonCrit, Crit }
    public enum ArState { Unlock, Lock }
    public enum MuAction{ Request, Release }
    
	static final FvmFacade fvmFacadeImpl = FvmFacade.createInstance();
	
	static public TransitionSystem<TsState, MuAction, String> buildP() {
		TransitionSystem<TsState, MuAction, String> ts = fvmFacadeImpl.createTransitionSystem();

		ts.addAllStates(TsState.values());
		ts.addInitialState(TsState.NonCrit);
        ts.addAllActions(MuAction.values());

		ts.addTransitionFrom(TsState.NonCrit).action(MuAction.Request).to(TsState.Crit);
        ts.addTransitionFrom(TsState.Crit).action(MuAction.Release).to(TsState.NonCrit);
        return ts;
    }

 
	static public TransitionSystem<ArState, MuAction, String> buildArbiter() {
		TransitionSystem<ArState, MuAction, String> ts = fvmFacadeImpl.createTransitionSystem();

		ts.addAllStates(ArState.values());
		ts.addInitialState(ArState.Unlock);
        ts.addAllActions(MuAction.values());

		ts.addTransition(new Transition<>(ArState.Unlock, MuAction.Request, ArState.Lock));
		ts.addTransition(new Transition<>(ArState.Lock, MuAction.Release, ArState.Unlock));

        return ts;
    }

}
