package il.ac.bgu.cs.fvm.transitionsystem;

import il.ac.bgu.cs.fvm.FvmFacade;
import java.util.Map;
import java.util.function.Function;
import static java.util.stream.Collectors.toMap;

/**
 * Converts a transition system of one type to another.
 * 
 * 
 * @param <S1> Type of states of the original system.
 * @param <S2> Type of states of the converted system.
 * @param <A1> Type of actions of the original system.
 * @param <A2> Type of actions of the converted system.
 * @param <P1> Type of atomic propositions of the original system.
 * @param <P2> Type of atomic propositions of the converted system.
 */
public class TransitionSystemConverter<S1,S2, A1,A2, P1,P2> {
    
    private final Function<S1,S2> stateConverter;
    private final Function<A1,A2> actionConverter;
    private final Function<P1,P2> apConverter;

    public TransitionSystemConverter(Function<S1, S2> stateConverter, Function<A1, A2> actionConverter, Function<P1, P2> apConverter) {
        this.stateConverter = stateConverter;
        this.actionConverter = actionConverter;
        this.apConverter = apConverter;
    }
    
    
    public TransitionSystem<S2, A2, P2> convert( TransitionSystem<S1, A1, P1> original ) {
        Map<S1,S2> states = original.getStates().stream().collect(toMap(Function.identity(), stateConverter::apply));;
        Map<A1,A2> actions = original.getActions().stream().collect(toMap(Function.identity(), actionConverter::apply));
        Map<P1,P2> aps = original.getAtomicPropositions().stream().collect(toMap(Function.identity(), apConverter::apply));
        
        TransitionSystem<S2, A2, P2> result = FvmFacade.createInstance().createTransitionSystem();
        result.addAllStates( states.values() );
        result.addAllActions( actions.values() );
        result.addAllAtomicPropositions( aps.values() );
        
        original.getTransitions().stream()
                .map( t -> new Transition<>(states.get(t.getFrom()), actions.get(t.getAction()), states.get(t.getTo()) ) )
                .forEach( result::addTransition );
        
        original.getLabelingFunction()
                .forEach((s,l) -> {
                    l.stream().map(apConverter::apply)
                              .forEach( ap -> result.addToLabel( states.get(s), ap) );
                });
        
        return result;
        
    }
    
    
}
