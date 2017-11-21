package il.ac.bgu.cs.fvm.util;

import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

/**
 * Objects that help serializing {@link TransitionSystem}s.
 * 
 * @author michael
 * @param <S> Type of the states in the serialized system.
 * @param <A> Type of the actions in the serialized system.
 * @param <P> Type of the atomic propositions in the serialized system.
 */
public interface TSSerializationHelper<S,A,P> {
    
    String serializeState(S s);
    String serializeAction(A a);
    String serializeAtomicProposition(P ap);
    
}
