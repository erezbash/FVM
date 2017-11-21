package il.ac.bgu.cs.fvm;

import static il.ac.bgu.cs.fvm.TSTestUtils.APs.P;
import static il.ac.bgu.cs.fvm.TSTestUtils.APs.Q;
import static il.ac.bgu.cs.fvm.TSTestUtils.APs.R;
import static il.ac.bgu.cs.fvm.TSTestUtils.Actions.alpha;
import static il.ac.bgu.cs.fvm.TSTestUtils.Actions.beta;
import static il.ac.bgu.cs.fvm.TSTestUtils.Actions.delta;
import static il.ac.bgu.cs.fvm.TSTestUtils.Actions.gamma;
import static il.ac.bgu.cs.fvm.TSTestUtils.States.a;
import static il.ac.bgu.cs.fvm.TSTestUtils.States.b;
import static il.ac.bgu.cs.fvm.TSTestUtils.States.c;
import static il.ac.bgu.cs.fvm.TSTestUtils.States.d;

import java.util.function.Function;
import java.util.stream.IntStream;

import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

/**
 * Helps building transition systems. Contains some sample transition systems
 * for us to work on.
 *
 * PDF drawings of some of the systems can be found in the "docs" folder at the
 * top repository level.
 * 
 * @author michael
 */
public class TSTestUtils {

    public static enum Actions {
        alpha, beta, gamma, delta, epsilon, zeta, eta, theta
    }

    public static enum States {
        a, b, c, d, e, f, g
    }

    public static enum APs {
        P, Q, R, S
    }

    /**
     * Adds a label for each state. Label is the state's {@code toString} method
     * result.
     *
     * @param <S> Type of states in the system
     * @param <A> Type of actions in the system
     * @param ts the system
     * @return same system, but with the APs added.
     */
    public static <S, A> TransitionSystem<S, A, String> addTagsByStateNames(TransitionSystem<S, A, String> ts) {

        ts.getStates().forEach(s -> {
            String ap = s.toString();
            ts.addAtomicProposition(ap);
            ts.addToLabel(s, ap);
        });

        return ts;
    }

    /**
     * {@code
     *    +----------------- delta ------------------+
     *    |                                          |
     *    v                                          |
     *  ((a))--alpha--> (b) --beta--> (c) --gamma-> (d)
     * }
     *
     * @return a simple transition system.
     */
    public static TransitionSystem<States, Actions, APs> simpleTransitionSystem() {
        TransitionSystem<States, Actions, APs> ts = FvmFacade.createInstance().createTransitionSystem();

        ts.setName("Simple Transition System");

        IntStream.range(0, 4).forEach(i -> {
            ts.addState(States.values()[i]);
            ts.addAction(Actions.values()[i]);
            ts.addAtomicProposition(APs.values()[i]);
        });

        ts.addInitialState(a);

        ts.addTransitionFrom(a).action(alpha).to(b);
        ts.addTransitionFrom(b).action(beta).to(c);
        ts.addTransitionFrom(c).action(gamma).to(d);
        ts.addTransitionFrom(d).action(delta).to(a);

        ts.addToLabel(a, P);
        ts.addToLabel(b, Q);
        ts.addToLabel(c, R);
        ts.addToLabel(d, R);

        return ts;
    }

    /**
     * {@code
     * alpha
     * +---+
     * |   |
     * |   V   alpha
     * +---a<--------->b
     *     |
     * beta|
     *     |     * Initial state: a
     *     V
     *     c
     * }
     *
     * @return
     */
    public static TransitionSystem<States, Actions, APs> threeStateTS() {
        TransitionSystem<States, Actions, APs> ts = FvmFacade.createInstance().createTransitionSystem();
        ts.setName("Three-state TS");
        ts.addStates(a, b, c);
        ts.addActions(alpha, beta);

        ts.addInitialState(a);

        ts.addTransitionFrom(a).action(alpha).to(a);
        ts.addTransitionFrom(a).action(alpha).to(b);
        ts.addTransitionFrom(b).action(alpha).to(a);
        ts.addTransitionFrom(a).action(beta).to(c);

        return ts;
    }

    /**
     * Creates a linear transition system, with the states starting from
     * {@code 1} to {@code <num>} and the actions going from {@code a2} to
     * {@code a<num-1>}.
     *
     * @param <S> Type of states in the generated system.
     * @param stateNum number of states in the generated system.
     * @param stateFactory Object creating the states based on their index.
     * @return A linear transition system.
     */
    public static <S> TransitionSystem<S, String, String> makeLinearTs(int stateNum, Function<Integer, S> stateFactory) {
        TransitionSystem<S, String, String> retVal = FvmFacade.createInstance().createTransitionSystem();
        retVal.setName("Linear of " + stateNum);
        IntStream.rangeClosed(1, stateNum).mapToObj(stateFactory::apply).forEach(retVal::addState);
        IntStream.rangeClosed(1, stateNum - 1).forEach(i -> retVal.addAction("a" + i));
        IntStream.rangeClosed(1, stateNum - 1)
                .forEach(i -> retVal.addTransitionFrom(stateFactory.apply(i))
                        .action("a" + i)
                        .to(stateFactory.apply(i + 1)));

        retVal.addInitialState(stateFactory.apply(1));

        return retVal;
    }

    public static TransitionSystem<Integer, String, String> makeLinearTs(int stateNum) {
        return makeLinearTs(stateNum, Integer::valueOf);
    }

    /**
     * Creates a circular transition system, with the states starting from
     * {@code s1} to {@code s<num>} and the actions going from {@code a1} to
     * {@code a<num>}.
     *
     * @param stateNum number of states in the generated system.
     * @return A circular transition system.
     */
    public static TransitionSystem<Integer, String, String> makeCircularTs(int stateNum) {
        TransitionSystem<Integer, String, String> retVal = makeLinearTs(stateNum);
        retVal.setName( "Circular of " + stateNum );
        retVal.addAction("a" + stateNum);
        retVal.addTransitionFrom(stateNum).action("a" + stateNum).to(1);

        return retVal;
    }

    /**
     * Creates a circular transition system, with the states starting from
     * {@code s1} to {@code s<num>} and the actions going from {@code a1} to
     * {@code a<num>}, and a reset action that goes to {@code s1} from every
     * state.
     *
     * @param stateNum number of states in the generated system.
     * @return A circular transition system with a "reset" action.
     */
    public static TransitionSystem<Integer, String, String> makeCircularTsWithReset(int stateNum) {
        TransitionSystem<Integer, String, String> retVal = makeCircularTs(stateNum);

        retVal.setName(String.format("circular %d w/reset", stateNum));

        String resetAction = "reset";
        retVal.addAction(resetAction);
        IntStream.rangeClosed(1, stateNum)
                .forEach(i -> retVal.addTransitionFrom(i).action(resetAction).to(1));

        return retVal;
    }

    /**
     * Creates a transition system that has an indeterministic 3-fork at
     * {@code statenum-3}. Branch states are {@code s_<b>_<i>}, where {@code b}
     * is the branch number. Indeterministic action is {@code fork}.
     *
     * @param pathLength
     * @param branchCount
     * @return
     */
    public static TransitionSystem<String, String, String> makeBranchingTs(int pathLength, int branchCount) {
        TransitionSystem<String, String, String> retVal = makeLinearTs(pathLength, i -> "s" + i);
        retVal.setName(String.format("branching %d/%d", pathLength, branchCount));
        int branchPoint = pathLength - 3;
        retVal.addAction("fork");
        IntStream.rangeClosed(1, branchCount).forEach(branchNum -> {
            final String statePrefix = "s_" + branchNum + "_";
            IntStream.rangeClosed(branchPoint + 1, pathLength).forEach(i -> retVal.addState(statePrefix + i));
            IntStream.rangeClosed(branchPoint + 1, pathLength - 1)
                    .forEach(i -> retVal.addTransitionFrom(statePrefix + i).action("a" + i).to(statePrefix + (i + 1)));
            retVal.addTransitionFrom("s" + branchPoint).action("fork").to(statePrefix + (branchPoint + 1));
        });

        return retVal;
    }

}
