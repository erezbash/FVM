package il.ac.bgu.cs.fvm.examples;

import static il.ac.bgu.cs.fvm.examples.VendingMachineBuilder.ACTION.*;
import static il.ac.bgu.cs.fvm.examples.VendingMachineBuilder.STATE.*;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

public class VendingMachineBuilder {

    static FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

    public enum STATE {
        pay,
        soda,
        beer,
        select
    };

    public enum ACTION {
        insertCoin,
        getSoda,
        getBeer,
        tau
    }

    public TransitionSystem<STATE, ACTION, String> build() {
        TransitionSystem<STATE, ACTION, String> vendingMachine = FvmFacade.createInstance().createTransitionSystem();

        vendingMachine.addState(pay);
        vendingMachine.addState(soda);
        vendingMachine.addState(select);
        vendingMachine.addState(beer);

        vendingMachine.addInitialState(pay);

        vendingMachine.addAction(insertCoin);
        vendingMachine.addAction(getBeer);
        vendingMachine.addAction(getSoda);
        vendingMachine.addAction(tau);

        vendingMachine.addTransition(new Transition<>(pay, insertCoin, select));
        vendingMachine.addTransition(new Transition<>(select, tau, soda));
        vendingMachine.addTransition(new Transition<>(select, tau, beer));
        vendingMachine.addTransition(new Transition<>(soda, getSoda, pay));
        vendingMachine.addTransition(new Transition<>(beer, getBeer, pay));

        vendingMachine.addAtomicProposition("paid");
        vendingMachine.addAtomicProposition("drink");

        vendingMachine.addToLabel(soda, "paid");
        vendingMachine.addToLabel(beer, "paid");
        vendingMachine.addToLabel(select, "paid");
        vendingMachine.addToLabel(soda, "drink");
        vendingMachine.addToLabel(beer, "drink");

        return vendingMachine;

    }

}
