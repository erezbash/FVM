package il.ac.bgu.cs.fvm.examples;

import il.ac.bgu.cs.fvm.FvmFacade;
import static java.util.Arrays.asList;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

public class CollatzProgramGraphBuilder {

    static FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

    public static ProgramGraph<String, String> build() {
        ProgramGraph<String, String> pg = fvmFacadeImpl.createProgramGraph();

        String running = "running";
        String finished = "finished";

        pg.addLocation(running);
        pg.addLocation(finished);

        pg.addInitialLocation(running);

        pg.addTransition(new PGTransition<>(running, "x % 2 == 1 && x != 1", "x:= (3 * x) + 1", running));
        pg.addTransition(new PGTransition<>(running, "x % 2 == 0", "x:= x / 2", running));
        pg.addTransition(new PGTransition<>(running, "x == 1", "", finished));

        pg.addInitalization(asList("x:=6"));

        return pg;
    }

}
