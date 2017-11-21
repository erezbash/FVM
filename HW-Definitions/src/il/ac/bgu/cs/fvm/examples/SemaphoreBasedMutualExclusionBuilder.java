package il.ac.bgu.cs.fvm.examples;

import il.ac.bgu.cs.fvm.FvmFacade;
import static java.util.Arrays.asList;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

public class SemaphoreBasedMutualExclusionBuilder {

    public static ProgramGraph<String, String> build(int id) {
        ProgramGraph<String, String> pg = FvmFacade.createInstance().createProgramGraph();

        String noncrit = "noncrit" + id;
        String wait = "wait" + id;
        String crit = "crit" + id;

        pg.addLocation(noncrit);
        pg.addLocation(wait);
        pg.addLocation(crit);

        pg.addInitialLocation(noncrit);

        pg.addTransition(new PGTransition<>(noncrit, "true", "", wait));
        pg.addTransition(new PGTransition<>(wait, "y>0", "y:=y-1", crit));
        pg.addTransition(new PGTransition<>(crit, "true", "y:=y+1", noncrit));

        pg.addInitalization(asList("y:=1"));

        return pg;

    }

}
