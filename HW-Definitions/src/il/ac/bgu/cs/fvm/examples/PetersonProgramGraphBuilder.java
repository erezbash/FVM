package il.ac.bgu.cs.fvm.examples;

import il.ac.bgu.cs.fvm.FvmFacade;
import static java.util.Arrays.asList;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

public class PetersonProgramGraphBuilder {

	/**
	 * Build the program graph for one of the processes in Peterson's mutual
	 * exclusion protocol.
	 *
	 * @param id
	 *            The id of the process (1 or 2)
	 *
	 * @return A program graph representing the process with the given id
	 */
	public static ProgramGraph<String, String> build(int id) {
		ProgramGraph<String, String> pg = FvmFacade.createInstance().createProgramGraph();

		String noncrit = "noncrit" + id;
		String wait = "wait" + id;
		String crit = "crit" + id;

		pg.addLocation(noncrit);
		pg.addLocation(wait);
		pg.addLocation(crit);

		pg.addInitialLocation(noncrit);

		pg.addTransition(
				new PGTransition<>(noncrit, "true", "atomic{b" + id + ":=1;x:=" + (id == 1 ? 2 : 1) + "}", wait));

		pg.addTransition(new PGTransition<>(wait, "x==" + id + " || b" + (id == 1 ? 2 : 1) + "==0", "", crit));
		pg.addTransition(new PGTransition<>(crit, "true", "b" + id + ":=0", noncrit));

		pg.addInitalization(asList("b" + id + ":=0", "x:=1"));
		pg.addInitalization(asList("b" + id + ":=0", "x:=2"));

		return pg;

	}

	/**
	 * Build the program graph for one of the processes in Peterson's mutual
	 * exclusion protocol.
	 *
	 * @param id
	 *            The id of the process (1 or 2)
	 *
	 * @return A program graph representing the process with the given id
	 */
	public static ProgramGraph<String, String> build2(int id) {
		ProgramGraph<String, String> pg = FvmFacade.createInstance().createProgramGraph();

		String noncrit = "noncrit" + id;
		String middle = "middle" + id;
		String wait = "wait" + id;
		String crit = "crit" + id;

		pg.addLocation(noncrit);
		pg.addLocation(wait);
		pg.addLocation(middle);
		pg.addLocation(crit);

		pg.addInitialLocation(noncrit);

		pg.addTransition(new PGTransition<>(noncrit, "true", "x:=" + (id == 1 ? 2 : 1), middle));
		pg.addTransition(new PGTransition<>(middle, "true", "b" + id + ":=1", wait));


		pg.addTransition(new PGTransition<>(wait, "x==" + id + " || b" + (id == 1 ? 2 : 1) + "==0", "", crit));
		pg.addTransition(new PGTransition<>(crit, "true", "b" + id + ":=0", noncrit));

		pg.addInitalization(asList("b" + id + ":=0", "x:=1"));
		pg.addInitalization(asList("b" + id + ":=0", "x:=2"));

		return pg;

	}

}
