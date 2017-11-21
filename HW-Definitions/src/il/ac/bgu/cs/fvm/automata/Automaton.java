package il.ac.bgu.cs.fvm.automata;

import static java.util.Arrays.asList;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Set;

import org.svvrl.goal.cmd.Constant;
import org.svvrl.goal.cmd.Context;
import org.svvrl.goal.cmd.EquivalenceCommand;
import org.svvrl.goal.cmd.Expression;
import org.svvrl.goal.cmd.LoadCommand;
import org.svvrl.goal.cmd.Lval;
import org.svvrl.goal.cmd.TranslateCommand;
import org.svvrl.goal.core.aut.fsa.FSA;
import org.svvrl.goal.core.aut.opt.RefinedSimulation;
import org.svvrl.goal.core.aut.opt.RefinedSimulation2;
import org.svvrl.goal.core.aut.opt.SimulationRepository;
import org.svvrl.goal.core.comp.ComplementRepository;
import org.svvrl.goal.core.comp.piterman.PitermanConstruction;
import org.svvrl.goal.core.io.CodecRepository;
import org.svvrl.goal.core.io.GFFCodec;

import il.ac.bgu.cs.fvm.goal.AutomatonIO;

/**
 * An non-deterministic automaton, composed of states and transitions.
 * 
 * @param <State>
 *            Type of states.
 * @param <L>
 *            Type of transitions/alphabet the automaton understands.
 */

public class Automaton<State, L> extends MultiColorAutomaton<State, L> {

	public void setAccepting(State s) {
		super.setAccepting(s, 0);
	}

	public Set<State> getAcceptingStates() {
		return super.getAcceptingStates(0);
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object other) {
		BufferedWriter writer = null;

		if (other instanceof Automaton) {
			try {
				AutomatonIO.write((Automaton<State, L>) other, "other.gff");
				AutomatonIO.write(this, "this.gff");

				Context context = new Context();

				Constant con1 = new Constant("this.gff");
				Constant con2 = new Constant("other.gff");

				Lval lval1 = new Lval("th", new Expression[] {});
				Lval lval2 = new Lval("ot", new Expression[] {});

				CodecRepository.add(0, new GFFCodec());

				SimulationRepository.addSimulation2("RefinedSimilarity", FSA.class, RefinedSimulation2.class);
				SimulationRepository.addSimulation("RefinedSimilarity", FSA.class, RefinedSimulation.class);

				ComplementRepository.add("Safra-Piterman Construction", PitermanConstruction.class);

				LoadCommand lc1 = new LoadCommand(asList(lval1, con1));
				lc1.eval(context);

				LoadCommand lc2 = new LoadCommand(asList(lval2, con2));
				lc2.eval(context);

				EquivalenceCommand ec = new EquivalenceCommand(asList(lval1, lval2));

				return (Boolean) ec.eval(context);

			} catch (Exception e) {
				e.printStackTrace();
				return false;
			}
		}

		if (other instanceof String) {
			try {
				String xml = "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\r\n"
						+ "<logic name=\"QPTL\">\r\n" + "    <name/>\r\n" + "    <description/>\r\n" + "    <formula>"
						+ other + "</formula>\r\n" + "</logic>\r\n" + "";

				writer = new BufferedWriter(new FileWriter("formula.gff"));
				writer.write(xml);
				writer.close();				

				AutomatonIO.write(this, "this.gff");

				Context context = new Context();

				Constant con1 = new Constant("this.gff");
				Constant con3 = new Constant("formula.gff");

				Lval lval1 = new Lval("th", new Expression[] {});
				Lval lval3 = new Lval("fo", new Expression[] {});

				CodecRepository.add(0, new GFFCodec());

				SimulationRepository.addSimulation2("RefinedSimilarity", FSA.class, RefinedSimulation2.class);
				SimulationRepository.addSimulation("RefinedSimilarity", FSA.class, RefinedSimulation.class);

				ComplementRepository.add("Safra-Piterman Construction", PitermanConstruction.class);

				LoadCommand lc1 = new LoadCommand(asList(lval1, con1));
				lc1.eval(context);
		
				LoadCommand lc3 = new LoadCommand(asList(lval3, con3));
				lc3.eval(context);

				TranslateCommand tc = new TranslateCommand(asList(lval3));
				tc.eval(context);
			
				EquivalenceCommand ec = new EquivalenceCommand(asList(lval1, tc));

				return (Boolean) ec.eval(context);

			} catch (Exception e) {
				e.printStackTrace();
				return false;
			} finally {
				try {
					if (writer != null)
						writer.close();
				} catch (IOException e) {
				}
			}

		}

		return false;
	}

}
