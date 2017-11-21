package il.ac.bgu.cs.fvm.util.codeprinter;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.CollectionHelper;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;
import il.ac.bgu.cs.fvm.verification.VerificationResult;

/**
 * Prints the code needed to generate a {@link TransitionSystem}. Generated code
 * relies on static imports of {@link CollectionHelper}.
 *
 */
@SuppressWarnings("rawtypes")
public class TsPrinter {

	private static final int ELEMENTS_PER_LINE = 5;

	private static final Map<Class<?>, ObjectPrinter> defaultPrinters = new HashMap<>();

	static {
		defaultPrinters.put(String.class, (s, t, p) -> p.print("\"" + s + "\""));
		defaultPrinters.put(Integer.class, (i, t, p) -> p.print(i));
		defaultPrinters.put(Long.class, (i, t, p) -> p.print(i + "l"));
		defaultPrinters.put(Boolean.class, (i, t, p) -> p.print(i));
		defaultPrinters.put(Set.class, (ObjectPrinter<Set>) (Set obj, TsPrinter tsp, PrintWriter out) -> {
			out.print("set(");
			int i = 0;
			for (Iterator it = obj.iterator(); it.hasNext();) {
				tsp.printObject(it.next());
				if (it.hasNext()) {
					out.print(", ");
				}
				if ((++i) % ELEMENTS_PER_LINE == 0) {
					out.println();
					out.print("    ");
				}
			}
			out.print(")");
		});

		defaultPrinters.put(List.class, (ObjectPrinter<List>) (List obj, TsPrinter tsp, PrintWriter out) -> {
			out.print("seq(");
			int i = 0;
			for (Iterator it = obj.iterator(); it.hasNext();) {
				tsp.printObject(it.next());
				if (it.hasNext()) {
					out.print(", ");
				}
				if ((++i) % ELEMENTS_PER_LINE == 0) {
					out.println();
					out.print("    ");
				}
			}
			out.print(")");
		});

		defaultPrinters.put(Map.class, (ObjectPrinter<Map>) (Map obj, TsPrinter tsp, PrintWriter out) -> {
			out.print("map(");
			int i = 0;
			for (Iterator it = obj.entrySet().iterator(); it.hasNext();) {
				final Map.Entry next = (Map.Entry) it.next();
				out.print("p(");
				tsp.printObject(next.getKey());
				out.print(",");
				tsp.printObject(next.getValue());
				out.print(")");

				if (it.hasNext()) {
					out.print(", ");
				}
				if ((++i) % ELEMENTS_PER_LINE == 0) {
					out.println();
					out.print("    ");
				}
			}
			out.print(")");
		});

		defaultPrinters.put(Pair.class, (ObjectPrinter<Pair>) (Pair o, TsPrinter tsp, PrintWriter prt) -> {
			prt.print("p(");
			tsp.printObject(o.first);
			prt.print(", ");
			tsp.printObject(o.second);
			prt.print(")");
		});

		defaultPrinters.put(Transition.class, (ObjectPrinter<Transition>) new ObjectPrinter<Transition>() {
			@Override
			public void print(Transition t, TsPrinter tsp, PrintWriter prt) {
				prt.print("transition(");
				tsp.printObject(t.getFrom());
				prt.print(", ");
				tsp.printObject(t.getAction());
				prt.print(", ");
				tsp.printObject(t.getTo());
				prt.print(")");
			}
		});

		defaultPrinters.put(PGTransition.class, (ObjectPrinter<PGTransition>) new ObjectPrinter<PGTransition>() {
			@Override
			public void print(PGTransition t, TsPrinter tsp, PrintWriter prt) {
				prt.print("pgtransition(");
				tsp.printObject(t.getFrom());
				prt.print(", ");
				tsp.printObject(t.getCondition());
				prt.print(", ");
				tsp.printObject(t.getAction());
				prt.print(", ");
				tsp.printObject(t.getTo());
				prt.print(")");
			}
		});

	}

	private final Map<Class<?>, ObjectPrinter> adHocPrinters = new HashMap<>();

	public <T> void setClassPrinter(Class<T> clz, ObjectPrinter<T> prt) {
		adHocPrinters.put(clz, prt);
	}

	/**
	 * @param <T>
	 *            Type of object.
	 * @param clz
	 *            The class.
	 *
	 * @return A best match printer for the objects of the class.
	 */
	public <T> ObjectPrinter getPrinterForClass(Class<T> clz) {
		Deque<Class> candidateClasses = new LinkedList<>();
		candidateClasses.add(clz);
		while (!candidateClasses.isEmpty()) {
			Class<?> cur = candidateClasses.pop();
			if (adHocPrinters.containsKey(cur)) {
				return adHocPrinters.get(cur);
			}
			if (defaultPrinters.containsKey(cur)) {
				return defaultPrinters.get(cur);
			}
			if (cur.getSuperclass() != null) {
				candidateClasses.addLast(cur.getSuperclass());
			}
			for (Class itf : cur.getInterfaces()) {
				candidateClasses.addLast(itf);
			}
		}
		throw new IllegalArgumentException("No Object printer defined for " + clz);
	}

	private StringWriter strm;
	private PrintWriter prt;

	@SuppressWarnings("unchecked")
	public String print(TransitionSystem ts) {
		strm = new StringWriter();
		prt = new PrintWriter(strm);

		prt.println("TransitionSystem ts = FvmFacade.createInstance().createTransitionSystem();");
		if (ts.getName() != null) {
			prt.println("ts.setName(\"" + ts.getName() + "\");");
		}

		prt.print("ts.addStates( ");
		int i = 0;
		for (Iterator it = ts.getStates().iterator(); it.hasNext();) {
			printObject(it.next());
			if (it.hasNext()) {
				prt.print(", ");
			}
			if ((++i) % ELEMENTS_PER_LINE == 0) {
				prt.print("\n    ");
			}
		}
		prt.println(");");

		prt.print("ts.addActions( ");
		i = 0;
		for (Iterator it = ts.getActions().iterator(); it.hasNext();) {
			printObject(it.next());
			if (it.hasNext()) {
				prt.print(", ");
			}
			if ((++i) % ELEMENTS_PER_LINE == 0) {
				prt.print("\n    ");
			}
		}
		prt.println(");");

		prt.print("ts.addAtomicPropositions( ");
		i = 0;
		for (Iterator it = ts.getAtomicPropositions().iterator(); it.hasNext();) {
			printObject(it.next());
			if (it.hasNext()) {
				prt.print(", ");
			}
			if ((++i) % ELEMENTS_PER_LINE == 0) {
				prt.print("\n    ");
			}
		}
		prt.println(");");

		ts.getInitialStates().forEach(is -> {
			prt.print("ts.addInitialState(");
			printObject(is);
			prt.println(");");
		});

		ts.getTransitions().forEach(t -> {
			prt.print("ts.addTransitionFrom(");
			printObject(((Transition) t).getFrom());
			prt.print(").action(");
			printObject(((Transition) t).getAction());
			prt.print(").to(");
			printObject(((Transition) t).getTo());
			prt.println(");");
		});

		ts.getLabelingFunction().forEach((k, v) -> {
			prt.print("ts.addLabel(");
			printObject(k);
			prt.print(", ");
			printObject(v);
			prt.println(");");
		});

		prt.close();
		return strm.toString();
	}

	@SuppressWarnings("unchecked")
	public void printObject(Object o) {
		if (o == null) {
			prt.print("null");
		} else {
			ObjectPrinter p = getPrinterForClass(o.getClass());
			p.print(o, this, prt);
		}
	}

	@SuppressWarnings("unchecked")
	public String getAssertions(TransitionSystem ts) {
		strm = new StringWriter();
		prt = new PrintWriter(strm);

		if (ts.getName() != null) {
			prt.println("assertEquals(\"" + ts.getName() + "\", ts.getName());");
		}

		prt.print("assertEquals(");
		printObject(ts.getStates());
		prt.println(",ts.getStates());");

		prt.print("assertEquals(");
		printObject(ts.getInitialStates());
		prt.println(",ts.getInitialStates());");

		prt.print("assertEquals(");
		printObject(ts.getActions());
		prt.println(",ts.getActions());");

		prt.print("assertEquals(");
		printObject(ts.getAtomicPropositions());
		prt.println(",ts.getAtomicPropositions());");

		prt.print("assertEquals(");
		printObject(ts.getTransitions());
		prt.println(",ts.getTransitions());");

		ts.getStates().stream().forEach((s) -> {
			prt.print("assertEquals(");
			printObject(ts.getLabel(s));
			prt.print(", ts.getLabel(");
			printObject(s);
			prt.print("));\n");
		});

		prt.close();
		return strm.toString();
	}

	public String getAssertions(ProgramGraph pg) {
		strm = new StringWriter();
		prt = new PrintWriter(strm);

		if (pg.getName() != null) {
			prt.println("assertEquals(\"" + pg.getName() + "\", pg.getName());");
		}

		prt.print("assertEquals(");
		printObject(pg.getLocations());
		prt.println(",pg.getLocations());");

		prt.print("assertEquals(");
		printObject(pg.getInitialLocations());
		prt.println(",pg.getInitialLocations());");

		prt.print("assertEquals(");
		printObject(pg.getInitalizations());
		prt.println(",pg.getInitalizations());");

		prt.print("assertEquals(");
		printObject(pg.getTransitions());
		prt.println(",pg.getTransitions());");

		prt.close();
		return strm.toString();
	}

	public <S> String getAssertions(VerificationResult<S> vr) {
		strm = new StringWriter();
		prt = new PrintWriter(strm);

		if (vr instanceof VerificationSucceeded) {
			prt.print("assertTrue(vr instanceof VeficationSucceeded);");
		} else {

			prt.print("assertTrue(vr instanceof VeficationFailed);");

			prt.print("assertEquals(");
			printObject( ((VerificationFailed) vr).getPrefix());
			prt.println(",((VeficationFailed) vr).getPrefix());");

			prt.print("assertEquals(");
			printObject(((VerificationFailed) vr).getCycle());
			prt.println(",((VeficationFailed) vr).getCycle());");
		}
		prt.close();
		return strm.toString();
	}

	public <S> String getAssertions(VerificationSucceeded<S> vrs) {
		strm = new StringWriter();
		prt = new PrintWriter(strm);

		prt.close();
		return strm.toString();
	}

	public String getObj(Object o) {
		strm = new StringWriter();
		prt = new PrintWriter(strm);

		printObject(o);

		prt.close();
		return strm.toString();
	}

}
