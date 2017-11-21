package il.ac.bgu.cs.fvm.nanopromela;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.BoolexprContext;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.IntexprContext;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.JoinedContext;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.StmtContext;import static il.ac.bgu.cs.fvm.util.CollectionHelper.singeltonMap;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.map;
;

public class Evaluator {

	Map<String, Object> eval;

	public Evaluator(Map<String, Object> eval) {
		super();
		this.eval = eval;
	}

	public int evaluate(IntexprContext context, Map<String, Object> eval) {
		if (context.POW() != null)
			return evaluate(context.intexpr(0)) ^ evaluate(context.intexpr(1));

		if (context.MINUS() != null && context.intexpr().size() == 1)
			return -evaluate(context.intexpr(0));

		if (context.MULT() != null)
			return evaluate(context.intexpr(0)) * evaluate(context.intexpr(1));

		if (context.DIV() != null)
			return evaluate(context.intexpr(0)) / evaluate(context.intexpr(1));

		if (context.MOD() != null)
			return evaluate(context.intexpr(0)) % evaluate(context.intexpr(1));

		if (context.PLUS() != null)
			return evaluate(context.intexpr(0)) + evaluate(context.intexpr(1));

		if (context.MINUS() != null)
			return evaluate(context.intexpr(0)) - evaluate(context.intexpr(1));

		if (context.INT() != null)
			return Integer.parseInt(context.getText());

		if (context.VARNAME() != null)
			return (int) eval.get(context.getText());

		assert (context.intexpr() != null);
		return evaluate(context.intexpr(0));
	}

	@SuppressWarnings({ "serial", "unchecked" })
	public Map<String, Object> evaluate(StmtContext context) {

		if (context.skipstmt() != null)
			return eval;

		if (context.assstmt() != null) {
			return new HashMap<String, Object>(eval) {
				{
					put(context.assstmt().VARNAME().getText(), evaluate(context.assstmt().intexpr()));
				}
			};
		}

		if (context.atomicstmt() != null) {
			return new HashMap<String, Object>(eval) {
				{
					for (int i = 0; i < context.atomicstmt().VARNAME().size(); i++) {
						put(context.atomicstmt().VARNAME(i).getText(), evaluate(context.atomicstmt().intexpr(i)));
					}
				}
			};
		}

		if (context.chanwritestmt() != null) {
			HashMap<String, Object> neweval = new HashMap<String, Object>(eval) {
				{

					List<Integer> q = (List<Integer>) eval.get(context.chanwritestmt().CHANNAME().getText());
					if (q == null) {
						q = new Vector<Integer>();
					}

					q = new Vector<Integer>(q) {
						{
							add(evaluate(context.chanwritestmt().intexpr()));
						}
					};

					put(context.chanwritestmt().CHANNAME().getText(), q);
				}
			};

			return neweval;

		}

		// chanreadstmt : CHANNAME '?' VARNAME ;
		if (context.chanreadstmt() != null) {
			HashMap<String, Object> neweval = new HashMap<String, Object>(eval);

			List<Integer> q = (List<Integer>) eval.get(context.chanreadstmt().CHANNAME().getText());

			if (q == null)
				return null;

			if (q.size() == 0)
				return null;

			q = new Vector<Integer>(q);
			Integer val = q.remove(0);

			neweval.put(context.chanreadstmt().CHANNAME().getText(), q);
			neweval.put(context.chanreadstmt().VARNAME().getText(), val);

			return neweval;

		}

		return null;
	}

	@SuppressWarnings("unchecked")
	public int evaluate(IntexprContext context) {

		if (context.POW() != null)
			return evaluate(context.intexpr(0)) ^ evaluate(context.intexpr(1));

		if (context.MINUS() != null && context.intexpr().size() == 1)
			return -evaluate(context.intexpr(0));

		if (context.MULT() != null)
			return evaluate(context.intexpr(0)) * evaluate(context.intexpr(1));

		if (context.DIV() != null)
			return evaluate(context.intexpr(0)) / evaluate(context.intexpr(1));

		if (context.MOD() != null) {
			int p = evaluate(context.intexpr(1));
			return (evaluate(context.intexpr(0)) + p) % p;
		}

		if (context.PLUS() != null)
			return evaluate(context.intexpr(0)) + evaluate(context.intexpr(1));

		if (context.MINUS() != null)
			return evaluate(context.intexpr(0)) - evaluate(context.intexpr(1));

		if (context.INT() != null)
			return Integer.parseInt(context.getText());

		if (context.VARNAME() != null) {
			Object object = eval.get(context.getText());
			return object == null ? 0 : (int) object;
		}

		if (context.CHANNAME() != null) {
			List<Integer> q = (List<Integer>) eval.get(context.CHANNAME().getText());
			return q == null ? 0 : q.size();
		}

		assert (context.intexpr() != null);
		return evaluate(context.intexpr(0));
	}

	@SuppressWarnings("unchecked")
	public Map<String, Object> evaluate(JoinedContext context) throws Exception {
		if (context.hsreadstmt() == null) {
			throw new Exception("Not an interleaved (hsreadstmt) statement. See the NanoPromela.g4 file.");
		}

		if (!context.hsreadstmt().ZEROCAPACITYCHANNAME().getText()
				.equals(context.hswritestmt().ZEROCAPACITYCHANNAME().getText()))
			throw new Exception("Incompatible hanshaking statements " + context.getText());

		if (context.hsreadstmt().VARNAME() == null && context.hswritestmt().intexpr() != null)
			throw new Exception("Incompatible hanshaking statements");

		if (context.hsreadstmt().VARNAME() != null && context.hswritestmt().intexpr() == null)
			throw new Exception("Incompatible hanshaking statements");

		if (context.hsreadstmt().VARNAME() != null && context.hswritestmt().intexpr() != null)
			return map(p(context.hsreadstmt().VARNAME().getText(), evaluate(context.hswritestmt().intexpr())));
		else
			return eval;
	}

	public boolean evaluate(BoolexprContext context) {
		if (context.NOT() != null)
			return !evaluate(context.boolexpr(0));

		if (context.AND() != null)
			return evaluate(context.boolexpr(0)) && evaluate(context.boolexpr(1));

		if (context.OR() != null)
			return evaluate(context.boolexpr(0)) || evaluate(context.boolexpr(1));

		if (context.LTEQ() != null)
			return evaluate(context.intexpr(0)) <= evaluate(context.intexpr(1));

		if (context.GTEQ() != null)
			return evaluate(context.intexpr(0)) >= evaluate(context.intexpr(1));

		if (context.LT() != null)
			return evaluate(context.intexpr(0)) < evaluate(context.intexpr(1));

		if (context.GT() != null)
			return evaluate(context.intexpr(0)) > evaluate(context.intexpr(1));

		if (context.EQ() != null)
			return evaluate(context.intexpr(0)) == evaluate(context.intexpr(1));

		if (context.NEQ() != null)
			return evaluate(context.intexpr(0)) != evaluate(context.intexpr(1));

		if (context.TRUE() != null)
			return true;

		if (context.FALSE() != null)
			return false;

		assert (context.boolexpr() != null);
		return evaluate(context.boolexpr(0));
	}

}