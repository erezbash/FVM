package il.ac.bgu.cs.fvm.programgraph;

import java.util.HashMap;
import java.util.Map;
import java.util.Random;

/**
 * A transition in a {@link ProgramGraph}.
 * 
 * @param <L>
 *            Type of locations
 * @param <A>
 *            Type of label
 */
public class PGTransition<L, A> {
	L from;
	String condition;
	A action;
	L to;

	/**
	 * Default constructor.
	 */
	public PGTransition() {
	}

	/**
	 * A constructor that takes all the fields.
	 * 
	 * @param from
	 *            The source of the transition. Should be a name of a location.
	 * @param condition
	 *            The condition on the transition.
	 * 
	 * @param action
	 *            The action on the transition.
	 * @param to
	 *            The destination of the transition. Should be a name of a
	 *            location.
	 */
	public PGTransition(L from, String condition, A action, L to) {
		super();
		this.from = from;
		this.condition = condition;
		this.action = action;
		this.to = to;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		@SuppressWarnings("rawtypes")
		PGTransition other = (PGTransition) obj;
		if (action == null) {
			if (other.action != null)
				return false;
		} else if (!action.equals(other.action))
			return false;
		if (condition == null) {
			if (other.condition != null)
				return false;
		} else if (!condition.equals(other.condition)) {
			ParserBasedCondDef pbc = new ParserBasedCondDef();

			for (int i = 0; i < 1000; i++) {
				RandomMap eval = new RandomMap();
				boolean x1 = pbc.evaluate(eval, condition);
				boolean x2 = pbc.evaluate(eval, other.condition);
				if (x1 != x2)
					return false;
			}

			return true;
		}
		if (from == null) {
			if (other.from != null)
				return false;
		} else if (!from.equals(other.from))
			return false;
		if (to == null) {
			if (other.to != null)
				return false;
		} else if (!to.equals(other.to))
			return false;
		return true;
	}

	/**
	 * Get the action that triggers the transition.
	 * 
	 * @return The name of the action on the transition.
	 */
	public A getAction() {
		return action;
	}

	/**
	 * Get the condition string.
	 * 
	 * @return A string representing the condition for this transition.
	 */
	public String getCondition() {
		return condition;
	}

	/**
	 * Get the source of the transition.
	 * 
	 * @return The name of the state from which the transition starts.
	 */
	public L getFrom() {
		return from;
	}

	/**
	 * Get the destination of the transition.
	 * 
	 * @return The name of the state to which the transition goes.
	 */
	public L getTo() {
		return to;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((action == null) ? 0 : action.hashCode());
		// result = prime * result + ((condition == null) ? 0 :
		// condition.hashCode());
		result = prime * result + ((from == null) ? 0 : from.hashCode());
		result = prime * result + ((to == null) ? 0 : to.hashCode());
		return result;
	}

	/**
	 * Get the action that triggers the transition.
	 * 
	 * @param action
	 *            The name of the action on the transition.
	 */
	public void setAction(A action) {
		this.action = action;
	}

	/**
	 * Get the condition string.
	 * 
	 * @param condition
	 *            A string representing the condition for this transition.
	 */
	public void setCondition(String condition) {
		this.condition = condition;
	}

	/**
	 * Set the source of the transition.
	 * 
	 * @param from
	 *            The name of the state from which the transition starts.
	 */
	public void setFrom(L from) {
		this.from = from;
	}

	/**
	 * Get the destination of the transition.
	 * 
	 * @param to
	 *            The name of the state to which the transition goes.
	 */
	public void setTo(L to) {
		this.to = to;
	}

	@Override
	public String toString() {
		return "PGTransition [from=" + from + ", condition=" + condition + ", action =" + action + ", to=" + to + "]";
	}

}

@SuppressWarnings("serial")
class RandomMap extends HashMap<String, Object> implements Map<String, Object> {

	public Object get(Object key) {
		Object val = super.get(key);

		if (val == null) {
			val = new Random().nextInt(20) - 10;
			put((String) key, val);
		}

		return val;
	}
}