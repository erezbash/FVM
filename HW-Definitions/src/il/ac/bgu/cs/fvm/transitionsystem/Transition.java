package il.ac.bgu.cs.fvm.transitionsystem;

/**
 * A single transition between states in a {@link TransitionSystem}. This is a
 * 3-tuple, containing the source and destination state, and the action that 
 * make the system transition between the two.
 *
 * @param <STATE> Type of the states
 * @param <ACTION> Type of the action
 */
public class Transition<STATE, ACTION> {
	private final STATE from;
	private final ACTION action;
	private final STATE to;

	/**
	 * A constructor that takes all the fields.
	 * 
	 * @param aFrom
	 *            The source of the transition. Should be a name of a state.
	 * @param anAction
	 *            The action on the transition. Should be a name of an action.
	 * @param aTo
	 *            The destination of the transition. Should be a name of a
	 *            state.
	 */
	public Transition(STATE aFrom, ACTION anAction, STATE aTo) {
		from = aFrom;
		action = anAction;
		to = aTo;

	}

	@Override
	public String toString() {
		return "[Transition " + from + "-" + action + "->" + to + "]";
	}

	/**
	 * Get the source of the transition.
	 * 
	 * @return The state from which the transition starts.
	 */
	public STATE getFrom() {
		return from;
	}

	/**
	 * Get the action that triggers the transition.
	 * 
	 * @return The action on the transition.
	 */
	public ACTION getAction() {
		return action;
	}

	/**
	 * Get the destination of the transition.
	 * 
	 * @return The state to which the transition goes.
	 */
	public STATE getTo() {
		return to;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((action == null) ? 0 : action.hashCode());
		result = prime * result + ((from == null) ? 0 : from.hashCode());
		result = prime * result + ((to == null) ? 0 : to.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		@SuppressWarnings("rawtypes")
		Transition other = (Transition) obj;
		if (action == null) {
			if (other.action != null)
				return false;
		} else if (!action.equals(other.action))
			return false;
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

}
