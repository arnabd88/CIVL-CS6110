/**
 * 
 */
package edu.udel.cis.vsl.civl.transition;

import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;

/**
 * A transition represents a single atomic step of execution in a CIVL model.
 * They are further specialized into simple and synchronous transitions in
 * sub-classes. However, every transition must have a path condition and must
 * belong to one model.
 * 
 * The path condition is the conjunction of the path condition in the pre-state
 * and the result of evaluating the guard. It is therefore the condition that
 * should hold when execution of the statement wrapped by this transition
 * begins. It is stored in the Transition as an optimization: since it must be
 * computed once when determining whether the transition is enabled, there is no
 * need to compute it again when executing the transition.
 * 
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public class Transition {

	private BooleanExpression pathCondition;

	private Model model;

	public Transition() {

	}

	/**
	 * A transition.
	 * 
	 * @param pathCondition
	 *            The path condition that should be used when executing the
	 *            statement * transition.
	 */
	public Transition(BooleanExpression pathCondition) {
		this.pathCondition = pathCondition;
	}

	/**
	 * @return The path condition that should result after executing the
	 *         transition.
	 */
	public BooleanExpression pathCondition() {
		return pathCondition;
	}

	/**
	 * @return The model to which this transition belongs.
	 */
	public Model model() {
		return model;
	}

	/**
	 * @param The
	 *            sets path condition to be used when executing statement
	 */
	public void setPathCondition(BooleanExpression pathCondition) {
		this.pathCondition = pathCondition;
	}

	/**
	 * @param The
	 *            model to which this transition belongs.
	 */
	public void setModel(Model model) {
		this.model = model;
	}

}
