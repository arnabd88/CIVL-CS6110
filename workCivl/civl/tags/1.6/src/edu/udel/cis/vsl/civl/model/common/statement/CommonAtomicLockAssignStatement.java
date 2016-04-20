package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.AtomicLockAssignStatement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * When translating an $atomic/$atom block, we need to create a noop statement
 * at the beginning and at the end of the block. In order to have more
 * information about the transitions, we create this class to extend
 * {@link CommonNoopStatement}. Currently, there is a field {@link #enter} to
 * denote if the statement is
 * <ol>
 * <li>entering an $atomic block; or</li>
 * <li>leaving an $atomic block.</li>
 * </ol>
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonAtomicLockAssignStatement extends CommonAssignStatement
		implements AtomicLockAssignStatement {

	/* *************************** Instance Fields ************************* */

	/**
	 * Denote if this statement is
	 * <ol>
	 * <li>enter == true: entering an $atomic or</li>
	 * <li>enter == false: leaving an $atomic block.</li>
	 * </ol>
	 */
	private boolean enter;

	/* **************************** Constructors *************************** */

	/**
	 * 
	 * @param civlSource
	 *            The CIVL source of this statement. More information in
	 *            {@link CIVLSource}.
	 * @param source
	 *            The source location of this goto statement
	 * @param atomicKind
	 *            The atomic kind of this statement
	 */
	public CommonAtomicLockAssignStatement(CIVLSource civlSource, Scope hscope,
			Scope lscope, Location source, Expression guard,
			boolean isEntering, LHSExpression lhs, Expression rhs) {
		super(civlSource, hscope, lscope, source, guard, lhs, rhs, false);
		this.enter = isEntering;
	}

	/* ************************* Methods from Object *********************** */

	@Override
	public String toString() {
		String result = super.toString();

		if (enter)
			return "ENTER_ATOMIC (" + result + ", atomicCount++)";
		else
			return "LEAVE_ATOMIC (" + result + ", atomicCount--)";
	}

	@Override
	public Set<Variable> variableAddressedOf(Scope scope) {
		return null;
	}

	@Override
	public Set<Variable> variableAddressedOf() {
		return null;
	}

	@Override
	public void calculateDerefs() {
		this.hasDerefs = false;
	}

	@Override
	public boolean enterAtomic() {
		return this.enter;
	}

	@Override
	public boolean leaveAtomic() {
		return !this.enter;
	}

}
