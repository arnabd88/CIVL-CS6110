/**
 * 
 */
package edu.udel.cis.vsl.civl.model.IF.expression;

import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;

/**
 * @author zirkel
 * 
 */
public interface QuantifiedExpression extends Expression {

	/**
	 * The different kinds of quantifiers which are possible. FORALL: the
	 * universal quantifier, EXISTS: the existential quantifier, UNIFORM: the
	 * uniform convergence quantifier.
	 * 
	 */
	enum Quantifier {
		FORALL, EXISTS, UNIFORM;
	}

	/**
	 * 
	 * @return The quantifier binding the variable.
	 */
	Quantifier quantifier();

	/** The name of the bound variable (e.g. x in forall x | ...). */
	Identifier boundVariableName();

	/** The type of the bound variable. */
	CIVLType boundVariableType();

	/** Is the quantifier specified to be a range? */
	boolean isRange();

	/**
	 * Integer-valued expression for the lower end of the range. Null iff
	 * isRange() == false.
	 */
	Expression lower();

	/**
	 * Integer-valued expression for the upper end of the range. Null iff
	 * isRange() == false.
	 */
	Expression upper();

	/**
	 * Boolean-valued expression assumed to hold when evaluating expression.
	 * Null iff isRange() == true.
	 */
	Expression boundRestriction();

	/** The expression e(x). */
	Expression expression();

}
