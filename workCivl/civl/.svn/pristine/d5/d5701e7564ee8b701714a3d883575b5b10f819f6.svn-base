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

	/** Boolean-valued expression assumed to hold when evaluating expression. */
	Expression boundRestriction();
	
	/** The expression e(x).*/
	Expression expression();
	
}
