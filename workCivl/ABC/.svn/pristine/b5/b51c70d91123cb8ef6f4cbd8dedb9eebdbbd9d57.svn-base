package edu.udel.cis.vsl.abc.ast.node.IF.statement;

import java.util.Iterator;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * Represents a C <code>switch</code> statement.
 * 
 * @author siegel
 * 
 */
public interface SwitchNode extends StatementNode {

	/**
	 * Returns the branch condition controlling this switch statement.
	 * 
	 * @return the condition
	 */
	ExpressionNode getCondition();

	/**
	 * Returns the switch statement body: the switch statement has the form
	 * "switch(expression) body".
	 * 
	 * @return switch statement body
	 */
	StatementNode getBody();

	/**
	 * <p>
	 * Returns the sequence of all <code>case</code>-labeled statements within
	 * this switch statement's body. This does <strong>not</strong> include the
	 * <code>default</code> case.
	 * </p>
	 * 
	 * <p>
	 * Note: these are not children since they are reachable through the switch
	 * statement's body.
	 * </p>
	 * 
	 * @return sequence node listing all case-labeled statements in this switch
	 *         statement
	 */
	Iterator<LabeledStatementNode> getCases();

	/**
	 * Adds a case clause to the list associated to this switch node.
	 * 
	 * @param statement
	 *            a <code>case</code>-labeled statement occurring in the body
	 */
	void addCase(LabeledStatementNode statement);

	/**
	 * Returns the "default"-labeled statement within this switch statement, or
	 * null if there isn't one.
	 * 
	 * @return the default statement or null
	 */
	LabeledStatementNode getDefaultCase();

	/**
	 * Sets the default clause for this switch statement.
	 * 
	 * @param statement
	 *            the <code>default</code>-labeled statement in the switch node
	 *            body
	 */
	void setDefaultCase(LabeledStatementNode statement);

	@Override
	SwitchNode copy();

	/**
	 * Remove cases and default case.
	 */
	void clear();

}
