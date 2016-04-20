package edu.udel.cis.vsl.abc.ast.node.IF.statement;

import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpNode;

public interface StatementNode extends BlockItemNode {

	public enum StatementKind {
		ASSUME, ASSERT, ATOMIC, CHOOSE, CIVL_FOR, COMPOUND, EXPRESSION, IF, JUMP, LABELED, LOOP, NULL,
		/**
		 * indicates a OmpNode instance {@link OmpNode}
		 */
		OMP, PRAGMA, SWITCH, WHEN,
	}

	@Override
	StatementNode copy();

	/**
	 * Different statement nodes have different statement kind. For example, a
	 * while statement node has the statement kind WHILE, an if statement node
	 * has the kind IF, etc.
	 * 
	 * @return The statement kind defined as an enum element
	 */
	StatementKind statementKind();
}
