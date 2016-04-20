package edu.udel.cis.vsl.abc.ast.node.IF.acsl;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;

/**
 * A contract node represents an element that may occur in a procedure contract.
 * The procedure contract consists of a sequence of contract nodes.
 * 
 * @author siegel
 * 
 */
public interface ContractNode extends ASTNode {

	/**
	 * The kinds of contract nodes
	 * 
	 * @author Manchun Zheng
	 *
	 */
	public enum ContractKind {
		/**
		 * defines memory units assigned by the function
		 */
		ASSIGNS_READS,
		/**
		 * an "assumes" clause
		 */
		ASSUMES,
		/**
		 * An "behavior" node encodes a named behavior block
		 */
		BEHAVIOR,
		/**
		 * An "completeness" node encodes either a complete or disjoint clause
		 */
		COMPLETENESS,
		/**
		 * defines features of the dependent processes of the current one
		 */
		DEPENDS,
		/**
		 * An "ensures" node encodes a post-condition in a procedure contract. A
		 * node of this kind can be safely cast to {@link EnsuresNode}.
		 */
		ENSURES,
		/**
		 * A "guard" node represents the guard of a CIVL-C function. A node of
		 * this kind may be safely cast to {@link GuardNode}.
		 */
		GUARDS,
		/**
		 * A "invariant" node represents a loop invariant or a general
		 * invariant.
		 */
		INVARIANT,
		/**
		 * A "\mpi_collective" node introduces a block of contracts which should
		 * satisfy mpi collective behaviors.
		 */
		MPI_COLLECTIVE,
		/**
		 * A "pure" node represents the contract for specifying a pure function.
		 * A node of this kind may be safely cast to {@link PureNode}.
		 */
		PURE,
		/**
		 * A "requires" node represents a pre-condition in a CIVL-C procedure
		 * contract. May be safely cast to {@link RequiresNode}.
		 */
		REQUIRES

	}

	/**
	 * The kind of this contract node.
	 * 
	 * @return
	 */
	ContractKind contractKind();

	@Override
	ContractNode copy();
}
