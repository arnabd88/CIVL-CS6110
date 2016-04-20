package edu.udel.cis.vsl.abc.ast.node.IF.statement;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.PragmaNode;
import edu.udel.cis.vsl.abc.ast.node.IF.StaticAssertionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.OrdinaryDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.TypedefDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpDeclarativeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.EnumerationTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.StructureOrUnionTypeNode;

/**
 * An item that can appear in a "block". Every instance of {@link BlockItemNode}
 * is also an instance of (at least) one of the following:
 * 
 * <ul>
 * <li>{@link EnumerationTypeNode}</li>
 * <li>{@link OmpDeclarativeNode}</li>
 * <li>{@link OrdinaryDeclarationNode}</li>
 * <li>{@link PragmaNode}</li>
 * <li>{@link StatementNode}</li>
 * <li>{@link StaticAssertionNode}</li>
 * <li>{@link StructureOrUnionTypeNode}</li>
 * <li>{@link TypedefDeclarationNode}</li>
 * </ul>
 * 
 * @author siegel
 * 
 */
public interface BlockItemNode extends ASTNode {

	public enum BlockItemKind {
		/**
		 * Indicates that the block item is an instance of
		 * {@link EnumerationTypeNode}.
		 */
		ENUMERATION,
		/**
		 * Indicates that the block item is an instance of
		 * {@link OmpDeclarativeNode}.
		 */
		OMP_DECLARATIVE,
		/**
		 * Indicates that the block item is an instance of
		 * {@link OrdinaryDeclarationNode}.
		 */
		ORDINARY_DECLARATION,
		/**
		 * Indicates that the block item is an instance of {@link PragmaNode}.
		 */
		PRAGMA,
		/**
		 * Indicates that the block item is an instance of {@link StatementNode}
		 * .
		 */
		STATEMENT,
		/**
		 * Indicates that the block item is an instance of
		 * {@link StaticAssertionNode}.
		 */
		STATIC_ASSERTION,
		/**
		 * Indicates that the block item is an instance of
		 * {@link StructureOrUnionTypeNode}.
		 */
		STRUCT_OR_UNION,
		/**
		 * Indicates that the block item is an instance of
		 * {@link TypedefDeclarationNode}.
		 */
		TYPEDEF
	}

	/**
	 * Returns the kind of this block item.
	 * 
	 * @return the kind
	 */
	BlockItemKind blockItemKind();

	@Override
	BlockItemNode copy();

}
