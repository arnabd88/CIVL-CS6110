package edu.udel.cis.vsl.abc.front.common.astgen;

import java.util.List;

import org.antlr.runtime.tree.CommonTree;

import antlr.ParseTree;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * An {@link ASTBuilderWorker} is used to perform specific translation tasks
 * related to a single {@link ParseTree}. The {@link ParseTree} is associated to
 * the worker when it is created and can never change.
 * 
 * @author siegel
 * 
 */
public abstract class ASTBuilderWorker {

	/**
	 * Assuming the {@link ParseTree} associated to this worker represents an
	 * entire translation unit, this method will translate the entire tree into
	 * an AST tree.
	 * 
	 * @return the root node of the new AST tree obtained by translating the
	 *         parse tree
	 * @throws SyntaxException
	 *             if any syntax error is encountered in the process of
	 *             translation
	 */
	public abstract SequenceNode<BlockItemNode> translateRoot()
			throws SyntaxException;

	/**
	 * Translates a single expression in the parse tree. The method takes a
	 * parse tree node (from the parse tree) representing an expression and
	 * produces a corresponding AST {@link ExpressionNode}.
	 * 
	 * @param expressionTree
	 *            parse tree node representing an expression
	 * @param scope
	 *            the simple scope in which the expressionTree resides. The
	 *            simple scopes are constructed during the translation process.
	 * @return the new {@link ExpressionNode}
	 * @throws SyntaxException
	 *             if there is a syntax error in the expression
	 */
	public abstract ExpressionNode translateExpression(
			CommonTree expressionTree, SimpleScope scope)
			throws SyntaxException;

	/**
	 * Translates an ANTLR {@link CommonTree} node of type BLOCK_ITEM. The
	 * result is a list of {@link BlockItemNode} because it is possible for a
	 * single ANTLR block item node to yield several AST {@link BlockItemNode}s.
	 * This can happen for example, if the block item is a declaration such as
	 * <code>int x,y</code> which is translated to two AST nodes, roughly
	 * corresponding to <code>int x</code> and <code>int y</code>.
	 * 
	 * @param blockItemTree
	 * @param scope
	 * @return
	 * @throws SyntaxException
	 */
	public abstract List<BlockItemNode> translateBlockItem(
			CommonTree blockItemTree, SimpleScope scope) throws SyntaxException;

}
