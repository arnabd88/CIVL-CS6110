package edu.udel.cis.vsl.abc.transform.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StringLiteralNode;
import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * A {@link Transformer} is a tool used to transform an {@link AST} in some way,
 * or, more precisely, it provides a method {@link #transform(AST)} which takes
 * an {@link AST} and returns the transformed {@link AST}.
 * 
 * <p>
 * The AST returned may or may not be the same object as the given AST: some
 * transformers might modify the given AST in place, while others might return
 * an entirely new AST with or without modifying the original one. This choice
 * is entirely up to the individual Transformer, but should be clearly
 * documented in the Transformer's javadoc.
 * </p>
 * 
 * <p>
 * Every Transformer should be <strong>re-useable</strong>, i.e., it should be
 * possible to use a single transfomer object to transform multiple ASTs, as in
 * 
 * <pre>
 * newAST1 = transformer.transform(ast1);
 * newAST2 = transformer.transform(ast2); // using same transformer
 * ...
 * </pre>
 * 
 * The easiest way to ensure this is to have the transformer instantiate a new
 * object each time {@link #transform(AST)} is invoked. The new object is
 * responsible for carrying out the transformation for that specific invocation,
 * it maintains all the state that is needed for that invocation, and it goes
 * away when the invocation completes.
 * </p>
 * 
 * @author siegel
 * 
 */
public interface Transformer {

	/**
	 * Returns the short name of this transformer, e.g., "mpi", or "prune".
	 * 
	 * @return the short name ("code") of this transformer
	 */
	String getCode();

	/**
	 * A brief (one line) description of what this transformer does, suitable
	 * for appearing in a help message.
	 * 
	 * @return a short description of what this transformer does
	 */
	String getShortDescription();

	/**
	 * Returns the long name of this transformer, e.g., "MPI Transformer" or
	 * "Pruner". The name is suitable for human consumption.
	 * 
	 * @return long name of this transformer
	 */
	@Override
	String toString();

	/**
	 * Apply a transformation to a translation unit. This may or may not result
	 * in modifications to the given AST, and may or may not return a new AST
	 * instance (as opposed to the given one).
	 * 
	 * @param ast
	 *            The abstract syntax tree being transformed
	 * @return the transformed AST, which may or may not be the same object that
	 *         was given
	 * @throws SyntaxException
	 *             If it encounters an error in the AST or an some case which it
	 *             cannot handle
	 */
	AST transform(AST ast) throws SyntaxException;

	/**
	 * Produces a new {@link StringLiteralNode}.
	 * 
	 * @param method
	 *            name of transformer method responsible for producing the new
	 *            token; used to form the {@link Formation} that will ultimately
	 *            be used in diagnostic message
	 * @param representation
	 *            the text of the string literal exactly as it would appear in a
	 *            program source; this must include the surrounding (single or
	 *            double) quotes
	 * @return new string literal node
	 * @throws SyntaxException
	 *             if the <code>representation</code> does not conform to the
	 *             C11 specification of string literals
	 */
	StringLiteralNode newStringLiteralNode(String method, String representation)
			throws SyntaxException;
}
