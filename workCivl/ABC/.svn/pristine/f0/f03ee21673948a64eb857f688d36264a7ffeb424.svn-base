package edu.udel.cis.vsl.abc.ast.IF;

import java.util.Collection;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.TypeFactory;
import edu.udel.cis.vsl.abc.token.IF.Inclusion;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

/**
 * An ASTFactory is used to create all objects associated to an AST. It actually
 * encompasses a number of other factories which deal with specific kinds of
 * objects. For examples, there is a {@link NodeFactory} for creating
 * {@link ASTNode}s, a {@link TypeFactory} for creating {@link Type}s, and so
 * on.
 * 
 * @author siegel
 * 
 */
public interface ASTFactory {

	/**
	 * Creates a new AST with the given root node. The root node is typically a
	 * translation unit, but it may also be the root of an AST formed by merging
	 * multiple translation units. This method also checks conformance with many
	 * facets of the C11 Standard, resolves references and adds this information
	 * to the AST, marks all the AST nodes reachable from root as "owned" by the
	 * new AST, and numbers the nodes from 0 to n-1, where n is the number of
	 * reachable nodes.
	 * 
	 * After this method returns, the nodes belonging to the new AST will be
	 * essentially immutable (with exceptions for certain "harmless" fields that
	 * cannot effect the correctness of the AST). If you want to modify the AST,
	 * you have to invoke its {@link AST#release()} method, which dissolves the
	 * AST but leaves the nodes untouched and free (so mutable again), and then
	 * create a new AST once the modifications are complete. You may also invoke
	 * {@link ASTNode#copy()} on the root node and use it to create a new AST
	 * equivalent to the original, with all new nodes, if you want to keep the
	 * original AST.
	 * 
	 * Some of the interpretation that takes place:
	 * 
	 * <ul>
	 * 
	 * <li>when creating the abstract type of a formal function parameter, the
	 * type "qualified array of T" is changed to "qualified pointer to T".</li>
	 * 
	 * <li>"f(void)" means 0 parameters. "f()" means unknown parameters.</li>
	 * 
	 * <li>determines and sets the cases in the switch statements</li>
	 * 
	 * </ul>
	 * 
	 * @param root
	 *            the root node of the new AST
	 * @param isWholeprogram
	 *            is this AST representing a whole program (see
	 *            {@link AST#isWholeProgram()} )
	 * @return the new AST
	 * @throws SyntaxException
	 *             if something violating the syntax rules is found while
	 *             traversing this AST
	 */
	AST newAST(SequenceNode<BlockItemNode> root,
			Collection<SourceFile> sourceFiles, boolean isWholeprogram)
			throws SyntaxException;

	/**
	 * Returns the node factory used by this AST factory. The node factory is
	 * responsible for producing new AST nodes.
	 * 
	 * @return the node factory
	 */
	NodeFactory getNodeFactory();

	/**
	 * Returns the token factory used by this AST factory. The token factory is
	 * responsible for creating not only tokens, but a number of objects related
	 * to tokens, such as {@link Source} and {@link Inclusion} objects.
	 * 
	 * @return the token factory
	 */
	TokenFactory getTokenFactory();

	/**
	 * Returns the type factory used by this AST factory. The type factory is
	 * used to create {@link Type} objects.
	 * 
	 * @return the type factory
	 */
	TypeFactory getTypeFactory();
}
