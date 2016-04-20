package edu.udel.cis.vsl.abc.front.common.astgen;

import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.PragmaNode;
import edu.udel.cis.vsl.abc.front.IF.ParseException;
import edu.udel.cis.vsl.abc.front.IF.ParseTree;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * <p>
 * An entity responsible for dealing with a family of pragmas. Every
 * <code>#pragma</code> line begins with an identifier (the first token
 * following <code>#pragma</code>), as in
 * 
 * <pre>
 * #pragma CIVL ...
 * </pre>
 * 
 * That identifier signifies the pragma family.
 * </p>
 * 
 * <p>
 * Each handler is responsible for dealing with pragmas with one code occurring
 * in one parse tree.
 * </p>
 * 
 * @author siegel
 * 
 */
public abstract class PragmaHandler implements Entity {

	/**
	 * Returns the parse tree associated to this handler. The handler should
	 * only be invoked on pragmas occurring in that tree.
	 * 
	 * @return the parse tree associated to this pragma
	 */
	public abstract ParseTree getParseTree();

	/**
	 * Translates a pragma node originating from the parse tree. The result can
	 * be any kind of rooted AST tree. The result will replace the pragma node
	 * in the AST.
	 * 
	 * @param pragmaNode
	 *            a pragma node that was formed from a pragma occurring in the
	 *            parse tree. The pragma node comprises the raw, unparsed
	 *            sequence of tokens occurring in the pragma
	 * @param scope
	 *            the simple scope in which the pragma occurrs
	 * @return the root of the tree which is the result of the translation
	 * @throws SyntaxException
	 *             if the pragma does not adhere to the syntax specified by the
	 *             pragma domain
	 */
	public abstract ASTNode processPragmaNode(PragmaNode pragmaNode,
			SimpleScope scope) throws SyntaxException, ParseException;

}
