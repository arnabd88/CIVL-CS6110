package edu.udel.cis.vsl.abc.front.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.front.common.astgen.PragmaFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * An object which translates an ANTLR tree to an ABC AST.
 * 
 * @author siegel
 * 
 */
public interface ASTBuilder {

	/**
	 * Builds the AST specified by a {@link ParseTree} which represents a
	 * translation unit.
	 * 
	 * @return the AST
	 * @throws SyntaxException
	 *             if something is wrong with the object being translated into
	 *             an ABC
	 */
	AST getTranslationUnit(ParseTree tree) throws SyntaxException;

	/**
	 * Gets the {@link ASTFactory} used by this builder to create new
	 * {@link ASTNode}s and other {@link AST} components.
	 * 
	 * @return the {@link ASTFactory} used by this builder
	 */
	ASTFactory getASTFactory();

	/**
	 * Gets the {@link PragmaFactory} used by this builder to translate pragmas
	 * that occur in the parse tree.
	 * 
	 * @return the pragma factory used by this builder
	 */
	PragmaFactory getPragmaFactory();

}
