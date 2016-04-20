package edu.udel.cis.vsl.abc.ast.IF;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.common.ASTPrettyPrinter;
import edu.udel.cis.vsl.abc.ast.common.CommonASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.TypeFactory;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

/**
 * Factory class providing static method to produce a new {@link ASTFactory}.
 * This is the entry point for the <strong>ast</strong> module. To construct an
 * AST, one starts by invoking
 * {@link #newASTFactory(NodeFactory, TokenFactory, TypeFactory)} to get an
 * {@link ASTFactory}, then uses that ASTFactory to produce the components of
 * the AST and finally the AST itself.
 * 
 * @author siegel
 * 
 */
public class ASTs {

	/**
	 * Create a new ASTFactory that used the given node factory, token factory,
	 * and type factory.
	 * 
	 * @param nodeFactory
	 *            a factory for producing {@link ASTNode}s
	 * @param tokenFactory
	 *            a factory for producing {@link CivlcToken}s
	 * @param typeFactory
	 *            a factory for producing {@link Type}s
	 * @return the new ASTFactory
	 */
	public static ASTFactory newASTFactory(NodeFactory nodeFactory,
			TokenFactory tokenFactory, TypeFactory typeFactory) {
		return new CommonASTFactory(nodeFactory, tokenFactory, typeFactory);
	}
	
	/**
	 * Prints an AST node in the form of the original programming language.
	 * 
	 * @param node
	 *            the AST node to be printed
	 * @param out
	 *            the print stream to be used for printing
	 */
	public static void prettyPrint(ASTNode node, PrintStream out){
		ASTPrettyPrinter.prettyPrint(node, out);
	}

}
