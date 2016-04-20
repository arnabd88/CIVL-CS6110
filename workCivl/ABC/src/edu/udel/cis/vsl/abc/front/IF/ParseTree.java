package edu.udel.cis.vsl.abc.front.IF;

import java.util.Collection;

import org.antlr.runtime.tree.CommonTree;

import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSequence;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

/**
 * This represents a parse tree which is the result of preprocessing and parsing
 * a source in various languages, such as CIVL-C, Fortran, C, etc. It will be
 * used as the input for the AST generation module {@link ASTBuilder}.
 * 
 * @author Manchun Zheng
 *
 */
public interface ParseTree {
	/**
	 * returns the language that associates with this Parse tree
	 * 
	 * @return
	 */
	Language getLanguage();

	/**
	 * Gets the root of the tree.
	 * 
	 * @return the root
	 */
	CommonTree getRoot();

	/**
	 * Given a node in the parse tree, returns a source object for it.
	 * 
	 * @param tree
	 *            node in tree returned by method getTree()
	 * @return a source object describing the origin of that node in the source
	 *         code
	 */
	Source source(CommonTree tree);

	/**
	 * The source files from which this parse tree was derived.
	 * 
	 * @return the set of source files
	 */
	Collection<SourceFile> getSourceFiles();

	/**
	 * Creates a new syntax exception.
	 * 
	 * @param message
	 *            the message to print out when this exception is reported to
	 *            the user
	 * @param tree
	 *            the node in the ANTLR tree that led to this exception
	 * @return the new syntax exception
	 */
	SyntaxException newSyntaxException(String message, CommonTree tree);

	/**
	 * Returns a token source consisting of the tokens from the children of the
	 * given node in the tree. This is useful, for example, to obtain the token
	 * source from the body of a pragma node. Child number 1 of the pragma node
	 * would be passed as the argument to this method.
	 * 
	 * @param tokenListNode
	 *            a node in the ANTLR tree whose children are all leaf nodes
	 * @return a token source comprising the sequence of tokens obtained from
	 *         the children of the given node
	 */
	CivlcTokenSequence getTokenSourceProducer(CommonTree tokenListNode);

	/**
	 * gets the Civlc token source associating with this parse tree, i.e., the
	 * CToken source that was used to produce this parse tree. It contains all
	 * tokens, including those hidden for the parser
	 * 
	 * @return
	 */
	CivlcTokenSource getCivlcTokenSource();

	/**
	 * gets the token factory associating with this parse tree.
	 * 
	 * @return
	 */
	TokenFactory getTokenFactory();
}
