package edu.udel.cis.vsl.abc.token.IF;

import org.antlr.runtime.Token;
import org.antlr.runtime.tree.Tree;

/**
 * An abstract representation of a preprocessor macro. Used to represent both
 * object and function macros.
 * 
 * @author siegel
 * 
 */
public interface Macro {

	/**
	 * The node in the ANTLR parse tree for the preprocessor grammar which is
	 * the root of the macro definition for this macro.
	 * 
	 * @return ANTLR tree node for the macro definition
	 */
	Tree getDefinitionNode();

	/**
	 * The node in the ANTLR parse tree which is the root of the macro body,
	 * i.e., the sequence of replacement tokens. This is a child of the
	 * definition node.
	 * 
	 * @return the ANTLR tree node for the macro body
	 */
	Tree getBodyNode();

	/**
	 * Returns the number of replacement tokens in the macro definition. In an
	 * object macro, the syntax is "#define NAME r0 r1 r2 ...", where the ri are
	 * the replacement tokens. In a function macro the syntax is
	 * "#define NAME(p0,p1,...) r0 r1 r2 ...".
	 * 
	 * @return the number of replacement tokens
	 */
	int getNumReplacementTokens();

	/**
	 * Returns the i-th replacement token.
	 * 
	 * @param i
	 *            int in range [0,numReplacementTokens-1]
	 * @return the i-th replacement token
	 */
	Token getReplacementToken(int i);

	/**
	 * Returns the macro name.
	 * 
	 * @return the macro name
	 */
	String getName();

	/**
	 * Returns the file in which this macro definition occurs.
	 * 
	 * @return file containing this macro definition
	 */
	SourceFile getFile();

	// /**
	// * Returns a shorter version of the file name which removes any path
	// * sequence prefix.
	// *
	// * @return shorter version of file name
	// */
	// String shortFileName();
}
