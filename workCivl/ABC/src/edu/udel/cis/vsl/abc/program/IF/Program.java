package edu.udel.cis.vsl.abc.program.IF;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.abc.transform.IF.Transformer;

/**
 * <p>
 * An abstract representation of a program. This is the highest level
 * representation and the one typically used first in most cases. The program is
 * represented by a single AST, which is obtained by merging a set of ASTs
 * representing translation units.
 * </p>
 * 
 * <p>
 * Future work: change the representation of a program to consist of a set of
 * entities and a set of ASTs, each representing one translation unit. There
 * should be a a method to get the "outer" (file-scope) entities, and a method
 * to get each AST. In this approach, there should not be any need for renaming
 * different entities, i.e., it should be possible, for example, for two structs
 * to have the same name but denote distinct entities because they come from
 * distinct translation units.
 * </p>
 * 
 * <p>
 * It seems that all the constituent ASTs can be analyzed using the same
 * analyzer, factories, etc.
 * </p>
 * 
 * <p>
 * Hence there wil be two ways to create a program: (1) from a collection of
 * ASTs, or (2) from one merged AST (which requires renaming).
 * </p>
 * 
 * @author siegel
 * 
 */
public interface Program {

	/**
	 * Returns the abstract syntax tree of this program. Note that this can
	 * return different values as the program is modified. I.e., a whole new AST
	 * can replace the current one.
	 * 
	 * @return the current AST of the program
	 */
	AST getAST();

	/**
	 * Returns the token factory used for the producing and manipulation of
	 * tokens associated to this Program.
	 * 
	 * @return the token factory
	 */
	TokenFactory getTokenFactory();

	/**
	 * Prints a human readable abstract representation of the program to the
	 * given output stream. (Not in source code format.)
	 * 
	 * @param out
	 *            a print stream
	 */
	void print(PrintStream out);

	/**
	 * Prints a human readable representation of the program in original
	 * language.
	 * 
	 * @param out
	 *            a print stream
	 */
	void prettyPrint(PrintStream out);

	void printSymbolTable(PrintStream out);

	/**
	 * Transforms this program using the given Transformer.
	 * 
	 * @param transformer
	 *            a program transformer
	 * @throws SyntaxException
	 *             if the syntax of this program is discovered to be
	 *             incompatible with that expected by the transformer
	 */
	void apply(Transformer transformer) throws SyntaxException;

	/**
	 * Transforms program using the transformer specifid by the unique code.
	 * 
	 * @param code
	 *            transformer code, e.g., "prune" or "mpi"
	 * @throws SyntaxException
	 *             if the syntax of this program is discovered to be
	 *             incompatible with that expected by the transformer
	 */
	void applyTransformer(String code) throws SyntaxException;

	/**
	 * Applies the given sequence of transformers to this program. The
	 * transformers will be applied in order.
	 * 
	 * @param transformers
	 *            any kind of iterable sequence of transformers
	 * @throws SyntaxException
	 *             if the syntax of this program is discovered to be
	 *             incompatible with that expected by any transformer in the
	 *             sequence
	 */
	void apply(Iterable<Transformer> transformers) throws SyntaxException;

	/**
	 * Applies the sequence of transformers specified by the given code sequence
	 * to this program. The transformers will be applied in order.
	 * 
	 * @param codes
	 *            a sequence of transformer codes
	 * @throws SyntaxException
	 *             if the syntax of this program is discovered to be
	 *             incompatible with that expected by any transformer in the
	 *             sequence
	 */
	void applyTransformers(Iterable<String> codes) throws SyntaxException;

	/**
	 * Checks if the AST of this program contains any pragma node with the
	 * identifier "omp".
	 * 
	 * @return True if the AST of this program contains at least one pragma
	 *         nodes with the identifier "omp"
	 */
	boolean hasOmpPragma();
}
