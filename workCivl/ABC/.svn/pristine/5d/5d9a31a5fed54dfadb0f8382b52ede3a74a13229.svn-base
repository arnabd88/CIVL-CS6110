package edu.udel.cis.vsl.abc.program.IF;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * <p>
 * This factory is used to produce a whole {@link Program} from a set of ASTs
 * representing individual translation units. This is similar to the process of
 * "linking". The resulting program is represented by a single AST that is
 * obtained by carefully merging the given ASTs. In the process of merging, some
 * entities may have to be re-named to avoid name conflicts, as described below.
 * </p>
 * 
 * <ol>
 * 
 * <li>For any entity that is renamed, the new name will be obtained by
 * appending a string beginning with <code>$TU</code> to the original name.
 * Hence the substring <code>$TU</code> should never be used in any identifier
 * in the original program, as it is reserved for this use.</li>
 * 
 * <li>The determination of compatibility for two tagged types will first strip
 * any suffix beginning with <code>$TU</code> from the tags. So, for example,
 * structs with tags such as <code>foo</code>, <code>foo$TU1</code>, and
 * <code>foo$TU2</code> may still be compatible, because all of them will be
 * considered to have the tag <code>foo</code> for the purpose of compatibility
 * checking.</li>
 * 
 * <li>After renaming, any two complete compatible tagged file-scope entities
 * will have the same name. The (redundant) complete definitions after the first
 * complete definition will be converted to incomplete declarations. That is, in
 * any subtree of the form <code>struct S { ... }</code>, the node
 * <code>{...}</code> will be replaced with <code>null</code>.</li>
 * 
 * <li>If all of the complete tagged file-scope entities with a given name are
 * compatible, then all those entities will keep the original name (including
 * the incomplete ones), and will therefore become one entity in the resulting
 * merged AST.</li>
 * 
 * <li>If there exist two incompatible file-scope tagged entities with the same
 * name from different translation units: the incompatible entities will be
 * given different names. Furthermore, any incomplete file-scope tagged entity
 * with that name will be given a name unique to its translation unit. However,
 * an incomplete type may still be considered compatible to any of these types,
 * due to the renaming scheme described above.</li>
 * 
 * <li>Given an ordinary file-scope entity E1 with internal or no linkage, if
 * there is another file-scope entity with the same name as E1 in a different
 * translation unit, the name of E1 will be modified to be unique in the whole
 * program, e.g., by appending a string of the form <code>TU</code><i>i</i> to
 * its name, where <i>i</i> is the ID of the translation unit to which E1
 * belongs.</li>
 * 
 * </ol>
 * 
 * <p>
 * Possible further work:
 * <ol>
 * <li>A second analysis pass on the merged AST could be implemented to update
 * the types of functions and objects. For example, the type of a function might
 * change after its definition. This could happen for example if a parameter
 * type had the form <code>struct S *p</code> and S was incomplete at the point
 * at which the function was analyzed. If S is completed later, the type of that
 * parameter (and the function) changes. Hence the analysis of the body of the
 * function should be re-done with the updated type of p---this might lead to
 * discovering an incompatibility. See example a0.c, a1.c, a2.c in
 * examples/link.</li>
 * <li>the Pruner could merge compatible typedefs. This has to happen after the
 * merged AST is anaylzed, because the new type information is needed.</li>
 * </ol>
 * 
 * </p>
 * 
 * @author siegel
 * 
 */
public interface ProgramFactory {

	/**
	 * Returns the AST factory associated to this program factory. This AST
	 * factory is used, for example, to create the new merged AST from a set of
	 * translation units.
	 * 
	 * @return the AST factory
	 */
	ASTFactory getASTFactory();

	/**
	 * Forms a new program from the given AST. The given AST is cleaned (i.e.,
	 * any residual analysis information from some previous analysis is removed)
	 * and analyzed in the process of creating the new program.
	 * 
	 * @param ast
	 *            an AST
	 * @return the program wrapping the given AST
	 * @throws SyntaxException
	 *             if any kind of static error is detected in the AST
	 */
	Program newProgram(AST ast) throws SyntaxException;

	/**
	 * Forms a new program by merging the given ASTs. Each AST represents a
	 * single translation unit. The ASTs will be cleared and analyzed in the
	 * process, so any existing analysis data will be discarded. In the process
	 * of merging, entities may have to be renamed to avoid name conflicts.
	 * 
	 * @param asts
	 *            a sequence of ASTs
	 * @return the program obtained by merging the given ASTs
	 * @throws SyntaxException
	 *             if any kind of static error is detected in any AST, or any
	 *             problem occurs in merging them
	 */
	Program newProgram(AST[] asts) throws SyntaxException;
}
