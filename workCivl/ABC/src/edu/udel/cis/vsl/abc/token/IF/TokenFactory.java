package edu.udel.cis.vsl.abc.token.IF;

import java.util.List;

import org.antlr.runtime.CharStream;
import org.antlr.runtime.Token;
import org.antlr.runtime.tree.Tree;

import edu.udel.cis.vsl.abc.token.IF.ExecutionCharacter.CharacterKind;

/**
 * A factory for producing all the objects under the control of the token
 * module. These includes instances of the following types (and their subtypes):
 * <ul>
 * <li>{@link CivlcToken}</li>
 * <li>{@link Formation}</li>
 * <li>{@link ExecutionCharacter}</li>
 * <li>{@link Source}</li>
 * <li>{@link SyntaxException}</li>
 * <li>{@link UnsourcedException}</li>
 * <li>{@link Macro}</li>
 * </ul>
 * 
 * @author siegel
 * 
 */
// TODO fix javadocs
public interface TokenFactory {

	// Formations (records of history of token creation)...

	MacroExpansion newMacroExpansion(CivlcToken startToken, Macro macro,
			int index);

	Concatenation newConcatenation(List<CivlcToken> tokens);

	/**
	 * Inclusion record for original source file.
	 * 
	 * @param file
	 *            the file which was included
	 * @return a new inclusion record
	 */
	Inclusion newInclusion(SourceFile file);

	Inclusion newInclusion(SourceFile file, CivlcToken includeToken);

	/**
	 * Creates a new formation which represents some code added by the system
	 * itself, as opposed to code that emanated from an actual source file. The
	 * identifier should be a short string indicating what part of the system
	 * created the code. Examples: "The CIVL-MPI Transformer".
	 * 
	 * @param identifier
	 *            short string indicating what part of the system created this
	 *            code; used in messages
	 * @return a new system formation object
	 */
	Formation newSystemFormation(String identifier);

	Formation newTransformFormation(String transformerName, String method);

	// Basic token creation...

	CivlcToken newCivlcToken(Token token, Formation formation);

	CivlcToken newCivlcToken(int type, String text, Formation formation);

	CivlcToken newCivlcToken(CharStream input, int type, int channel,
			int start, int stop, Formation formation);

	// Characters and Strings...

	ExecutionCharacter executionCharacter(CharacterKind kind, int codePoint,
			char[] characters);

	CharacterToken characterToken(CivlcToken token) throws SyntaxException;

	StringToken newStringToken(CivlcToken token) throws SyntaxException;

	StringToken newStringToken(List<CivlcToken> tokens) throws SyntaxException;

	// Source objects...

	Source newSource(CivlcToken token);

	Source newSource(CivlcToken first, CivlcToken last);

	Source join(Source source, CivlcToken token);

	Source join(Source source1, Source source2);

	// Exceptions...

	SyntaxException newSyntaxException(String message, Source source);

	SyntaxException newSyntaxException(String message, CivlcToken token);

	SyntaxException newSyntaxException(UnsourcedException e, Source source);

	SyntaxException newSyntaxException(UnsourcedException e, CivlcToken token);

	UnsourcedException newUnsourcedException(String message);

	// Macros...

	ObjectMacro newObjectMacro(Tree definitionNode, SourceFile file);

	FunctionMacro newFunctionMacro(Tree definitionNode, SourceFile file);

	// TokenSources...

	CivlcTokenSequence getTokenSubsequence(CivlcTokenSource fullSource,
			CivlcToken startToken, CivlcToken stopToken);

	CivlcTokenSequence getEmptyTokenSubsequence(CivlcTokenSource originalSource);

	CivlcTokenSource getCivlcTokenSourceByTokens(List<? extends Token> tokens,
			Formation formation);
}
