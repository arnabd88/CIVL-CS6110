package edu.udel.cis.vsl.abc.token.common;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.antlr.runtime.CharStream;
import org.antlr.runtime.Token;
import org.antlr.runtime.tree.Tree;

import edu.udel.cis.vsl.abc.token.IF.CharacterToken;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSequence;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.IF.Concatenation;
import edu.udel.cis.vsl.abc.token.IF.ExecutionCharacter;
import edu.udel.cis.vsl.abc.token.IF.ExecutionCharacter.CharacterKind;
import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.FunctionMacro;
import edu.udel.cis.vsl.abc.token.IF.Inclusion;
import edu.udel.cis.vsl.abc.token.IF.Macro;
import edu.udel.cis.vsl.abc.token.IF.MacroExpansion;
import edu.udel.cis.vsl.abc.token.IF.ObjectMacro;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.StringLiteral;
import edu.udel.cis.vsl.abc.token.IF.StringToken;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.abc.token.IF.UnsourcedException;

public class CommonTokenFactory implements TokenFactory {

	private CommonCharacterFactory characterFactory;

	private CommonSourceFactory sourceFactory;

	private Map<String, SourceFile> transformerMap = new HashMap<>();

	public CommonTokenFactory() {
		characterFactory = new CommonCharacterFactory(this);
		sourceFactory = new CommonSourceFactory();
	}

	@Override
	public CivlcToken newCivlcToken(Token token, Formation formation) {
		return new CommonCivlcToken(token, formation);
	}

	@Override
	public CivlcToken newCivlcToken(int type, String text, Formation formation) {
		return new CommonCivlcToken(type, text, formation);
	}

	@Override
	public CivlcToken newCivlcToken(CharStream input, int type, int channel,
			int start, int stop, Formation formation) {
		return new CommonCivlcToken(input, type, channel, start, stop,
				formation);
	}

	@Override
	public Concatenation newConcatenation(List<CivlcToken> tokens) {
		return new CommonConcatenation(new ArrayList<CivlcToken>(tokens));
	}

	@Override
	public Inclusion newInclusion(SourceFile file, CivlcToken includeToken) {
		return new CommonInclusion(file, includeToken);
	}

	@Override
	public Inclusion newInclusion(SourceFile file) {
		return new CommonInclusion(file);
	}

	@Override
	public Formation newSystemFormation(String identifier) {
		return new SystemFormation(identifier, -1);
	}

	@Override
	public Formation newTransformFormation(String transformerName, String method) {
		SourceFile transformer = transformerMap.get(transformerName);

		if (transformer == null) {
			transformer = new SourceFile(new File(transformerName), -1);
			transformerMap.put(transformerName, transformer);
		}
		return new CommonTransformFormation(transformer, method);
	}

	@Override
	public ExecutionCharacter executionCharacter(CharacterKind kind,
			int codePoint, char[] characters) {
		return characterFactory.executionCharacter(kind, codePoint, characters);
	}

	@Override
	public CharacterToken characterToken(CivlcToken token)
			throws SyntaxException {
		return characterFactory.characterToken(token);
	}

	/**
	 * 
	 * @param type
	 *            usually PreprocessorParser.STRING_LITERAL
	 * @return
	 * @throws SyntaxException
	 */
	@Override
	public StringToken newStringToken(CivlcToken token) throws SyntaxException {
		StringLiteral data = characterFactory.stringLiteral(token);

		return new CommonStringToken(token, token.getFormation(), data);
	}

	/**
	 * Precondition: tokens has length at least 2.
	 */
	@Override
	public StringToken newStringToken(List<CivlcToken> tokens)
			throws SyntaxException {
		int type = tokens.get(0).getType();
		CommonStringLiteral data = characterFactory.stringLiteral(tokens);
		Concatenation concatenation = newConcatenation(tokens);
		CommonStringToken result = new CommonStringToken(type, concatenation,
				data);

		return result;
	}

	@Override
	public Source newSource(CivlcToken token) {
		return sourceFactory.newSource(token);
	}

	@Override
	public Source newSource(CivlcToken first, CivlcToken last) {
		return sourceFactory.newSource(first, last);
	}

	@Override
	public Source join(Source source, CivlcToken token) {
		return sourceFactory.join(source, token);
	}

	@Override
	public Source join(Source source1, Source source2) {
		return sourceFactory.join(source1, source2);
	}

	@Override
	public SyntaxException newSyntaxException(String message, Source source) {
		return new SyntaxException(message, source);
	}

	@Override
	public SyntaxException newSyntaxException(UnsourcedException e,
			Source source) {
		return new SyntaxException(e, source);
	}

	@Override
	public UnsourcedException newUnsourcedException(String message) {
		return new UnsourcedException(message);
	}

	@Override
	public SyntaxException newSyntaxException(String message, CivlcToken token) {
		return newSyntaxException(message, newSource(token));
	}

	@Override
	public SyntaxException newSyntaxException(UnsourcedException e,
			CivlcToken token) {
		return newSyntaxException(e, newSource(token));
	}

	@Override
	public ObjectMacro newObjectMacro(Tree definitionNode, SourceFile file) {
		return new CommonObjectMacro(definitionNode, file);
	}

	@Override
	public FunctionMacro newFunctionMacro(Tree definitionNode, SourceFile file) {
		return new CommonFunctionMacro(definitionNode, file);
	}

	@Override
	public MacroExpansion newMacroExpansion(CivlcToken startToken, Macro macro,
			int index) {
		return new CommonMacroExpansion(startToken, macro, index);
	}

	@Override
	public CivlcTokenSequence getTokenSubsequence(CivlcTokenSource fullSource,
			CivlcToken startToken, CivlcToken stopToken) {
		return new CivlcTokenSubSequence(fullSource, startToken.getIndex(),
				stopToken.getIndex());
	}

	@Override
	public CivlcTokenSequence getEmptyTokenSubsequence(
			CivlcTokenSource originalSource) {
		return new CivlcTokenSubSequence(originalSource, 0, -1);
	}

	@SuppressWarnings("unchecked")
	@Override
	public CivlcTokenSource getCivlcTokenSourceByTokens(
			List<? extends Token> tokens, Formation formation) {
		int num = tokens.size();
		List<CivlcToken> ctokens = new ArrayList<>(num);
		boolean needsTransformed = false;

		for (Token token : tokens) {
			if (token instanceof CivlcToken)
				ctokens.add((CivlcToken) token);
			else {
				needsTransformed = true;
				ctokens.add(this.newCivlcToken(token, formation));
			}
		}
		if (needsTransformed) {
			for (int i = 0; i < num - 1; i++) {
				CivlcToken current = ctokens.get(i), next = ctokens.get(i + 1);

				current.setNext(next);
			}
			return new CommonCivlcTokenSource(ctokens, this);
		} else
			return new CommonCivlcTokenSource((List<CivlcToken>) tokens, this);
	}
}
