package edu.udel.cis.vsl.abc.token.common;

import java.util.HashMap;
import java.util.Map;

import org.antlr.runtime.Token;
import org.antlr.runtime.tree.CommonTree;
import org.antlr.runtime.tree.Tree;

import edu.udel.cis.vsl.abc.front.c.preproc.PreprocessorLexer;
import edu.udel.cis.vsl.abc.token.IF.FunctionMacro;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;

public class CommonFunctionMacro extends CommonMacro implements FunctionMacro {

	private int[] replacementFormalIndexes;

	public CommonFunctionMacro(Tree definitionNode, SourceFile file) {
		super(definitionNode, file);
		initialize();
	}

	private void initialize() {
		int numFormals = getNumFormals();
		int numReplacementTokens = getNumReplacementTokens();
		Map<String, Integer> nameMap = new HashMap<String, Integer>(numFormals);

		for (int i = 0; i < numFormals; i++) {
			nameMap.put(getFormal(i).getText(), i);
		}
		replacementFormalIndexes = new int[numReplacementTokens];
		for (int j = 0; j < numReplacementTokens; j++) {
			Token token = getReplacementToken(j);

			if (token.getType() == PreprocessorLexer.IDENTIFIER) {
				String name = token.getText();
				Integer formalIndex = nameMap.get(name);

				if (formalIndex != null) {
					replacementFormalIndexes[j] = formalIndex;
					continue;
				}
			}
			replacementFormalIndexes[j] = -1;
		}
	}

	@Override
	public Tree getBodyNode() {
		return definitionNode.getChild(2);
	}

	public int getNumFormals() {
		return definitionNode.getChild(1).getChildCount();
	}

	public Token getFormal(int index) {
		return ((CommonTree) definitionNode.getChild(1).getChild(index))
				.getToken();
	}

	/**
	 * Given i, 0<=i<n, where n is the number of replacement tokens, let t be
	 * the i-th replacement token. Returns -1 if t is not an identifier equal to
	 * one of the formal parameter identifiers. Otherwise, returns the index of
	 * that formal parameter. This is to faciliate substitution of actuals for
	 * formals.
	 * 
	 * @param i
	 *            integer in [0,numReplacementTokens)
	 * @return -1 or index of matching formal parameter in [0,numFormals)
	 */
	public int getReplacementFormalIndex(int i) {
		return replacementFormalIndexes[i];
	}

	@Override
	public String toString() {
		String result = "FunctionMacro[" + getName() + "(";
		int numFormals = getNumFormals();
		int numReplacementTokens = getNumReplacementTokens();

		for (int j = 0; j < numFormals; j++) {
			if (j > 0)
				result += ",";
			result += getFormal(j).getText();
		}
		result += ") =";
		for (int i = 0; i < numReplacementTokens; i++)
			result += " " + getReplacementToken(i).getText();
		result += "]";
		return result;
	}

	@Override
	public boolean equals(Object object) {
		if (object instanceof CommonFunctionMacro) {
			CommonFunctionMacro that = (CommonFunctionMacro) object;

			if (!super.equals(that))
				return false;

			int numFormals = getNumFormals();

			if (numFormals != that.getNumFormals())
				return false;

			for (int i = 0; i < numFormals; i++) {
				Token t1 = getFormal(i);
				Token t2 = that.getFormal(i);

				if (t1.getType() != t2.getType()
						|| !t1.getText().equals(t2.getText()))
					return false;
			}
			return true;
		}
		return false;
	}

}
