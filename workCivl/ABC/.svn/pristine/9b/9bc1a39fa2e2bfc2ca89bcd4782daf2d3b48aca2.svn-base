package edu.udel.cis.vsl.abc.token.common;

import org.antlr.runtime.tree.Tree;

import edu.udel.cis.vsl.abc.token.IF.ObjectMacro;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;

public class CommonObjectMacro extends CommonMacro implements ObjectMacro {

	public CommonObjectMacro(Tree definitionNode, SourceFile file) {
		super(definitionNode, file);
	}

	@Override
	public Tree getBodyNode() {
		return definitionNode.getChild(1);
	}

	@Override
	public String toString() {
		String result = "ObjectMacro[" + getName() + " =";
		int numReplacementTokens = getNumReplacementTokens();

		for (int i = 0; i < numReplacementTokens; i++)
			result += " " + getReplacementToken(i).getText();
		result += "]";
		return result;
	}

	@Override
	public boolean equals(Object object) {
		return object instanceof CommonObjectMacro && super.equals(object);
	}
}
