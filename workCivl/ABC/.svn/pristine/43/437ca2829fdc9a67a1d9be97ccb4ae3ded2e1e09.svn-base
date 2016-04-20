package edu.udel.cis.vsl.abc.ast.node.common.type;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

/**
 * Type node representing the type "$scope". This is used to give a scope a
 * name. It is very much like a variable declaration and is treated as such.
 * 
 * "$scope s;" is translated as a variable declaration of a variable named "s",
 * with type node an instances of this class.
 * 
 * @author siegel
 * 
 */
public class CommonScopeTypeNode extends CommonTypeNode {

	public CommonScopeTypeNode(Source source) {
		super(source, TypeNodeKind.SCOPE);
	}

	@Override
	public TypeNode copy() {
		CommonScopeTypeNode result = new CommonScopeTypeNode(getSource());

		copyData(result);
		return result;
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("$scope");
	}
}
