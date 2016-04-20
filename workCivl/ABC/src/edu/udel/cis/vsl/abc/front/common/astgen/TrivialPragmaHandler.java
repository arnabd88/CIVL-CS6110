package edu.udel.cis.vsl.abc.front.common.astgen;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.PragmaNode;
import edu.udel.cis.vsl.abc.front.IF.ParseTree;

public class TrivialPragmaHandler extends PragmaHandler {

	private String name;

	private ParseTree parseTree;

	public TrivialPragmaHandler(String name, ParseTree parseTree) {
		this.name = name;
		this.parseTree = parseTree;
	}

	@Override
	public EntityKind getEntityKind() {
		return EntityKind.PRAGMA_HANDLER;
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public ASTNode processPragmaNode(PragmaNode pragmaNode, SimpleScope scope) {
		return pragmaNode;
	}

	@Override
	public ParseTree getParseTree() {
		return parseTree;
	}

}
