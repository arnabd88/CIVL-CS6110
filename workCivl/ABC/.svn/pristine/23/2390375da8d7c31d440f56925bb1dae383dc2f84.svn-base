package edu.udel.cis.vsl.abc.ast.node.IF.statement;

public interface JumpNode extends StatementNode {

	public static enum JumpKind {
		GOTO, CONTINUE, BREAK, RETURN
	};

	JumpKind getKind();

	@Override
	JumpNode copy();

}
