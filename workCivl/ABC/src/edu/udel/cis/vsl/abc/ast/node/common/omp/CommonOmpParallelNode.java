package edu.udel.cis.vsl.abc.ast.node.common.omp;

import java.io.PrintStream;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject.DiffKind;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpExecutableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.Source;

public class CommonOmpParallelNode extends CommonOmpStatementNode implements
		OmpParallelNode {
	private boolean isDefaultShared = true;

	/**
	 * Children
	 * <ul>
	 * <li>Children 0-7: same as {@link CommonOmpStatementNode};</li>
	 * <li>Child 8: ExpressionNode, the expression of <code>num_threads()</code>
	 * ;</li>
	 * <li>Child 9: ExpressionNode, the expression of <code>if()</code>.</li>
	 * </ul>
	 * 
	 * @param source
	 */
	public CommonOmpParallelNode(Source source, StatementNode statement) {
		super(source, statement);
		this.ompStatementKind = OmpExecutableKind.PARALLEL;
		this.addChild(null);// child 8
		this.addChild(null);// child 9
	}

	public CommonOmpParallelNode(Source source, IdentifierNode identifier,
			List<CivlcToken> body, CivlcToken eofToken, ExpressionNode numThreads,
			ExpressionNode ifClause, StatementNode statementNode,
			boolean isDefaultShared) {
		super(source, statementNode);
		this.ompStatementKind = OmpExecutableKind.PARALLEL;
		this.setNumThreads(numThreads);
		this.setIfClause(ifClause);
		this.isDefaultShared = isDefaultShared;
	}

	@Override
	public void setStatementNode(StatementNode statement) {
		StatementNode statementNode = (StatementNode) this.child(7);

		if (statementNode != null) {
			((OmpExecutableNode) statementNode).setStatementNode(statement);
		} else {
			super.setStatementNode(statement);
		}

	}

	@Override
	public ExpressionNode numThreads() {
		return (ExpressionNode) this.child(8);
	}

	@Override
	public ExpressionNode ifClause() {
		return (ExpressionNode) this.child(9);
	}

	@Override
	public boolean isDefaultShared() {
		return this.isDefaultShared;
	}

	@Override
	public void setDefault(boolean shared) {
		this.isDefaultShared = shared;
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("OmpParallel");
	}

	@Override
	protected void printExtras(String prefix, PrintStream out) {
		if (this.isDefaultShared) {
			out.println();
			out.print(prefix + "default(shared)");
		} else {
			out.println();
			out.print(prefix + "default(none)");
		}

	}

	@Override
	public void setNumThreads(ExpressionNode value) {
		this.setChild(8, value);
	}

	@Override
	public void setIfClause(ExpressionNode value) {
		this.setChild(9, value);
	}

	@Override
	public OmpParallelNode copy() {
		OmpParallelNode newParallelNode = new CommonOmpParallelNode(
				this.getSource(), null);
		int numChildren = this.numChildren();

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = this.child(i);

			if (child != null) {
				newParallelNode.setChild(i, child.copy());
			}
		}
		return newParallelNode;
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof OmpParallelNode)
			if (this.isDefaultShared == ((OmpParallelNode) that)
					.isDefaultShared())
				return null;
			else
				return new DifferenceObject(this, that, DiffKind.OTHER,
						"different default(shared|none) clause");
		return new DifferenceObject(this, that);
	}
}
