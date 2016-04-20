package edu.udel.cis.vsl.abc.ast.node.common.omp;

import java.io.PrintStream;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject.DiffKind;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

/**
 * This implements the OpenMP loop construct. The loop construct specifies that
 * the iterations of one or more associated loops will be executed in parallel
 * by threads in the team in the context of their implicit tasks. The iterations
 * are distributed across threads that already exist in the team executing the
 * parallel region to which the loop region binds.<br>
 * The syntax of the loop construct is as follows:<br>
 * <code>
 * #pragma omp for [clause[[,] clause] ... ] new-line <br>
 * for-loops<br>
 * </code> where clause is one of the following:<br>
 * <code>private(list)<br>
 * firstprivate(list) <br>
 * lastprivate(list) <br>
 * reduction(reduction-identifier: list) <br>
 * schedule(kind[, chunk_size]) <br>
 * collapse(n)<br>
 * ordered<br>
 * nowait<br></code>
 * 
 * @author Manchun Zheng
 * 
 */
public class CommonOmpForNode extends CommonOmpWorkshareNode implements
		OmpForNode {

	/**
	 * The schedule specified by the optional schedule clause
	 * <code>schedule(kind[, chunk_size])</code>. The schedule can be one of the
	 * following:
	 * <ul>
	 * <li>STATIC (default)</li>
	 * <li>DYNAMIC</li>
	 * <li>GUIDED</li>
	 * <li>AUTO</li>
	 * <li>RUNTIME</li>
	 * </ul>
	 */
	private OmpScheduleKind schedule;

	/**
	 * The number of loops of this node, specified by the optional clause
	 * <code>collapse(n)</code>. If <code>collapse(n)</code> is absent, collapse
	 * is 1 by default.
	 */
	private int collapse;

	/**
	 * True if the clause <code>ordered</code> is present, otherwise, false
	 * (default).
	 */
	private boolean ordered;

	/**
	 * Creates a new instance of CommonOmpForNode. The children are:
	 * 
	 * <ul>
	 * <li>Children 0-7: same as {@link CommonOmpStatementNode};</li>
	 * <li>Child 8: ExpressionNode, the expression of chunk_size in
	 * <code>schedule()</code> ;</li>
	 * <li>Child 9: SequenceNode&lt;FunctionCallNode&gt;, the list of assertions
	 * to be checked befor entering the for loop;</li>
	 * <li>Child 10: FunctionCallNode, the loop invariant;</li>
	 * </ul>
	 * All children are set to null except the statement node.
	 * 
	 * @param source
	 *            The source code element of the OpenMP for node.
	 * @param statement
	 *            The statement node of the OpenMP for node to be created.
	 */
	public CommonOmpForNode(Source source, StatementNode statement) {
		super(source, OmpWorksharingNodeKind.FOR, statement);
		collapse = 1;
		schedule = OmpScheduleKind.NONE;
		ordered = false;
		this.addChild(null);// child 8
		this.addChild(null);// child 9
		this.addChild(null);// child 10
	}

	@Override
	public OmpScheduleKind schedule() {
		return this.schedule;
	}

	@Override
	public int collapse() {
		return this.collapse;
	}

	@Override
	public boolean ordered() {
		return this.ordered;
	}

	@SuppressWarnings("unchecked")
	@Override
	public SequenceNode<FunctionCallNode> assertions() {
		return (SequenceNode<FunctionCallNode>) this.child(9);
	}

	@Override
	public FunctionCallNode invariant() {
		return (FunctionCallNode) this.child(10);
	}

	@Override
	protected void printBody(PrintStream out) {
		out.print("OmpFor");
	}

	@Override
	public ExpressionNode chunkSize() {
		return (ExpressionNode) this.child(8);
	}

	@Override
	public void setSchedule(OmpScheduleKind ompScheduleKind) {
		this.schedule = ompScheduleKind;
	}

	@Override
	public void setCollapse(int value) {
		this.collapse = value;
	}

	@Override
	public void setOrdered(boolean value) {
		this.ordered = value;
	}

	@Override
	public void setChunsize(ExpressionNode chunkSize) {
		this.setChild(8, chunkSize);
	}

	@Override
	protected void printExtras(String prefix, PrintStream out) {
		String scheduleText;
		ExpressionNode chunkSize = (ExpressionNode) this.child(8);

		switch (schedule) {
		case STATIC:
			scheduleText = "static";
			break;
		case DYNAMIC:
			scheduleText = "dynamic";
			break;
		case GUIDED:
			scheduleText = "guided";
			break;
		case AUTO:
			scheduleText = "auto";
			break;
		case RUNTIME:
			scheduleText = "runtime";
			break;
		default:// NONE
			scheduleText = null;
		}
		if (chunkSize != null && scheduleText != null) {
			out.println();
			out.print(prefix + "schedule(");
			out.print(scheduleText);
			out.print(",");
			out.print(chunkSize.toString());
			out.print(")");
		}
		if (collapse > 1) {
			out.println();
			out.print(prefix + "collapse(");
			out.print(this.collapse);
			out.print(")");
		}
		if (this.ordered) {
			out.println();
			out.print("ordered");
		}
		super.printExtras(prefix, out);
	}

	@Override
	public void setAssertions(SequenceNode<FunctionCallNode> assertions) {
		this.setChild(9, assertions);
	}

	@Override
	public void setInvariant(FunctionCallNode invariant) {
		this.setChild(9, invariant);
	}

	@Override
	public OmpForNode copy() {
		OmpForNode newForNode = new CommonOmpForNode(this.getSource(), null);
		int numChildren = this.numChildren();

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = this.child(i);

			if (child != null) {
				newForNode.setChild(i, child.copy());
			}
		}
		newForNode.setCollapse(this.collapse);
		newForNode.setOrdered(this.ordered);
		newForNode.setSchedule(this.schedule);
		return newForNode;
	}

	@Override
	protected DifferenceObject diffWork(ASTNode that) {
		if (that instanceof OmpForNode) {
			OmpForNode thatFor = (OmpForNode) that;

			if (this.collapse == thatFor.collapse()
					&& this.ordered == thatFor.ordered()
					&& this.schedule == thatFor.schedule())
				return null;
			else
				return new DifferenceObject(this, that, DiffKind.OTHER,
						"different collapse/ordered/schedule clauses");
		}
		return new DifferenceObject(this, that);
	}
}
