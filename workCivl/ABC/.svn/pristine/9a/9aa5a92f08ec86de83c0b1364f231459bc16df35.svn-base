package edu.udel.cis.vsl.abc.ast.node.IF.omp;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;

/**
 * This interface represents the OpenMP loop construct. <br>
 * The syntax of the loop construct is specified in Section 2.7.1, OpenMP 4.0.0,
 * as follows:
 * 
 * <pre>
 * #pragma omp for [clause[[,] clause] ... ] new-line 
 * for-loops
 * </pre>
 * 
 * where clause is one of the following:
 * 
 * <pre>
 * private(list)
 * firstprivate(list) 
 * lastprivate(list) 
 * reduction(reduction-identifier: list)
 * schedule(kind[, chunk_size])
 * collapse(n)
 * ordered
 * nowait
 * </pre>
 * 
 * @author Manchun Zheng
 * 
 */
public interface OmpForNode extends OmpWorksharingNode {

	/**
	 * The schedule kind of an OpenMP for pragma.
	 * 
	 * @author Manchun Zheng
	 * 
	 */
	public enum OmpScheduleKind {
		AUTO, DYNAMIC, GUIDED, RUNTIME, STATIC, 
		/**
		 * The schedule clause is absent
		 */
		NONE
	};

	/**
	 * Returns the schedule kind of the loop construct. The default schedule is
	 * implementation defined, in our case we choose <code>STATIC</code>.
	 * 
	 * @return The schedule kind of the loop construct.
	 */
	OmpScheduleKind schedule();

	/**
	 * Updates the schedule kind of this loop construct.
	 * 
	 * @param ompScheduleKind
	 *            The schedule kind to be used to update this loop construct.
	 */
	void setSchedule(OmpScheduleKind ompScheduleKind);

	/**
	 * Returns the number of loops associated with this loop construct. 1 by
	 * default if there is no explicit collapse clause.
	 * 
	 * @return The number of loops associated with this loop construct.
	 */
	int collapse();

	/**
	 * Updates the number of loops associated with this loop construct.
	 * 
	 * @param value
	 *            The number to be used to update this loop construct.
	 */
	void setCollapse(int value);

	/**
	 * Returns true iff <code>ordered</code> clause is present.
	 * 
	 * @return true iff <code>ordered</code> clause is present.
	 */
	boolean ordered();

	/**
	 * Updates the ordered flag of this loop construct.
	 * 
	 * @param value
	 *            The value to be used to update this loop construct.
	 */
	void setOrdered(boolean value);

	/**
	 * Returns the chunk size. NULL if there is no schedule clause.
	 * 
	 * @return the chunk size, NULL if there is no schedule clause.
	 */
	ExpressionNode chunkSize();

	/**
	 * Updates the chunk size of this loop construct.
	 * 
	 * @param chunkSize
	 *            The expression node representing the new chunk size.
	 */
	void setChunsize(ExpressionNode chunkSize);

	/**
	 * Returns the assertions to be checked before the entry of this loop
	 * construct.
	 * 
	 * @return the assertions to be checked before the entry of this loop
	 *         construct.
	 */
	SequenceNode<FunctionCallNode> assertions();

	/**
	 * Updates the assertions to be checked before the entry of this loop
	 * construct.
	 * 
	 * @param assertions
	 *            The assertions to be used to update this loop construct.
	 */
	void setAssertions(SequenceNode<FunctionCallNode> assertions);

	/**
	 * Returns the loop invariant.
	 * 
	 * @return the loop invariant.
	 */
	FunctionCallNode invariant();

	/**
	 * Updates the loop invariant of this loop construct.
	 * 
	 * @param invariant
	 *            The assertion to be used as the new invariant.
	 */
	void setInvariant(FunctionCallNode invariant);
}
