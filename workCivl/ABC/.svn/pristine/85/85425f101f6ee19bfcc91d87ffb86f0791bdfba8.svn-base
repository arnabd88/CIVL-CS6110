package edu.udel.cis.vsl.abc.ast.node.IF.omp;

import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * This represents an OpenMP parallel pragma. The syntax of a parallel construct
 * is as follows (Section 2.5, OpenMP Specification 4.0.0):
 * 
 * <pre>
 * #pragma omp parallel [clause[ [, ]clause] ...] new-line 
 * structured-block
 * where clause is one of the following:
 * if(scalar-expression) 
 * num_threads(integer-expression) 
 * default(shared | none) 
 * private(list) 
 * firstprivate(list) 
 * shared(list)
 * copyin(list)
 * reduction(redution-identifier :list) 
 * proc_bind(master | close | spread)
 * </pre>
 * 
 * @author Manchun Zheng
 * 
 */
public interface OmpParallelNode extends OmpExecutableNode {
	/**
	 * Returns the expression node of <code>num_threads()</code>. NULL if
	 * num_threads() is absent.
	 * 
	 * @return the expression node of <code>num_threads()</code>; NULL if
	 *         <code>num_threads()</code> is absent.
	 */
	ExpressionNode numThreads();

	/**
	 * Updates the number of threads when the clause <code>num_threads()</code>
	 * is present.
	 * 
	 * @param value
	 *            The expression node representing the argument of the clause
	 *            <code>num_threads()</code>.
	 */
	void setNumThreads(ExpressionNode value);

	/**
	 * Returns the expression node of <code>if()</code>. NULL if
	 * <code>if()</code> is absent.
	 * 
	 * @return the expression node of <code>if()</code>; NULL if
	 *         <code>if()</code> is absent.
	 */
	ExpressionNode ifClause();

	/**
	 * Updates the if-condition when the clause <code>if()</code> is present.
	 * 
	 * @param value
	 *            The expression node representing the argument of the clause
	 *            <code>if()</code>.
	 */
	void setIfClause(ExpressionNode value);

	/**
	 * true iff <code>default(shared)</code>, false iff
	 * <code>default(none)</code>. The default(none) clause requires that each
	 * variable that is referenced in the construct, and that does not have a
	 * predetermined data-sharing attribute, must have its data-sharing
	 * attribute explicitly determined by being listed in a data-sharing
	 * attribute clause. By default, <code>default(shared)</code> is assumed.
	 */
	boolean isDefaultShared();

	/**
	 * Updates the default setting when <code>default()</code> clause is
	 * present.
	 * 
	 * @param shared
	 *            The value to be used to update the default setting.
	 */
	void setDefault(boolean shared);

}
