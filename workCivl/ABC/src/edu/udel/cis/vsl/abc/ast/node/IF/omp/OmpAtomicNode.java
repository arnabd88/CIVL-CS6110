package edu.udel.cis.vsl.abc.ast.node.IF.omp;

/**
 * This represents an OpenMP atomic construct, which has the syntax:
 * 
 * <pre>
 * #pragma omp atomic [read | write | update | capture][seq_cst] new-line
 * expression-stmt
 * </pre>
 * 
 * or
 * 
 * <pre>
 * #pragma omp atomic capture [seq_cst] new-line 
 * structured-block
 * </pre>
 * 
 * @author zmanchun
 *
 */
public interface OmpAtomicNode extends OmpSyncNode {

	public enum OmpAtomicKind {
		READ, WRITE, UPDATE, CAPTURE, NONE
	};

	/**
	 * Returns the atomic kind of this OpenMP atomic construct, whether it is
	 * READ, WRITE, UPDATE, CAPTURE, or NONE.
	 * 
	 * @return the atomic kind of this OpenMP atomic construct
	 */
	OmpAtomicKind atomicKind();

	/**
	 * Does this atomic construct has the seq_cst clause?
	 * 
	 * @return true iff this atomic construct has the seq_cst clause
	 */
	boolean seq_cst();
}
