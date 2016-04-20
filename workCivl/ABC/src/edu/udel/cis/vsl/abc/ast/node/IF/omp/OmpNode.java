package edu.udel.cis.vsl.abc.ast.node.IF.omp;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;

/**
 * A node representing any kind of an OpenMP pragma. There are two
 * sub-categories:
 * <ul>
 * <li>DECLARATIVE: an OpenMP pragma that is only allowed to be placed in
 * declarative context;</li>
 * <li>EXECUTABLE: an OpenMP pragma that is not declarative.</li>
 * </ul>
 * 
 * @author Manchun Zheng
 * 
 */
public interface OmpNode extends ASTNode {
	/**
	 * The kind of this OpenMP pragma.
	 * 
	 * @author Manchun Zheng
	 * 
	 */
	public enum OmpNodeKind {
		DECLARATIVE, EXECUTABLE
	}

	/**
	 * The kind of this OpenMP pragma.
	 * 
	 * @return the kind of this OpenMP pragma.
	 */
	OmpNodeKind ompNodeKind();
}
