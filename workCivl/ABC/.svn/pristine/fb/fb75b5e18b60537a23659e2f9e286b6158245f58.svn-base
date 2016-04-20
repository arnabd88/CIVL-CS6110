package edu.udel.cis.vsl.abc.ast.node.IF.omp;

/**
 * This represents an OpenMP worksharing construct, either a loop,
 * sections/section, or single construct.
 * 
 * @author Manchun Zheng
 */
public interface OmpWorksharingNode extends OmpExecutableNode {

	/**
	 * The kind of this OmpWorksharingNode:
	 * 
	 * <ul>
	 * <li>FOR: the loop construct</li>
	 * <li>SECTIONS: the sections construct</li>
	 * <li>SECTION: the section construct</li>
	 * <li>SINGLE: the single construct</li>
	 * </ul>
	 * 
	 * @author Manchun Zheng
	 * 
	 */
	public enum OmpWorksharingNodeKind {
		FOR, SECTIONS, SINGLE, SECTION
	}

	/**
	 * Returns the kind of this worksharing node.
	 * 
	 * @return the kind of this worksharing node.
	 */
	OmpWorksharingNodeKind ompWorkshareNodeKind();
}
