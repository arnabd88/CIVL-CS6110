package edu.udel.cis.vsl.abc.ast.node.IF.type;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

public interface TypedefNameNode extends TypeNode {

	IdentifierNode getName();

	void setName(IdentifierNode name);

	@Override
	TypedefNameNode copy();

	/**
	 * Returns the actual scope parameters used in this instances of a
	 * scope-generic typedef. Returns null if there are no scope parameters.
	 * 
	 * A typedef declaration can have any number of scope parameters associated
	 * to it, e.g.:
	 * 
	 * <pre>
	 * <s1,s2,s3> typedef struct _triple {
	 *   double *<s1> a;
	 *   double *<s2> b;
	 *   double *<s3> c;
	 * } triple;
	 * </pre>
	 * 
	 * When triple is used
	 * 
	 * <pre>
	 * triple&lt;t1, t2, t3&gt; t;
	 * </pre>
	 * 
	 * @return the list of scope identifiers in the declaration, or null if no
	 *         such list occurred
	 */
	SequenceNode<ExpressionNode> getScopeList();

}
