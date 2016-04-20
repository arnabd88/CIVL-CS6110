package edu.udel.cis.vsl.abc.ast.node.IF.compound;

import edu.udel.cis.vsl.abc.ast.node.IF.PairNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CompoundLiteralNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;

/**
 * <p>
 * A compound initializer (written with curly braces in C) is used to initialize
 * an array, struct, or union. It is specified as a sequence of
 * designation-initializer pairs. In any such pair, the designation is optional;
 * if it is absent, it is represented here by <code>null</code>. The initializer
 * node can never be <code>null</code>.
 * </p>
 * 
 * <p>
 * This class is also used in the representation of a compound literal. A
 * {@link CompoundLiteralNode} has a reference to a
 * {@link CompoundInitializerNode}. This is because the two structures are
 * essentially identical. The only difference is that a compound literal
 * expression begins with a type name in parentheses, which specifies the type
 * of the compound literal, while a compound initializer does not have that
 * component because the type is taken from the type of the variable being
 * initialized.
 * </p>
 * 
 * <p>
 * This class is also used to represent a CIVL-C Cartesian domain literal. A
 * Cartesian domain is the Cartesian product of a sequence of ranges. Each range
 * represents an (ordered) set of integers. The domain is an (ordered) set of
 * tuples of integers. All tuples in a domain have the same arity, say n, called
 * the dimension of the domain. For a Cartesian domain, n is the number of
 * ranges used to form the domain. The order on the domain is the dictionary
 * order. In a Cartesian domain literal, all the designation nodes are null, and
 * each initializer node is an expression of range type. Moreover, the method
 * {@link #getLiteralObject()} will return <code>null</code>, as there is not
 * object associated to a Caretesian domain literal, only a type. The method
 * {@link #getType()} returns (after analysis) all the information you need
 * about the domain.
 * </p>
 * 
 * @see CompoundLiteralNode
 * 
 * @author siegel
 * 
 */
public interface CompoundInitializerNode extends InitializerNode,
		SequenceNode<PairNode<DesignationNode, InitializerNode>> {

	@Override
	CompoundInitializerNode copy();

	/**
	 * Returns the type of this initializer. The type is determined from the
	 * type of the expression of which this initializer is part, or the declared
	 * type of the variable which it is being used to initialize.
	 * 
	 * @return the type of this initializer
	 * @see #setType(ObjectType)
	 */
	ObjectType getType();

	/**
	 * Sets the type of this initializer. This method should only be called by
	 * an Analyzer.
	 * 
	 * @param type
	 *            the type of the thing being initialized
	 * @see #getType()
	 */
	void setType(ObjectType type);

	/**
	 * <p>
	 * Returns the compound literal object obtained by analyzing the tree rooted
	 * at this compound initializer node. The compound literal object provides
	 * an abstract view of the literal which is very simple and easy to use.
	 * This method will return <code>null</code> before the analysis has been
	 * carried out. The analyzer will set the literal object value using method
	 * {@link #setLiteralObject(CompoundLiteralObject)}.
	 * </p>
	 * 
	 * <p>
	 * Note that for a CIVL-C Cartestian domain literal, this will always return
	 * <code>null</code>, as there is no compound object associated to the
	 * construct, only a type.
	 * </p>
	 * 
	 * @return the compound literal object or null
	 */
	CompoundLiteralObject getLiteralObject();

	/**
	 * Sets the value of this compound initializer to the given object.
	 * 
	 * @param object
	 *            the value of this compound initializer
	 * @see #getLiteralObject()
	 */
	void setLiteralObject(CompoundLiteralObject object);

}
