package edu.udel.cis.vsl.abc.analysis.entity;

import java.util.ArrayList;
import java.util.NoSuchElementException;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.CompoundLiteralObject;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.LiteralObject;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;

/**
 * Implementation of CompoundLiteral that provides additional functionality for
 * modifications.
 * 
 * While reads that go beyond the bounds of the inferred type will throw an
 * exception (as specified in CompoundLiteral), write that go beyond the bounds
 * of the inferred type will either throw an exception (if the write violates a
 * bound in the declared type) or succeed and extend the bounds of the inffered
 * type (otherwise).
 * 
 * In any case, the inferred type will be kept in sync with the writes.
 * 
 * This class maintains the following invariant: the inferred type will be
 * consistent with the inferred types of the members. I.e., if the inferred type
 * is an array type with element type T, all of the (non-null) members will have
 * inferred type T. If the inferred type is a struct or union type with member
 * types (T_i), the i-th member (if not null) will have inferred type T_i.
 * Similar remarks hold for the declared type.
 * 
 * @author siegel
 * 
 */
public class CommonCompoundLiteralObject extends CommonLiteralObject implements
		CompoundLiteralObject {

	/**
	 * The members of this compound object. Entires may be null.
	 */
	private ArrayList<LiteralObject> elements = new ArrayList<>();

	public CommonCompoundLiteralObject(LiteralTypeNode ltNode,
			ASTNode sourceNode) {
		super(ltNode, sourceNode);
	}

	@Override
	public int size() {
		return elements.size();
	}

	@Override
	public LiteralObject get(int index) {
		return index >= elements.size() ? null : elements.get(index);
	}

	@Override
	public String toString() {
		return elements.toString();
	}

	/**
	 * Assumes navigator respects all bounds.
	 * 
	 * @param navigator
	 * @return
	 */
	public LiteralObject get(Designation designation) {
		int length = designation.length();
		LiteralObject result = this;

		for (int i = 0; i < length; i++) {
			Navigator navigator = designation.get(i);
			int index = navigator.getIndex();

			assert result != null;
			if (result instanceof CommonCompoundLiteralObject) {
				result = ((CommonCompoundLiteralObject) result).get(index);
				if (result == null)
					break;
			} else
				throw new NoSuchElementException();
		}
		return result;
	}

	public void setElement(int index, LiteralObject value) {
		LiteralTypeNode typeNode = getTypeNode();
		int length = typeNode.length();

		if (typeNode.hasFixedLength() && index >= length)
			throw new ABCRuntimeException("Exceeded object bound: index="
					+ index + ", length=" + length);
		while (index >= elements.size())
			elements.add(null);
		elements.set(index, value);
		// the literal value was created using the same type nodes
		// as those in this literal, therefore those nodes are already
		// up to date. so it is only this length that has to be updated
		if (elements.size() > length)
			((LiteralArrayTypeNode) typeNode).setLength(elements.size());
	}

	private void set(Designation designation, int desStart, LiteralObject value) {
		int deslen = designation.length() - desStart;
		int index0 = designation.get(desStart).getIndex();

		assert deslen > 0;
		if (deslen == 1) {
			setElement(index0, value);
		} else {
			CommonCompoundLiteralObject r = (CommonCompoundLiteralObject) get(index0);

			if (r == null) {
				r = new CommonCompoundLiteralObject(getTypeNode().getChild(
						index0), getSourceNode());
				setElement(index0, r);
			}
			r.set(designation, desStart + 1, value);
		}
	}

	/**
	 * Sets the sub-object at the designated position to value. Updates type
	 * nodes as necessary.
	 * 
	 * @param designation
	 * @param value
	 */
	public void set(Designation designation, LiteralObject value) {
		if (designation.length() == 0)
			throw new ABCRuntimeException("saw empty designation in set");
		set(designation, 0, value);
	}

}
