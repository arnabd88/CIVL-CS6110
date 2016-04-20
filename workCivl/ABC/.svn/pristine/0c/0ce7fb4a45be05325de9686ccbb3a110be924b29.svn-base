package edu.udel.cis.vsl.abc.analysis.entity;

import java.util.ArrayList;

import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * A designation is specifies (or "designates") a point in a compound literal
 * object. It consists of a sequence of Navigators.
 * 
 * The points in a compound literal object form a rooted tree. The root is a
 * reference to the whole object. The children of the root are references to the
 * immediate sub-objects, and so on. The leaves in this are references to simple
 * literals which wrap expressions. The edges in the tree correspond to
 * Navigators. A Designation specifies a path in the tree starting from the
 * root.
 * 
 * @see {@link Navigator}
 * 
 * @author siegel
 * 
 */
public class Designation {

	private LiteralTypeNode rootType;

	private ArrayList<Navigator> navigators;

	Designation(LiteralTypeNode rootType, ArrayList<Navigator> navigators) {
		this.rootType = rootType;
		this.navigators = navigators;
	}

	public Designation(LiteralTypeNode rootType) {
		this(rootType, new ArrayList<Navigator>());
	}

	/**
	 * Returns the number of naviagators in the sequence which comprises this
	 * designation.
	 * 
	 * @return the number of navigators
	 */
	public int length() {
		return navigators.size();
	}

	public Navigator get(int index) {
		return navigators.get(index);
	}

	public void add(Navigator navigator) {
		navigators.add(navigator);
	}

	public void removeLast() {
		navigators.remove(navigators.size() - 1);
	}

	public void append(Designation that) {
		navigators.addAll(that.navigators);
	}

	/**
	 * Modifies this designation so that it refers to the next point in the
	 * compound literal tree in depth-first-search order.
	 * 
	 * @throws SyntaxException
	 */
	public void increment(LiteralTypeNode typeNode) throws SyntaxException {
		LiteralTypeNode subType = getDesignatedType().parent();
		int length = navigators.size();

		while (true) {
			Navigator last = navigators.get(length - 1);
			int newIndex = last.getIndex() + 1;

			if (subType.hasFixedLength() && newIndex >= subType.length()) {
				// backtrack
				if (length == 0)
					throw new ABCRuntimeException("unreachable");
				removeLast();
				subType = subType.parent();
				length--;
			} else {
				navigators.set(length - 1,
						new Navigator(newIndex, last.getSource()));
				return;
			}
		}
	}

	@Override
	public String toString() {
		String result = "";

		for (Navigator n : navigators)
			result += n;
		return result;
	}

	public LiteralTypeNode getRootType() {
		return rootType;
	}

	public LiteralTypeNode getDesignatedType() throws SyntaxException {
		LiteralTypeNode result = rootType;

		for (Navigator navigator : navigators) {
			int index = navigator.getIndex();

			if (result instanceof LiteralArrayTypeNode) {
				result = ((LiteralArrayTypeNode) result).getElementNode();
			} else if (result instanceof LiteralStructOrUnionTypeNode) {
				LiteralStructOrUnionTypeNode sunode = (LiteralStructOrUnionTypeNode) result;
				int length = sunode.length();

				if (index < 0 || index >= length)
					throw new SyntaxException(
							"Member index out of range for struct or union",
							navigator.getSource());
				result = sunode.getMemberNode(index);
			} else {
				throw new SyntaxException(
						"Navigator in compound literal/initializer is incompatible with type",
						navigator.getSource());
			}
		}
		return result;
	}

	private int distanceToScalar(ObjectType type) {
		int result = 0;

		while (true) {
			switch (type.kind()) {
			case ARRAY:
				result++;
				type = ((ArrayType) type).getElementType();
				break;
			case STRUCTURE_OR_UNION:
				result++;
				type = ((StructureOrUnionType) type).getField(0).getType();
				break;
			default:
				return result;
			}
		}
	}

	public void descendToType(ObjectType type, Source source)
			throws SyntaxException {
		LiteralTypeNode subtype = getDesignatedType();
		int upperDistance = distanceToScalar(subtype.getType());
		int lowerDistance = distanceToScalar(type);
		int difference = upperDistance - lowerDistance;

		if (difference < 0)
			throw new SyntaxException("Literal member has incompatible type",
					source);
		for (int i = 0; i < difference; i++) {
			if (subtype instanceof LiteralArrayTypeNode) {
				subtype = ((LiteralArrayTypeNode) subtype).getElementNode();
				navigators.add(new Navigator(0, source));
			} else if (subtype instanceof LiteralStructOrUnionTypeNode) {
				subtype = ((LiteralStructOrUnionTypeNode) subtype)
						.getMemberNode(0);
				navigators.add(new Navigator(0, source));
			} else
				throw new ABCRuntimeException(
						"Unreachable: subtype not array or struct/union: "
								+ subtype);
		}
	}

}
