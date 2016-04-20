package edu.udel.cis.vsl.abc.ast.node.common;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTException;
import edu.udel.cis.vsl.abc.ast.IF.ASTs;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject.DiffKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.Scope;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.AttributeKey;
import edu.udel.cis.vsl.abc.ast.node.IF.NodePredicate;
import edu.udel.cis.vsl.abc.token.IF.Source;

public abstract class CommonASTNode implements ASTNode {

	private static long instanceCount = 0;

	private long instanceId;

	private int id = -1;

	private AST owner = null;

	private ASTNode parent;

	private int childIndex = -1;

	private ArrayList<ASTNode> children;

	private Source source;

	private ArrayList<Object> attributes = null;

	private Scope scope;

	private void checkModifiable() {
		if (owner != null)
			throw new ASTException(
					"Cannot modify node until released from AST:\n" + this);
	}

	protected static <T extends ASTNode> T duplicate(T node) {
		if (node == null)
			return null;
		else {
			@SuppressWarnings("unchecked")
			T copy = (T) node.copy();

			return copy;
		}
	}

	protected static <T extends ASTNode> List<T> duplicate(List<T> list) {
		LinkedList<T> newList = new LinkedList<T>();

		for (T node : list)
			newList.add(duplicate(node));
		return newList;
	}

	public CommonASTNode(Source source,
			Iterator<? extends ASTNode> childIterator) {
		int childCount = 0;

		instanceId = instanceCount++;
		this.source = source;
		children = new ArrayList<ASTNode>();
		while (childIterator.hasNext()) {
			CommonASTNode child = (CommonASTNode) childIterator.next();

			children.add(child);
			if (child != null) {
				if (child.parent() != null)
					throw new ASTException("Cannot make\n" + child
							+ "\na child of node\n" + this
							+ "\nbecause it is already a child of\n"
							+ child.parent());
				child.parent = this;
				child.childIndex = childCount;
			}
			childCount++;
		}
	}

	public CommonASTNode(Source source,
			Iterable<? extends ASTNode> childCollection) {
		this(source, childCollection.iterator());
	}

	public CommonASTNode(Source source, ASTNode[] childArray) {
		this(source, Arrays.asList(childArray).iterator());
	}

	public CommonASTNode(Source source) {
		this.source = source;
		children = new ArrayList<ASTNode>();
	}

	public CommonASTNode(Source source, ASTNode child) {
		this(source, new ASTNode[] { child });
	}

	public CommonASTNode(Source source, ASTNode child0, ASTNode child1) {
		this(source, new ASTNode[] { child0, child1 });
	}

	public CommonASTNode(Source source, ASTNode child0, ASTNode child1,
			ASTNode child2) {
		this(source, new ASTNode[] { child0, child1, child2 });
	}

	public CommonASTNode(Source source, ASTNode child0, ASTNode child1,
			ASTNode child2, ASTNode child3) {
		this(source, new ASTNode[] { child0, child1, child2, child3 });
	}

	@Override
	public int id() {
		return id;
	}

	@Override
	public void setId(int id) {
		this.id = id;
	}

	@Override
	public void setOwner(AST owner) {
		this.owner = owner;
	}

	@Override
	public AST getOwner() {
		return owner;
	}

	@Override
	public ASTNode parent() {
		return parent;
	}

	@Override
	public int childIndex() {
		return childIndex;
	}

	@Override
	public int numChildren() {
		return children.size();
	}

	@Override
	public ASTNode child(int index) throws NoSuchElementException {
		return children.get(index);
	}

	@Override
	public Iterable<ASTNode> children() {
		return children;
	}

	@Override
	public void print(String prefix, PrintStream out, boolean includeSource) {
		out.print(prefix);
		if (childIndex >= 0)
			out.print(childIndex);
		out.print("[" + id + "]: ");
		printBody(out);
		if (scope != null) {
			out.print(" (scope " + scope.getId() + ")");
		} else {
			out.print(" (scope UNKNOWN)");
		}
		if (includeSource && source != null) {
			out.println();
			out.print(prefix + "| source: " + source.getSummary(false));
		}
		printExtras(prefix + "| ", out);
	}

	protected abstract void printBody(PrintStream out);

	protected void printExtras(String prefix, PrintStream out) {

	}

	@Override
	public Object getAttribute(AttributeKey key) {
		if (attributes == null)
			return null;
		else {
			int id = ((CommonAttributeKey) key).getId();

			if (id >= attributes.size())
				return null;
			return attributes.get(id);
		}
	}

	@Override
	public void setAttribute(AttributeKey key, Object value) {
		int id = ((CommonAttributeKey) key).getId();
		Class<? extends Object> attributeClass = key.getAttributeClass();
		int size;

		if (!(attributeClass.isInstance(value)))
			throw new IllegalArgumentException("Attribute "
					+ ((CommonAttributeKey) key).getAttributeName()
					+ " has type  " + attributeClass + " but given " + value
					+ " of type " + value.getClass());
		if (attributes == null)
			attributes = new ArrayList<Object>();
		size = attributes.size();
		while (id >= size) {
			attributes.add(null);
			size++;
		}
		attributes.set(id, value);
	}

	@Override
	public Source getSource() {
		return source;
	}

	protected int addChild(ASTNode child) {
		int index = numChildren();

		checkModifiable();
		children.add(child);
		if (child != null) {
			if (child.parent() != null)
				throw new ASTException("Cannot make\n" + child
						+ "\na child of node\n" + this
						+ "\nbecause it is already a child of\n"
						+ child.parent());
			((CommonASTNode) child).parent = this;
			((CommonASTNode) child).childIndex = index;
		}
		return index;
	}

	@Override
	public ASTNode setChild(int index, ASTNode child) {
		int numChildren = children.size();
		ASTNode oldChild;

		checkModifiable();
		if (index < 0)
			throw new ASTException("Negative index " + index
					+ " used in setChild on " + this);
		if (child != null && child.parent() != null)
			throw new ASTException("Cannot make\n" + child
					+ "\na child of node\n" + this
					+ "\nbecause it is already a child of\n" + child.parent());
		while (index >= numChildren) {
			children.add(null);
			numChildren++;
		}
		oldChild = children.get(index);
		if (oldChild != null) {
			((CommonASTNode) oldChild).parent = null;
			((CommonASTNode) oldChild).childIndex = -1;
		}
		children.set(index, child);
		if (child != null) {
			((CommonASTNode) child).parent = this;
			((CommonASTNode) child).childIndex = index;
		}
		return oldChild;
	}

	/**
	 * Insert a sequence of nodes into the child list of this node.
	 * 
	 * @param index
	 *            an integer in [0,numChildren]
	 * @param list
	 *            a non-null list of free nodes, any of which may be null
	 */
	protected void insertChildrenAt(int index, List<? extends ASTNode> list) {
		int oldSize = children.size();
		int listSize = list.size();
		int newSize = oldSize + listSize;

		checkModifiable();
		if (index < 0)
			throw new ASTException("Negative index " + index
					+ " used in insertChildren on " + this);
		if (index > oldSize)
			throw new ASTException("Index " + index + " exceeds size "
					+ oldSize + " in insertChildren on " + this);
		children.addAll(index, list);
		for (int i = index; i < index + listSize; i++) {
			ASTNode child = children.get(i);

			if (child != null) {
				if (child.parent() != null)
					throw new ASTException("Cannot make\n" + child
							+ "\na child of node\n" + this
							+ "\nbecause it is already a child of\n"
							+ child.parent());
				((CommonASTNode) child).parent = this;
				((CommonASTNode) child).childIndex = i;
			}
		}
		for (int i = index + listSize; i < newSize; i++) {
			ASTNode child = children.get(i);

			if (child != null) {
				((CommonASTNode) child).childIndex = i;
			}
		}
	}

	@Override
	public ASTNode removeChild(int index) {
		int numChildren = children.size();
		ASTNode oldChild;

		checkModifiable();
		if (index < 0 || index >= numChildren)
			throw new ASTException("Index " + index + " out of range [0,"
					+ (numChildren - 1) + "]:" + this);
		oldChild = children.get(index);
		if (oldChild != null) {
			((CommonASTNode) oldChild).parent = null;
			((CommonASTNode) oldChild).childIndex = -1;
		}
		children.set(index, null);
		return oldChild;
	}

	@Override
	public void remove() {
		if (parent != null) {
			parent.removeChild(childIndex);
		}
	}

	/**
	 * Default implementation, for non-sequence nodes. Must be overridden for
	 * sequence nodes.
	 */
	@Override
	public void keepOnly(NodePredicate keep) {
		int numChildren = numChildren();

		checkModifiable();
		for (int i = 0; i < numChildren; i++) {
			ASTNode child = child(i);

			if (child != null) {
				if (keep.holds(child)) {
					// // add the file name to the file name map
					// TokenUtils.addFileName(TokenUtils.getShortFilename(this
					// .getSource().getFirstToken(), false));
					child.keepOnly(keep);
				} else
					removeChild(i);
			}
		}
	}

	/**
	 * Removes children and shifts down to remove the gaps; also applies
	 * keepOnly to children not removed. This method is meant to be applied to
	 * sequence nodes.
	 * 
	 * @param keep
	 *            a node predicate telling which nodes to keep
	 */
	protected void keepOnlyAndShift(NodePredicate keep) {
		int numChildren = numChildren();
		int count = 0; // number of children to keep

		checkModifiable();
		for (int i = 0; i < numChildren; i++) {
			ASTNode child = child(i);

			if (child != null) {
				if (keep.holds(child)) {
					child.keepOnly(keep);
					if (count < i) {
						children.set(count, child);
						((CommonASTNode) child).childIndex = count;
					}
					count++;
				} else
					removeChild(i);
			}
		}
		children.subList(count, numChildren).clear();
	}

	@Override
	public void setScope(Scope scope) {
		this.scope = scope;
	}

	@Override
	public Scope getScope() {
		return scope;
	}

	@Override
	public boolean equiv(ASTNode that) {
		return diff(that) == null;
	}

	@Override
	public DifferenceObject diff(ASTNode that) {
		DifferenceObject diff;

		if (that == null)
			return new DifferenceObject(this, false);
		diff = diffWork(that);
		if (diff != null)
			return diff;
		if (this.numChildren() != that.numChildren())
			return new DifferenceObject(this, that, DiffKind.NUM_CHILDREN);
		for (int i = 0; i < this.numChildren(); i++) {
			ASTNode thisChild = this.child(i), thatChild = that.child(i);

			if (thisChild != null) {
				diff = thisChild.diff(thatChild);
				if (diff != null)
					return diff;
			} else if (thatChild != null)
				return new DifferenceObject(that, true);
		}
		return null;
	}

	protected DifferenceObject diffWork(ASTNode that) {
		if (this.nodeKind() == that.nodeKind())
			return null;
		return new DifferenceObject(this, that);
	}

	@Override
	public String toString() {
		return "Node[" + id + ", " + instanceId + ", "
				+ source.getSummary(false) + "]";
	}

	@Override
	public ASTNode nextDFS() {
		// look for a child...
		for (ASTNode child : children) {
			if (child != null)
				return child;
		}
		// if no child, backtrack...
		{
			ASTNode node = this;

			while (true) {
				int index = node.childIndex();

				node = node.parent();
				if (node == null)
					return null;
				else {
					int numChildren = node.numChildren();

					for (int i = index + 1; i < numChildren; i++) {
						ASTNode child = node.child(i);

						if (child != null)
							return child;
					}
				}
			}
		}
	}

	@Override
	public void prettyPrint(PrintStream out) {
		ASTs.prettyPrint(this, out);
	}

	@Override
	public StringBuffer prettyRepresentation() {
		// TODO there has to be a better way to do this that does
		// not involve File I/O
		StringBuffer result = new StringBuffer();

		try {
			File temp = File.createTempFile("tmp" + System.currentTimeMillis(),
					".data");
			PrintStream tmpOut = new PrintStream(temp);
			FileReader fileReader;
			BufferedReader bufferReader;
			String line;
			boolean first = true;

			ASTs.prettyPrint(this, tmpOut);
			fileReader = new FileReader(temp);
			bufferReader = new BufferedReader(fileReader);
			line = bufferReader.readLine();
			while (line != null) {
				if (first)
					first = false;
				else
					result.append("\n");
				result.append(line);
				line = bufferReader.readLine();
			}
			bufferReader.close();
			fileReader.close();
			tmpOut.close();
			temp.delete();
		} catch (IOException e) {
			result.append(this.toString());
		}
		return result;
	}
}
