/**
 * 
 */
package edu.udel.cis.vsl.abc.front.fortran.ptree;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.antlr.runtime.Token;
import org.antlr.runtime.tree.CommonTree;

import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.front.IF.ParseTree;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSequence;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

/**
 * @author Wenhao Wu
 *
 */
public class FortranTree implements ParseTree {

	private Language language = Language.FORTRAN77;

	private static boolean TEXT_ONLY = false;

	private static long COUNT = 0;

	private long id;

	private int index;

	private int childIndex;

	private CivlcToken[] cTokens;

	private int rule;

	private int type;

	private String nodeName;

	private FortranTree parent;

	private ArrayList<FortranTree> children;

	// Constructor
	public FortranTree(String name, CivlcToken... cTokens) {
		id = COUNT++;
		index = -1;
		childIndex = -1;
		this.cTokens = cTokens;
		this.type = -1;
		rule = Integer.MIN_VALUE;
		this.nodeName = name;
		parent = null;
		children = new ArrayList<FortranTree>();
	}

	public FortranTree(int rule, String name, CivlcToken... cTokens) {
		id = COUNT++;
		index = -1;
		childIndex = -1;
		this.cTokens = cTokens;
		this.type = -1;
		this.rule = rule;
		this.nodeName = name;
		parent = null;
		children = new ArrayList<FortranTree>();
	}

	public FortranTree(int rule, String name, int type, CivlcToken... cTokens) {
		id = COUNT++;
		index = -1;
		childIndex = -1;
		this.cTokens = cTokens;
		this.type = type;
		this.rule = rule;
		this.nodeName = name;
		parent = null;
		children = new ArrayList<FortranTree>();
	}

	// Functions:
	public long COUNT() {
		return COUNT;
	}

	public long id() {
		return id;
	}

	public int index() {
		return index;
	}

	public void setIndex(int index) {
		this.index = index;
	}

	public int childIndex() {
		return childIndex;
	}

	public void setChildIndex(int newIndex) {
		childIndex = newIndex;
	}

	public CivlcToken[] cTokens() {
		return cTokens;
	}

	public void setTokens(CivlcToken... cTokens) {
		this.cTokens = cTokens;
	}

	public int type() {
		return type;
	}

	public int rule() {
		return rule;
	}

	public void setRule(int rule) {
		this.rule = rule;
	}

	public String nodeName() {
		return nodeName;
	}

	public void setNodeName(String nodeName) {
		this.nodeName = nodeName;
	}

	public FortranTree parent() {
		return parent;
	}

	public void setParent(FortranTree parent) {
		this.parent = parent;
	}

	public Iterable<FortranTree> children() {
		return children;
	}

	public int numChildren() {
		return children.size();
	}

	public void addChild(int index, FortranTree newChild) {
		assert newChild != null;
		assert newChild.parent == null;
		assert index >= 0 && index <= children.size();

		newChild.parent = this;
		newChild.childIndex = index;
		children.add(index, newChild);
		index++;
		while (index < children.size()) {
			children.get(index).childIndex++;
			index++;
		}
	}

	public int addChild(FortranTree newChild) {
		assert newChild != null;
		assert newChild.parent == null;

		int index = children.size();

		newChild.parent = this;
		newChild.childIndex = index;
		children.add(newChild);

		return index;
	}

	public FortranTree setChild(int index, FortranTree newChild) {
		assert newChild != null;
		assert newChild.parent == null;

		FortranTree oldChild = null;
		int numChildren = children.size();

		assert index >= 0 && index < numChildren;
		index = Math.min(index, numChildren - 1);
		index = Math.max(index, 0);
		oldChild = children.get(index);
		oldChild.parent = null;
		oldChild.childIndex = -1;
		newChild.parent = this;
		newChild.childIndex = index;
		children.set(index, newChild);
		return oldChild;
	}

	public void insertChildrenAt(int start,
			List<? extends FortranTree> newChildren) {
		int i = 0;
		int oldSize = children.size();
		int numNewChildren = newChildren.size();
		int newSize = oldSize + numNewChildren;

		assert start >= 0 && start <= oldSize;
		children.addAll(start, newChildren);
		for (i = start; i < start + numNewChildren; i++) {
			FortranTree newChild = children.get(i);

			assert newChild != null;
			assert newChild.parent == null;
			newChild.parent = this;
			newChild.childIndex = i;
		}
		for (; i < newSize; i++) {
			FortranTree child = children.get(i);

			assert child != null;
			child.childIndex = i;
		}
	}

	public void remove() {
		if (children != null)
			parent.removeChild(childIndex);
	}

	public FortranTree removeChild(int index) {
		int numChildren = children.size();
		FortranTree oldChild = null;

		assert index >= 0 && index < numChildren;
		oldChild = children.get(index);
		assert oldChild != null;
		oldChild.parent = null;
		oldChild.childIndex = -1;
		children.remove(index);
		return oldChild;
	}

	public FortranTree getChildByIndex(int index) {
		return children.get(index);
	}

	public String toString() {
		String result = "";

		FortranTree temp = this;
		while (temp.parent != null) {
			temp = temp.parent;
			result += "| ";
		}

		result += "{";
		if (parent == null) {
			result += "Root";
		} else if (parent.childIndex < 0) {
			// result += "R";
			result += "[" + childIndex + "]";
		} else {
			// result += parent.childIndex;
			result += "[" + childIndex + "]";
			// result += parent.nodeKind;
		}
		result += ": ";
		//result += this.id;
		result += "[";
		if(rule != Integer.MIN_VALUE) result += " " + rule + " ";
		result += nodeName + "]";
		if (cTokens != null && cTokens.length > 0) {
			result += "<";
			for (Token t : cTokens) {
				if (t != null) {
					if (TEXT_ONLY) {
						result += t.getText();
					} else {
						result += t.toString();
						// result += "{" + t.getInputStream().getSourceName() +
						// "}";
					}
				} else {
					result += "null";
				}
			}
			result += ">";
		}
		result += "}\n";
		if (numChildren() > 0) {
			for (FortranTree i : children) {
				if (i != null)
					result += i.toString();
			}
		}
		return result;
	}

	public void printNode() {
		System.out.print(this.toString());
	}

	@Override
	public Language getLanguage() {
		return language;
	}

	@Override
	public CommonTree getRoot() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Source source(CommonTree tree) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<SourceFile> getSourceFiles() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SyntaxException newSyntaxException(String message, CommonTree tree) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public CivlcTokenSequence getTokenSourceProducer(CommonTree tokenListNode) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public CivlcTokenSource getCivlcTokenSource() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public TokenFactory getTokenFactory() {
		// TODO Auto-generated method stub
		return null;
	}
}
