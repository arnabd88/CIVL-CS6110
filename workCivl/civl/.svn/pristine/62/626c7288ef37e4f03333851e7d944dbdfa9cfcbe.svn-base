package edu.udel.cis.vsl.civl.gui.common;

import javax.swing.tree.DefaultMutableTreeNode;

/**
 * A DyscopeNode is a node in the stateTree that keeps track of the children of
 * the current dyscope. It is used so that all children of the current dyscope
 * can be added to a folder called children dyscopes within this dyscope in the
 * tree representation of a state
 */
public class DyscopeNode extends DefaultMutableTreeNode {
	private static final long serialVersionUID = 1L;
	private DefaultMutableTreeNode children;

	public DyscopeNode(String name) {
		super(name);
	}

	public void setChildNode(DefaultMutableTreeNode n) {
		children = n;
	}

	public DefaultMutableTreeNode getChildren() {
		return children;
	}
}