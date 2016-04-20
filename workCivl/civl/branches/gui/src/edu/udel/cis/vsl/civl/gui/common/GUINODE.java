package edu.udel.cis.vsl.civl.gui.common;

import javax.swing.tree.DefaultMutableTreeNode;

/**
 * A GUINODE will be used only for the root nodes of any tree in this GUI. The
 * reason a GUINODE is used is to be able to collapse all nodes when the root
 * node is clicked
 */
public class GUINODE extends DefaultMutableTreeNode {
	
	public enum GUINodeKind{
		ROOT_NODE, TRANSITION_NODE, STATE_NODE,STEP_NODE
	}
	
//	/**
//	 * Only used for GUINODE (see Private Classes) to indicate that it is the
//	 * root of the tree. Used by the selection listener so that when clicked the
//	 * tree will collapse the children of the root node
//	 */
//	public static final int ROOT_NODE = 0;
//
//	/**
//	 * Only used for TransitionNode (see Private Classes) to indicate that it is
//	 * a node representing a compound transition. It is used by the tree
//	 * selection listener so that when clicked it will display the transition's
//	 * tree on the right side of the GUI
//	 */
//	public static final int TRANSITION_NODE = 1;
//
//	/**
//	 * Only used for StateNode (see Private Classes) to indicate that it is a
//	 * node representing a State. It is used by the tree selection listener so
//	 * that when clicked it will display the state tree on the right side of the
//	 * GUI
//	 */
//	public static final int STATE_NODE = 2;
//
//	/**
//	 * Only used for StepNode (see Private Classes) to indicate that it is a
//	 * node representing a step. It is used by the three selection listener so
//	 * that when clicked it will display the target state of the step as a tree
//	 * on the right side of the GUI
//	 */
//	protected static final int STEP_NODE = 3;
	static final long serialVersionUID = 1L;
	private boolean collapsed;

	public GUINODE(String name) {
		super(name);
		collapsed = true;
	}

	public void setCollapsed(boolean value) {
		collapsed = value;
	}

	public GUINodeKind getKind() {
		return GUINodeKind.ROOT_NODE;
	}

	public boolean isCollapsed() {
		return collapsed;
	}
	
	

}