package edu.udel.cis.vsl.civl.gui;

import java.awt.Dimension;

import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTree;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeSelectionModel;

import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.immutable.ImmutableDynamicScope;
import edu.udel.cis.vsl.civl.transition.Transition;

public class CIVL_GUI extends JFrame {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private JTree tree;
	private JPanel textView;
	private JScrollPane treeView;
	private JPanel left, right;

	/**
	 * Constructor for the CIVL GUI
	 */
	public CIVL_GUI(State[] states, Transition[] transitions) {

		// initialize components of this CIVL GUI
		initComponents(states, transitions);

		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		// Make the GUI visible
		pack();
		setVisible(true);

	}

	/**
	 * Initialize the components of the CIVL GUI
	 * 
	 * @param state
	 * @param manager
	 */
	private void initComponents(State[] states, Transition[] transitions) {

		// //Make the GUI split vertically down the middle
		// setLayout(new BoxLayout(this, BoxLayout.LINE_AXIS));

		// Specify panels for the left and right half of the GUI
		// left = new JPanel();
		right = new JPanel();
		// draw the transitions
		textView = drawTransitions(states, transitions);
		// draw the state
		treeView = drawState(states[0]);

		// Add the views to the panels
		left.add(textView);
		right.add(treeView);

		// Add the panels to the Frame
		add(left);
		add(right);

	}

	/**
	 * Draws the ImmutableState object to a JTree of nodes, and then makes a
	 * pane with that tree and returns the view of that tree
	 * 
	 * @param state
	 * @return JScrollPane
	 */
	public JScrollPane drawState(State state) {

		int numDyscopes = state.numScopes();
		ImmutableDynamicScope[] dyscopes = new ImmutableDynamicScope[numDyscopes];
		for (int i = 0; i < state.numScopes(); i++) {
			dyscopes[i] = (ImmutableDynamicScope) state.getScope(i);
		}

		DefaultMutableTreeNode[] treeNodes = new DefaultMutableTreeNode[dyscopes.length];

		// Make an array of nodes corresponding to the dyscopes of the state
		for (int i = 0; i < dyscopes.length; i++) {
			treeNodes[i] = new DefaultMutableTreeNode(dyscopes[i].toString());
		}

		for (int i = 0; i < dyscopes.length; i++) {
			int parentID = state.getParentId(i);

			if (parentID != -1) {
				treeNodes[parentID].add(treeNodes[i]);
			}
		}
		DefaultMutableTreeNode procs = new DefaultMutableTreeNode(
				"Process States");
		DefaultMutableTreeNode procNode;
		String output = "";
		for (ProcessState p : state.getProcessStates()) {
			for (StackEntry s : p.getStackEntries()) {
				output += s.toString() + "\n";
			}
			procNode = new DefaultMutableTreeNode(output);
			procs.add(procNode);
		}

		DefaultMutableTreeNode top = new DefaultMutableTreeNode("State: "
				+ state.getCanonicId());
		DefaultMutableTreeNode dy = new DefaultMutableTreeNode("Dyscopes");
		dy.add(treeNodes[0]);
		top.add(dy);
		top.add(procs);
		// Create a tree that allows one selection at a time.
		tree = new JTree(top);
		tree.getSelectionModel().setSelectionMode(
				TreeSelectionModel.SINGLE_TREE_SELECTION);

		// Create the view of the tree and set their preferred size
		JScrollPane treeView = new JScrollPane(tree);
		treeView.setPreferredSize(new Dimension(300, 500));
		return treeView;
	}

	/**
	 * Draw the transitions of the execution of the program to a JTextPane
	 * 
	 * @param manager
	 * @return JTextPane
	 */
	public JPanel drawTransitions(State[] states, Transition[] transitions) {
		JLabel output = new JLabel();
		JPanel result = new JPanel();
		for (int i = 0; i < states.length; i++) {
			String newOutput = output.getText() + "<p>" + states[i].toString()
					+ " : " + transitions.toString();
			output.setText(newOutput);
		}
		result.add(output);
		return result;
	}

	/**
	 * This method will redraw a new state once it is clicked in the transitions
	 * TODO:Implement
	 */
	// public void stateClickedEvent() {
	// right.removeAll();
	// treeView = drawState(newStateClicked);
	// right.add(treeView);
	// right.repaint();
	// }

}
