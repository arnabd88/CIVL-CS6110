package edu.udel.cis.vsl.civl.gui.IF;

import java.awt.Dimension;
import java.util.Enumeration;

import javax.swing.JFrame;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTree;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeSelectionModel;

import edu.udel.cis.vsl.civl.gui.common.DyscopeNode;
import edu.udel.cis.vsl.civl.gui.common.GUINODE;
import edu.udel.cis.vsl.civl.gui.common.GUINODE.GUINodeKind;
import edu.udel.cis.vsl.civl.gui.common.StateNode;
import edu.udel.cis.vsl.civl.gui.common.StepNode;
import edu.udel.cis.vsl.civl.gui.common.TransitionNode;
import edu.udel.cis.vsl.civl.gui.common.TreeUtil;
import edu.udel.cis.vsl.civl.kripke.IF.AtomicStep;
import edu.udel.cis.vsl.civl.kripke.IF.TraceStep;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.semantics.IF.Transition;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.civl.state.IF.ProcessState;
import edu.udel.cis.vsl.civl.state.IF.StackEntry;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.gmc.Trace;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * This class is the graphical user interface for replaying attempted
 * verifications of CIVL-C programs
 * 
 * @author Ben Handanyan (bhandy)
 * 
 */
public class CIVL_GUI extends JFrame implements TreeSelectionListener {

	/* **************************** Final Fields *************************** */

	/**
	 * 
	 */
	static final long serialVersionUID = 1L;

	/* ************************** instance Fields ************************** */

	/**
	 * A tree that represents the transitions of the execution. It is drawn once
	 * when the GUI is created
	 */
	private JTree transitionTree;

	/**
	 * A tree that represents the selected state. States are drawn when the user
	 * selects a StateNode from the transitionTree on the left side of the GUI
	 */
	private JTree stateTree;

	/**
	 * The view currently displayed on the left side of the GUI. Only the
	 * transitionTree is ever drawn as the leftView
	 */
	private JScrollPane leftView;

	/**
	 * The view currently displayed on the right side of the GUI. This can be
	 * one of the following: stateTree, statementTree, or singleTransTree
	 */
	private JScrollPane rightView;

	/**
	 * The split pane that is added to the frame. It contains the leftView and
	 * the rightView
	 */
	private JSplitPane split;

	/**
	 * The list of transitions of the execution
	 */
	private TraceStep[] transitions;

	private State initState;

	/**
	 * The SymbolicAnalyzer of the system
	 */
	private SymbolicAnalyzer symbolicAnalyzer;

	/* **************************** Constructor **************************** */

	/**
	 * Constructs a new CIVL_GUI using a list of transitions
	 * 
	 * @param transitions
	 *            the array of transitions of the execution
	 */
	public CIVL_GUI(Trace<Transition, State> trace,
			SymbolicAnalyzer symbolicAnalyzer) {
		this.initState = trace.init();
		this.transitions = new TraceStep[trace.traceSteps().size()];
		trace.traceSteps().toArray(this.transitions);
		this.symbolicAnalyzer = symbolicAnalyzer;
		initComponents();
		setPreferredSize(new Dimension(1500, 1000));
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		pack();
		setVisible(true);
	}

	/* ************************** private Methods ************************** */

	/**
	 * Initialize the components of the CIVL GUI
	 */
	private void initComponents() {
		leftView = drawTransitions();
		rightView = drawState(this.initState);
		split = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, leftView, rightView);
		add(split); // To the CIVL_GUI JFrame
	}

	/**
	 * Draws the ImmutableState object to a JTree of nodes, and then makes a
	 * pane with that tree and returns the view of that tree
	 * 
	 * @param state
	 *            The State object that is drawn
	 * @return JScrollPane rightView with stateTree as its component with the
	 *         new state drawn
	 */
	private JScrollPane drawState(State state) {
		JTree oldTree = stateTree;
		int numDyscopes = state.numDyscopes();
		DynamicScope[] dyscopes = new DynamicScope[numDyscopes];

		// Create an array of dyscopes
		for (int i = 0; i < numDyscopes; i++) {
			dyscopes[i] = (DynamicScope) state.getDyscope(i);
		}

		// Make an array of nodes corresponding to the dyscopes of the state
		DyscopeNode[] treeNodes = new DyscopeNode[dyscopes.length];
		for (int i = 0; i < dyscopes.length; i++) {
			treeNodes[i] = new DyscopeNode("d" + dyscopes[i].identifier()
					+ " (static = " + dyscopes[i].lexicalScope().id() + ")",
					dyscopes[i]);
		}

		// For each dyscope
		// This comes first because Variables should be listed
		// before the current dyscopes children dyscopes
		for (int i = 0; i < dyscopes.length; i++) {
			addVariables(state, dyscopes[i], treeNodes[i]);
		}

		// The process states of the state
		DefaultMutableTreeNode procs = makeProcessStates(state);

		// Create the root node of the entire tree
		GUINODE top = new GUINODE(state.toString());
		top.setCollapsed(false);

		// Node for the dyscopes of the state
		DefaultMutableTreeNode dy = new DefaultMutableTreeNode("Dyscopes");

		// Add the dyscopes of the state to the dyscopes node
		for (int i = 0; i < treeNodes.length; i++) {
			dy.add(treeNodes[i]);
		}

		// Add the path condition to the root of the tree
		top.add(new DefaultMutableTreeNode("Path Condition: "
				+ state.getPathCondition().toString()));

		// Add the dyscopes to the root of the tree
		top.add(dy);

		// Add the process states to the root of the tree only if there are
		// stack entries to display
		top.add(procs);

		// Make the stateTree a JTree with the top as the root
		stateTree = new JTree(top);
		stateTree.getSelectionModel().setSelectionMode(
				TreeSelectionModel.SINGLE_TREE_SELECTION);

		setDyscopeNodeExpansion(oldTree, stateTree);

		// Listen for the root node to be selected
		// Collapse the root nodes children
		stateTree.addTreeSelectionListener(new TreeSelectionListener() {

			@Override
			public void valueChanged(TreeSelectionEvent e) {
				try {
					GUINODE n = (GUINODE) stateTree
							.getLastSelectedPathComponent();
					if (n == null)
						return;
					if (n.getKind() == GUINodeKind.ROOT_NODE) {
						if (!n.isCollapsed()) {
							for (int i = stateTree.getRowCount() - 1; i > 0; i--) {
								stateTree.collapseRow(i);
							}
							n.setCollapsed(true);
						} else {
							for (int i = 0; i < stateTree.getRowCount(); i++) {
								stateTree.expandRow(i);
							}
							n.setCollapsed(false);
						}
					}
				} catch (Exception ex) {
					return;
				}
			}
		});
		// Create the view of the tree and set its preferred size
		stateTree.setFocusable(false);
		rightView = new JScrollPane(stateTree);
		rightView.setPreferredSize(new Dimension(500, 500));
		return rightView;
	}

	/**
	 * Make the variable nodes for the given dynamic scope
	 * 
	 * @param state
	 *            The current state
	 * @param dScope
	 *            The given dynamic scope
	 * @return TreeNode
	 */
	private void addVariables(State state, DynamicScope dScope, DyscopeNode node) {
		if (dScope.numberOfValues() > 0) {

			// Keep track of which variable we're on with vid
			int vid = 0;

			// For each variable value of the dyscope
			for (SymbolicExpression s : dScope.getValues()) {
				Variable var = dScope.lexicalScope().variable(vid);
				String variableName = var.name().name();
				DefaultMutableTreeNode variableNode = new DefaultMutableTreeNode(
						variableName
								+ " = "
								+ symbolicAnalyzer.symbolicExpressionToString(
										var.getSource(), state, s));
				if (!(variableName == "__heap" && s.isNull())) {
					node.add(variableNode);
				}
				vid++;
			}
		}
	}

	// /**
	// * Display the dyscopes nodes in a tree pattern that resembles their
	// * parent/child relationship in the state
	// *
	// * @param state
	// * The current state
	// * @param index
	// * The current index
	// * @param treeNodes
	// * Array of dyscope nodes
	// */
	// private void arrangeChildDyscopes(State state, int index,
	// DyscopeNode[] treeNodes) {
	// // If the dyscope isn't the root dyscope (ie parentID != -1) add
	// // it's node to the node corresponding to it's parent dyscope
	// int parentID = state.getParentId(index);
	// if (parentID != -1) {
	// DefaultMutableTreeNode children;
	//
	// // If no children nodes have been added yet
	// if (treeNodes[parentID].getChildren() == null) {
	// children = new DefaultMutableTreeNode("Child Dyscopes");
	//
	// // Set the children node as the parent's child dyscope node
	// treeNodes[parentID].setChildNode(children);
	//
	// // Add the current node to the parent dyscopes children
	// // dyscopes node
	// treeNodes[parentID].getChildren().add(treeNodes[index]);
	//
	// // Add the children dyscopes node to the parent node
	// treeNodes[parentID].add(treeNodes[parentID].getChildren());
	// }
	// // Children nodes have already been created
	// else {
	// // Set the children to be the child dyscope node
	// children = treeNodes[parentID].getChildren();
	//
	// // Add the current node to the parent dyscopes children
	// // dyscopes node
	// treeNodes[parentID].getChildren().add(treeNodes[index]);
	// }
	// }
	// }

	/**
	 * Make the process state nodes for the given state
	 * 
	 * @param state
	 *            The current state
	 * @return TreeNode
	 */
	private DefaultMutableTreeNode makeProcessStates(State state) {
		// The process states of the state
		DefaultMutableTreeNode procs = new DefaultMutableTreeNode(
				"Process States");

		// Add the process states
		for (ProcessState p : state.getProcessStates()) {
			if (p != null) {
				DefaultMutableTreeNode proc = new DefaultMutableTreeNode("p"
						+ p.identifier() + " (id=" + p.getPid() + ")");
				for (StackEntry s : p.getStackEntries()) {
					DefaultMutableTreeNode stackEntryNode = new DefaultMutableTreeNode(
							s.toString());
					proc.add(stackEntryNode);
				}
				procs.add(proc);
			}
		}
		return procs;
	}

	/**
	 * Expand/collapse the nodes of the newTree to replicate the oldTree
	 * 
	 * TODO: Make expansion correspond to nodes and not rows in JTree
	 * 
	 * @param oldTree
	 * @param newTree
	 */
	private void setDyscopeNodeExpansion(JTree oldTree, JTree newTree) {
		// Expand all nodes by default if no oldTree
		if (oldTree == null) {
			for (int i = 0; i < newTree.getRowCount(); i++) {
				newTree.expandRow(i);
			}
		}
		// Restore expansion states for newTree
		else {
			// Iterate over the newTree's nodes
			for (@SuppressWarnings("unchecked")
			Enumeration<DefaultMutableTreeNode> e = ((DefaultMutableTreeNode) newTree
					.getModel().getRoot()).depthFirstEnumeration(); e
					.hasMoreElements();) {

				DefaultMutableTreeNode current = e.nextElement();
				int indexInOldTree = TreeUtil.containsNode(oldTree, current);

				// The oldTree contains the current node in newTree
				if (indexInOldTree != -1) {
					String expansionState = TreeUtil.getExpansionState(oldTree,
							indexInOldTree);
					TreeUtil.restoreExpanstionState(newTree,
							current.getLevel(), expansionState);
				}

				// The oldTree doesn't contain the current node
				// TODO: do this if oldTree contained the current node but has a
				// new node
				// as a child
				else {
					newTree.expandRow(current.getLevel());
					int currentRow = current.getLevel();
					int numChildren = current.getChildCount();
					for (int i = currentRow; i < currentRow + numChildren; i++) {
						newTree.expandRow(i);
					}
					// if (current.getChildCount() > 0) {
					// DefaultMutableTreeNode lastChild =
					// (DefaultMutableTreeNode) current.getLastChild();
					// DefaultMutableTreeNode parent = (DefaultMutableTreeNode)
					// lastChild
					// .getParent();
					// while (parent != null) {
					// newTree.expandRow(parent.getLevel());
					// parent = (DefaultMutableTreeNode) parent
					// .getParent();
					// }
					// }
					// else {
					// DefaultMutableTreeNode parent = (DefaultMutableTreeNode)
					// current
					// .getParent();
					// while (parent != null) {
					// newTree.expandRow(parent.getLevel());
					// parent = (DefaultMutableTreeNode) parent
					// .getParent();
					// }
					// }
				}
			}
		}
	}

	/**
	 * Draws the transitions array to a JTree of nodes, and then makes a pane
	 * with that tree and returns the view of that tree
	 * 
	 * @return JScrollPane leftView with transitionTree as its component with
	 *         the new state drawn
	 */
	private JScrollPane drawTransitions() {
		// The root of the tree
		GUINODE top = new GUINODE("Transitions");

		top.add(new StateNode("State: 0", this.initState));

		// For each transition
		for (int i = 0; i < transitions.length; i++) {
			if (transitions[i].getNumAtomicSteps() < 1) {
				break;
			}

			String transitionName = getTransitionName(transitions[i]);

			// Create the transition node
			TransitionNode transitionNode = new TransitionNode(transitionName,
					transitions[i]);

			// For each step in the transition
			for (AtomicStep s : transitions[i].getAtomicSteps()) {
				// Make the step node
				StepNode stepNode = makeStepNode(s);

				// Add the step to the transition
				transitionNode.add(stepNode);
			}

			// Add transition to the root node
			top.add(transitionNode);
		}

		// Make the transition tree with root node top
		transitionTree = new JTree(top);
		transitionTree.getSelectionModel().setSelectionMode(
				TreeSelectionModel.SINGLE_TREE_SELECTION);

		// CIVL_GUI is the listener for transition trees
		transitionTree.addTreeSelectionListener(this);

		// Create the view of the tree and set its preferred size
		leftView = new JScrollPane(transitionTree);
		leftView.setPreferredSize(new Dimension(600, 500));
		return leftView;
	}

	/**
	 * Returns a string of the transition name
	 * 
	 * @param transition
	 *            The current transition
	 * @return String
	 */
	private String getTransitionName(TraceStep transition) {
		// The name of the transition
		StringBuffer transitionName = new StringBuffer();
		transitionName.append("p" + transition.processIdentifier() + ": ");

		// Add step information to the name of the transition
		for (AtomicStep s : transition.getAtomicSteps()) {
			if (transitionName.length() < 50) {
				transitionName.append(s.getStatement().toString() + "; ");
			} else {
				transitionName.append("...");
				break;
			}
		}
		return transitionName.toString();
	}

	/**
	 * Make a step node out of the given step
	 * 
	 * @param step
	 *            The current step
	 * @return StepNode
	 */
	private StepNode makeStepNode(AtomicStep step) {
		Statement stmt = step.getStatement();

		String targetString;

		StepNode stepNode;
		if (stmt.target() != null) {
			targetString = String.valueOf(stmt.target().id());
		} else {
			targetString = "RET";
		}

		stepNode = new StepNode(stmt.source().id() + "->" + targetString + ": "
				+ stmt.toString(), step);
		return stepNode;

	}

	/* *************************** Private Classes *************************** */

	/* ***************** TreeSelectionListener Method ***************** */

	@Override
	public void valueChanged(TreeSelectionEvent e) {
		try {
			// Get the last selected node
			GUINODE n = (GUINODE) transitionTree.getLastSelectedPathComponent();
			// If no node selected do nothing
			if (n == null)
				return;

			// If node is a root node collapse all of the roots children
			if (n.getKind() == GUINodeKind.ROOT_NODE) {
				try {
					if (!n.isCollapsed()) {
						for (int i = transitionTree.getRowCount() - 1; i > 0; i--) {
							transitionTree.collapseRow(i);
						}
						n.setCollapsed(true);
					} else {
						for (int i = 0; i < transitionTree.getRowCount(); i++) {
							transitionTree.expandRow(i);
						}
						n.setCollapsed(false);
					}
				} catch (Exception rootEX) {
					rootEX.printStackTrace();
				}
			}

			// If node is a transition node draw the single transition to the
			// right side of the GUI
			else if (n.getKind() == GUINodeKind.TRANSITION_NODE) {
				try {
					TransitionNode t = (TransitionNode) n;
					if (split.getRightComponent() != null) {
						split.remove(split.getRightComponent());
					}
					rightView = drawState(t.transition().getFinalState());
					split.setRightComponent(rightView);
				} catch (Exception tranEX) {
					tranEX.printStackTrace();
				}
			}

			// If node is a state node draw the state to the right side of the
			// GUI
			else if (n.getKind() == GUINodeKind.STATE_NODE) {
				try {
					StateNode s = (StateNode) n;
					if (split.getRightComponent() != null) {
						split.remove(split.getRightComponent());
					}
					rightView = drawState(s.getState());
					split.setRightComponent(rightView);
				} catch (Exception stateEX) {
					stateEX.printStackTrace();
				}
			}

			// If node is a step node draw the target state of the step to the
			// right side of the gui
			else if (n.getKind() == GUINodeKind.STEP_NODE) {
				try {
					StepNode s = (StepNode) n;
					if (split.getRightComponent() != null) {
						split.remove(split.getRightComponent());
					}
					rightView = drawState(s.getStep().getPostState());
					split.setRightComponent(rightView);
				} catch (Exception stepEX) {
					stepEX.printStackTrace();
				}
			}
		}
		// If the node wasn't a GUINODE (or a node extending from GUINODE)
		// Do nothing
		catch (Exception ex) {
			ex.printStackTrace();
		}
	}
}
