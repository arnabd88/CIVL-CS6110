package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpExecutableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.civl.util.IF.Pair;

/**
 * A parallel region is a program fragment defined by an AST subtree rooted at a
 * single starting statement and delimited by a set of possible successor
 * statements. Thus a region is given by a pair, (s, Set<e>), with an
 * interpretation that it includes all paths beginning at statement s and ending
 * at a statement whose successor is some e.
 * 
 * Empty regions for a given parallel statement are not computed explicitly.
 * These can arise with initial, final or trivial use of barriers (e.g., barrier
 * as first or last statement in the parallel statement).
 * 
 * A region may include multiple execution paths.
 * 
 * This class computes a set of regions for a given OpenMP parallel statement
 * and makes that relation available through getter methods.
 * 
 * @author dwyer
 * 
 */
public class OpenMPParallelRegions {

	private boolean debug = false;
	private Map<ASTNode, List<Pair<ASTNode, List<ASTNode>>>> regionsForParallel;

	public OpenMPParallelRegions(ASTNode rootNode) {
		regionsForParallel = new HashMap<ASTNode, List<Pair<ASTNode, List<ASTNode>>>>();

		collectAllRegions(rootNode);

		if (debug)
			for (ASTNode key : regionsForParallel.keySet()) {
				List<Pair<ASTNode, List<ASTNode>>> regions = regionsForParallel
						.get(key);
				System.out
						.println("For OMP Parallel Region found the following regions:");
				int r = 0;
				for (Pair<ASTNode, List<ASTNode>> region : regions) {
					System.out.println("------------ region " + (r++)
							+ " ---------------");
					System.out.println("   " + region);
				}
				System.out.println("------------ end regions --------------");

			}
	}

	/*
	 */
	private void collectAllRegions(ASTNode node) {
		if (node instanceof OmpParallelNode) {
			if (debug)
				System.out.println("collectAllRegions for node " + node);
			OmpParallelNode opn = (OmpParallelNode) node;

			List<Pair<ASTNode, List<ASTNode>>> setForParallel = new ArrayList<Pair<ASTNode, List<ASTNode>>>();
			regionsForParallel.put(opn, setForParallel);

			setForParallel.addAll(collectRegions(opn.statementNode()));

		} else if (node instanceof OmpExecutableNode) {
			if (debug)
				System.out.println("Found non-Parallel OmpExecutableNode: "
						+ node);

		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				collectAllRegions(child);
			}
		}
	}

	/*
	 * There are two phases of this calculation.
	 * 
	 * 1) Compute the current region via DFS. A single region is terminated by
	 * an implicit or explicit barrier or by reaching the leaves of the AST.
	 * 
	 * NB: explain why this works without a control flow analysis, i.e., we
	 * target OpenMP Parallel node subtrees which contain the control flow
	 * 
	 * 2) Compute followon regions rooted at the frontier of the current region.
	 * Since this computation is done for an OpenMP parallel statement there is
	 * an implicit barrier ending any final regions.
	 */
	private List<Pair<ASTNode, List<ASTNode>>> collectRegions(ASTNode root) {
		List<Pair<ASTNode, List<ASTNode>>> result = new ArrayList<Pair<ASTNode, List<ASTNode>>>();
		List<ASTNode> worklist = new ArrayList<ASTNode>();
		worklist.add(root);

		while (worklist.size() > 0) {
			ASTNode regionRoot = worklist.get(0);
			worklist.remove(regionRoot);

			List<ASTNode> regionSuccessors = buildRegion(regionRoot);

			result.add(new Pair<ASTNode, List<ASTNode>>(regionRoot,
					regionSuccessors));

			// Region successors that are under the scope of the root
			// each require a separate region to be constructed.
			for (ASTNode succ : regionSuccessors) {
				if (isReachable(root, succ)) {
					worklist.add(succ);
				}
			}

		}
		return result;
	}

	/*
	 * Recursively traverse the node and build up the set of frontier nodes,
	 * i.e., the statements following implicit/explicit barriers.
	 */
	private List<ASTNode> buildRegion(ASTNode node) {
		List<ASTNode> frontier = new ArrayList<ASTNode>();

		/*
		 * Does this logic overestimate the regions? What if there are nested
		 * OpenMP constructs with barriers?
		 */
		if (node instanceof OmpForNode) {
			OmpForNode ompFor = (OmpForNode) node;
			if (!ompFor.nowait()) {
				ASTNode succ = successor(ompFor);
				if (succ != null)
					frontier.add(succ);
				return frontier;
			}

		} else if (node instanceof OmpSyncNode) {
			OmpSyncNode syncNode = (OmpSyncNode) node;

			if (syncNode.ompSyncNodeKind() == OmpSyncNode.OmpSyncNodeKind.BARRIER) {
				if (!syncNode.nowait()) {
					ASTNode succ = successor(syncNode);
					if (succ != null)
						frontier.add(succ);
					return frontier;
				}
			}

		} else if (node instanceof OmpWorksharingNode) {
			OmpWorksharingNode wsNode = (OmpWorksharingNode) node;

			if ((wsNode.ompWorkshareNodeKind() == OmpWorksharingNode.OmpWorksharingNodeKind.SECTIONS)
					|| (wsNode.ompWorkshareNodeKind() == OmpWorksharingNode.OmpWorksharingNodeKind.SINGLE)) {
				if (!wsNode.nowait()) {
					ASTNode succ = successor(wsNode);
					if (succ != null)
						frontier.add(succ);
					return frontier;
				}
			}
		}

		if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				frontier.addAll(buildRegion(child));
			}
		}

		return frontier;
	}

	/*
	 * Computes the successor statement in the AST for a given node If the node
	 * has a successor among its siblings (i.e., the next child of its parent)
	 * then return it. Otherwise continue up the AST until a successor can be
	 * found.
	 */
	private ASTNode successor(ASTNode node) {
		if (node instanceof StatementNode) {
			ASTNode parent = node.parent();
			int idx = 0;

			while ((idx = getChildIndex(parent, node)) + 1 >= parent
					.numChildren()) {
				node = parent; // now we look for the successor of the parent
				parent = node.parent();
			}
			return parent.child(idx + 1);

		} else {
			assert false : "Expected statement node, but was called with "
					+ node;
		}
		return null;
	}

	/*
	 * Returns the index of "child" in the children of "node"; -1 if "child" is
	 * not one of "node"'s children.
	 */
	private int getChildIndex(ASTNode node, ASTNode child) {
		for (int childIndex = 0; childIndex < node.numChildren(); childIndex++) {
			if (node.child(childIndex) == child)
				return childIndex;
		}
		return -1;
	}

	private boolean isReachable(ASTNode from, ASTNode to) {
		if (from != null) {
			Iterable<ASTNode> children = from.children();
			for (ASTNode child : children) {
				if (child != null) {
					if (child.equals(to)) {
						return true;
					} else {
						isReachable(child, to);
					}
				}
			}
		}
		return false;
	}

}
