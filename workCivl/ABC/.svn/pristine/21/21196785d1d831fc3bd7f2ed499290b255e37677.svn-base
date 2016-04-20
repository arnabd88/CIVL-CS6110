package edu.udel.cis.vsl.abc.ast.node.IF.acsl;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;

/**
 * A <code>depends</code> clause specifies part of the dependence relation used
 * in partial order reduction (POR). It has the syntax
 * 
 * <pre>
 * $depends event0, event1, ...;
 * </pre>
 * 
 * , where <code>event0, event1, ...</code> are depends events
 * {@link DependsEventNode}.
 * 
 * <p>
 * For each process p, the event can be evaluated in the context of p. If event
 * evaluates to be valid, then p must be included in an ample set containing a
 * call to this function. The event <code>e</code> hence defines a predicate
 * <code>d(s,p)</code>, where s ranges over states, and p over processes.
 * </p>
 *
 * @see ContractNode
 * 
 * @author Manchun Zheng
 * 
 */
public interface DependsNode extends ContractNode {
	/**
	 * Gets the list of events specified by this depends clause
	 * 
	 * @return the list of events specified by this depends clause
	 */
	SequenceNode<DependsEventNode> getEventList();

	@Override
	DependsNode copy();
}
