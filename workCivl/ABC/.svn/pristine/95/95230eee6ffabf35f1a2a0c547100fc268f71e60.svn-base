package edu.udel.cis.vsl.abc.ast.node.IF.acsl;

import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;

/**
 * A depends event which specifies reading or writing a list of memory units. It
 * has the syntax
 * 
 * <pre>
 * \read(m0, m1, ...)
 * </pre>
 * 
 * or
 * 
 * <pre>
 * \write(m0, m1, ...)
 * </pre>
 * 
 * @author Manchun Zheng
 *
 */
public interface MemoryEventNode extends DependsEventNode {

	public enum MemoryEventNodeKind {
		READ, WRITE, REACH
	}

	boolean isRead();

	boolean isWrite();

	boolean isReach();

	MemoryEventNodeKind memoryEventKind();

	SequenceNode<ExpressionNode> getMemoryList();

	@Override
	MemoryEventNode copy();
}
