/**
 * <p>Submodule <strong>ast.node</strong> defines every kind of
 * node in an AST.</p>
 * 
 * <p>The interface {@link edu.udel.cis.vsl.abc.ast.node.IF.ASTNode}
 * is the root of the AST node
 * type hierarchy.   All AST nodes implement that interface.</p>
 * 
 * <p>Other miscellaneous interfaces dealing with nodes are included
 * in this package.  This includes the
 * {@link edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory}, which specifies
 * a factory for producing every kind of AST node and related objects.</p>
 * 
 * <p>Any AST node can have any number of "attributes" associated to it.
 * This is a flexible mechanism for allowing clients to "hang" any kind
 * of information on to AST nodes.  To do this one first creates an
 * {@link edu.udel.cis.vsl.abc.ast.node.IF.AttributeKey}
 * using the appropriate method in the {@link edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory}.
 * That key can then be used to associate a value to a node.</p>
 */
package edu.udel.cis.vsl.abc.ast.node.IF;
