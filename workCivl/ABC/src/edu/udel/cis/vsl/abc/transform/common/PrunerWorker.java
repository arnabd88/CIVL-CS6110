package edu.udel.cis.vsl.abc.transform.common;

import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.ASTException;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Scope;
import edu.udel.cis.vsl.abc.ast.entity.IF.TaggedEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.AttributeKey;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.PragmaNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.StaticAssertionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.OrdinaryDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.TypedefDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode.BlockItemKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CivlForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Enumerator;
import edu.udel.cis.vsl.abc.ast.type.IF.QualifiedObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.common.Pruner.Reachability;

/**
 * Finds all reachable nodes in the AST and marks them REACHABLE. Assumes that
 * the AST has already had the standard analyses performed, so that every
 * identifier has been resolved to refer to some Entity.
 * 
 * @author siegel
 * 
 */
public class PrunerWorker {

	private ASTNode root;

	private AttributeKey reachedKey;

	List<ASTNode> reachableNodes = new LinkedList<ASTNode>();

	public PrunerWorker(AttributeKey reachedKey, ASTNode root)
			throws SyntaxException {
		this.reachedKey = reachedKey;
		this.root = root;
		search();
	}

	/**
	 * Marks a node and its descendants reachable.
	 * 
	 * If <code>node</code> is already marked reachable, returns immediately.
	 * Otherwise marks the node as reachable and recurses over the node's
	 * children. For each child, if the child is an identifier node, the entity
	 * to which that identifier refers is explored. In addition, if the child is
	 * anything other than an ordinary declaration (i.e., a function or variable
	 * declaration) or a typedef declaration, then <code>markReachable</code> is
	 * invoked recursively on the child.
	 * 
	 * @param node
	 */
	private void markReachable(ASTNode node) {
		if (node.getAttribute(reachedKey) == Reachability.REACHABLE)
			return;
		else {
			Iterable<ASTNode> children = node.children();

			node.setAttribute(reachedKey, Reachability.REACHABLE);
			reachableNodes.add(node);
			if (node instanceof FunctionTypeNode) {
				// special case: don't want to remove unused formal parameters
				SequenceNode<VariableDeclarationNode> formals = ((FunctionTypeNode) node)
						.getParameters();

				for (VariableDeclarationNode formal : formals)
					markReachable(formal);
			} else if (node instanceof CivlForNode) {
				// special case: cannot remove any loop variables
				CivlForNode forNode = (CivlForNode) node;

				for (VariableDeclarationNode decl : forNode.getVariables())
					markReachable(decl);
			}
			if (node instanceof TypeNode) {
				// special case: if this is a type node under a
				// typedef declaration node, the whole typedef declaration
				// is reachable...
				ASTNode parent = node.parent();

				if (parent instanceof TypedefDeclarationNode) {
					markReachable(parent);
				}
			}
			for (ASTNode child : children) {
				if (child != null) {
					if (child instanceof IdentifierNode) {
						Entity entity = ((IdentifierNode) child).getEntity();

						if (entity != null && entity instanceof ProgramEntity)
							// TODO: check this: throw new
							// ASTException("Identifier not resolved: "
							// + child.getSource().getSummary(false));
							explore((ProgramEntity) entity);
					}
					if (child instanceof OrdinaryDeclarationNode
							|| child instanceof TypedefDeclarationNode) {
						if (child instanceof VariableDeclarationNode) {
							InitializerNode init = ((VariableDeclarationNode) child)
									.getInitializer();

							// at some point improve this to keep the init
							// but not necessarily the variable...
							if (init != null && !init.isSideEffectFree(true))
								markReachable(child);
						}
						// do nothing: we want to see if we can reach these
					} else
						markReachable(child);
				}
			}
		}
	}

	/**
	 * Invokes {@link #markReachable(ASTNode)} on all declarations of the
	 * entity.
	 * 
	 * @param entity
	 *            an Entity occurring in the AST
	 */
	private void explore(ProgramEntity entity) {
		if (entity instanceof TaggedEntity) {
			// only need the first decl and the defn:
			ASTNode firstDecl = entity.getFirstDeclaration();
			ASTNode defn = entity.getDefinition();

			if (firstDecl != null)
				markReachable(firstDecl);
			if (defn != null && defn != firstDecl)
				markReachable(defn);
		} else {
			for (DeclarationNode dn : entity.getDeclarations())
				markReachable(dn);
			// special case: if you use at least one enumerator
			// in the enumeration, you use the whole enumeration...
			if (entity instanceof Enumerator) {
				explore(((Enumerator) entity).getType());
			}
		}
	}

	/**
	 * Searches AST, marking reachable nodes as REACHABLE.
	 * 
	 * @throws SyntaxException
	 */
	private void search() throws SyntaxException {
		Scope rootScope = root.getScope();
		Function main = (Function) rootScope.getOrdinaryEntity(false, "main");
		Iterable<ASTNode> children = root.children();

		for (Variable variable : rootScope.getVariables()) {
			Type type = variable.getType();

			if (type instanceof QualifiedObjectType) {
				QualifiedObjectType qotype = (QualifiedObjectType) type;

				if (qotype.isInputQualified() || qotype.isOutputQualified()) {
					VariableDeclarationNode decl = variable.getDefinition();

					if (decl == null)
						throw new ASTException(
								"No definition for input or output variable: "
										+ variable);
					markReachable(decl);
				}
			}
		}
		for (ASTNode child : children) {
			BlockItemNode externalDef = (BlockItemNode) child;

			if (externalDef instanceof PragmaNode
					|| externalDef instanceof StaticAssertionNode
					|| isAssumeOrAssert(externalDef)
					|| externalDef instanceof StatementNode)
				// || isElaborateDomainFunction(externalDef))
				markReachable(externalDef);
		}
		explore(main);
	}

	// private boolean isElaborateDomainFunction(BlockItemNode item) {
	// if ((item != null) && item instanceof FunctionDeclarationNode)
	// return ((FunctionDeclarationNode) item).getIdentifier().name()
	// .equals("$elaborate_rectangular_domain");
	// return false;
	// }

	private boolean isAssumeOrAssert(BlockItemNode item) {
		if (item == null)
			return false;
		if (item.blockItemKind() == BlockItemKind.STATEMENT) {
			if (item instanceof ExpressionStatementNode) {
				ExpressionStatementNode exprStmt = (ExpressionStatementNode) item;
				ExpressionNode expr = exprStmt.getExpression();

				if (expr instanceof FunctionCallNode) {
					FunctionCallNode funcCall = (FunctionCallNode) expr;
					ExpressionNode function = funcCall.getFunction();

					if (function instanceof IdentifierExpressionNode) {
						IdentifierExpressionNode funcID = (IdentifierExpressionNode) function;
						String funcName = funcID.getIdentifier().name();

						if (funcName.equals("$assert")
								|| funcName.equals("$assume"))
							return true;
					}
				}
			}
		}
		return false;
	}

	public List<ASTNode> getReachableNodes() {
		return reachableNodes;
	}

}
