package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpExecutableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.parse.IF.CParser;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.util.IF.Triple;

/**
 * This transformer transforms away the orphaned constructs of OpenMP programs.
 * 
 */
public class OpenMPOrphanWorker extends BaseWorker {
	
	private ArrayList<Triple<FunctionDefinitionNode, FunctionCallNode, Boolean>> functionCalls = new ArrayList<Triple<FunctionDefinitionNode, FunctionCallNode, Boolean>>();


	public OpenMPOrphanWorker(ASTFactory astFactory) {
		super("OpenMPOrphanTransformer", astFactory);
		this.identifierPrefix = "$omp_orphan_";
	}

	@Override
	public AST transform(AST ast) throws SyntaxException {
		SequenceNode<BlockItemNode> root = ast.getRootNode();
		AST newAst;
		ast.release();
		FunctionDefinitionNode main = ast.getMain().getDefinition();
		ompOrphan(main, null, false);
		newAst = astFactory.newAST(root, ast.getSourceFiles());
		//newAst.prettyPrint(System.out, true);
		return newAst;
	}

	private void ompOrphan(ASTNode node, Set<Function> callees, boolean isInParallel){
		if(node instanceof OmpParallelNode){
			isInParallel = true;
		} else if(node instanceof FunctionDefinitionNode){
			callees = ((FunctionDefinitionNode) node).getEntity().getCallees();
		} else if (node instanceof FunctionCallNode) {
			String funcName = ((IdentifierExpressionNode) ((FunctionCallNode) node).getFunction()).getIdentifier().name();

			if(callees != null){
				for(Function call : callees){
					if(call.getName().equals(funcName)){
						FunctionDefinitionNode orphan = call.getDefinition();
						boolean isOrphan = checkOrphan(orphan);

						if(orphan != null){
							ASTNode parentFunc = node.parent();
							while(!(parentFunc instanceof FunctionDefinitionNode)){
								parentFunc = parentFunc.parent();
							}	
							
							Triple<FunctionDefinitionNode, FunctionCallNode, Boolean> temp;
							temp = new Triple<>((FunctionDefinitionNode)parentFunc, (FunctionCallNode)node, isInParallel);
							functionCalls.add(temp);
						}
						
						if(isOrphan){
							ArrayList<FunctionDefinitionNode> funcs = new ArrayList<FunctionDefinitionNode>();
							funcs.add(orphan);
							ASTNode parent = node;
							boolean direct = false;
							direct = insertFuncs((FunctionCallNode) node, funcs);
							
							if(!direct){
								parent = node;
								while(!(parent instanceof FunctionDefinitionNode)){
									parent = parent.parent();
								}
								boolean foundPar = false;
								int count=0;
								
								FunctionDefinitionNode currDef = orphan;
								FunctionCallNode origCall = null;
								funcs = new ArrayList<FunctionDefinitionNode>();
								while(!foundPar && count < functionCalls.size()){
									for (Triple<FunctionDefinitionNode, FunctionCallNode, Boolean> triple : functionCalls){
										if(((IdentifierExpressionNode) triple.second.getFunction()).getIdentifier().name().equals(currDef.getIdentifier().name())){
											funcs.add(currDef);
											currDef = triple.first; 
											count = 0;
											if(triple.third){
												foundPar = true;
												origCall = triple.second;
											}
											break;
										}
										count++;
									}
								}	
								if(foundPar){
									insertFuncs(origCall, funcs);
								}
							}
						}
						if(orphan != null){
							ompOrphan(orphan, callees, false);
						}
					}
				}
			}
		}

		if(node != null){
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				ompOrphan(child, callees, isInParallel);
			}
		}
		
	}
	
	private boolean insertFuncs(FunctionCallNode node, ArrayList<FunctionDefinitionNode> funcs){
		ASTNode parent = node;
		boolean direct = false;
		while(parent != null){
			if(parent instanceof OmpParallelNode){
				direct = true;
				StatementNode statement = ((OmpParallelNode) parent).statementNode();
				int index = statement.childIndex();
				CompoundStatementNode body;

				if(!(statement instanceof CompoundStatementNode)){
					List<BlockItemNode> items = new LinkedList<BlockItemNode>();
					statement.remove();
					for(FunctionDefinitionNode func : funcs){
						items.add(func.copy());
						removeOmpConstruct(func);
					}
					items.add(statement);
					body = nodeFactory.newCompoundStatementNode(newSource("Orphan", CParser.COMPOUND_STATEMENT), items);
					parent.setChild(index, body);
				} else {
					for(FunctionDefinitionNode func : funcs){
						insertChildAt(0, statement, func.copy());
					}
				}

			}
			parent = parent.parent();
		}
		return direct;
	}
	
	private boolean checkOrphan(ASTNode node){
		boolean isOrphan = true;
		boolean foundOmpNode = false;
		if(node instanceof OmpForNode 
				|| node instanceof OmpSyncNode
				|| node instanceof OmpWorksharingNode){
			
			//Check if some parent is a OmpParallelNode
			ASTNode parent = node;
			foundOmpNode = true;
			
			while(parent != null){
				if(parent instanceof OmpParallelNode){
					isOrphan = false;
					break;
				}
				parent = parent.parent();
			}
		}
			
		if(node != null){
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				isOrphan = foundOmpNode = (isOrphan && foundOmpNode) || checkOrphan(child);
			}
		}
		
		return isOrphan && foundOmpNode;
	}
	
	/*
	 * This method assumes that all of the OMP statements that are encountered
	 * can be safely removed or transformed into non-OMP equivalents.
	 */
	private void removeOmpConstruct(ASTNode node) {
		if (node instanceof OmpExecutableNode) {
			// Remove "statement" node from "omp statement" node
			StatementNode stmt = ((OmpExecutableNode) node).statementNode();
			int stmtIndex = getChildIndex(node, stmt);
			assert stmtIndex != -1;
			node.removeChild(stmtIndex);

			// Link "statement" into the "omp workshare" parent
			ASTNode parent = node.parent();
			int parentIndex = getChildIndex(parent, node);
			assert parentIndex != -1;
			parent.setChild(parentIndex, stmt);

			removeOmpConstruct(stmt);

		} else if (node instanceof FunctionCallNode
				&& ((FunctionCallNode) node).getFunction() instanceof IdentifierExpressionNode
				&& ((IdentifierExpressionNode) ((FunctionCallNode) node)
						.getFunction()).getIdentifier().name()
						.startsWith("omp_")) {
			/*
			 * Replace
			 */
			String ompFunctionName = ((IdentifierExpressionNode) ((FunctionCallNode) node)
					.getFunction()).getIdentifier().name();
			ASTNode replacement = null;
			if (ompFunctionName.equals("omp_get_thread_num")) {
				try {
					replacement = nodeFactory.newIntegerConstantNode(
							node.getSource(), "0");
				} catch (SyntaxException e) {
					e.printStackTrace();
				}
			} else if (ompFunctionName.equals("omp_get_num_threads")
					|| ompFunctionName.equals("omp_get_max_threads")
					|| ompFunctionName.equals("omp_get_num_procs")
					|| ompFunctionName.equals("omp_get_thread_limit")) {
				try {
					replacement = nodeFactory.newIntegerConstantNode(
							node.getSource(), "1");
				} catch (SyntaxException e) {
					e.printStackTrace();
				}

			} else if (ompFunctionName.equals("omp_init_lock")
					|| ompFunctionName.equals("omp_set_lock")
					|| ompFunctionName.equals("omp_unset_lock")
					|| ompFunctionName.equals("omp_set_num_threads")) {
				// delete this node
				replacement = nodeFactory
						.newNullStatementNode(node.getSource());

			} else if (ompFunctionName.equals("omp_get_wtime")) {
				// this will be transformed by the OMP transformer

			} else {
				assert false : "Unsupported omp function call "
						+ ompFunctionName
						+ " cannot be replaced by OpenMP simplifier";
			}

			// Link "replacement" into the omp call's parent
			ASTNode parent = node.parent();
			int parentIndex = getChildIndex(parent, node);
			assert parentIndex != -1;
			parent.setChild(parentIndex, replacement);

		} else if (node != null) {
			Iterable<ASTNode> children = node.children();
			for (ASTNode child : children) {
				removeOmpConstruct(child);
			}
		}
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
	
	private void insertChildAt(int k, ASTNode parent, ASTNode nodeToInsert) {
		int numChildren = parent.numChildren();

		if (k >= numChildren) {
			parent.setChild(k, nodeToInsert);
		} else {
			ASTNode current = parent.removeChild(k);
			ASTNode next = null;
			parent.setChild(k, nodeToInsert);
			if (current != null) {
				for (int i = k + 1; i <= numChildren; i++) {
					if (i == numChildren) {
						parent.setChild(i, current);
						break;
					}
					next = parent.child(i);
					if (next != null) {
						parent.removeChild(i);
						parent.setChild(i, current);
					} else {
						parent.setChild(i, current);
						break;
					}
					current = next;

				}
			}
		}
	}
}
