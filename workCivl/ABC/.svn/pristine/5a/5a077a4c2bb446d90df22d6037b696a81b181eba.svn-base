package edu.udel.cis.vsl.abc.transform.common;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTException;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.TypedefDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StringLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.front.IF.CivlcTokenConstant;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.StringToken;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.abc.transform.IF.Combiner;
import edu.udel.cis.vsl.abc.transform.IF.Transformer;

/**
 * Combine two ASTs to form a new AST to be used for comparison. The
 * CompareCombiner treats the first argument to combine() as the specification
 * program, and the second argument as the implementation.
 * 
 * @author zirkel
 * 
 */
public class CompareCombiner implements Combiner {

	private final static String MY_NAME = "CompareCombiner";

	/**
	 * The node factory that creates new AST nodes.
	 */
	private NodeFactory factory;

	/**
	 * The AST factory that creates new AST's.
	 */
	private ASTFactory astFactory;

	/**
	 * The source of the specification.
	 */
	private Source specSource;

	/**
	 * The source of the implementation.
	 */
	private Source implSource;

	private final static String ASSERT_EQUALS = "$assert_equals";

	@Override
	public AST combine(AST spec, AST impl) throws SyntaxException {
		SequenceNode<BlockItemNode> specRoot = spec.getRootNode();
		SequenceNode<BlockItemNode> implRoot = impl.getRootNode();
		SequenceNode<BlockItemNode> newRoot;
		Map<String, VariableDeclarationNode> inputVariables;
		Map<String, VariableDeclarationNode> specOutputs;
		Map<String, VariableDeclarationNode> implOutputs;
		FunctionDefinitionNode specSystem;
		FunctionDefinitionNode implSystem;
		FunctionDefinitionNode newMain;
		List<BlockItemNode> newMainBodyNodes = new ArrayList<BlockItemNode>();
		List<BlockItemNode> nodes = new ArrayList<BlockItemNode>();
		Transformer nameTransformer;
		TypedefDeclarationNode specFileTypeDef = null, implFileTypeDef = null;
		FunctionDeclarationNode equalsFunc = null;
		Collection<SourceFile> sourceFiles0 = spec.getSourceFiles(), sourceFiles1 = impl
				.getSourceFiles(), allSourceFiles = new LinkedHashSet<>();

		allSourceFiles.addAll(sourceFiles0);
		allSourceFiles.addAll(sourceFiles1);
		astFactory = spec.getASTFactory();
		spec.release();
		impl.release();
		specFileTypeDef = this.getAndRemoveFileTypeNode(specRoot);
		implFileTypeDef = this.getAndRemoveFileTypeNode(implRoot);
		processExternVariables(specRoot);
		processExternVariables(implRoot);
		if (specFileTypeDef != null)
			nodes.add(specFileTypeDef);
		else if (implFileTypeDef != null)
			nodes.add(implFileTypeDef);
		equalsFunc = this.getAndRemoveEqualsFuncNode(specRoot);
		nodes.add(equalsFunc);
		spec = astFactory.newAST(specRoot, sourceFiles0, spec.isWholeProgram());
		impl = astFactory.newAST(implRoot, sourceFiles1, impl.isWholeProgram());
		specSource = this.getMainSource(specRoot);
		implSource = this.getMainSource(implRoot);
		factory = astFactory.getNodeFactory();
		inputVariables = combineInputs(specRoot, implRoot);
		nodes.add(this.assertFunctionNode(specSource));
		nodes.add(definedFunctionNode(specSource));
		nodes.add(assertEquals(specSource));
		nodes.addAll(inputVariables.values());
		specOutputs = getOutputs(specRoot);
		implOutputs = getOutputs(implRoot);
		checkOutputs(specOutputs, implOutputs);
		// systemFunctions = combineSystemFunctions(specRoot, implRoot);
		// nodes.addAll(systemFunctions.values());
		nameTransformer = new CommonNameTransformer(renameVariables(
				specOutputs.values(), "_spec"), astFactory);
		spec = nameTransformer.transform(spec);
		// TODO: Check consistency of assumptions
		specSystem = wrapperFunction(specSource, specRoot, "system_spec");
		implSystem = wrapperFunction(implSource, implRoot, "system_impl");
		for (VariableDeclarationNode v : specOutputs.values()) {
			v.getTypeNode().setOutputQualified(false);
			nodes.add(v.copy());
		}
		for (VariableDeclarationNode v : implOutputs.values()) {
			v.getTypeNode().setOutputQualified(false);
			nodes.add(v.copy());
		}
		nodes.add(specSystem);
		nodes.add(implSystem);

		newMainBodyNodes.add(factory.newVariableDeclarationNode(specSource,
				factory.newIdentifierNode(specSource, "_isEqual"),
				factory.newBasicTypeNode(specSource, BasicTypeKind.BOOL)));

		newMainBodyNodes.add(factory.newExpressionStatementNode(factory
				.newFunctionCallNode(specSource, factory
						.newIdentifierExpressionNode(specSource, factory
								.newIdentifierNode(specSource, "system_spec")),
						new ArrayList<ExpressionNode>(), null)));
		newMainBodyNodes.add(factory.newExpressionStatementNode(factory
				.newFunctionCallNode(implSource, factory
						.newIdentifierExpressionNode(implSource, factory
								.newIdentifierNode(implSource, "system_impl")),
						new ArrayList<ExpressionNode>(), null)));
		// TODO: spawn and join (but calls ok until joint assertions
		// implemented)
		newMainBodyNodes.addAll(outputAssertions(specOutputs, implOutputs));
		newMain = factory
				.newFunctionDefinitionNode(
						specSource,
						factory.newIdentifierNode(specSource, "main"),
						factory.newFunctionTypeNode(
								specSource,
								factory.newVoidTypeNode(specSource),
								factory.newSequenceNode(
										specSource,
										"Formals",
										new ArrayList<VariableDeclarationNode>()),
								false), factory.newSequenceNode(specSource,
								"Contract", new ArrayList<ContractNode>()),
						factory.newCompoundStatementNode(specSource,
								newMainBodyNodes));
		nodes.add(newMain);
		newRoot = factory.newSequenceNode(
				astFactory.getTokenFactory().join(specSource, implSource),
				"Composite System", nodes);

		AST result = astFactory.newAST(newRoot, allSourceFiles, true);

		// result.prettyPrint(System.out, false);
		return result;
	}

	private FunctionDeclarationNode assertFunctionNode(Source specSource) {
		IdentifierNode name = factory.newIdentifierNode(specSource, "$assert");
		FunctionTypeNode funcType = factory.newFunctionTypeNode(specSource,
				factory.newVoidTypeNode(specSource), factory.newSequenceNode(
						specSource, "Formals", Arrays.asList(factory
								.newVariableDeclarationNode(specSource, factory
										.newIdentifierNode(specSource,
												"expression"), factory
										.newBasicTypeNode(specSource,
												BasicTypeKind.BOOL))))

				, false);

		FunctionDeclarationNode function = factory.newFunctionDeclarationNode(
				specSource, name, funcType, null);

		function.setSystemFunctionSpeciier(true);
		return function;
	}

	/**
	 * Construct the function declaration of the system function $equals.
	 * 
	 * @param specSource
	 * @return
	 */
	private FunctionDeclarationNode assertEquals(Source specSource) {
		IdentifierNode name = factory.newIdentifierNode(specSource,
				ASSERT_EQUALS);
		FunctionTypeNode funcType = factory
				.newFunctionTypeNode(
						specSource,
						factory.newBasicTypeNode(specSource, BasicTypeKind.BOOL),
						factory.newSequenceNode(
								specSource,
								"Formals",
								Arrays.asList(
										factory.newVariableDeclarationNode(
												specSource,
												factory.newIdentifierNode(
														specSource, "first"),
												factory.newPointerTypeNode(
														specSource,
														factory.newVoidTypeNode(specSource))),
										factory.newVariableDeclarationNode(
												specSource,
												factory.newIdentifierNode(
														specSource, "second"),
												factory.newPointerTypeNode(
														specSource,
														factory.newVoidTypeNode(specSource)))))

						, false);

		funcType.setVariableArgs(true);

		FunctionDeclarationNode function = factory.newFunctionDeclarationNode(
				specSource, name, funcType, null);

		function.setSystemFunctionSpeciier(true);
		return function;
	}

	/**
	 * Construct the function declaration of the system function $defined.
	 * 
	 * @param specSource
	 * @return
	 */
	private FunctionDeclarationNode definedFunctionNode(Source specSource) {
		IdentifierNode name = factory.newIdentifierNode(specSource, "$defined");
		FunctionTypeNode funcType = factory
				.newFunctionTypeNode(
						specSource,
						factory.newBasicTypeNode(specSource, BasicTypeKind.BOOL),
						factory.newSequenceNode(
								specSource,
								"Formals",
								Arrays.asList(factory
										.newVariableDeclarationNode(
												specSource,
												factory.newIdentifierNode(
														specSource, "obj"),
												factory.newPointerTypeNode(
														specSource,
														factory.newVoidTypeNode(specSource))))),
						false);
		FunctionDeclarationNode function = factory.newFunctionDeclarationNode(
				specSource, name, funcType, null);

		function.setSystemFunctionSpeciier(true);
		return function;
	}

	/**
	 * Finds the $file type declaration node from an AST, returns it and remove
	 * it from the AST if it is found. $file type declaration node is required
	 * by the output variable CIVL_filesystem (array-of-$file type) (if IO
	 * transformer has been applied). So we need to move it to the final file
	 * scope.
	 * 
	 * @param root
	 *            The root node of the AST
	 * @return the $file type declaration node, or null if it absent from the
	 *         AST.
	 */
	private TypedefDeclarationNode getAndRemoveFileTypeNode(
			SequenceNode<BlockItemNode> root) {
		int numChildren = root.numChildren();

		for (int i = 0; i < numChildren; i++) {
			BlockItemNode def = root.getSequenceChild(i);

			if (def != null && def instanceof TypedefDeclarationNode) {
				TypedefDeclarationNode typeDefNode = (TypedefDeclarationNode) def;
				String sourceFile = typeDefNode.getSource().getFirstToken()
						.getSourceFile().getName();

				if (sourceFile.equals("stdio.cvl")
						&& typeDefNode.getName().equals("$file")) {
					typeDefNode.parent().removeChild(typeDefNode.childIndex());
					return typeDefNode;
				}
			}
		}
		return null;
	}

	/**
	 * Finds the $equals function declaration node from an AST, returns it and
	 * remove it from the AST if it is found.
	 * 
	 * @param root
	 *            The root node of the AST
	 * @return the $equals function declaration node, or null if it absent from
	 *         the AST.
	 */
	private FunctionDeclarationNode getAndRemoveEqualsFuncNode(
			SequenceNode<BlockItemNode> root) {
		int numChildren = root.numChildren();

		for (int i = 0; i < numChildren; i++) {
			BlockItemNode def = root.getSequenceChild(i);

			if (def != null && def instanceof FunctionDeclarationNode) {
				FunctionDeclarationNode funcDec = (FunctionDeclarationNode) def;
				String sourceFile = funcDec.getSource().getFirstToken()
						.getSourceFile().getName();

				if (sourceFile.equals("pointer.cvh")
						&& funcDec.getName().equals("$equals")) {
					funcDec.parent().removeChild(funcDec.childIndex());
					return funcDec;
				}
			}
		}
		return null;
	}

	// /**
	// * Removes the $file type node from the AST. This is called after
	// * {@link #getAndRemoveFileTypeNode(SequenceNode)}. When the compare
	// * combiner moves the $file type node from one AST, it still needs to
	// remove
	// * it from
	// *
	// * @param root
	// * the root node of the AST.
	// */
	// private void removeFileTypeNode(SequenceNode<ExternalDefinitionNode>
	// root) {
	// int numChildren = root.numChildren();
	//
	// for (int i = 0; i < numChildren; i++) {
	// ExternalDefinitionNode def = root.getSequenceChild(i);
	//
	// if (def != null && def instanceof TypedefDeclarationNode) {
	// TypedefDeclarationNode typeDefNode = (TypedefDeclarationNode) def;
	// String sourceFile = typeDefNode.getSource().getFirstToken()
	// .getSourceFile().getName();
	//
	// if (sourceFile.equals("stdio.cvl")
	// && typeDefNode.getName().equals("$file")) {
	// typeDefNode.parent().removeChild(typeDefNode.childIndex());
	// return;
	// }
	// }
	// }
	// }

	/**
	 * Take the input variable declaration nodes from the specification and the
	 * implementation into a list. The input variables of the specification
	 * should be a subset of those of the implementation.
	 * 
	 * @param specRoot
	 *            The root node of the specification AST.
	 * @param implRoot
	 *            The root node of the implementation AST.
	 * @return The combined list of input variable declaration nodes, key is
	 *         name of variable.
	 */
	private Map<String, VariableDeclarationNode> combineInputs(
			ASTNode specRoot, ASTNode implRoot) {
		Map<String, VariableDeclarationNode> inputs = new LinkedHashMap<String, VariableDeclarationNode>();

		// Put all input variables from the implementation into the map.
		for (int i = 0; i < implRoot.numChildren(); i++) {
			ASTNode child = implRoot.child(i);

			if (child != null
					&& child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
				VariableDeclarationNode var = (VariableDeclarationNode) child;

				if (var.getTypeNode().isInputQualified()) {
					inputs.put(var.getName(), var.copy());
				}
			}
		}
		// Check that all input variables from the spec were also in the impl.
		for (int i = 0; i < specRoot.numChildren(); i++) {
			ASTNode child = specRoot.child(i);

			if (child != null
					&& child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
				VariableDeclarationNode var = (VariableDeclarationNode) child;

				if (var.getTypeNode().isInputQualified()) {
					if (!inputs.containsKey(var.getName())) {
						// throw new ASTException(
						// "Implementation program does not contain specification input variable "
						// + var.getName() + ".");
						inputs.put(var.getName(), var.copy());
					}
				}
			}
		}
		return inputs;
	}

	/**
	 * Returns the output variables of the AST.
	 * 
	 * @param root
	 *            The root node of the AST.
	 * @return the output variables of the AST, where key is name of variable.
	 */
	private Map<String, VariableDeclarationNode> getOutputs(ASTNode root) {
		Map<String, VariableDeclarationNode> outputs = new LinkedHashMap<String, VariableDeclarationNode>();

		// Put all output variables into the map.
		for (int i = 0; i < root.numChildren(); i++) {
			ASTNode child = root.child(i);

			if (child != null
					&& child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
				VariableDeclarationNode var = (VariableDeclarationNode) child;

				if (var.getTypeNode().isOutputQualified()) {
					outputs.put(var.getName(), var);
				}
			}
		}
		return outputs;
	}

	/**
	 * Checks if the output variables of the specification and the
	 * implementation satisfy the precondition that all the output variables of
	 * the specification should also be the output variables of the
	 * implementation. The output variable CIVL_filesystem which is introduced
	 * by IO transformer is an exception, i.e., it is fine for the specification
	 * to contain CIVL_filesystem while the implementation doesn't.
	 * 
	 * @param specOutputs
	 *            The output variables of the
	 * @param implOutputs
	 */
	private void checkOutputs(Map<String, VariableDeclarationNode> specOutputs,
			Map<String, VariableDeclarationNode> implOutputs) {
		for (String name : specOutputs.keySet()) {
			// allow CIVL_output_filesystem to exist in only one program
			// TODO better solution for IO transformer
			if (name.equals("CIVL_output_filesystem"))
				continue;
			if (!implOutputs.containsKey(name)) {
				throw new ASTException(
						"No implementation output variable matching specification outputs variable "
								+ name + ".");
			}
		}
	}

	/**
	 * Given an AST, remove input and output variables and create a new function
	 * wrapping the remaining file scope items.
	 * 
	 * @param root
	 *            The root node of the AST being wrapped in a new function.
	 * @param name
	 *            The name of the new function.
	 * @return A function definition node with the appropriate name, void return
	 *         type, and no parameters.
	 */
	private FunctionDefinitionNode wrapperFunction(Source source, ASTNode root,
			String name) {
		FunctionTypeNode functionType = factory.newFunctionTypeNode(source,
				factory.newBasicTypeNode(source, BasicTypeKind.INT), factory
						.newSequenceNode(source, "Formals",
								new ArrayList<VariableDeclarationNode>()),
				false);
		List<BlockItemNode> items = new ArrayList<BlockItemNode>();
		CompoundStatementNode body;
		FunctionDefinitionNode result;

		for (int i = 0; i < root.numChildren(); i++) {
			ASTNode child = root.child(i);

			if (child == null)
				continue;
			if (child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
				VariableDeclarationNode var = (VariableDeclarationNode) child;

				if (!var.getTypeNode().isInputQualified()
						&& !var.getTypeNode().isOutputQualified()) {
					items.add(var.copy());
				}
			} else if (child.nodeKind() == NodeKind.FUNCTION_DECLARATION) {
				FunctionDeclarationNode function = (FunctionDeclarationNode) child;

				items.add(function.copy());
			} else if (child.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
				FunctionDefinitionNode function = (FunctionDefinitionNode) child;
				if (function.getName() != null
						&& function.getName().equals("main")) {
					for (int j = 0; j < ((FunctionDefinitionNode) function)
							.getBody().numChildren(); j++) {
						items.add(((FunctionDefinitionNode) function).getBody()
								.getSequenceChild(j).copy());
					}
				} else {
					items.add(function.copy());
				}
			} else {
				assert child instanceof BlockItemNode;
				items.add((BlockItemNode) child.copy());
			}
		}
		body = factory.newCompoundStatementNode(source, items);
		result = factory.newFunctionDefinitionNode(source, factory
				.newIdentifierNode(root.getSource(), name), functionType,
				factory.newSequenceNode(source, "Contract",
						new ArrayList<ContractNode>()), body);
		return result;
	}

	/**
	 * Generate the set of assertions comparing output variables. We assume that
	 * checkOutputs has been called, so the sets are of equal cardinality and
	 * the names correspond. Furthermore, we assume that name substitutions have
	 * happened, but that the String key values in the argument maps are the old
	 * names.
	 * 
	 * @param specOutputs
	 *            Mapping from original output variable name to the
	 *            corresponding variable declaration from the spec program.
	 * @param implOutputs
	 *            Mapping from original output variable name to the
	 *            corresponding variable declaration from the impl program.
	 * @return A list of assertion statements checking equivalence of
	 *         corresponding output variables.
	 * @throws SyntaxException
	 */
	private List<StatementNode> outputAssertions(
			Map<String, VariableDeclarationNode> specOutputs,
			Map<String, VariableDeclarationNode> implOutputs)
			throws SyntaxException {
		List<StatementNode> result = new ArrayList<StatementNode>();
		// TODO: do something better for source
		// ExpressionNode equalFunction = factory.newIdentifierExpressionNode(
		// specSource, factory.newIdentifierNode(specSource, "$equals"));
		ExpressionNode assertEqualFunction = factory
				.newIdentifierExpressionNode(specSource,
						factory.newIdentifierNode(specSource, ASSERT_EQUALS));

		for (String outputName : specOutputs.keySet()) {
			Source source = specOutputs.get(outputName).getSource();
			List<ExpressionNode> args = new ArrayList<ExpressionNode>();
			FunctionCallNode assertEqualCall;
			VariableDeclarationNode specOutput = specOutputs.get(outputName);
			VariableDeclarationNode implOutput = implOutputs.get(outputName);
			String message;

			// don't compare outputs if only one program has output
			// CIVL_output_system
			// TODO better solution from IO transformer
			if (outputName.equals("CIVL_output_filesystem")
					&& (specOutput == null || implOutput == null))
				continue;
			message = "\"Specification and implementation have"
					+ " different values for the output " + outputName + "!\"";
			args.add(factory.newOperatorNode(specOutput.getSource(),
					Operator.ADDRESSOF, Arrays.asList((ExpressionNode) factory
							.newIdentifierExpressionNode(
									specOutput.getSource(), specOutput
											.getIdentifier().copy()))));
			args.add(factory.newOperatorNode(implOutput.getSource(),
					Operator.ADDRESSOF, Arrays.asList((ExpressionNode) factory
							.newIdentifierExpressionNode(
									implOutput.getSource(), implOutput
											.getIdentifier().copy()))));
			args.add(this.createStringLiteral(message));
			assertEqualCall = factory.newFunctionCallNode(source,
					assertEqualFunction.copy(), args, null);
			result.add(factory.newExpressionStatementNode(assertEqualCall));
		}
		return result;
	}

	/**
	 * Create a mapping from Entity to String where the entities are variables
	 * and the strings are those variable names with a suffix added.
	 * 
	 * @param variables
	 *            A set of variable declarations.
	 * @param suffix
	 *            The suffix to be added to each variable name.
	 * @return The mapping from entities to their new names.
	 */
	private Map<Entity, String> renameVariables(
			Collection<VariableDeclarationNode> variables, String suffix) {
		Map<Entity, String> result = new LinkedHashMap<Entity, String>();

		for (VariableDeclarationNode var : variables) {
			result.put(var.getEntity(), var.getName() + suffix);
		}
		return result;
	}

	private Source getMainSource(ASTNode node) {
		if (node.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
			FunctionDefinitionNode functionNode = (FunctionDefinitionNode) node;
			IdentifierNode functionName = (IdentifierNode) functionNode
					.child(0);

			if (functionName.name().equals("main")) {
				return node.getSource();
			}
		}
		for (ASTNode child : node.children()) {
			if (child == null)
				continue;
			else {
				Source childResult = getMainSource(child);

				if (childResult != null)
					return childResult;
			}
		}
		return null;
	}

	private StringLiteralNode createStringLiteral(String text)
			throws SyntaxException {
		TokenFactory tokenFactory = astFactory.getTokenFactory();
		Formation formation = tokenFactory.newTransformFormation(MY_NAME,
				"stringLiteral");
		CivlcToken ctoke = tokenFactory.newCivlcToken(
				CivlcTokenConstant.STRING_LITERAL, text, formation);
		StringToken stringToken = tokenFactory.newStringToken(ctoke);

		return factory.newStringLiteralNode(tokenFactory.newSource(ctoke),
				text, stringToken.getStringLiteral());
	}

	/**
	 * removed extra declaration nodes for extern variables; also make remove
	 * the extern qualifier for the definition node
	 * 
	 * @param root
	 */
	private void processExternVariables(SequenceNode<BlockItemNode> root) {
		for (BlockItemNode item : root) {
			if (item == null)
				continue;
			if (item instanceof VariableDeclarationNode) {
				VariableDeclarationNode variable = (VariableDeclarationNode) item;

				if (variable.hasExternStorage())
					if (!variable.getEntity().getDefinition().equals(variable))
						variable.remove();
					else
						variable.setExternStorage(false);
			}
		}
	}
}
