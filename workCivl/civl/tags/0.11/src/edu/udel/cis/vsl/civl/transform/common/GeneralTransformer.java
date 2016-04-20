package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;
import edu.udel.cis.vsl.abc.transform.IF.Transformer;

public class GeneralTransformer extends BaseTransformer implements Transformer {

	public static String CODE = "general";
	public static String LONG_NAME = "GeneralTransformer";
	public static String SHORT_DESCRIPTION = "transforms general features of C programs to CIVL-C";

	public GeneralTransformer(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	@Override
	public AST transform(AST unit) throws SyntaxException {
		@SuppressWarnings("unchecked")
		SequenceNode<ASTNode> root = (SequenceNode<ASTNode>) unit.getRootNode();
		AST newAst;
		List<VariableDeclarationNode> inputVars = new ArrayList<>();
		List<ASTNode> newExternalList = new ArrayList<>();

		unit.release();
		for (ASTNode child : root) {
			if (child.nodeKind() == NodeKind.FUNCTION_DEFINITION) {
				FunctionDefinitionNode functionNode = (FunctionDefinitionNode) child;
				IdentifierNode functionName = (IdentifierNode) functionNode
						.child(0);

				if (functionName.name().equals("main")) {
					inputVars = processMainFunction(functionNode);
				}
			}
		}
		if (inputVars.size() > 0) {
			for (ASTNode inputVar : inputVars) {
				newExternalList.add(inputVar);
			}
			for (ASTNode child : root) {
				newExternalList.add(child);
				child.parent().removeChild(child.childIndex());
			}
			root = nodeFactory.newSequenceNode(root.getSource(),
					"TranslationUnit", newExternalList);
		}
		newAst = astFactory.newTranslationUnit(root);
		return newAst;
	}

	/**
	 * Processes the original main function, including:
	 * <ul>
	 * <li>Removes all arguments of the function;</li>
	 * </ul>
	 * 
	 * @param mainFunction
	 *            The function definition node representing the original main
	 *            function.
	 * @param vars
	 *            The list of variable declaration nodes that are the arguments
	 *            of the original main function. These variables will be moved
	 *            up to the higher scope (i.e., the file scope of the final AST)
	 *            and become $input variables of the final AST. When invoking
	 *            this function, this parameter should be an empty list and this
	 *            function will update this list.
	 */
	private List<VariableDeclarationNode> processMainFunction(
			FunctionDefinitionNode mainFunction) {
		List<VariableDeclarationNode> inputVars = new ArrayList<>();
		FunctionTypeNode functionType = mainFunction.getTypeNode();
		SequenceNode<VariableDeclarationNode> parameters = functionType
				.getParameters();
		int count = parameters.numChildren();

		if (count > 0) {
			List<VariableDeclarationNode> newParameters = new ArrayList<>(0);

			for (int k = 0; k < count; k++) {
				VariableDeclarationNode parameter = parameters
						.getSequenceChild(k);

				parameters.removeChild(k);
				parameter.getTypeNode().setInputQualified(true);
				inputVars.add(parameter);
			}
			functionType.setParameters(nodeFactory.newSequenceNode(
					parameters.getSource(), "FormalParameterDeclarations",
					newParameters));
		}
		return inputVars;
	}

}
