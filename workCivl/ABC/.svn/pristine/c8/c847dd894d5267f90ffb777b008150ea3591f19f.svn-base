package edu.udel.cis.vsl.abc.ast.node.common.declaration;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.AbstractFunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.token.IF.Source;

/**
 * An abstract function definition contains the information for an abstract
 * function (i.e. a function in the mathematical sense, treated as uninterpreted
 * in the code).
 * 
 * An abstract function has an identifier, return type, parameters, and an
 * integer specifying the number of partial derivatives that may be taken.
 * 
 * @author zirkel
 *
 */
public class CommonAbstractFunctionDefinitionNode extends
		CommonFunctionDeclarationNode implements AbstractFunctionDefinitionNode {

	/**
	 * The number of partial derivatives (in total, of any parameters) that may
	 * be taken for this abstract function.
	 */
	private int continuity;

	public CommonAbstractFunctionDefinitionNode(Source source,
			IdentifierNode identifier, FunctionTypeNode type,
			SequenceNode<ContractNode> contract, int continuity) {
		super(source, identifier, type, contract);
		this.continuity = continuity;
	}

	@Override
	public AbstractFunctionDefinitionNode copy() {
		CommonAbstractFunctionDefinitionNode result = new CommonAbstractFunctionDefinitionNode(
				getSource(), duplicate(getIdentifier()),
				duplicate(getTypeNode()), duplicate(getContract()), continuity);

		result.setInlineFunctionSpecifier(hasInlineFunctionSpecifier());
		result.setNoreturnFunctionSpecifier(hasNoreturnFunctionSpecifier());
		copyStorage(result);
		return result;
	}

	@Override
	public int continuity() {
		return continuity;
	}
	
	@Override
	public OrdinaryDeclarationKind ordinaryDeclarationKind() {
		return OrdinaryDeclarationKind.ABSTRACT_FUNCTION_DEFINITION;
	}

}
