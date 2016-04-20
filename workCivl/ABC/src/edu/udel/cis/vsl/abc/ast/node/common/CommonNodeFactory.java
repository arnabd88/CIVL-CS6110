package edu.udel.cis.vsl.abc.ast.node.common;

import java.util.Arrays;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.AttributeKey;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.PairNode;
import edu.udel.cis.vsl.abc.ast.node.IF.PragmaNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.StaticAssertionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AnyactNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssignsOrReadsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssumesNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.BehaviorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CallEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CompletenessNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CompositeEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CompositeEventNode.EventOperator;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.DependsEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.DependsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.EnsuresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.GuardsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.InvariantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode.MPICollectiveKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractConstantNode.MPIConstantKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode.MPIContractExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MemoryEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MemoryEventNode.MemoryEventNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MemorySetNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.NoactNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.NothingNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.PureNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.RequiresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.ArrayDesignatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.CompoundInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.DesignationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.DesignatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.FieldDesignatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.AbstractFunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.EnumeratorDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FieldDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.TypedefDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.AlignOfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ArrowNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CallsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CharacterConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CompoundLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode.ConstantKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ContractVerifyNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DerivativeExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DotNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.EnumerationConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FloatingConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.QuantifiedExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.QuantifiedExpressionNode.Quantifier;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RegularRangeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RemoteExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ScopeOfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SizeableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SizeofNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SpawnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StatementExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StringLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.WildcardNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.LabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.OrdinaryLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.SwitchLabelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpDeclarativeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpFunctionReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSymbolReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode.OmpSyncNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode.OmpWorksharingNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AtomicNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ChooseStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CivlForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.GotoNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.IfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.JumpNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.JumpNode.JumpKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LabeledStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode.LoopKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ReturnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.SwitchNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.WhenNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.ArrayTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.AtomicTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.BasicTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.DomainTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.EnumerationTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.FunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.PointerTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.StructureOrUnionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypedefNameNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeofNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonAnyactNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonAssignsOrReadsNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonAssumesNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonBehaviorNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonCallEventNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonCompletenessNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonCompositeEventNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonDependsNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonEnsuresNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonGuardNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonInvariantNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonMPICollectiveBlockNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonMPIConstantNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonMPIContractExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonMemoryEventNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonMemorySetNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonNoactNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonNothingNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonPureNode;
import edu.udel.cis.vsl.abc.ast.node.common.acsl.CommonRequiresNode;
import edu.udel.cis.vsl.abc.ast.node.common.compound.CommonArrayDesignatorNode;
import edu.udel.cis.vsl.abc.ast.node.common.compound.CommonCompoundInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.common.compound.CommonDesignationNode;
import edu.udel.cis.vsl.abc.ast.node.common.compound.CommonFieldDesignatorNode;
import edu.udel.cis.vsl.abc.ast.node.common.declaration.CommonAbstractFunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.common.declaration.CommonEnumeratorDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.common.declaration.CommonFieldDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.common.declaration.CommonFunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.common.declaration.CommonFunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.common.declaration.CommonTypedefDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.common.declaration.CommonVariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonAlignOfNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonArrowNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonCallsNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonCastNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonCharacterConstantNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonCompoundLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonContractVerifyNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonDerivativeExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonDotNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonEnumerationConstantNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonFunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonHereOrRootNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonIdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonIntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonOperatorNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonProcnullNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonQuantifiedExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonRegularRangeNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonRemoteExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonResultNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonScopeOfNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonSelfNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonSizeofNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonSpawnNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonStatementExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonStringLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.common.expression.CommonWildcardNode;
import edu.udel.cis.vsl.abc.ast.node.common.label.CommonOrdinaryLabelNode;
import edu.udel.cis.vsl.abc.ast.node.common.label.CommonSwitchLabelNode;
import edu.udel.cis.vsl.abc.ast.node.common.omp.CommonOmpDeclarativeNode;
import edu.udel.cis.vsl.abc.ast.node.common.omp.CommonOmpForNode;
import edu.udel.cis.vsl.abc.ast.node.common.omp.CommonOmpFunctionReductionNode;
import edu.udel.cis.vsl.abc.ast.node.common.omp.CommonOmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.common.omp.CommonOmpSymbolReductionNode;
import edu.udel.cis.vsl.abc.ast.node.common.omp.CommonOmpSyncNode;
import edu.udel.cis.vsl.abc.ast.node.common.omp.CommonOmpWorkshareNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonAtomicNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonChooseStatementNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonCivlForNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonCompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonDeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonGotoNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonIfNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonJumpNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonLabeledStatementNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonLoopNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonNullStatementNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonReturnNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonSwitchNode;
import edu.udel.cis.vsl.abc.ast.node.common.statement.CommonWhenNode;
import edu.udel.cis.vsl.abc.ast.node.common.type.CommonArrayTypeNode;
import edu.udel.cis.vsl.abc.ast.node.common.type.CommonAtomicTypeNode;
import edu.udel.cis.vsl.abc.ast.node.common.type.CommonBasicTypeNode;
import edu.udel.cis.vsl.abc.ast.node.common.type.CommonDomainTypeNode;
import edu.udel.cis.vsl.abc.ast.node.common.type.CommonEnumerationTypeNode;
import edu.udel.cis.vsl.abc.ast.node.common.type.CommonFunctionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.common.type.CommonPointerTypeNode;
import edu.udel.cis.vsl.abc.ast.node.common.type.CommonRangeTypeNode;
import edu.udel.cis.vsl.abc.ast.node.common.type.CommonScopeTypeNode;
import edu.udel.cis.vsl.abc.ast.node.common.type.CommonStructureOrUnionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.common.type.CommonTypedefNameNode;
import edu.udel.cis.vsl.abc.ast.node.common.type.CommonTypeofNode;
import edu.udel.cis.vsl.abc.ast.node.common.type.CommonVoidTypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardUnsignedIntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardUnsignedIntegerType.UnsignedIntKind;
import edu.udel.cis.vsl.abc.ast.type.IF.TypeFactory;
import edu.udel.cis.vsl.abc.ast.value.IF.CharacterValue;
import edu.udel.cis.vsl.abc.ast.value.IF.IntegerValue;
import edu.udel.cis.vsl.abc.ast.value.IF.StringValue;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.ast.value.IF.ValueFactory;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.front.c.parse.CivlCParser;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSequence;
import edu.udel.cis.vsl.abc.token.IF.ExecutionCharacter;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.StringLiteral;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

public class CommonNodeFactory implements NodeFactory {

	private int attributeCount = 0;

	private LiteralInterpreter literalInterpreter;

	private ValueFactory valueFactory;

	private TypeFactory typeFactory;

	private StandardUnsignedIntegerType booleanType;

	private ObjectType processType;

	private ObjectType scopeType;

	private Configuration configuration;

	public CommonNodeFactory(Configuration configuration,
			TypeFactory typeFactory, ValueFactory valueFactory) {
		this.literalInterpreter = new LiteralInterpreter(typeFactory,
				valueFactory);
		this.typeFactory = typeFactory;
		this.valueFactory = valueFactory;
		this.booleanType = typeFactory
				.unsignedIntegerType(UnsignedIntKind.BOOL);
		this.processType = typeFactory.processType();
		this.scopeType = typeFactory.scopeType();
		this.configuration = configuration;
	}

	@Override
	public ValueFactory getValueFactory() {
		return valueFactory;
	}

	@Override
	public AttributeKey newAttribute(String attributeName,
			Class<? extends Object> attributeClass) {
		AttributeKey key = new CommonAttributeKey(attributeCount,
				attributeName, attributeClass);

		attributeCount++;
		return key;
	}

	@Override
	public <T extends ASTNode> SequenceNode<T> newSequenceNode(Source source,
			String name, List<T> nodes) {
		return new CommonSequenceNode<T>(source, name, nodes);
	}

	@Override
	public <S extends ASTNode, T extends ASTNode> PairNode<S, T> newPairNode(
			Source source, S node1, T node2) {
		return new CommonPairNode<S, T>(source, node1, node2);
	}

	@Override
	public IdentifierNode newIdentifierNode(Source source, String name) {
		return new CommonIdentifierNode(source, name);
	}

	@Override
	public BasicTypeNode newBasicTypeNode(Source source, BasicTypeKind kind) {
		return new CommonBasicTypeNode(source, kind);
	}

	@Override
	public TypeNode newVoidTypeNode(Source source) {
		return new CommonVoidTypeNode(source);
	}

	@Override
	public EnumerationTypeNode newEnumerationTypeNode(Source source,
			IdentifierNode tag,
			SequenceNode<EnumeratorDeclarationNode> enumerators) {
		return new CommonEnumerationTypeNode(source, tag, enumerators);
	}

	@Override
	public ArrayTypeNode newArrayTypeNode(Source source, TypeNode elementType,
			ExpressionNode extent) {
		return new CommonArrayTypeNode(source, elementType, extent);
	}

	@Override
	public AtomicTypeNode newAtomicTypeNode(Source source, TypeNode baseType) {
		return new CommonAtomicTypeNode(source, baseType);
	}

	@Override
	public PointerTypeNode newPointerTypeNode(Source source,
			TypeNode referencedType) {
		return new CommonPointerTypeNode(source, referencedType);
	}

	@Override
	public StructureOrUnionTypeNode newStructOrUnionTypeNode(Source source,
			boolean isStruct, IdentifierNode tag,
			SequenceNode<FieldDeclarationNode> structDeclList) {
		return new CommonStructureOrUnionTypeNode(source, isStruct, tag,
				structDeclList);
	}

	@Override
	public FunctionTypeNode newFunctionTypeNode(Source source,
			TypeNode returnType, SequenceNode<VariableDeclarationNode> formals,
			boolean hasIdentifierList) {
		return new CommonFunctionTypeNode(source, returnType, formals,
				hasIdentifierList);
	}

	@Override
	public TypeNode newScopeTypeNode(Source source) {
		return new CommonScopeTypeNode(source);
	}

	@Override
	public TypeNode newRangeTypeNode(Source source) {
		return new CommonRangeTypeNode(source);
	}

	@Override
	public DomainTypeNode newDomainTypeNode(Source source) {
		return new CommonDomainTypeNode(source, null);
	}

	@Override
	public DomainTypeNode newDomainTypeNode(Source source,
			ExpressionNode dimension) {
		return new CommonDomainTypeNode(source, dimension);
	}

	@Override
	public TypedefNameNode newTypedefNameNode(IdentifierNode name,
			SequenceNode<ExpressionNode> scopeList) {
		return new CommonTypedefNameNode(name.getSource(), name, scopeList);
	}

	@Override
	public CharacterConstantNode newCharacterConstantNode(Source source,
			String representation, ExecutionCharacter character) {
		CharacterValue constant = valueFactory.characterValue(character);

		return new CommonCharacterConstantNode(source, representation, constant);
	}

	@Override
	public StringLiteralNode newStringLiteralNode(Source source,
			String representation, StringLiteral literal) {
		StringValue stringValue = valueFactory.stringValue(literal);

		return new CommonStringLiteralNode(source, representation, stringValue);
	}

	@Override
	public IntegerConstantNode newIntegerConstantNode(Source source,
			String representation) throws SyntaxException {
		return literalInterpreter.integerConstant(source, representation);
	}

	@Override
	public FloatingConstantNode newFloatingConstantNode(Source source,
			String representation) throws SyntaxException {
		return literalInterpreter.floatingConstant(source, representation);
	}

	@Override
	public EnumerationConstantNode newEnumerationConstantNode(
			IdentifierNode name) {
		return new CommonEnumerationConstantNode(name.getSource(), name);
	}

	@Override
	public CompoundLiteralNode newCompoundLiteralNode(Source source,
			TypeNode typeNode, CompoundInitializerNode initializerList) {
		return new CommonCompoundLiteralNode(source, typeNode, initializerList);
	}

	@Override
	public IdentifierExpressionNode newIdentifierExpressionNode(Source source,
			IdentifierNode identifier) {
		return new CommonIdentifierExpressionNode(source, identifier);
	}

	@Override
	public AlignOfNode newAlignOfNode(Source source, TypeNode type) {
		return new CommonAlignOfNode(source, type);
	}

	@Override
	public CastNode newCastNode(Source source, TypeNode type,
			ExpressionNode argument) {
		return new CommonCastNode(source, type, argument);
	}

	@Override
	public FunctionCallNode newFunctionCallNode(Source source,
			ExpressionNode function, List<ExpressionNode> arguments,
			SequenceNode<ExpressionNode> scopeList) {
		SequenceNode<ExpressionNode> argumentSequenceNode = newSequenceNode(
				source, "ActualParameterList", arguments);

		return new CommonFunctionCallNode(source, function, null,
				argumentSequenceNode, scopeList);
	}

	@Override
	public FunctionCallNode newFunctionCallNode(Source source,
			ExpressionNode function, List<ExpressionNode> contextArguments,
			List<ExpressionNode> arguments,
			SequenceNode<ExpressionNode> scopeList) {
		SequenceNode<ExpressionNode> contextArgumentSequenceNode = newSequenceNode(
				source, "ActualContextParameterList", contextArguments);
		SequenceNode<ExpressionNode> argumentSequenceNode = newSequenceNode(
				source, "ActualParameterList", arguments);

		return new CommonFunctionCallNode(source, function,
				contextArgumentSequenceNode, argumentSequenceNode, scopeList);
	}

	@Override
	public DotNode newDotNode(Source source, ExpressionNode structure,
			IdentifierNode fieldName) {
		return new CommonDotNode(source, structure, fieldName);
	}

	@Override
	public ArrowNode newArrowNode(Source source,
			ExpressionNode structurePointer, IdentifierNode fieldName) {
		return new CommonArrowNode(source, structurePointer, fieldName);
	}

	@Override
	public OperatorNode newOperatorNode(Source source, Operator operator,
			List<ExpressionNode> arguments) {
		return new CommonOperatorNode(source, operator, arguments);
	}

	@Override
	public SizeofNode newSizeofNode(Source source, SizeableNode argument) {
		return new CommonSizeofNode(source, argument);
	}

	@Override
	public ScopeOfNode newScopeOfNode(Source source, ExpressionNode argument) {
		return new CommonScopeOfNode(source, argument);
	}

	@Override
	public VariableDeclarationNode newVariableDeclarationNode(Source source,
			IdentifierNode name, TypeNode type) {
		return new CommonVariableDeclarationNode(source, name, type);
	}

	@Override
	public VariableDeclarationNode newVariableDeclarationNode(Source source,
			IdentifierNode name, TypeNode type, InitializerNode initializer) {
		return new CommonVariableDeclarationNode(source, name, type,
				initializer);
	}

	@Override
	public FunctionDeclarationNode newFunctionDeclarationNode(Source source,
			IdentifierNode name, FunctionTypeNode type,
			SequenceNode<ContractNode> contract) {
		return new CommonFunctionDeclarationNode(source, name, type, contract);
	}

	@Override
	public EnumeratorDeclarationNode newEnumeratorDeclarationNode(
			Source source, IdentifierNode name, ExpressionNode value) {
		return new CommonEnumeratorDeclarationNode(source, name, value);
	}

	@Override
	public FieldDeclarationNode newFieldDeclarationNode(Source source,
			IdentifierNode name, TypeNode type) {
		return new CommonFieldDeclarationNode(source, name, type);
	}

	@Override
	public FieldDeclarationNode newFieldDeclarationNode(Source source,
			IdentifierNode name, TypeNode type, ExpressionNode bitFieldWidth) {
		return new CommonFieldDeclarationNode(source, name, type, bitFieldWidth);
	}

	@Override
	public OrdinaryLabelNode newStandardLabelDeclarationNode(Source source,
			IdentifierNode name, StatementNode statement) {
		CommonOrdinaryLabelNode label = new CommonOrdinaryLabelNode(source,
				name);

		label.setStatement(statement);
		return label;
	}

	@Override
	public SwitchLabelNode newCaseLabelDeclarationNode(Source source,
			ExpressionNode constantExpression, StatementNode statement) {
		CommonSwitchLabelNode label = new CommonSwitchLabelNode(source,
				constantExpression);

		label.setStatement(statement);
		return label;
	}

	@Override
	public SwitchLabelNode newDefaultLabelDeclarationNode(Source source,
			StatementNode statement) {
		CommonSwitchLabelNode label = new CommonSwitchLabelNode(source);

		label.setStatement(statement);
		return label;
	}

	@Override
	public TypedefDeclarationNode newTypedefDeclarationNode(Source source,
			IdentifierNode name, TypeNode type) {
		return new CommonTypedefDeclarationNode(source, name, type);
	}

	@Override
	public CompoundInitializerNode newCompoundInitializerNode(Source source,
			List<PairNode<DesignationNode, InitializerNode>> initList) {
		return new CommonCompoundInitializerNode(source, initList);
	}

	@Override
	public DesignationNode newDesignationNode(Source source,
			List<DesignatorNode> designators) {
		return new CommonDesignationNode(source, designators);
	}

	@Override
	public FieldDesignatorNode newFieldDesignatorNode(Source source,
			IdentifierNode name) {
		return new CommonFieldDesignatorNode(source, name);
	}

	@Override
	public ArrayDesignatorNode newArrayDesignatorNode(Source source,
			ExpressionNode index) {
		return new CommonArrayDesignatorNode(source, index);
	}

	@Override
	public CompoundStatementNode newCompoundStatementNode(Source source,
			List<BlockItemNode> items) {
		return new CommonCompoundStatementNode(source, items);
	}

	@Override
	public ExpressionStatementNode newExpressionStatementNode(
			ExpressionNode expression) {
		return new CommonExpressionStatementNode(expression.getSource(),
				expression);
	}

	@Override
	public StatementNode newNullStatementNode(Source source) {
		return new CommonNullStatementNode(source);
	}

	@Override
	public ForLoopNode newForLoopNode(Source source,
			ForLoopInitializerNode initializer, ExpressionNode condition,
			ExpressionNode incrementer, StatementNode body,
			SequenceNode<ContractNode> contracts) {
		return new CommonForLoopNode(source, condition, body, initializer,
				incrementer, contracts);
	}

	@Override
	public DeclarationListNode newForLoopInitializerNode(Source source,
			List<VariableDeclarationNode> declarations) {
		return new CommonDeclarationListNode(source, declarations);
	}

	@Override
	public LoopNode newWhileLoopNode(Source source, ExpressionNode condition,
			StatementNode body, SequenceNode<ContractNode> contracts) {
		return new CommonLoopNode(source, LoopKind.WHILE, condition, body,
				contracts);
	}

	@Override
	public LoopNode newDoLoopNode(Source source, ExpressionNode condition,
			StatementNode body, SequenceNode<ContractNode> contracts) {
		return new CommonLoopNode(source, LoopKind.DO_WHILE, condition, body,
				contracts);
	}

	@Override
	public GotoNode newGotoNode(Source source, IdentifierNode label) {
		return new CommonGotoNode(source, label);
	}

	@Override
	public IfNode newIfNode(Source source, ExpressionNode condition,
			StatementNode trueBranch) {
		return new CommonIfNode(source, condition, trueBranch);
	}

	@Override
	public IfNode newIfNode(Source source, ExpressionNode condition,
			StatementNode trueBranch, StatementNode falseBranch) {
		return new CommonIfNode(source, condition, trueBranch, falseBranch);
	}

	@Override
	public JumpNode newContinueNode(Source source) {
		return new CommonJumpNode(source, JumpKind.CONTINUE);
	}

	@Override
	public JumpNode newBreakNode(Source source) {
		return new CommonJumpNode(source, JumpKind.BREAK);
	}

	@Override
	public ReturnNode newReturnNode(Source source, ExpressionNode argument) {
		return new CommonReturnNode(source, argument);
	}

	@Override
	public LabeledStatementNode newLabeledStatementNode(Source source,
			LabelNode label, StatementNode statement) {
		return new CommonLabeledStatementNode(source, label, statement);
	}

	@Override
	public SwitchNode newSwitchNode(Source source, ExpressionNode condition,
			StatementNode body) {
		CommonSwitchNode switchNode = new CommonSwitchNode(source, condition,
				body);

		return switchNode;
	}

	@Override
	public CivlForNode newCivlForNode(Source source, boolean isParallel,
			DeclarationListNode variables, ExpressionNode domain,
			StatementNode body, ExpressionNode invariant) {
		return new CommonCivlForNode(source, isParallel, variables, domain,
				body, invariant);
	}

	@Override
	public StaticAssertionNode newStaticAssertionNode(Source source,
			ExpressionNode expression, StringLiteralNode message) {
		return new CommonStaticAssertionNode(source, expression, message);
	}

	@Override
	public PragmaNode newPragmaNode(Source source, IdentifierNode identifier,
			CivlcTokenSequence producer, CivlcToken newlineToken) {
		newlineToken.setType(CivlCParser.EOF);
		return new CommonPragmaNode(source, identifier, producer, newlineToken);
	}

	@Override
	public FunctionDefinitionNode newFunctionDefinitionNode(Source source,
			IdentifierNode name, FunctionTypeNode type,
			SequenceNode<ContractNode> contract, CompoundStatementNode body) {
		return new CommonFunctionDefinitionNode(source, name, type, contract,
				body);
	}

	@Override
	public AbstractFunctionDefinitionNode newAbstractFunctionDefinitionNode(
			Source source, IdentifierNode name, FunctionTypeNode type,
			SequenceNode<ContractNode> contract, int continuity) {
		return new CommonAbstractFunctionDefinitionNode(source, name, type,
				contract, continuity);
	}

	@Override
	public SequenceNode<BlockItemNode> newTranslationUnitNode(Source source,
			List<BlockItemNode> definitions) {
		return newSequenceNode(source, "TranslationUnit", definitions);
	}

	@Override
	public SequenceNode<BlockItemNode> newProgramNode(Source source,
			List<BlockItemNode> definitions) {
		return newSequenceNode(source, "Program", definitions);
	}

	@Override
	public Value getConstantValue(ExpressionNode expression)
			throws SyntaxException {
		CommonExpressionNode commonNode = (CommonExpressionNode) expression;

		if (commonNode.constantComputed()) {
			return commonNode.getConstantValue();
		} else {
			Value value = valueFactory.evaluate(expression);

			commonNode.setConstantValue(value);
			return value;
		}
	}

	@Override
	public SpawnNode newSpawnNode(Source source, FunctionCallNode callNode) {
		return new CommonSpawnNode(source, callNode);
	}

	@Override
	public CallsNode newCallsNode(Source source, FunctionCallNode callNode) {
		return new CommonCallsNode(source, callNode);
	}

	@Override
	public RemoteExpressionNode newRemoteExpressionNode(Source source,
			ExpressionNode left, IdentifierExpressionNode right) {
		return new CommonRemoteExpressionNode(source, left, right);
	}

	@Override
	public ScopeOfNode newScopeOfNode(Source source,
			IdentifierExpressionNode variableExpression) {
		return new CommonScopeOfNode(source, variableExpression);
	}

	// @Override
	// public AssumeNode newAssumeNode(Source source, ExpressionNode expression)
	// {
	// return new CommonAssumeNode(source, expression);
	// }
	//
	// @Override
	// public AssertNode newAssertNode(Source source, ExpressionNode expression,
	// SequenceNode<ExpressionNode> explanation) {
	// return new CommonAssertNode(source, expression, explanation);
	// }

	@Override
	public WhenNode newWhenNode(Source source, ExpressionNode guard,
			StatementNode body) {
		return new CommonWhenNode(source, guard, body);
	}

	@Override
	public ChooseStatementNode newChooseStatementNode(Source source,
			List<StatementNode> statements) {
		return new CommonChooseStatementNode(source, statements);
	}

	@Override
	public ConstantNode newBooleanConstantNode(Source source, boolean value) {
		IntegerValue theValue;
		String representation;

		if (value) {
			representation = "\\true";
			theValue = valueFactory.integerValue(booleanType, 1);
		} else {
			representation = "\\false";
			theValue = valueFactory.integerValue(booleanType, 0);
		}
		return new CommonIntegerConstantNode(source, representation, theValue);
	}

	@Override
	public ExpressionNode newSelfNode(Source source) {
		ExpressionNode result = new CommonSelfNode(source, processType);

		result.setInitialType(processType);
		return result;
	}

	@Override
	public ExpressionNode newHereNode(Source source) {
		ExpressionNode result = new CommonHereOrRootNode(source, "$here",
				scopeType);

		result.setInitialType(scopeType);
		return result;
	}

	@Override
	public ExpressionNode newRootNode(Source source) {
		ExpressionNode result = new CommonHereOrRootNode(source, "$root",
				scopeType);

		result.setInitialType(scopeType);
		return result;
	}

	@Override
	public ExpressionNode newResultNode(Source source) {
		return new CommonResultNode(source);
	}

	@Override
	public RequiresNode newRequiresNode(Source source, ExpressionNode expression) {
		return new CommonRequiresNode(source, expression);
	}

	@Override
	public EnsuresNode newEnsuresNode(Source source, ExpressionNode expression) {
		return new CommonEnsuresNode(source, expression);
	}

	@Override
	public QuantifiedExpressionNode newQuantifiedExpressionNode(Source source,
			Quantifier quantifier, VariableDeclarationNode variable,
			ExpressionNode restriction, ExpressionNode expression) {
		return new CommonQuantifiedExpressionNode(source, quantifier, variable,
				restriction, expression);
	}

	@Override
	public QuantifiedExpressionNode newQuantifiedExpressionNode(Source source,
			Quantifier quantifier, VariableDeclarationNode variable,
			ExpressionNode lower, ExpressionNode upper,
			ExpressionNode expression) {
		return new CommonQuantifiedExpressionNode(source, quantifier, variable,
				lower, upper, expression);
	}

	@Override
	public DerivativeExpressionNode newDerivativeExpressionNode(
			Source source,
			ExpressionNode function,
			SequenceNode<PairNode<IdentifierExpressionNode, IntegerConstantNode>> partials,
			SequenceNode<ExpressionNode> arguments) {
		return new CommonDerivativeExpressionNode(source, function, partials,
				arguments);
	}

	@Override
	public void setConstantValue(ExpressionNode expression, Value value) {
		((CommonExpressionNode) expression).setConstantValue(value);
	}

	@Override
	public AtomicNode newAtomicStatementNode(Source statementSource,
			boolean deterministic, StatementNode body) {
		return new CommonAtomicNode(statementSource, deterministic, body);
	}

	@Override
	public ExpressionNode newProcnullNode(Source source) {
		ExpressionNode result = new CommonProcnullNode(source, processType);

		result.setInitialType(processType);
		return result;
	}

	/* *************************** OpenMP Section ************************** */

	@Override
	public OmpParallelNode newOmpParallelNode(Source source,
			StatementNode statement) {
		return new CommonOmpParallelNode(source, statement);
	}

	@Override
	public OmpForNode newOmpForNode(Source source, StatementNode statement) {
		return new CommonOmpForNode(source, statement);
	}

	@Override
	public OmpSyncNode newOmpMasterNode(Source source, StatementNode statement) {
		return new CommonOmpSyncNode(source, OmpSyncNodeKind.MASTER, statement);
	}

	@Override
	public OmpSyncNode newOmpAtomicNode(Source source, StatementNode statement) {
		return new CommonOmpSyncNode(source, OmpSyncNodeKind.OMPATOMIC,
				statement);
	}

	@Override
	public OmpSyncNode newOmpBarrierNode(Source source) {
		return new CommonOmpSyncNode(source, OmpSyncNodeKind.BARRIER, null);
	}

	@Override
	public OmpWorksharingNode newOmpSectionsNode(Source source,
			StatementNode statement) {
		return new CommonOmpWorkshareNode(source,
				OmpWorksharingNodeKind.SECTIONS, statement);
	}

	@Override
	public OmpWorksharingNode newOmpSectionNode(Source source,
			StatementNode statement) {
		return new CommonOmpWorkshareNode(source,
				OmpWorksharingNodeKind.SECTION, statement);
	}

	@Override
	public OmpDeclarativeNode newOmpThreadprivateNode(Source source,
			SequenceNode<IdentifierExpressionNode> variables) {
		return new CommonOmpDeclarativeNode(source, variables);
	}

	@Override
	public OmpSymbolReductionNode newOmpSymbolReductionNode(Source source,
			Operator operator, SequenceNode<IdentifierExpressionNode> variables) {
		return new CommonOmpSymbolReductionNode(source, operator, variables);
	}

	@Override
	public OmpSyncNode newOmpCriticalNode(Source source, IdentifierNode name,
			StatementNode statement) {
		OmpSyncNode criticalNode = new CommonOmpSyncNode(source,
				OmpSyncNodeKind.CRITICAL, statement);

		criticalNode.setCriticalName(name);
		return criticalNode;
	}

	@Override
	public OmpSyncNode newOmpFlushNode(Source source,
			SequenceNode<IdentifierExpressionNode> variables) {
		OmpSyncNode flushNode = new CommonOmpSyncNode(source,
				OmpSyncNodeKind.FLUSH, null);

		flushNode.setFlushedList(variables);
		return flushNode;
	}

	@Override
	public OmpSyncNode newOmpOrederedNode(Source source, StatementNode statement) {
		return new CommonOmpSyncNode(source, OmpSyncNodeKind.ORDERED, statement);
	}

	@Override
	public OmpWorksharingNode newOmpSingleNode(Source source,
			StatementNode statement) {
		return new CommonOmpWorkshareNode(source,
				OmpWorksharingNodeKind.SINGLE, statement);
	}

	@Override
	public OmpFunctionReductionNode newOmpFunctionReductionNode(Source source,
			IdentifierExpressionNode function,
			SequenceNode<IdentifierExpressionNode> variables) {
		return new CommonOmpFunctionReductionNode(source, function, variables);
	}

	@Override
	public OmpWorksharingNode newWorksharingNode(Source source,
			OmpWorksharingNodeKind kind) {
		return new CommonOmpWorkshareNode(source, kind, null);
	}

	@Override
	public RegularRangeNode newRegularRangeNode(Source source,
			ExpressionNode low, ExpressionNode high) {
		return new CommonRegularRangeNode(source, low, high);
	}

	@Override
	public RegularRangeNode newRegularRangeNode(Source source,
			ExpressionNode low, ExpressionNode high, ExpressionNode step) {
		return new CommonRegularRangeNode(source, low, high, step);
	}

	@Override
	public OperatorNode newOperatorNode(Source source, Operator operator,
			ExpressionNode argument) {
		return new CommonOperatorNode(source, operator, Arrays.asList(argument));
	}

	@Override
	public OperatorNode newOperatorNode(Source source, Operator operator,
			ExpressionNode arg0, ExpressionNode arg1) {
		return new CommonOperatorNode(source, operator, Arrays.asList(arg0,
				arg1));
	}

	@Override
	public OperatorNode newOperatorNode(Source source, Operator operator,
			ExpressionNode arg0, ExpressionNode arg1, ExpressionNode arg2) {
		return new CommonOperatorNode(source, operator, Arrays.asList(arg0,
				arg1, arg2));
	}

	@Override
	public DependsNode newDependsNode(Source source, ExpressionNode condition,
			SequenceNode<DependsEventNode> eventList) {
		return new CommonDependsNode(source, eventList);
	}

	@Override
	public GuardsNode newGuardNode(Source source, ExpressionNode expression) {
		return new CommonGuardNode(source, expression);
	}

	@Override
	public AssignsOrReadsNode newAssignsNode(Source source,
			SequenceNode<ExpressionNode> expressionList) {
		return new CommonAssignsOrReadsNode(source, true, expressionList);
	}

	@Override
	public AssignsOrReadsNode newReadsNode(Source source,
			SequenceNode<ExpressionNode> expressionList) {
		return new CommonAssignsOrReadsNode(source, false, expressionList);
	}

	@Override
	public WildcardNode newWildcardNode(Source source) {
		return new CommonWildcardNode(source);
	}

	@Override
	public Configuration configuration() {
		return this.configuration;
	}

	@Override
	public StatementExpressionNode newStatementExpressionNode(Source source,
			CompoundStatementNode statement) {
		return new CommonStatementExpressionNode(source, statement);
	}

	@Override
	public TypeofNode newTypeofNode(Source source, ExpressionNode expression) {
		return new CommonTypeofNode(source, expression);
	}

	@Override
	public MemoryEventNode newMemoryEventNode(Source source,
			MemoryEventNodeKind kind, SequenceNode<ExpressionNode> memoryList) {
		return new CommonMemoryEventNode(source, kind, memoryList);
	}

	@Override
	public CompositeEventNode newOperatorEventNode(Source source,
			EventOperator op, DependsEventNode left, DependsEventNode right) {
		return new CommonCompositeEventNode(source, op, left, right);
	}

	@Override
	public NothingNode newNothingNode(Source source) {
		return new CommonNothingNode(source);
	}

	@Override
	public BehaviorNode newBehaviorNode(Source source, IdentifierNode name,
			SequenceNode<ContractNode> body) {
		return new CommonBehaviorNode(source, name, body);
	}

	@Override
	public CompletenessNode newCompletenessNode(Source source,
			boolean isComplete, SequenceNode<IdentifierNode> idList) {
		return new CommonCompletenessNode(source, isComplete, idList);
	}

	@Override
	public AssumesNode newAssumesNode(Source source, ExpressionNode predicate) {
		return new CommonAssumesNode(source, predicate);
	}

	@Override
	public NoactNode newNoactNode(Source source) {
		return new CommonNoactNode(source);
	}

	@Override
	public AnyactNode newAnyactNode(Source source) {
		return new CommonAnyactNode(source);
	}

	@Override
	public CallEventNode newCallEventNode(Source source,
			IdentifierExpressionNode function, SequenceNode<ExpressionNode> args) {
		return new CommonCallEventNode(source, function, args);
	}

	@Override
	public MPICollectiveBlockNode newMPICollectiveBlockNode(Source source,
			ExpressionNode mpiComm, MPICollectiveKind kind,
			SequenceNode<ContractNode> body) {
		return new CommonMPICollectiveBlockNode(source, mpiComm, kind, body);
	}

	@Override
	public MPIContractConstantNode newMPIConstantNode(Source source,
			String stringRepresentation, MPIConstantKind kind,
			ConstantKind constKind) {
		return new CommonMPIConstantNode(source, stringRepresentation, kind,
				constKind);
	}

	@Override
	public MPIContractExpressionNode newMPIExpressionNode(Source source,
			List<ExpressionNode> arguments, MPIContractExpressionKind kind,
			String exprName) {
		return new CommonMPIContractExpressionNode(source, arguments, kind,
				exprName);
	}

	@Override
	public TypeFactory typeFactory() {
		return typeFactory;
	}

	@Override
	public InvariantNode newInvariantNode(Source source,
			boolean isLoopInvariant, ExpressionNode expression) {
		return new CommonInvariantNode(source, isLoopInvariant, expression);
	}

	@Override
	public PureNode newPureNode(Source source) {
		return new CommonPureNode(source);
	}

	@Override
	public MemorySetNode newMemorySetNode(Source source, ExpressionNode term,
			SequenceNode<VariableDeclarationNode> binders,
			ExpressionNode predicate) {
		return new CommonMemorySetNode(source, term, binders, predicate);
	}

	@Override
	public ArrayTypeNode newArrayTypeNode(Source source, TypeNode elementType,
			ExpressionNode extent, ExpressionNode startIndex) {
		return new CommonArrayTypeNode(source, elementType, extent, startIndex);
	}

	@Override
	public ContractVerifyNode newContractVerifyNode(Source source,
			ExpressionNode function, List<ExpressionNode> arguments,
			SequenceNode<ExpressionNode> scopeList) {
		SequenceNode<ExpressionNode> argumentSequenceNode = newSequenceNode(
				source, "ActualParameterList", arguments);

		return new CommonContractVerifyNode(source, function, null,
				argumentSequenceNode, scopeList);
	}
}
