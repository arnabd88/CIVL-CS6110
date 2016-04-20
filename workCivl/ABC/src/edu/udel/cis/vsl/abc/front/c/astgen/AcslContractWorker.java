package edu.udel.cis.vsl.abc.front.c.astgen;

import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.AMPERSAND;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.ANYACT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.ARROW;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.ASSIGN;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.BAR;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.BITXOR;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.BOOLEAN;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.CALL;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.CAST;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.CHAR;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.CHARACTER_CONSTANT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.COMMA;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.COMP;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.C_TYPE;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.DIVIDE;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.DOT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.DOTDOT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.DOUBLE;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.ELLIPSIS;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.EQ;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.EVENT_BASE;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.EVENT_INTS;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.EVENT_PARENTHESIZED;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.EVENT_PLUS;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.EVENT_SUB;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.EXISTS;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.FALSE;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.FLOAT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.FLOATING_CONSTANT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.FORALL;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.GT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.GTE;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.HASH;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.ID;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.IMPLY;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.INDEX;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.INT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.INTEGER;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.INTEGER_CONSTANT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.LAND;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.LOGIC_TYPE;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.LONG;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.LOR;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.LT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.LTE;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.MOD;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.MPI_CONSTANT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.MPI_EXPRESSION;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.NEQ;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.NOACT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.NOT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.NOTHING;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.OPERATOR;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.PLUS;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.QUESTION;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.REACH;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.READ;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.REAL;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.REMOTE_ACCESS;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.RESULT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.SELF;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.SET_BINDERS;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.SHIFTLEFT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.SHIFTRIGHT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.SHORT;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.SIZEOF;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.STAR;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.STRING_LITERAL;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.SUB;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.TERM_PARENTHESIZED;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.TRUE;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.TYPE_BUILTIN;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.TYPE_ID;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.VALID;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.VAR_ID;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.VAR_ID_BASE;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.VAR_ID_SQUARE;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.VAR_ID_STAR;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.VOID;
import static edu.udel.cis.vsl.abc.front.c.parse.AcslParser.WRITE;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.antlr.runtime.Token;
import org.antlr.runtime.tree.CommonTree;

import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssignsOrReadsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.AssumesNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.BehaviorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CompletenessNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CompositeEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.CompositeEventNode.EventOperator;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.DependsEventNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.DependsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.EnsuresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.GuardsNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPICollectiveBlockNode.MPICollectiveKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractConstantNode.MPIConstantKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MPIContractExpressionNode.MPIContractExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.MemoryEventNode.MemoryEventNodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.RequiresNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CharacterConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode.ConstantKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.EnumerationConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FloatingConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StringLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardSignedIntegerType.SignedIntKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardUnsignedIntegerType.UnsignedIntKind;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.TypeFactory;
import edu.udel.cis.vsl.abc.front.c.parse.AcslParser;
import edu.udel.cis.vsl.abc.front.c.ptree.CParseTree;
import edu.udel.cis.vsl.abc.front.common.astgen.SimpleScope;
import edu.udel.cis.vsl.abc.token.IF.CharacterToken;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.StringToken;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

public class AcslContractWorker {

	private CParseTree parseTree;
	private NodeFactory nodeFactory;
	private TokenFactory tokenFactory;
	private TypeFactory typeFactory;
	private Formation formation;

	/* ******************** Constants ******************* */
	private final String MPI_COMM_RANK = "\\mpi_comm_rank";
	private final String MPI_COMM_SIZE = "\\mpi_comm_size";

	public AcslContractWorker(NodeFactory factory, TokenFactory tokenFactory,
			CParseTree parseTree) {
		this.nodeFactory = factory;
		this.tokenFactory = tokenFactory;
		this.parseTree = parseTree;
		this.typeFactory = nodeFactory.typeFactory();
		formation = tokenFactory.newTransformFormation("ACSL", "contract");
	}

	public List<ContractNode> generateASTNodes(SimpleScope scope)
			throws SyntaxException {
		CommonTree contractTree = parseTree.getRoot();

		switch (contractTree.getType()) {
		case AcslParser.FUNC_CONTRACT: {
			CommonTree pure = (CommonTree) contractTree.getChild(1);
			List<ContractNode> result = translateFunctionContractBlock(
					(CommonTree) contractTree.getChild(0), scope);

			if (pure != null) {
				result.add(this.nodeFactory.newPureNode(this.newSource(pure)));
			}
			return result;
		}
		case AcslParser.LOOP_CONTRACT:
			return translateLoopContractBlock(
					(CommonTree) contractTree.getChild(0), scope);
		default:
			throw this.error("unknown kind of contract", contractTree);
		}
	}

	private List<ContractNode> translateLoopContractBlock(CommonTree tree,
			SimpleScope scope) throws SyntaxException {
		int numChildren = tree.getChildCount();
		List<ContractNode> result = new ArrayList<>();

		assert tree.getType() == AcslParser.LOOP_CONTRACT_BLOCK;
		for (int i = 0; i < numChildren; i++) {
			CommonTree loopIterm = (CommonTree) tree.getChild(i);
			int loopItemKind = loopIterm.getType();

			switch (loopItemKind) {
			case AcslParser.LOOP_CLAUSE:
				result.add(this.translateLoopClause(
						(CommonTree) loopIterm.getChild(0), scope));
				break;
			case AcslParser.LOOP_BEHAVIOR:
			case AcslParser.LOOP_VARIANT:
			default:
				throw this.error("unknown kind of loop contract", loopIterm);
			}
		}
		return result;
	}

	private ContractNode translateLoopClause(CommonTree tree, SimpleScope scope)
			throws SyntaxException {
		int loopClauseKind = tree.getType();
		Source source = this.newSource(tree);

		switch (loopClauseKind) {
		case AcslParser.LOOP_INVARIANT: {
			CommonTree exprTree = (CommonTree) tree.getChild(0);
			ExpressionNode expression = this.translateExpression(exprTree,
					scope);

			return this.nodeFactory.newInvariantNode(source, true, expression);
		}
		case AcslParser.LOOP_ASSIGNS:
		case AcslParser.LOOP_ALLOC:
		case AcslParser.LOOP_FREE:
		default:
			throw this.error("unkown kind of loop contract clause", tree);
		}
	}

	private List<ContractNode> translateFunctionContractBlock(CommonTree tree,
			SimpleScope scope) throws SyntaxException {
		int numChildren = tree.getChildCount();
		List<ContractNode> result = new ArrayList<>();

		assert tree.getType() == AcslParser.FUNC_CONTRACT_BLOCK;
		for (int i = 0; i < numChildren; i++) {
			CommonTree child = (CommonTree) tree.getChild(i);
			int childKind = child.getType();

			switch (childKind) {
			case AcslParser.CLAUSE_NORMAL:
				result.add(this.translateContractClause(
						(CommonTree) child.getChild(0), scope));
				break;
			case AcslParser.CLAUSE_BEHAVIOR:
				result.add(this.translateBehavior(
						(CommonTree) child.getChild(0), scope));
				break;
			case AcslParser.CLAUSE_COMPLETE:
				result.add(this.translateCompleteness(
						(CommonTree) child.getChild(0), scope));
				break;
			case AcslParser.MPI_COLLECTIVE:
				result.add(this.translateMPICollectiveBlock(
						this.parseTree.source(child), child, scope));
				break;
			default:
				throw this.error("Unknown contract kind", tree);
			}
		}
		return result;
	}

	private CompletenessNode translateCompleteness(CommonTree tree,
			SimpleScope scope) throws SyntaxException {
		int kind = tree.getType();
		boolean isComplete = false;
		SequenceNode<IdentifierNode> idList = this.translateIdList(
				(CommonTree) tree.getChild(0), scope);
		Source source = this.parseTree.source(tree);

		switch (kind) {
		case AcslParser.BEHAVIOR_COMPLETE:
			isComplete = true;
			break;
		case AcslParser.BEHAVIOR_DISJOINT:
			break;
		default:
			throw this.error("Unknown kind of completeness clause", tree);
		}
		return this.nodeFactory.newCompletenessNode(source, isComplete, idList);
	}

	private SequenceNode<IdentifierNode> translateIdList(CommonTree tree,
			SimpleScope scope) {
		int numChildren = tree.getChildCount();
		List<IdentifierNode> list = new ArrayList<>();
		Source source = this.parseTree.source(tree);

		for (int i = 0; i < numChildren; i++) {
			CommonTree idTree = (CommonTree) tree.getChild(i);

			list.add(this.translateIdentifier(idTree));
		}
		return this.nodeFactory.newSequenceNode(source, "ID list", list);
	}

	private BehaviorNode translateBehavior(CommonTree tree, SimpleScope scope)
			throws SyntaxException {
		CommonTree idTree = (CommonTree) tree.getChild(0);
		CommonTree bodyTree = (CommonTree) tree.getChild(1);
		IdentifierNode id = this.translateIdentifier(idTree);
		SequenceNode<ContractNode> body = this.translateBehaviorBody(bodyTree,
				scope);

		return this.nodeFactory.newBehaviorNode(this.parseTree.source(tree),
				id, body);
	}

	private SequenceNode<ContractNode> translateBehaviorBody(CommonTree tree,
			SimpleScope scope) throws SyntaxException {
		Source source = this.parseTree.source(tree);
		int numChildren = tree.getChildCount();
		List<ContractNode> clauses = new ArrayList<>();

		for (int i = 0; i < numChildren; i++) {
			CommonTree clause = (CommonTree) tree.getChild(i);

			clauses.add(this.translateContractClause(clause, scope));
		}
		return this.nodeFactory.newSequenceNode(source, "behavior body",
				clauses);
	}

	private ContractNode translateContractClause(CommonTree tree,
			SimpleScope scope) throws SyntaxException {
		int kind = tree.getType();

		switch (kind) {
		case AcslParser.REQUIRES:
			return this.translateRequires(tree, scope);
		case AcslParser.ENSURES:
			return this.translateEnsures(tree, scope);
		case AcslParser.ASSIGNS:
			return this.translateReadsOrAssigns(tree, scope, false);
		case AcslParser.ASSUMES:
			return this.translateAssumes(tree, scope);
		case AcslParser.READS:
			return this.translateReadsOrAssigns(tree, scope, true);
		case AcslParser.DEPENDS:
			return this.translateDepends(tree, scope);
		case AcslParser.GUARDS:
			return this.translateGuards(tree, scope);
		default:
			throw this.error("Unknown contract clause kind", tree);
		}
	}

	private GuardsNode translateGuards(CommonTree tree, SimpleScope scope)
			throws SyntaxException {
		CommonTree expressionTree = (CommonTree) tree.getChild(0);

		return this.nodeFactory.newGuardNode(this.newSource(tree),
				this.translateExpression(expressionTree, scope));
	}

	private AssumesNode translateAssumes(CommonTree tree, SimpleScope scope)
			throws SyntaxException {
		CommonTree exprTree = (CommonTree) tree.getChild(0);
		ExpressionNode predicate = this.translateExpression(exprTree, scope);
		Source source = this.parseTree.source(tree);

		return this.nodeFactory.newAssumesNode(source, predicate);
	}

	private AssignsOrReadsNode translateReadsOrAssigns(CommonTree tree,
			SimpleScope scope, boolean isRead) throws SyntaxException {
		Source source = this.parseTree.source(tree);
		SequenceNode<ExpressionNode> memoryList = translateArgumentList(
				(CommonTree) tree.getChild(0), scope);

		if (isRead)
			return this.nodeFactory.newReadsNode(source, memoryList);
		else
			return this.nodeFactory.newAssignsNode(source, memoryList);
	}

	private DependsNode translateDepends(CommonTree tree, SimpleScope scope)
			throws SyntaxException {
		Source source = this.parseTree.source(tree);
		CommonTree argumentTree = (CommonTree) tree.getChild(0);
		SequenceNode<DependsEventNode> argumentList = this
				.translateDependsEventList(argumentTree, scope);

		return this.nodeFactory.newDependsNode(source, null, argumentList);
	}

	private SequenceNode<ExpressionNode> translateArgumentList(CommonTree tree,
			SimpleScope scope) throws SyntaxException {
		int numChildren = tree.getChildCount();
		List<ExpressionNode> list = new ArrayList<>();

		for (int i = 0; i < numChildren; i++) {
			CommonTree arg = (CommonTree) tree.getChild(i);

			list.add(this.translateExpression(arg, scope));
		}
		return this.nodeFactory.newSequenceNode(this.parseTree.source(tree),
				"argument list", list);
	}

	private SequenceNode<DependsEventNode> translateDependsEventList(
			CommonTree tree, SimpleScope scope) throws SyntaxException {
		int numChildren = tree.getChildCount();
		List<DependsEventNode> events = new ArrayList<>();
		Source source = this.parseTree.source(tree);

		for (int i = 0; i < numChildren; i++) {
			CommonTree event = (CommonTree) tree.getChild(i);

			events.add(this.translateDependsEvent(event, scope));
		}
		return this.nodeFactory.newSequenceNode(source, "depends event list",
				events);
	}

	private DependsEventNode translateDependsEvent(CommonTree tree,
			SimpleScope scope) throws SyntaxException {
		int kind = tree.getType();

		switch (kind) {
		case EVENT_PLUS:
			EventOperator operator = EventOperator.UNION;
			return translateOperatorEvent(tree, operator, scope);
		case EVENT_SUB:
			operator = EventOperator.DIFFERENCE;
			return translateOperatorEvent(tree, operator, scope);
		case EVENT_INTS:
			operator = EventOperator.INTERSECT;
			return translateOperatorEvent(tree, operator, scope);
		case EVENT_BASE:
			return translateDependsEventBase((CommonTree) tree.getChild(0),
					scope);
		default:
			throw this.error("unknown kind of operator for depends events",
					tree);
		}
	}

	private CompositeEventNode translateOperatorEvent(CommonTree tree,
			EventOperator op, SimpleScope scope) throws SyntaxException {
		Source source = this.parseTree.source(tree);
		CommonTree leftTree = (CommonTree) tree.getChild(0), rightTree = (CommonTree) tree
				.getChild(1);
		DependsEventNode left = this.translateDependsEventBase(leftTree, scope), right = this
				.translateDependsEventBase(rightTree, scope);

		return this.nodeFactory.newOperatorEventNode(source, op, left, right);
	}

	private DependsEventNode translateDependsEventBase(CommonTree tree,
			SimpleScope scope) throws SyntaxException {
		int kind = tree.getType();
		Source source = this.parseTree.source(tree);

		switch (kind) {
		case READ: {
			SequenceNode<ExpressionNode> memList = this.translateArgumentList(
					(CommonTree) tree.getChild(0), scope);

			return nodeFactory.newMemoryEventNode(source,
					MemoryEventNodeKind.READ, memList);
		}
		case WRITE: {
			SequenceNode<ExpressionNode> memList = this.translateArgumentList(
					(CommonTree) tree.getChild(0), scope);

			return nodeFactory.newMemoryEventNode(source,
					MemoryEventNodeKind.WRITE, memList);
		}
		case REACH: {
			SequenceNode<ExpressionNode> memList = this.translateArgumentList(
					(CommonTree) tree.getChild(0), scope);

			return nodeFactory.newMemoryEventNode(source,
					MemoryEventNodeKind.REACH, memList);

		}
		case CALL: {
			IdentifierNode function = this
					.translateIdentifier((CommonTree) tree.getChild(0));
			SequenceNode<ExpressionNode> args = this.translateArgumentList(
					(CommonTree) tree.getChild(1), scope);

			return nodeFactory.newCallEventNode(
					source,
					this.nodeFactory.newIdentifierExpressionNode(
							function.getSource(), function), args);
		}
		case NOACT:
			return nodeFactory.newNoactNode(source);
		case ANYACT:
			return nodeFactory.newAnyactNode(source);
		case EVENT_PARENTHESIZED:
			return translateDependsEvent((CommonTree) tree.getChild(0), scope);
		default:
			throw this.error("unknown kind of nodes for depends events", tree);
		}
	}

	private RequiresNode translateRequires(CommonTree tree, SimpleScope scope)
			throws SyntaxException {
		CommonTree expressionTree = (CommonTree) tree.getChild(0);
		Source source = this.newSource(tree);
		ExpressionNode expression = this.translateExpression(expressionTree,
				scope);

		return nodeFactory.newRequiresNode(source, expression);
	}

	private EnsuresNode translateEnsures(CommonTree tree, SimpleScope scope)
			throws SyntaxException {
		Source source = this.newSource(tree);
		CommonTree expressionTree = (CommonTree) tree.getChild(0);
		ExpressionNode expression = this.translateExpression(expressionTree,
				scope);

		return nodeFactory.newEnsuresNode(source, expression);
	}

	/**
	 * Translates an expression.
	 * 
	 * @param expressionTree
	 *            any CommonTree node representing an expression
	 * @return an ExpressionNode
	 * @throws SyntaxException
	 */
	private ExpressionNode translateExpression(CommonTree expressionTree,
			SimpleScope scope) throws SyntaxException {
		Source source = this.newSource(expressionTree);
		int kind = expressionTree.getType();

		switch (kind) {
		case INTEGER_CONSTANT:
			return translateIntegerConstant(source, expressionTree);
		case FLOATING_CONSTANT:
			return translateFloatingConstant(source, expressionTree);
		case CHARACTER_CONSTANT:
			return translateCharacterConstant(source, expressionTree);
		case STRING_LITERAL:
			return translateStringLiteral(source, expressionTree);
		case ID:
			return nodeFactory.newIdentifierExpressionNode(source,
					translateIdentifier(expressionTree));
		case TERM_PARENTHESIZED:
			return translateExpression((CommonTree) expressionTree.getChild(0),
					scope);
		case CALL:
			return translateCall(source, expressionTree, scope);
		case DOT:
		case ARROW:
			return translateDotOrArrow(source, expressionTree, scope);
		case OPERATOR:
			return translateOperatorExpression(source, expressionTree, scope);
		case TRUE:
			return translateTrue(source);
		case FALSE:
			return translateFalse(source);
		case RESULT:
			return nodeFactory.newResultNode(source);
		case SELF:
			return nodeFactory.newSelfNode(source);
		case DOTDOT:
			return translateRegularRange(source, expressionTree, scope);
		case WRITE:
			return translateWriteEvent(source, expressionTree, scope);
		case NOTHING:
			return this.nodeFactory.newNothingNode(source);
		case ELLIPSIS:
			return this.nodeFactory.newWildcardNode(source);
		case MPI_CONSTANT:
			return translateMPIConstantNode(expressionTree, source);
		case MPI_EXPRESSION:
			return translateMPIExpressionNode(expressionTree, source, scope);
		case VALID:
			return this.translateValidNode(expressionTree, source, scope);
		case SET_BINDERS:
			return this.translateSetBinders(expressionTree, source, scope);
		case REMOTE_ACCESS:
			return translateRemoteExpression(expressionTree, source, scope);
		case SIZEOF:
			// return translateSizeOf(source, expressionTree, scope);
		case FORALL:
			// return translateForall(source, expressionTree, scope);
		case EXISTS:
			// return translateExists(source, expressionTree, scope);
		case CAST:
			// return nodeFactory.newCastNode(
			// source,
			// translateTypeName((CommonTree) expressionTree.getChild(0),
			// scope),
			// translateExpression(
			// (CommonTree) expressionTree.getChild(1), scope));
		default:
			throw error("Unknown expression kind", expressionTree);
		} // end switch
	}

	/**
	 * <pre>
	 * LCURLY term BAR binders (SEMICOL term)? RCURLY 
	 *   ->^(SET_BINDERS term binders term?)
	 * </pre>
	 * 
	 * @param tree
	 * @param source
	 * @param scope
	 * @return
	 * @throws SyntaxException
	 */
	private ExpressionNode translateSetBinders(CommonTree tree, Source source,
			SimpleScope scope) throws SyntaxException {
		SimpleScope newScope = new SimpleScope(scope);
		CommonTree termTree = (CommonTree) tree.getChild(0);
		CommonTree bindersTree = (CommonTree) tree.getChild(1);
		CommonTree predicateTree = tree.getChildCount() > 2 ? (CommonTree) tree
				.getChild(2) : null;
		ExpressionNode term = this.translateExpression(termTree, newScope), predicate = null;
		SequenceNode<VariableDeclarationNode> binders = this.translateBinders(
				bindersTree, source, newScope);

		if (predicateTree != null)
			predicate = this.translateExpression(predicateTree, newScope);
		return this.nodeFactory.newMemorySetNode(source, term, binders,
				predicate);
	}

	private ExpressionNode translateRemoteExpression(CommonTree tree,
			Source source, SimpleScope scope) throws SyntaxException {
		SimpleScope newScope = new SimpleScope(scope);
		CommonTree var = (CommonTree) tree.getChild(0);
		CommonTree proc = (CommonTree) tree.getChild(1);
		ExpressionNode varExpr, procExpr;

		varExpr = translateExpression(var, newScope);
		procExpr = translateExpression(proc, newScope);
		if (!varExpr.expressionKind().equals(
				ExpressionKind.IDENTIFIER_EXPRESSION))
			this.error(
					"The first operand of a remote access operator must be an identifier: "
							+ varExpr, var);
		return nodeFactory.newRemoteExpressionNode(source, procExpr,
				(IdentifierExpressionNode) varExpr);

	}

	private SequenceNode<VariableDeclarationNode> translateBinders(
			CommonTree tree, Source source, SimpleScope scope)
			throws SyntaxException {
		int count = tree.getChildCount();
		List<VariableDeclarationNode> vars = new LinkedList<>();

		for (int i = 0; i < count; i++) {
			CommonTree binder = (CommonTree) tree.getChild(i);

			vars.addAll(this.translateBinder(binder, scope));
		}
		return this.nodeFactory.newSequenceNode(source, "Binder List", vars);
	}

	private List<VariableDeclarationNode> translateBinder(CommonTree tree,
			SimpleScope scope) throws SyntaxException {
		CommonTree typeTree = (CommonTree) tree.getChild(0);
		int numChild = tree.getChildCount();
		TypeNode type = this.translateTypeExpr(typeTree, scope);
		List<VariableDeclarationNode> result = new LinkedList<>();

		for (int i = 1; i < numChild; i++) {
			CommonTree varIdent = (CommonTree) tree.getChild(i);

			result.add(this.translateVariableIdent(varIdent, scope, type.copy()));
		}
		return result;
	}

	private TypeNode translateTypeExpr(CommonTree tree, SimpleScope scope)
			throws SyntaxException {
		int kind = tree.getType();

		switch (kind) {
		case LOGIC_TYPE:
			return this
					.translateLogicType((CommonTree) tree.getChild(0), scope);
		case C_TYPE:
			return this.translateCType((CommonTree) tree.getChild(0), scope);
		default:
			throw this.error("unkown kind of tyep expression", tree);
		}
	}

	private TypeNode translateCType(CommonTree tree, SimpleScope scope)
			throws SyntaxException {
		int kind = tree.getType();
		Source source = this.newSource(tree);

		switch (kind) {
		case CHAR:
			return this.nodeFactory
					.newBasicTypeNode(source, BasicTypeKind.CHAR);
		case DOUBLE:
			return this.nodeFactory.newBasicTypeNode(source,
					BasicTypeKind.DOUBLE);
		case FLOAT:
			return this.nodeFactory.newBasicTypeNode(source,
					BasicTypeKind.FLOAT);
		case INT:
			return this.nodeFactory.newBasicTypeNode(source, BasicTypeKind.INT);
		case LONG:
			return this.nodeFactory
					.newBasicTypeNode(source, BasicTypeKind.LONG);
		case SHORT:
			return this.nodeFactory.newBasicTypeNode(source,
					BasicTypeKind.SHORT);
		case VOID:
			return this.nodeFactory.newVoidTypeNode(source);
		default:
			throw this.error("unknown C type", tree);
		}
	}

	private TypeNode translateLogicType(CommonTree tree, SimpleScope scope)
			throws SyntaxException {
		int kind = tree.getType();
		Source source = this.newSource(tree);

		switch (kind) {
		case TYPE_BUILTIN: {
			int typeKind = tree.getChild(0).getType();

			switch (typeKind) {
			case BOOLEAN:
				return this.nodeFactory.newBasicTypeNode(source,
						BasicTypeKind.BOOL);
			case INTEGER:
				return this.nodeFactory.newBasicTypeNode(source,
						BasicTypeKind.INT);
			case REAL:
				return this.nodeFactory.newBasicTypeNode(source,
						BasicTypeKind.REAL);
			default:
				throw this.error("unknown built-in logic type", tree);
			}
		}
		case TYPE_ID:
			return this.nodeFactory.newTypedefNameNode(
					this.translateIdentifier((CommonTree) tree.getChild(0)),
					null);
		default:
			throw this.error("unknown kind of logic type", tree);
		}
	}

	private VariableDeclarationNode translateVariableIdent(CommonTree tree,
			SimpleScope scope, TypeNode baseType) throws SyntaxException {
		int kind = tree.getType();
		Source source = this.newSource(tree);

		switch (kind) {
		case VAR_ID_STAR: {
			VariableDeclarationNode baseVar = this.translateVariableIdentBase(
					(CommonTree) tree.getChild(0), source, scope, baseType);
			TypeNode baseVarType, type;

			baseVarType = baseVar.getTypeNode();
			baseVarType.remove();
			type = this.nodeFactory.newPointerTypeNode(source, baseVarType);
			baseVar.setTypeNode(type);
			return baseVar;
		}
		case VAR_ID_SQUARE: {
			VariableDeclarationNode baseVar = this.translateVariableIdentBase(
					(CommonTree) tree.getChild(0), source, scope, baseType);
			TypeNode baseVarType, type;

			baseVarType = baseVar.getTypeNode();
			baseVarType.remove();
			type = this.nodeFactory.newArrayTypeNode(source, baseVarType, null);
			baseVar.setTypeNode(type);
			return baseVar;
		}
		case VAR_ID:
			return this.translateVariableIdentBase(
					(CommonTree) tree.getChild(0), source, scope, baseType);
		default:
			throw this.error("unknown kind of variable identity", tree);
		}
	}

	private VariableDeclarationNode translateVariableIdentBase(CommonTree tree,
			Source source, SimpleScope scope, TypeNode baseType)
			throws SyntaxException {
		int kind = tree.getType();

		switch (kind) {
		case ID: {
			IdentifierNode identifier = this.translateIdentifier(tree);

			return this.nodeFactory.newVariableDeclarationNode(
					identifier.getSource(), identifier, baseType);
		}
		case VAR_ID_BASE:
			return this.translateVariableIdent((CommonTree) tree.getChild(0),
					scope, baseType);
		default:
			throw this.error("unknown kind of variable identity base", tree);
		}
	}

	// ////////////////////////////////////
	private ExpressionNode translateValidNode(CommonTree tree, Source source,
			SimpleScope scope) throws SyntaxException {
		CommonTree pointer = (CommonTree) tree.getChild(0);
		ExpressionNode ptrNode;
		ExpressionNode rangeNode;

		ptrNode = translateExpression(pointer, scope);
		if (tree.getChildCount() > 1) {
			CommonTree range;

			range = (CommonTree) tree.getChild(1);
			rangeNode = translateExpression(range, scope);
			return nodeFactory.newOperatorNode(source, Operator.VALID, ptrNode,
					rangeNode);
		} else
			return nodeFactory.newOperatorNode(source, Operator.VALID, ptrNode);
	}

	private ExpressionNode translateWriteEvent(Source source,
			CommonTree expressionTree, SimpleScope scope) {
		// TODO Auto-generated method stub
		return null;
	}

	private IntegerConstantNode translateIntegerConstant(Source source,
			CommonTree integerConstant) throws SyntaxException {
		return nodeFactory.newIntegerConstantNode(source,
				integerConstant.getText());
	}

	private FloatingConstantNode translateFloatingConstant(Source source,
			CommonTree floatingConstant) throws SyntaxException {
		return nodeFactory.newFloatingConstantNode(source,
				floatingConstant.getText());
	}

	private CharacterConstantNode translateCharacterConstant(Source source,
			CommonTree characterConstant) throws SyntaxException {
		CharacterToken token = (CharacterToken) characterConstant.getToken();

		return nodeFactory.newCharacterConstantNode(source,
				characterConstant.getText(), token.getExecutionCharacter());
	}

	private ConstantNode translateTrue(Source source) {
		return nodeFactory.newBooleanConstantNode(source, true);
	}

	private ConstantNode translateFalse(Source source) {
		return nodeFactory.newBooleanConstantNode(source, false);
	}

	private StringLiteralNode translateStringLiteral(Source source,
			CommonTree stringLiteral) throws SyntaxException {
		StringToken token = (StringToken) stringLiteral.getToken();

		return nodeFactory.newStringLiteralNode(source,
				stringLiteral.getText(), token.getStringLiteral());
	}

	private ExpressionNode translateRegularRange(Source source,
			CommonTree expressionTree, SimpleScope scope)
			throws SyntaxException {
		{// regular range expression lo..hi or lo..hi#step
			ExpressionNode loNode = translateExpression(
					(CommonTree) expressionTree.getChild(0), scope);
			ExpressionNode hiNode = translateExpression(
					(CommonTree) expressionTree.getChild(1), scope);
			if (expressionTree.getChildCount() > 2) {
				CommonTree stepTree = (CommonTree) expressionTree.getChild(2);

				if (stepTree != null /* && stepTree.getType() != ABSENT */) {
					ExpressionNode stepNode = translateExpression(stepTree,
							scope);

					return nodeFactory.newRegularRangeNode(source, loNode,
							hiNode, stepNode);
				}
			}
			return nodeFactory.newRegularRangeNode(source, loNode, hiNode);
		}
	}

	/**
	 * Translates a function call expression.
	 * 
	 * @param callTree
	 *            CommonTree node of type CALL, representing a function call
	 * @return a FunctionCallNode corresponding to the ANTLR tree
	 * @throws SyntaxException
	 */
	private FunctionCallNode translateCall(Source source, CommonTree callTree,
			SimpleScope scope) throws SyntaxException {
		CommonTree functionTree = (CommonTree) callTree.getChild(1);
		CommonTree contextArgumentListTree = (CommonTree) callTree.getChild(2);
		CommonTree argumentListTree = (CommonTree) callTree.getChild(3);
		ExpressionNode functionNode = translateExpression(functionTree, scope);
		int numContextArgs = contextArgumentListTree.getChildCount();
		int numArgs = argumentListTree.getChildCount();
		List<ExpressionNode> contextArgumentList = new LinkedList<ExpressionNode>();
		List<ExpressionNode> argumentList = new LinkedList<ExpressionNode>();
		// SequenceNode<ExpressionNode> scopeList =
		// translateScopeListUse((CommonTree) callTree
		// .getChild(4));

		for (int i = 0; i < numContextArgs; i++) {
			CommonTree argumentTree = (CommonTree) contextArgumentListTree
					.getChild(i);
			ExpressionNode contextArgumentNode = translateExpression(
					argumentTree, scope);

			contextArgumentList.add(contextArgumentNode);
		}

		for (int i = 0; i < numArgs; i++) {
			CommonTree argumentTree = (CommonTree) argumentListTree.getChild(i);
			ExpressionNode argumentNode = translateExpression(argumentTree,
					scope);

			argumentList.add(argumentNode);
		}
		return nodeFactory.newFunctionCallNode(source, functionNode,
				contextArgumentList, argumentList, null);
	}

	/**
	 * 
	 * @param expressionTree
	 * @return
	 * @throws SyntaxException
	 */
	private ExpressionNode translateDotOrArrow(Source source,
			CommonTree expressionTree, SimpleScope scope)
			throws SyntaxException {
		int kind = expressionTree.getType();
		CommonTree argumentNode = (CommonTree) expressionTree.getChild(0);
		CommonTree fieldNode = (CommonTree) expressionTree.getChild(1);
		ExpressionNode argument = translateExpression(argumentNode, scope);
		IdentifierNode fieldName = translateIdentifier(fieldNode);

		if (kind == DOT)
			return nodeFactory.newDotNode(source, argument, fieldName);
		else
			return nodeFactory.newArrowNode(source, argument, fieldName);
	}

	/**
	 * 
	 * @param expressionTree
	 * @return
	 * @throws SyntaxException
	 */
	private OperatorNode translateOperatorExpression(Source source,
			CommonTree expressionTree, SimpleScope scope)
			throws SyntaxException {
		CommonTree operatorTree = (CommonTree) expressionTree.getChild(0);
		int operatorKind = operatorTree.getType();
		CommonTree argumentList = (CommonTree) expressionTree.getChild(1);
		int numArgs = argumentList.getChildCount();
		List<ExpressionNode> arguments = new LinkedList<ExpressionNode>();
		Operator operator;

		for (int i = 0; i < numArgs; i++) {
			ExpressionNode argument = translateExpression(
					(CommonTree) argumentList.getChild(i), scope);

			arguments.add(argument);
		}
		switch (operatorKind) {
		case AMPERSAND:
			operator = numArgs == 1 ? Operator.ADDRESSOF : Operator.BITAND;
			break;
		case ASSIGN:
			operator = Operator.ASSIGN;
			break;
		case COMP:
			operator = Operator.BITCOMPLEMENT;
			break;
		case BAR:
			operator = Operator.BITOR;
			break;
		case BITXOR:
			operator = Operator.BITXOR;
			break;
		case COMMA:
			operator = Operator.COMMA;
			break;
		case QUESTION:
			operator = Operator.CONDITIONAL;
			break;
		case STAR:
			operator = numArgs == 1 ? Operator.DEREFERENCE : Operator.TIMES;
			break;
		case DIVIDE:
			operator = Operator.DIV;
			break;
		case EQ:
			operator = Operator.EQUALS;
			break;
		case GT:
			operator = Operator.GT;
			break;
		case GTE:
			operator = Operator.GTE;
			break;
		case HASH:
			operator = Operator.HASH;
			break;
		case LAND:
			operator = Operator.LAND;
			break;
		case LOR:
			operator = Operator.LOR;
			break;
		case IMPLY:
			operator = Operator.IMPLIES;
			break;
		case LT:
			operator = Operator.LT;
			break;
		case LTE:
			operator = Operator.LTE;
			break;
		case SUB:
			operator = numArgs == 1 ? Operator.UNARYMINUS : Operator.MINUS;
			break;
		case MOD:
			operator = Operator.MOD;
			break;
		case NEQ:
			operator = Operator.NEQ;
			break;
		case NOT:
			operator = Operator.NOT;
			break;
		case PLUS:
			operator = numArgs == 1 ? Operator.UNARYPLUS : Operator.PLUS;
			break;
		case SHIFTLEFT:
			operator = Operator.SHIFTLEFT;
			break;
		case SHIFTRIGHT:
			operator = Operator.SHIFTRIGHT;
			break;
		case INDEX:
			operator = Operator.SUBSCRIPT;
			break;
		default:
			throw error("Unknown operator :", operatorTree);
		}
		return nodeFactory.newOperatorNode(source, operator, arguments);
	}

	private IdentifierNode translateIdentifier(CommonTree identifier) {
		Token idToken = identifier.getToken();
		CivlcToken token;
		Source source;

		if (idToken instanceof CivlcToken)
			token = (CivlcToken) idToken;
		else {
			token = tokenFactory.newCivlcToken(idToken, formation);
		}
		source = tokenFactory.newSource(token);
		return nodeFactory.newIdentifierNode(source, token.getText());
	}

	// ////////////////////////////////////

	private MPICollectiveBlockNode translateMPICollectiveBlock(Source source,
			CommonTree colBlock, SimpleScope scope) throws SyntaxException {
		CommonTree mpiComm = (CommonTree) colBlock.getChild(0);
		CommonTree kind = (CommonTree) colBlock.getChild(1);
		CommonTree body = (CommonTree) colBlock.getChild(2);
		List<ContractNode> bodyComponents = new LinkedList<>();
		SequenceNode<ContractNode> bodyNode;
		ExpressionNode mpiCommNode;
		MPICollectiveKind colKind;

		mpiCommNode = translateExpression(mpiComm, scope);
		// The mpi collective kind can only be :COL, P2P or BOTH
		switch (kind.getType()) {
		case AcslParser.COL:
			colKind = MPICollectiveKind.COL;
			break;
		case AcslParser.P2P:
			colKind = MPICollectiveKind.P2P;
			break;
		case AcslParser.BOTH:
			colKind = MPICollectiveKind.BOTH;
			break;
		default:
			throw error("Unknown MPI collective kind", kind);
		}
		bodyComponents.addAll(translateFunctionContractBlock(body, scope));
		bodyNode = nodeFactory.newSequenceNode(source, "mpi_collective body",
				bodyComponents);
		return nodeFactory.newMPICollectiveBlockNode(source, mpiCommNode,
				colKind, bodyNode);
	}

	private MPIContractConstantNode translateMPIConstantNode(CommonTree tree,
			Source source) throws SyntaxException {
		String text = tree.getChild(0).getText();
		MPIContractConstantNode result;

		if (text.equals(MPI_COMM_RANK)) {
			result = nodeFactory.newMPIConstantNode(source, MPI_COMM_RANK,
					MPIConstantKind.MPI_COMM_RANK, ConstantKind.INT);
		} else if (text.equals(MPI_COMM_SIZE)) {
			result = nodeFactory.newMPIConstantNode(source, MPI_COMM_SIZE,
					MPIConstantKind.MPI_COMM_SIZE, ConstantKind.INT);
		} else
			throw error("Unknown MPI Constant " + text, tree);
		result.setInitialType(typeFactory.signedIntegerType(SignedIntKind.INT));
		return result;
	}

	private MPIContractExpressionNode translateMPIExpressionNode(
			CommonTree expressionTree, Source source, SimpleScope scope)
			throws SyntaxException {
		CommonTree expression = (CommonTree) expressionTree.getChild(0);
		int kind = expression.getType();
		int numArgs;
		List<ExpressionNode> args = new LinkedList<>();
		String exprName = expression.getText();
		MPIContractExpressionKind mpiExprKind;
		MPIContractExpressionNode result;
		Type initialType;

		switch (kind) {
		case AcslParser.MPI_EMPTY_IN:
			numArgs = 1;
			mpiExprKind = MPIContractExpressionKind.MPI_EMPTY_IN;
			initialType = typeFactory.unsignedIntegerType(UnsignedIntKind.BOOL);
			break;
		case AcslParser.MPI_EMPTY_OUT:
			numArgs = 1;
			mpiExprKind = MPIContractExpressionKind.MPI_EMPTY_OUT;
			initialType = typeFactory.unsignedIntegerType(UnsignedIntKind.BOOL);
			break;
		case AcslParser.MPI_EQUALS:
			numArgs = 4;
			mpiExprKind = MPIContractExpressionKind.MPI_EQUALS;
			initialType = typeFactory.unsignedIntegerType(UnsignedIntKind.BOOL);
			break;
		case AcslParser.MPI_REGION:
			numArgs = 3;
			mpiExprKind = MPIContractExpressionKind.MPI_REGION;
			initialType = typeFactory.pointerType(typeFactory.voidType());
			break;
		case AcslParser.MPI_AGREE:
			numArgs = 1;
			mpiExprKind = MPIContractExpressionKind.MPI_AGREE;
			initialType = typeFactory.unsignedIntegerType(UnsignedIntKind.BOOL);
			break;
		default:
			throw error("Unknown MPI expression " + exprName, expressionTree);
		}
		for (int i = 0; i < numArgs; i++) {
			if (i == 2 && kind == AcslParser.MPI_EQUALS) {
				args.add(this.translateEnumerationConstantNode(
						(CommonTree) expression.getChild(i), source, scope));
			} else
				args.add(this.translateExpression(
						(CommonTree) expression.getChild(i), scope));
		}
		result = nodeFactory.newMPIExpressionNode(source, args, mpiExprKind,
				exprName);
		result.setInitialType(initialType);
		return result;
	}

	private EnumerationConstantNode translateEnumerationConstantNode(
			CommonTree expressionTree, Source source, SimpleScope scope)
			throws SyntaxException {
		ExpressionNode identifierExpr = this.translateExpression(
				expressionTree, scope);

		if (identifierExpr.expressionKind().equals(
				ExpressionKind.IDENTIFIER_EXPRESSION)) {
			IdentifierNode ident = ((IdentifierExpressionNode) identifierExpr)
					.getIdentifier();

			return nodeFactory.newEnumerationConstantNode(ident.copy());
		}
		throw error("Expecting an identifer for an enumeration constant.",
				expressionTree);
	}

	private SyntaxException error(String message, CommonTree tree) {
		return new SyntaxException(message, newSource(tree));
	}

	private Source newSource(CommonTree tree) {
		return parseTree.source(tree);
	}

}
