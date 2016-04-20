package edu.udel.cis.vsl.abc.transform.common;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.PairNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.ArrayDesignatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.CompoundInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.DesignationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.DesignatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.compound.FieldDesignatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.EnumeratorDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FieldDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.OrdinaryDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.OrdinaryDeclarationNode.OrdinaryDeclarationKind;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.TypedefDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ArrowNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CastNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.CompoundLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ContractVerifyNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.DotNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.GenericSelectionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.QuantifiedExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RegularRangeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.RemoteExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ScopeOfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SizeableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SizeofNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.SpawnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StatementExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpExecutableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.AtomicNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode.BlockItemKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ChooseStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CivlForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.DeclarationListNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopInitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ForLoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.IfNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.JumpNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LabeledStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.LoopNode.LoopKind;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ReturnNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.StatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.SwitchNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.WhenNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.EnumerationTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.StructureOrUnionTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.TypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ArrayType;
import edu.udel.cis.vsl.abc.ast.type.IF.AtomicType;
import edu.udel.cis.vsl.abc.ast.type.IF.DomainType;
import edu.udel.cis.vsl.abc.ast.type.IF.EnumerationType;
import edu.udel.cis.vsl.abc.ast.type.IF.IntegerType;
import edu.udel.cis.vsl.abc.ast.type.IF.PointerType;
import edu.udel.cis.vsl.abc.ast.type.IF.QualifiedObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType;
import edu.udel.cis.vsl.abc.ast.type.IF.StandardBasicType.BasicTypeKind;
import edu.udel.cis.vsl.abc.ast.type.IF.StructureOrUnionType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.Type.TypeKind;
import edu.udel.cis.vsl.abc.ast.value.IF.CharacterValue;
import edu.udel.cis.vsl.abc.ast.value.IF.IntegerValue;
import edu.udel.cis.vsl.abc.ast.value.IF.StringValue;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.err.IF.ABCUnsupportedException;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;

// add extra parameter to all the expression translation methods
// boolean voidExpr: if true, this means the expression return value
// will not be used.  therefore you have to make sure all
// real side-effects and error side-effects are in the before/after.

/**
 * <p>
 * A transformer which modifies an AST so that no expressions other than a very
 * few prescribed ones have side effects.
 * </p>
 * 
 * <p>
 * An expression is <strong>side-effect-free</strong> if it does not contain a
 * function call or any subexpression which can modify the state (such as an
 * assignment). In this definition, an expression which may cause an exception
 * (division by 0, illegal pointer dereference, etc.) is NOT considered to be a
 * side-effect.
 * </p>
 * 
 * <p>
 * A expression e is in <code>normal form</code> if it has one of the following
 * forms:
 * <ul>
 * 
 * <li>e is an assignment expression e1=e2, for side-effect-free expressions e1
 * and e2, and e1 is a lhs expression</li>
 * 
 * <li>e is of the form e1=f(arg0,...), for side-effect-free expressions e1, f,
 * arg0, .... (function call with left-hand-side)</li>
 * 
 * <li>e is of the form f(arg0,...), for side-effect-free expressions f, arg0,
 * ... (function call with no left-hand-side)</li>
 * 
 * <li>ditto last two with $spawn inserted before the call</li>
 * </ul>
 * </p>
 * 
 * <p>
 * A statement is in normal form if: - if it is an expression statement wrapping
 * e, then e is in normal form - for other kinds of statements: all its member
 * expressions are side-effect-free and all its member statements are in normal
 * form.
 * </p>
 * 
 * <p>
 * A triple is in normal form if all of the statements in the before and after
 * clauses are in normal form and the expression is in normal form. The goal of
 * most of the methods below is to produce a triple in normal form which is
 * equivalent to a given expression or statement. In some cases an additional
 * goal is that the expression be side-effect-free.
 * </p>
 * 
 * <p>
 * Helper functions: <br>
 * emptyAfter([a|e|b]): makes the triple's "after" component empty. If the after
 * component is already empty, does nothing and returns <code>false</code>.
 * Otherwise, the triple becomes [a,(var x=e),b|x|], i.e., introducing a
 * temporary variable to store the value of e and shift the after component to
 * the before component, and returns <code>true</code>. <br>
 * //TODO why do we need this function? <br>
 * purify([a|e|b]): makes the triple side-effect-free and the "after" component
 * empty. If the triple already satisfies those properties, this does nothing
 * and returns <code>false</code>. Otherwise, the triple becomes [a,(var
 * x=e),b|x|], i.e., introducing a temporary variable to store the value of e
 * and shift the after component to the before component, and returns
 * <code>true</code>.<br>
 * //TODO check it <br>
 * shift([a|e|b], isVoid): modifies the triple to an equivalent form but with a
 * side-effect-free or <code>null</code> (if <code>isVoid</code>) expression,
 * and an empty "after" component.
 * </p>
 * 
 * TODO: check if a contract contains side-effects and report an error
 * 
 * @author Timothy K. Zirkel
 * @author Stephen F. Siegel
 * @author Manchun Zheng
 */
public class SideEffectRemover extends BaseTransformer {

	/* Static Fields */

	/**
	 * The unique identifier of this transformer.
	 */
	public final static String CODE = "sef";

	/**
	 * The full name of this transformer.
	 */
	public final static String LONG_NAME = "SideEffectRemover";

	/**
	 * A short description of this transformer.
	 */
	public final static String SHORT_DESCRIPTION = "transforms program to side-effect-free form";

	/**
	 * The prefix for temporary variables created by this transformer.
	 */
	private final static String tempVariablePrefix = "$" + CODE + "$";

	/* Instance Fields */

	/**
	 * The number of temporary variables created by this transformer.
	 */
	private int tempVariableCounter = 0;

	/* Constructors */

	/**
	 * Creates a new instance of side effect remover.
	 * 
	 * @param astFactory
	 */
	public SideEffectRemover(ASTFactory astFactory) {
		super(CODE, LONG_NAME, SHORT_DESCRIPTION, astFactory);
	}

	/* Private methods */

	/**
	 * Given a {@link Type}, creates a new type node tree that will generate
	 * that type.
	 * 
	 * @param type
	 *            An AST type.
	 * @return An AST type node corresponding to the type.
	 */
	private TypeNode typeNode(Source source, Type type) {
		switch (type.kind()) {
		case ARRAY:
			ArrayType arrayType = (ArrayType) type;

			return nodeFactory.newArrayTypeNode(source,
					typeNode(source, arrayType.getElementType()), null);
		case ATOMIC:
			AtomicType atomicType = (AtomicType) type;

			return nodeFactory.newAtomicTypeNode(source,
					typeNode(source, atomicType.getBaseType()));
		case BASIC:
			StandardBasicType basicType = (StandardBasicType) type;

			return nodeFactory.newBasicTypeNode(source,
					basicType.getBasicTypeKind());
		case DOMAIN: {
			DomainType domainType = (DomainType) type;

			if (domainType.hasDimension()) {
				String dimensionString = Integer.toString(domainType
						.getDimension());
				IntegerConstantNode dimensionNode;

				try {
					dimensionNode = nodeFactory.newIntegerConstantNode(source,
							dimensionString);
				} catch (SyntaxException e) {
					throw new ABCRuntimeException(
							"error creating integer constant node for "
									+ dimensionString);
				}
				return nodeFactory.newDomainTypeNode(source, dimensionNode);
			} else
				return nodeFactory.newDomainTypeNode(source);
		}
		case POINTER: {
			PointerType pointerType = (PointerType) type;

			return nodeFactory.newPointerTypeNode(source,
					typeNode(source, pointerType.referencedType()));
		}
		case VOID:
			return nodeFactory.newVoidTypeNode(source);
		case ENUMERATION: {
			// if original type is anonymous enum, need to spell out
			// the type again.
			// if original type has tag, and is visible, can leave out
			// the enumerators
			EnumerationType enumType = (EnumerationType) type;
			String tag = enumType.getTag();

			if (tag != null) {
				IdentifierNode tagNode = nodeFactory.newIdentifierNode(source,
						tag);
				TypeNode result = nodeFactory.newEnumerationTypeNode(source,
						tagNode, null);

				return result;
			} else {
				throw new ABCUnsupportedException(
						"converting anonymous enumeration type  " + type,
						source.getSummary(false));
			}
		}
		case STRUCTURE_OR_UNION: {
			StructureOrUnionType structOrUnionType = (StructureOrUnionType) type;

			return nodeFactory.newStructOrUnionTypeNode(
					source,
					structOrUnionType.isStruct(),
					nodeFactory.newIdentifierNode(source,
							structOrUnionType.getName()), null);
		}
		case SCOPE:
			return nodeFactory.newScopeTypeNode(source);
		case OTHER_INTEGER: {
			// for now, just using "int" for all the "other integer types"
			return nodeFactory.newBasicTypeNode(source, BasicTypeKind.INT);
		}
		case PROCESS: {
			return nodeFactory.newTypedefNameNode(
					nodeFactory.newIdentifierNode(source, "$proc"), null);
		}
		case QUALIFIED: {
			QualifiedObjectType qualifiedType = (QualifiedObjectType) type;
			TypeNode baseTypeNode = this.typeNode(source,
					qualifiedType.getBaseType());

			baseTypeNode.setConstQualified(qualifiedType.isConstQualified());
			// baseTypeNode.setAtomicQualified(qualifiedType.is); TODO how to
			// get _Atomic qualified feature?
			baseTypeNode.setInputQualified(qualifiedType.isInputQualified());
			baseTypeNode.setOutputQualified(qualifiedType.isOutputQualified());
			baseTypeNode.setRestrictQualified(qualifiedType
					.isRestrictQualified());
			baseTypeNode.setVolatileQualified(qualifiedType
					.isVolatileQualified());
			return baseTypeNode;
		}
		case FUNCTION:
			// TODO
		case HEAP:
			// TODO
		default:
			throw new ABCUnsupportedException("converting type " + type
					+ " to a type node.", source.getSummary(false));
		}
	}

	/**
	 * Modifies the triple to an equivalent form but with a side-effect-free or
	 * <code>null</code> (if <code>isVoid</code>) expression, and an empty after
	 * list.
	 * 
	 * <p>
	 * If <code>isVoid</code>, moves the expression to the before list as an
	 * expression statement, then adds all the after clauses to the before list.
	 * </p>
	 * 
	 * <p>
	 * If not <code>isVoid</code>, introduces a new temporary variable t whose
	 * type is same as the type of the expression, appends a declaration for t
	 * to the before clause, moves all the after clauses to the end of the
	 * before clause, and replaces the expression with t.
	 * </p>
	 * 
	 * @param triple
	 *            any triple
	 * @param isVoid
	 *            is the result of the expression needed (and not just its
	 *            side-effects)?
	 */
	private void shift(ExprTriple triple, boolean isVoid) {
		ExpressionNode expression = triple.getNode();
		Source source = expression.getSource();

		expression.remove();
		if (isVoid) {
			triple.addBefore(nodeFactory.newExpressionStatementNode(expression));
			triple.setNode(null);
		} else {
			String tmpId = tempVariablePrefix + tempVariableCounter;

			tempVariableCounter++;

			VariableDeclarationNode decl = nodeFactory
					.newVariableDeclarationNode(source,
							nodeFactory.newIdentifierNode(source, tmpId),
							typeNode(source, expression.getType()), expression);

			triple.setNode(nodeFactory.newIdentifierExpressionNode(source,
					nodeFactory.newIdentifierNode(source, tmpId)));
			triple.getBefore().add(decl);
		}
		triple.getBefore().addAll(triple.getAfter());
		triple.setAfter(new LinkedList<BlockItemNode>());
	}

	/**
	 * Makes the triple after component empty. If the after component is already
	 * empty, does nothing and returns <code>false</code>. Otherwise, invokes
	 * {@link #shift(ExprTriple)} and returns <code>true</code>.
	 * 
	 * @param triple
	 *            any triple
	 * @return <code>true</code> iff the triple changed
	 */
	private boolean emptyAfter(ExprTriple triple) {
		if (triple.getAfter().isEmpty()) {
			return false;
		} else {
			shift(triple, false);
			return true;
		}
	}

	/**
	 * Makes the triple expression side-effect-free and the "after" clauses
	 * empty. If the triple already satisfies those properties, this does
	 * nothing and returns <code>false</code>. Otherwise, it performs a
	 * {@link #shift(ExprTriple)} and returns <code>true</code>.
	 * 
	 * @param triple
	 *            any triple
	 * @return <code>true</code> iff the triple changed
	 */
	private boolean purify(ExprTriple triple) {
		if (triple.getAfter().isEmpty()
				&& triple.getNode().isSideEffectFree(false)) {
			assert triple.getNode().parent() == null;
			return false;
		} else {
			shift(triple, false);
			assert triple.getNode().parent() == null;
			return true;
		}
	}

	/**
	 * Makes the triple expression side-effect-free. Transforms the triple into
	 * an equivalent form in which the expression is side-effect-free. If the
	 * expression is already side-effect-free, this does nothing and returns
	 * false. Otherwise, it applies {@link #shift(ExprTriple, boolean)} and
	 * returns true.
	 * 
	 * @param triple
	 *            any triple
	 * @return <code>true</code> iff the triple changed
	 */
	private boolean makesef(ExprTriple triple) {
		if (triple.getNode().isSideEffectFree(false)) {
			return false;
		} else {
			shift(triple, false);
			return true;
		}
	}

	/**
	 * Is the given expression a call to one of the functions "malloc" or
	 * "$malloc"?
	 * 
	 * @param node
	 *            any expression node
	 * @return <code>true</code> iff the node is a function call node for a
	 *         function named "malloc" or "$malloc"
	 */
	private boolean isMallocCall(ExpressionNode node) {
		if (node instanceof FunctionCallNode) {
			ExpressionNode functionNode = ((FunctionCallNode) node)
					.getFunction();

			if (functionNode instanceof IdentifierExpressionNode) {
				String functionName = ((IdentifierExpressionNode) functionNode)
						.getIdentifier().name();

				if ("$malloc".equals(functionName))
					return true;
				if ("malloc".equals(functionName))
					return true;
			}
		}
		return false;
	}

	/**
	 * Translates a left-hand-side expression into a triple. The result returned
	 * will always have empty after clause. The expression component of the
	 * triple returned will be left-hand-side expression that will refer to the
	 * same memory unit as the original.
	 * 
	 * Example: a[i++] -> [int tmp = i; i=i+1 | a[tmp] | ].
	 * 
	 * @param lhs
	 * @return
	 */
	private ExprTriple lhsTranslate(ExpressionNode lhs) {
		ExpressionKind kind = lhs.expressionKind();

		switch (kind) {
		case ARROW: {
			// p->f = (*p).f
			ArrowNode arrow = (ArrowNode) lhs;
			ExprTriple result = translate(arrow.getStructurePointer(), false);

			purify(result);
			arrow.setStructurePointer(result.getNode());
			result.setNode(arrow);
			return result;
		}
		case DOT: {
			// e.f
			DotNode dotNode = (DotNode) lhs;
			ExprTriple result = translate(dotNode.getStructure(), false);

			purify(result);
			dotNode.setStructure(result.getNode());
			result.setNode(dotNode);
			return result;
		}
		case IDENTIFIER_EXPRESSION:
			return new ExprTriple(lhs);
		case OPERATOR: {
			OperatorNode opNode = (OperatorNode) lhs;
			Operator op = opNode.getOperator();

			switch (op) {
			case DEREFERENCE: { // *p
				ExprTriple result = translate(opNode.getArgument(0), false);

				purify(result);
				opNode.setArgument(0, result.getNode());
				result.setNode(opNode);
				return result;
			}
			case SUBSCRIPT: {
				// expr[i].
				// expr can be a LHSExpression of array type (like a[j][k])
				// expr can be an expression of pointer type

				ExprTriple t1 = translate(opNode.getArgument(0), false), t2 = translate(
						opNode.getArgument(1), false);

				purify(t1);
				purify(t2);
				opNode.setArgument(0, t1.getNode());
				opNode.setArgument(1, t2.getNode());
				t1.addAllBefore(t2.getBefore());
				t1.setNode(opNode);
				return t1;
			}
			default:
				throw new ABCRuntimeException(
						"Unreachable: unknown LHS operator: " + op);
			}
		}
		default:
			throw new ABCRuntimeException(
					"Unreachable: unknown LHS expression kind: " + kind);
		}
	}

	/**
	 * Creates a new integer constant node "1" with given source.
	 * 
	 * @param source
	 *            a source object
	 * @return a new integer constant node with value 1 and that source
	 */
	private IntegerConstantNode newOneNode(Source source) {
		try {
			return nodeFactory.newIntegerConstantNode(source, "1");
		} catch (SyntaxException e) {
			throw new ABCRuntimeException("unreachable");
		}
	}

	/**
	 * Translates an expression of one of the following forms to a triple: e++,
	 * e--, ++e, --e. Strategy:
	 * 
	 * <pre>
	 * lhs++:
	 * Let lhstranslate(lhs)=[b|e|].
	 * translate(lhs++)=[b|e|e=e+1]
	 * 
	 * ++lhs:
	 * Let lhstranslate(lhs)=[b|e|].
	 * translate(++lhs)=[b,e=e+1|e|]
	 * </pre>
	 * 
	 * @param opNode
	 *            an operator node in which the operator is one of the four
	 *            operators {@link Operator#PREINCREMENT},
	 *            {@link Operator#POSTINCREMENT}, {@link Operator#PREDECREMENT},
	 *            {@link Operator#POSTDECREMENT}.
	 * @param isVoid
	 *            is the value of this expression not needed?
	 * @return an equivalent triple in normal form; expression field will be
	 *         <code>null</code> iff <code>isVoid</code>
	 */
	private ExprTriple translateIncrementOrDecrement(OperatorNode opNode,
			boolean isVoid) {
		Source source = opNode.getSource();
		Operator op = opNode.getOperator();
		Operator unaryOp;
		boolean pre;

		switch (op) {
		case PREINCREMENT:
			unaryOp = Operator.PLUS;
			pre = true;
			break;
		case POSTINCREMENT:
			unaryOp = Operator.PLUS;
			pre = false;
			break;
		case PREDECREMENT:
			unaryOp = Operator.MINUS;
			pre = true;
			break;
		case POSTDECREMENT:
			unaryOp = Operator.MINUS;
			pre = false;
			break;
		default:
			throw new ABCRuntimeException("Unreachable: unexpected operator: "
					+ op);
		}

		ExpressionNode arg = opNode.getArgument(0);
		ExprTriple result = lhsTranslate(arg);
		ExpressionNode newArg = result.getNode();
		StatementNode assignment = nodeFactory
				.newExpressionStatementNode(nodeFactory.newOperatorNode(
						source,
						Operator.ASSIGN,
						newArg.copy(),
						nodeFactory.newOperatorNode(source, unaryOp,
								newArg.copy(), newOneNode(source))));

		if (pre)
			result.addBefore(assignment);
		else
			result.addAfter(assignment);
		if (isVoid) {
			// must make sure to not erase any exception-side-effects.
			// this is guaranteed here because the lhs already occurs
			// in the assignment, which is being kept in any case.
			// exception-side-effects only need to happen ONCE
			result.setNode(null);
		}
		return result;
	}

	/**
	 * Translates an assignment expression to an equivalent triple.
	 * 
	 * <p>
	 * Note from C11 6.15.16: "The side effect of updating the stored value of
	 * the left operand is sequenced after the value computations of the left
	 * and right operands. The evaluations of the operands are unsequenced."
	 * </p>
	 *
	 * Strategy:
	 * 
	 * <pre>
	 * lhs=rhs:
	 * Let lhstranslate(lhs)=[b1|e1|], emptyAfter(translate(rhs))=[b2|e2|].
	 * translate(lhs=rhs) = [b1,b2,e1=e2|e1|]
	 * </pre>
	 * 
	 * @param assign
	 *            an assignment node (operator node for which the operator is
	 *            {@link Operator.ASSIGN}
	 * @param isVoid
	 *            is the value of this expression not needed?
	 * @return an equivalent triple in normal form; expression field will be
	 *         <code>null</code> iff <code>isVoid</code>
	 */
	private ExprTriple translateAssign(OperatorNode assign, boolean isVoid) {
		assert assign.getOperator() == Operator.ASSIGN;

		ExpressionNode lhs = assign.getArgument(0);
		ExpressionNode rhs = assign.getArgument(1);
		ExprTriple leftTriple = lhsTranslate(lhs);
		ExprTriple rightTriple = translate(rhs, false);

		emptyAfter(rightTriple);

		ExpressionNode newLhs = leftTriple.getNode();
		ExpressionNode newRhs = rightTriple.getNode();

		assign.setArgument(0, newLhs);
		assign.setArgument(1, newRhs);

		ExprTriple result = new ExprTriple(isVoid ? null : newLhs.copy());

		result.addAllBefore(leftTriple.getBefore());
		result.addAllBefore(rightTriple.getBefore());
		assign.remove();
		result.addBefore(nodeFactory.newExpressionStatementNode(assign));
		return result;
	}

	/**
	 * Translates a pointer dereference expression <code>*e</code> to an
	 * equivalent triple. Strategy:
	 * 
	 * <pre>
	 * Pointer dereference *(expr):
	 * Let purify(translate(expr))=[b|e|].
	 * if !isVoid
	 * translate(*(expr))=[b|*e|];
	 * else
	 * translate(*(expr))=[b,*e||];
	 * </pre>
	 * 
	 * @param dereference
	 *            a pointer dereference expression
	 * @param isVoid
	 *            is the value of this expression not needed?
	 * @return an equivalent triple in normal form; expression field will be
	 *         <code>null</code> iff <code>isVoid</code>
	 */
	private ExprTriple translateDereference(OperatorNode dereference,
			boolean isVoid) {
		Operator operator = dereference.getOperator();
		ExprTriple result = translate(dereference.getArgument(0), false);

		assert operator == Operator.DEREFERENCE;
		makesef(result);
		dereference.setArgument(0, result.getNode());
		if (isVoid) {
			// in this case we need to keep the dereference
			// because it might have an exception side-effect (illegal
			// dereference)
			dereference.remove();
			result.addBefore(nodeFactory
					.newExpressionStatementNode(dereference));
			result.setNode(null);
		} else {
			result.setNode(dereference);
		}
		return result;
	}

	// /**
	// * Does this kind of expression possibly generate an exception. This is
	// * referring to the expression itself, not the children. In other words,
	// if
	// * all children are exception-less, is it possible the evaluation of this
	// * expression could throw an exception?
	// *
	// * @param expression
	// * any expression node, non-<code>null</code>
	// * @return <code>true</code> iff this kind of expression can lead to an
	// * exception
	// */
	// private boolean hasException(ExpressionNode expression) {
	// ExpressionKind kind = expression.expressionKind();
	//
	// switch (kind) {
	// case ARROW:
	// case CAST:
	// case FUNCTION_CALL:
	// case GENERIC_SELECTION:
	// case SPAWN:
	// return true;
	// case OPERATOR:
	// return hasException(((OperatorNode) expression).getOperator());
	// default:
	// return false;
	// }
	// }

	/**
	 * Translates most binary operator expressions to an equivalent triple. This
	 * is the default behavior used for a binary operator. Strategy:
	 * 
	 * <pre>
	 * expr1+expr2:
	 * Let makesef(translate(expr1))=[b1|e1|a1],
	 * makesef(translate(expr2))=[b2|e2|a2].
	 * translate(expr1+expr2)=[b1,b2|e1+e2|a1,a2].
	 * Replace + with any side-effect-free binary operator.
	 * </pre>
	 * 
	 * @param opNode
	 *            a binary operator expression
	 * @param isVoid
	 *            is the value of this expression not needed?
	 * @return an equivalent triple
	 */
	private ExprTriple translateGenericBinaryOperator(OperatorNode opNode,
			boolean isVoid) {
		ExprTriple leftTriple = translate(opNode.getArgument(0), false);
		ExprTriple rightTriple = translate(opNode.getArgument(1), false);

		makesef(leftTriple);
		makesef(rightTriple);
		opNode.setArgument(0, leftTriple.getNode());
		opNode.setArgument(1, rightTriple.getNode());
		if (isVoid) {
			// because the evaluation of the expression may lead to
			// undefined behaviors, we cannot entirely eliminate it,
			// but we do not need to store the result
			opNode.remove();
			leftTriple
					.addBefore(nodeFactory.newExpressionStatementNode(opNode));
			leftTriple.setNode(null);
		} else {
			leftTriple.setNode(opNode);
		}
		leftTriple.addAllBefore(rightTriple.getBefore());
		leftTriple.addAllAfter(rightTriple.getAfter());
		return leftTriple;
	}

	/**
	 * Translates most unary expressions to equivalent triple. Strategy:
	 * 
	 * <pre>
	 * -expr:
	 * Let makesef(translate(expr))=[b1|e1|a1].
	 * TODO update it with isVoid
	 * translate(-expr)=[b1|-e1|a1].
	 * Replace - with any side-effect-free unary operator.
	 * </pre>
	 * 
	 * @param opNode
	 *            a unary operator node
	 * @param isVoid
	 *            is the value of this expression not needed?
	 * @return equivalent triple
	 */
	private ExprTriple translateGenericUnaryOperator(OperatorNode opNode,
			boolean isVoid) {
		ExprTriple result = translate(opNode.getArgument(0), false);

		makesef(result);
		opNode.setArgument(0, result.getNode());
		if (isVoid) {
			// because the evaluation of the expression may lead to
			// undefined behaviors, we cannot entirely eliminate it,
			// but we do not need to store the result
			opNode.remove();
			result.addBefore(nodeFactory.newExpressionStatementNode(opNode));
			result.setNode(null);
		} else {
			result.setNode(opNode);
		}
		return result;
	}

	/**
	 * Translates a function call node to an equivalent triple.
	 * 
	 * <p>
	 * Note from C11 6.5.2.2: "There is a sequence point after the evaluations
	 * of the function designator and the actual arguments but before the actual
	 * call. Every evaluation in the calling function (including other function
	 * calls) that is not otherwise specifically sequenced before or after the
	 * execution of the body of the called function is indeterminately sequenced
	 * with respect to the execution of the called function."
	 * </p>
	 * 
	 * <p>
	 * As stated above, all side-effects must complete before the function call
	 * occurs. Hence all side-effects will take place in the "before" component
	 * of the returned triple, and the "after" component will be empty.
	 * </p>
	 * 
	 * Strategy:
	 * 
	 * <pre>
	 * func(arg1, arg2, ...):
	 * Let purify(func)=[b0|f|].
	 * Let purify(arg1)=[b1|e1|], ...
	 * translate(func(arg1, ...)) = [b1,b2,...|f(e1,e2,...)|].
	 * </pre>
	 * 
	 * @param callNode
	 *            a function call node
	 * @param isVoid
	 *            is the value of this expression not needed?
	 * @return an equivalent triple with empty after
	 */
	private ExprTriple translateFunctionCall(FunctionCallNode callNode,
			boolean isVoid) {
		ExprTriple functionTriple = translate(callNode.getFunction(), false);
		int numContextArgs = callNode.getNumberOfContextArguments();
		int numArgs = callNode.getNumberOfArguments();
		ExprTriple result = new ExprTriple(callNode);

		// you need the result of the function expression (even if isVoid)...
		purify(functionTriple);
		callNode.setFunction(functionTriple.getNode());
		result.addAllBefore(functionTriple.getBefore());
		for (int i = 0; i < numContextArgs; i++) {
			ExprTriple triple = translate(callNode.getContextArgument(i), false);

			purify(triple);
			result.addAllBefore(triple.getBefore());
			callNode.setContextArgument(i, triple.getNode());
		}
		for (int i = 0; i < numArgs; i++) {
			ExprTriple triple = translate(callNode.getArgument(i), false);

			purify(triple);
			result.addAllBefore(triple.getBefore());
			callNode.setArgument(i, triple.getNode());
		}
		if (isVoid) {
			// shift the call to the begin clause without a temporary variable:
			shift(result, true);
		}
		return result;
	}

	private ExprTriple translateContractVerify(ContractVerifyNode conVeri,
			boolean isVoid) {
		ExprTriple functionTriple = translate(conVeri.getFunction(), false);
		int numContextArgs = conVeri.getNumberOfContextArguments();
		int numArgs = conVeri.getNumberOfArguments();
		ExprTriple result = new ExprTriple(conVeri);

		// you need the result of the function expression (even if isVoid)...
		purify(functionTriple);
		conVeri.setFunction(functionTriple.getNode());
		result.addAllBefore(functionTriple.getBefore());
		for (int i = 0; i < numContextArgs; i++) {
			ExprTriple triple = translate(conVeri.getContextArgument(i), false);

			purify(triple);
			result.addAllBefore(triple.getBefore());
			conVeri.setContextArgument(i, triple.getNode());
		}
		for (int i = 0; i < numArgs; i++) {
			ExprTriple triple = translate(conVeri.getArgument(i), false);

			purify(triple);
			result.addAllBefore(triple.getBefore());
			conVeri.setArgument(i, triple.getNode());
		}
		result.addAfter(nodeFactory.newExpressionStatementNode(conVeri));
		return result;
	}

	/**
	 * Translates a spawn expression. A spawn expression simply wraps a function
	 * call expression, so the specification is exactly the same as that of
	 * {@link #translateFunctionCall(FunctionCallNode)}.
	 * 
	 * @param spawn
	 *            a spawn node
	 * @param isVoid
	 *            is the value of this expression not needed?
	 * @return an equivalent triple
	 */
	private ExprTriple translateSpawn(SpawnNode spawn, boolean isVoid) {
		ExprTriple result = translate(spawn.getCall(), false);

		spawn.setCall((FunctionCallNode) result.getNode());
		result.setNode(spawn);
		if (isVoid) {
			shift(result, true);
		}
		return result;
	}

	/**
	 * Translates an expression using one of the following operators:
	 * {@link Operator#PLUSEQ}, {@link Operator#MINUSEQ},
	 * {@link Operator#BITANDEQ}, {@link Operator#BITOREQ},
	 * {@link Operator#BITXOREQ}, {@link Operator#DIVEQ}, {@link Operator#MODEQ}
	 * , {@link Operator#SHIFTLEFTEQ}, {@link Operator#SHIFTRIGHTEQ},
	 * {@link Operator#TIMESEQ}.
	 * 
	 * @param opNode
	 *            an operator node using one of the generalized assignment
	 *            operators (but not the standard assignment operator)
	 * @param isVoid
	 *            is the value of this expression not needed?
	 * @return an equivalent triple
	 */
	private ExprTriple translateGeneralAssignment(OperatorNode opNode,
			boolean isVoid) {
		Operator assignmentOp = opNode.getOperator();
		Operator binaryOp;

		switch (assignmentOp) {
		case PLUSEQ:
			binaryOp = Operator.PLUS;
			break;
		case MINUSEQ:
			binaryOp = Operator.MINUS;
			break;
		case BITANDEQ:
			binaryOp = Operator.BITAND;
			break;
		case BITOREQ:
			binaryOp = Operator.BITOR;
			break;
		case BITXOREQ:
			binaryOp = Operator.BITXOR;
			break;
		case DIVEQ:
			binaryOp = Operator.DIV;
			break;
		case MODEQ:
			binaryOp = Operator.MOD;
			break;
		case SHIFTLEFTEQ:
			binaryOp = Operator.SHIFTLEFT;
			break;
		case SHIFTRIGHTEQ:
			binaryOp = Operator.SHIFTRIGHT;
			break;
		case TIMESEQ:
			binaryOp = Operator.TIMES;
			break;
		default:
			throw new ABCRuntimeException("Unexpected assignment operator: "
					+ assignmentOp);
		}

		ExpressionNode lhs = opNode.getArgument(0);
		ExpressionNode rhs = opNode.getArgument(1);
		ExprTriple result = lhsTranslate(lhs);
		ExprTriple rightTriple = translate(rhs, false);

		purify(rightTriple);

		ExpressionNode newLhs = result.getNode();
		ExpressionNode newRhs = rightTriple.getNode();
		Source source = opNode.getSource();
		StatementNode assignment = nodeFactory
				.newExpressionStatementNode(nodeFactory.newOperatorNode(
						source,
						Operator.ASSIGN,
						newLhs.copy(),
						nodeFactory.newOperatorNode(source, binaryOp,
								newLhs.copy(), newRhs)));

		result.addAllBefore(rightTriple.getBefore());
		result.addBefore(assignment);
		if (isVoid) {
			result.setNode(null);
		}
		return result;
	}

	/**
	 * Translates a comma expression into side-effect-free triple form. There is
	 * a sequence point at the comma. So all side effects from the first
	 * argument must complete before the second argument is evaluated. Strategy:
	 * 
	 * <pre>
	 * expr1,expr2:
	 * let translate(expr1)   = [b1|e1|a1].
	 * let translate(expr2)   = [b2|e2|a2].
	 * translate(expr1,expr2) = [b1,e1^,a1,b2|e2|a2].
	 * Here e1^ means: omit this if e1 is s.e.f., else make it the expression
	 * statement e1;.
	 * </pre>
	 * 
	 * @param expression
	 *            a comma expression
	 * @param isVoid
	 *            is the value of this expression not needed?
	 * @return result of converting expression to side-effect-free triple
	 */
	private ExprTriple translateComma(OperatorNode expression, boolean isVoid) {
		// the result of the left arg is not needed:
		ExprTriple leftTriple = translate(expression.getArgument(0), true);
		// the result of the right arg might be needed:
		ExprTriple rightTriple = translate(expression.getArgument(1), isVoid);
		ExprTriple result = new ExprTriple(rightTriple.getNode());

		result.addAllBefore(leftTriple.getBefore());
		result.addAllBefore(leftTriple.getAfter());
		result.addAllBefore(rightTriple.getBefore());
		result.addAllAfter(rightTriple.getAfter());
		return result;
	}

	/**
	 * Translates a conditional expression <code>x?y:z</code> to a triple. There
	 * is a sequence point at the <code>?</code>.
	 * 
	 * @param conditional
	 *            the conditional expression
	 * @param isVoid
	 *            is the value of this expression not needed?
	 * @return result of translation
	 */
	private ExprTriple translateConditional(OperatorNode conditional,
			boolean isVoid) {
		Source source = conditional.getSource();
		Operator operator = conditional.getOperator();
		// the result of the test is needed:
		ExprTriple condTriple = translate(conditional.getArgument(0), false);
		// the results of the true/false clauses may or may not be needed:
		ExprTriple triple1 = translate(conditional.getArgument(1), isVoid);
		ExprTriple triple2 = translate(conditional.getArgument(2), isVoid);
		ExprTriple result;

		assert operator == Operator.CONDITIONAL;
		purify(condTriple);

		if (!isVoid) {
			makesef(triple1);
			makesef(triple2);
		}

		List<BlockItemNode> b0 = condTriple.getBefore();
		ExpressionNode e0 = condTriple.getNode();
		List<BlockItemNode> b1 = triple1.getBefore(), b2 = triple2.getBefore();
		List<BlockItemNode> a1 = triple1.getAfter(), a2 = triple2.getAfter();
		ExpressionNode e1 = triple1.getNode(), e2 = triple2.getNode();

		if (b1.isEmpty() && b2.isEmpty() && a1.isEmpty() && a2.isEmpty()) {
			if (isVoid) {
				assert e1 == null && e2 == null;
				result = new ExprTriple(null);
			} else {
				conditional.setChild(0, e0);
				conditional.setChild(1, e1);
				conditional.setChild(2, e2);
				result = new ExprTriple(conditional);
			}
			result.addAllBefore(b0);
		} else if (isVoid) {
			result = new ExprTriple(null);
			result.addAllBefore(b0);
			b1.addAll(a1);
			b2.addAll(a2);
			result.addBefore(nodeFactory.newIfNode(source, e0,
					nodeFactory.newCompoundStatementNode(source, b1),
					nodeFactory.newCompoundStatementNode(source, b2)));
		} else {
			String tmpId = tempVariablePrefix + (tempVariableCounter++);
			VariableDeclarationNode decl = nodeFactory
					.newVariableDeclarationNode(source,
							nodeFactory.newIdentifierNode(source, tmpId),
							typeNode(source, conditional.getType()));
			ExpressionNode tmpNode = nodeFactory.newIdentifierExpressionNode(
					source, nodeFactory.newIdentifierNode(source, tmpId));
			StatementNode ifNode;

			{
				CompoundStatementNode stmt1, stmt2;

				{
					List<BlockItemNode> stmtlist = new LinkedList<>(b1);

					stmtlist.add(nodeFactory
							.newExpressionStatementNode(nodeFactory
									.newOperatorNode(source, Operator.ASSIGN,
											tmpNode.copy(), e1)));
					stmtlist.addAll(a1);
					stmt1 = nodeFactory.newCompoundStatementNode(source,
							stmtlist);
				}
				{
					List<BlockItemNode> stmtlist = new LinkedList<>(b2);

					stmtlist.add(nodeFactory
							.newExpressionStatementNode(nodeFactory
									.newOperatorNode(source, Operator.ASSIGN,
											tmpNode.copy(), e2)));
					stmtlist.addAll(a2);
					stmt2 = nodeFactory.newCompoundStatementNode(source,
							stmtlist);
				}
				ifNode = nodeFactory.newIfNode(source, e0, stmt1, stmt2);
			}
			result = new ExprTriple(tmpNode);
			result.addAllBefore(b0);
			result.addBefore(decl);
			result.addBefore(ifNode);
		}
		return result;
	}

	/**
	 * Translates any operator expression to an equivalent triple. Delegates to
	 * helper methods as needed.
	 * 
	 * @param expression
	 *            any operator expression
	 * @return an equivalent triple
	 */
	private ExprTriple translateOperatorExpression(OperatorNode expression,
			boolean isVoid) {
		ExprTriple result;

		switch (expression.getOperator()) {
		case ASSIGN:
			result = translateAssign(expression, isVoid);
			break;
		case DEREFERENCE:
			result = translateDereference(expression, isVoid);
			break;
		case ADDRESSOF:
		case NOT:
		case UNARYMINUS:
		case UNARYPLUS:
		case BIG_O:
		case BITCOMPLEMENT:
			result = translateGenericUnaryOperator(expression, isVoid);
			break;
		case PREINCREMENT:
		case PREDECREMENT:
		case POSTINCREMENT:
		case POSTDECREMENT:
			result = translateIncrementOrDecrement(expression, isVoid);
			break;
		case HASH:
		case BITAND:
		case BITOR:
		case BITXOR:
		case PLUS:
		case MINUS:
		case DIV:
		case TIMES:
		case SUBSCRIPT:
		case LAND:
		case LOR:
		case EQUALS:
		case NEQ:
		case LT:
		case GT:
		case LTE:
		case GTE:
		case IMPLIES:
		case MOD:
		case SHIFTLEFT:
		case SHIFTRIGHT:
			result = translateGenericBinaryOperator(expression, isVoid);
			break;
		case BITANDEQ:
		case BITOREQ:
		case BITXOREQ:
		case PLUSEQ:
		case MINUSEQ:
		case TIMESEQ:
		case DIVEQ:
		case MODEQ:
		case SHIFTLEFTEQ:
		case SHIFTRIGHTEQ:
			result = translateGeneralAssignment(expression, isVoid);
			break;
		case COMMA:
			result = translateComma(expression, isVoid);
			break;
		case CONDITIONAL:
			result = translateConditional(expression, isVoid);
			break;
		default:
			throw new ABCRuntimeException("Unexpected operator: "
					+ expression.getOperator() + ": " + expression, expression
					.getSource().getSummary(false));
		}
		return result;
	}

	/**
	 * Translates a <code>sizeof</code> expression to an equivalent triple.
	 * 
	 * @param expression
	 *            any {@link SizeofNode}
	 * @return equivalent triple
	 */
	private ExprTriple translateSizeof(SizeofNode expression, boolean isVoid) {
		SizeableNode arg = expression.getArgument();
		ExprTriple triple;

		if (arg instanceof ExpressionNode) {
			triple = translate((ExpressionNode) arg, false);
			makesef(triple);
			if (isVoid) {
				triple.addBefore(nodeFactory.newExpressionStatementNode(triple
						.getNode()));
				triple.setNode(null);
			} else {
				expression.setArgument(triple.getNode());
				triple.setNode(expression);
			}
		} else if (arg instanceof TypeNode) {
			SETriple typeTriple = translateGenericNode(arg);

			expression.setArgument((TypeNode) typeTriple.getNode());
			triple = new ExprTriple(typeTriple.getBefore(), expression,
					new LinkedList<BlockItemNode>());
		} else
			throw new ABCRuntimeException("Unexpected kind of SizeableNode: "
					+ arg);
		return triple;
	}

	/**
	 * Translates a <code>$scopeof</code> expression into an equivalent triple.
	 * 
	 * @param expression
	 *            an instance of {@link ScopeOfNode}
	 * @return equivalent triple
	 */
	private ExprTriple translateScopeOf(ScopeOfNode expression, boolean isVoid) {
		ExprTriple result = translate(expression.expression(), false);

		makesef(result);
		expression.setExpression(result.getNode());
		result.setNode(expression);
		if (isVoid) {
			shift(result, true);
		}
		return result;
	}

	/**
	 * A remote reference can occur only in contract, which should not have
	 * side-effects.
	 * 
	 * @param expression
	 * @return
	 */
	private ExprTriple translateRemoteReference(RemoteExpressionNode expression) {
		return new ExprTriple(expression);
	}

	/**
	 * Translates a regular range expression into an equivalent triple.
	 * Strategy:
	 * 
	 * <pre>
	 * (e1 .. e2 # e3):
	 * let translate(expr1)   = [b1|e1|a1].
	 * let translate(expr2)   = [b2|e2|a2].
	 * let translate(expr3)   = [b3|e3|a3].
	 * 
	 * translate(expr1 .. expr2 # expr3) = [b1,b2,b3|(e1, e2, e3)|a1,a2,a3].
	 * </pre>
	 * 
	 * @param expression
	 * @param isVoid
	 *            true if the expression is void, i.e., its value is never used
	 * @return
	 */
	private ExprTriple translateRegularRange(RegularRangeNode expression,
			boolean isVoid) {
		ExpressionNode step = expression.getStep();
		ExprTriple lowTriple = translate(expression.getLow(), false), hiTriple = translate(
				expression.getHigh(), false);

		makesef(lowTriple);
		makesef(hiTriple);
		expression.setLow(lowTriple.getNode());
		expression.setHigh(hiTriple.getNode());

		ExprTriple result = new ExprTriple(expression);

		result.addAllBefore(lowTriple.getBefore());
		result.addAllBefore(hiTriple.getBefore());
		result.addAllAfter(lowTriple.getAfter());
		result.addAllAfter(hiTriple.getAfter());
		if (step != null) {
			ExprTriple stepTriple = translate(expression.getStep(), false);

			makesef(stepTriple);
			expression.setStep(stepTriple.getNode());
			result.addAllBefore(stepTriple.getBefore());
			result.addAllAfter(stepTriple.getAfter());
		}
		if (isVoid) {
			shift(result, true);
		}
		return result;
	}

	/**
	 * A quantified expression shouldn't have side-effects.
	 * 
	 * @param expression
	 * @param isVoid
	 * @return
	 */
	private ExprTriple translateQuantifiedExpression(
			QuantifiedExpressionNode expression, boolean isVoid) {
		// should never have side-effects: check it in Analyzer
		assert (expression.isSideEffectFree(false));
		return new ExprTriple(expression);
	}

	/**
	 * Not implemented yet.
	 * 
	 * @param expression
	 * @return
	 */
	private ExprTriple translateGenericSelection(GenericSelectionNode expression) {
		throw new ABCUnsupportedException(
				"generic selections not yet implemented: " + expression
						+ " in side-effect remover");
	}

	/**
	 * Translates a dots expression into an equivalent triple.
	 * 
	 * Strategy:
	 * 
	 * <pre>
	 * expr.f:
	 * Let translate(expr)=[b,a|e|],
	 * translate(expr.f) = [b,a|e.f|]
	 * </pre>
	 * 
	 * @param expression
	 * @param isVoid
	 * @return
	 */
	private ExprTriple translateDot(DotNode expression, boolean isVoid) {
		ExprTriple result = translate(expression.getStructure(), false);

		makesef(result);
		expression.setStructure(result.getNode());
		result.setNode(expression);
		if (isVoid) {
			shift(result, true);
		}
		return result;
	}

	/**
	 * Translates an initializer node. By definition, an initializer cannot be a
	 * void expression since it occurs within an assignment expression.
	 * 
	 * @param node
	 *            an initializer node
	 * @param emptyAfter
	 *            must the resulting triple have an empty after clause?
	 * @return result of translation
	 */
	private SETriple translateInitializer(InitializerNode node,
			boolean emptyAfter) {
		if (node instanceof ExpressionNode) {
			ExprTriple triple = translate((ExpressionNode) node, false);

			emptyAfter(triple);
			return triple;
		} else if (node instanceof CompoundInitializerNode) {
			return translateCompoundInitializer((CompoundInitializerNode) node,
					emptyAfter);
		} else
			throw new ABCRuntimeException(
					"Unexpected kind of initializer node: " + node);
	}

	/**
	 * Translates a compound initializer. There are no sequence points.
	 * 
	 * @param node
	 *            a compound initializer node, possibly containing side-effects
	 * @param emptyAfter
	 *            should the triple returned have an empty after clause?
	 * @return triple corresponding to given node
	 */
	private SETriple translateCompoundInitializer(CompoundInitializerNode node,
			boolean emptyAfter) {
		SETriple result = new SETriple(node);

		for (PairNode<DesignationNode, InitializerNode> pair : node) {
			DesignationNode designationNode = pair.getLeft();

			if (designationNode != null)
				for (DesignatorNode designator : designationNode) {
					if (designator instanceof FieldDesignatorNode) {
						// no side effects possible
					} else if (designator instanceof ArrayDesignatorNode) {
						ExpressionNode indexNode = ((ArrayDesignatorNode) designator)
								.getIndex();
						ExprTriple triple = translate(indexNode, false);

						if (emptyAfter) {
							purify(triple);
							result.addAllBefore(triple.getBefore());
						} else {
							makesef(triple);
							result.addAllBefore(triple.getBefore());
							result.addAllAfter(triple.getAfter());
						}
						((ArrayDesignatorNode) designator).setIndex(triple
								.getNode());
					} else {
						throw new ABCRuntimeException(
								"Unexpected kind of designator node: "
										+ designator);
					}
				}

			SETriple initTriple = translateInitializer(pair.getRight(),
					emptyAfter);

			result.addAllBefore(initTriple.getBefore());
			result.addAllAfter(initTriple.getAfter());
			pair.setRight((InitializerNode) initTriple.getNode());
		}
		return result;
	}

	/**
	 * Translates a compound literal. There are no sequence points.
	 * 
	 * @param expression
	 *            a compound literal expression
	 * @return result of translation
	 */
	private ExprTriple translateCompoundLiteral(CompoundLiteralNode expression,
			boolean isVoid) {
		CompoundInitializerNode ciNode = expression.getInitializerList();
		SETriple triple = translateCompoundInitializer(ciNode, false);
		ExprTriple result = new ExprTriple(expression);

		expression.setInitializerList((CompoundInitializerNode) triple
				.getNode());
		result.setBefore(triple.getBefore());
		result.setAfter(triple.getAfter());
		if (isVoid) {
			shift(result, true);
		}
		return result;
	}

	// private ExprTriple translateCollective(CollectiveExpressionNode
	// expression) {
	// ExprTriple result = new ExprTriple(expression);
	// ExprTriple e0 = translate(expression.getProcessesGroupExpression(),
	// false);
	// // ExprTriple e1 = translate(expression.getLengthExpression());
	// ExprTriple e2 = translate(expression.getBody(), false);
	//
	// makesef(e0);
	// // makesef(e1);
	// makesef(e2);
	// expression.setProcessesGroupExpression(e0.getNode());
	// // expression.setLengthExpression(e1.getNode());
	// expression.setBody(e2.getNode());
	// result.addAllBefore(e0.getBefore());
	// // result.addAllBefore(e1.getBefore());
	// result.addAllBefore(e2.getBefore());
	// result.addAllAfter(e0.getAfter());
	// // result.addAllAfter(e1.getAfter());
	// result.addAllAfter(e2.getAfter());
	// return result;
	// }

	/**
	 * Translates a cast expression. Strategy:
	 * 
	 * <pre>
	 * (T)expr:
	 * Let translate(expr)=[b,a|e|],
	 * translate((T)expr) = [b,a,(T)e||] if isVoid, otherwise [b,a|(T)e|].
	 * </pre>
	 * 
	 * @param expression
	 * @param isVoid
	 * @return
	 */
	private ExprTriple translateCast(CastNode expression, boolean isVoid) {
		ExpressionNode arg = expression.getArgument();

		if (isVoid && expression.getType().kind() == TypeKind.VOID) {
			return translate(arg, true);
		}

		ExprTriple triple = translate(arg, false);
		ExpressionNode newArg = triple.getNode();

		// if arg started off as a function call, will newArg
		// still be a function call? Yes! See translateFunctionCall.

		// mallocs need to keep their casts, i.e., no
		// tmp=malloc | (int*)tmp | ...

		if (isMallocCall(newArg)) {
			expression.setArgument(newArg);
		} else {
			makesef(triple);
			expression.setArgument(triple.getNode());
		}
		triple.setNode(expression);
		if (isVoid) {
			shift(triple, true);
		}
		return triple;
	}

	/**
	 * 
	 * Translates an arrow expression. Strategy:
	 * 
	 * <pre>
	 * expr->f:
	 * Let translate(expr)=[b,a|e|],
	 * translate(expr->f) = [b,a,e->f||] if isVoid, otherwise [b,a|e->f|].
	 * </pre>
	 * 
	 * @param expression
	 * @param isVoid
	 * @return
	 */
	private ExprTriple translateArrow(ArrowNode expression, boolean isVoid) {
		ExprTriple result = translate(expression.getStructurePointer(), false);

		makesef(result);
		expression.setStructurePointer(result.getNode());
		result.setNode(expression);
		if (isVoid) {
			shift(result, true);
		}
		return result;
	}

	/**
	 * Determines if a value is a legal value of its type in any implementation.
	 * If such a value is used as a void expression, it can be ignored.
	 * 
	 * @param value
	 *            a value
	 * @return best estimate as to whether this value is strictly conforming; if
	 *         this method returns true, the value is strictly conforming for
	 *         its type; otherwise nothing is guaranteed (value may or may not
	 *         be strictly conforming)
	 */
	@SuppressWarnings("unused")
	private boolean isStrictlyConformingValue(Value value) {
		// TODO: make more precise
		Configuration config = this.getConfiguration();

		if (value instanceof IntegerValue) {
			IntegerType type = ((IntegerValue) value).getType();
			BigInteger val = ((IntegerValue) value).getIntegerValue();

			// eventually, do this right...based on type. use case stmt.
			if (config.inRangeSignedInt(val))
				return true;
			return false;
		}
		if (value instanceof StringValue) {
			return true;
		}
		if (value instanceof CharacterValue) {
			return true;
		}
		return false;
	}

	/**
	 * For a compound statement expression:
	 * 
	 * <pre>
	 * ({s1; s2; ... sn; expr;})
	 * </pre>
	 * 
	 * translates it into:
	 * <ul>
	 * <li>if <code>isVoid</code>
	 * 
	 * <pre>
	 * before({s1; s2; ... sn; expr;})
	 * NULL
	 * after({s1; s2; ... sn; expr;})
	 * </pre>
	 * 
	 * </li>
	 * <li>else
	 * 
	 * <pre>
	 * before({s1; s2; ... sn; expr;})
	 * side-effect-free(expr)
	 * after({s1; s2; ... sn; expr;})
	 * </pre>
	 * 
	 * </li>
	 * </ul>
	 * 
	 * @param expression
	 * @param isVoid
	 * @return
	 */
	private ExprTriple translateStatementExpression(
			StatementExpressionNode expression, boolean isVoid) {
		CompoundStatementNode statement = expression.getCompoundStatement(), newCompound = (CompoundStatementNode) this
				.translateCompound(statement).get(0);
		List<BlockItemNode> newBlockItems = new LinkedList<>();
		ExpressionNode lastExpression = expression.getExpression();
		ExprTriple exprTriple = this.translate(lastExpression, isVoid);
		VariableDeclarationNode decl = null;
		ExpressionNode newExpression = null;

		purify(exprTriple);
		if (!isVoid) {
			makesef(exprTriple);
		}
		newBlockItems.addAll(exprTriple.getBefore());
		// removed the last item of the compound statement, which is handled
		// separately by lastExpression
		newCompound.removeChild(newCompound.numChildren() - 1);
		newCompound = this.normalizeCompoundStatement(newCompound);
		if (!isVoid) {
			Source source = lastExpression.getSource();
			String tmpId = tempVariablePrefix + (tempVariableCounter++);
			ExpressionNode tmpNode = nodeFactory.newIdentifierExpressionNode(
					source, nodeFactory.newIdentifierNode(source, tmpId));

			decl = nodeFactory.newVariableDeclarationNode(source,
					nodeFactory.newIdentifierNode(source, tmpId),
					typeNode(source, lastExpression.getType()));
			newCompound.addSequenceChild(nodeFactory
					.newExpressionStatementNode(nodeFactory.newOperatorNode(
							source, Operator.ASSIGN, tmpNode,
							exprTriple.getNode())));
			newExpression = tmpNode.copy();
		}
		newBlockItems.add(newCompound);
		newCompound = nodeFactory.newCompoundStatementNode(
				statement.getSource(), newBlockItems);
		newBlockItems = new LinkedList<>();
		if (!isVoid)
			newBlockItems.add(decl);
		newBlockItems.add(newCompound);
		return new ExprTriple(newBlockItems, newExpression,
				new LinkedList<BlockItemNode>());
	}

	/**
	 * Translates an expression into an equivalent triple in normal form. The
	 * resulting triple will have the same side-effects and
	 * exception-side-effects as the original expression.
	 * 
	 * @param expression
	 *            an expression node
	 * @param isVoid
	 *            is the result of evaluating the expression not needed (only
	 *            its side-effects)? If true, the expression node in the
	 *            resulting triple will be <code>null</code>, but the
	 *            begin/after clauses may contain expression statements
	 *            corresponding to exception side-effects in the expression.
	 * @return a side-effect-free triple equivalent to the original expression
	 * 
	 * @throws SyntaxException
	 *             if a syntax error is discovered in the process
	 */
	private ExprTriple translate(ExpressionNode expression, boolean isVoid) {
		ExpressionKind kind = expression.expressionKind();

		switch (kind) {
		case CONSTANT: {
			if (isVoid) {
				Value value = ((ConstantNode) expression).getConstantValue();

				if (this.isStrictlyConformingValue(value))
					return new ExprTriple(null);

				ExprTriple result = new ExprTriple(expression);

				shift(result, true);
				return result;
			} else {
				return new ExprTriple(expression);
			}
		}
		case ALIGNOF:
		case DERIVATIVE_EXPRESSION:
		case IDENTIFIER_EXPRESSION:
		case RESULT: {
			ExprTriple result = new ExprTriple(expression);

			if (isVoid)
				shift(result, true);
			return result;
		}
		case ARROW:
			return translateArrow((ArrowNode) expression, isVoid);
		case CAST:
			return translateCast((CastNode) expression, isVoid);
		case COMPOUND_LITERAL:
			return translateCompoundLiteral((CompoundLiteralNode) expression,
					isVoid);
		case DOT:
			return translateDot((DotNode) expression, isVoid);
		case FUNCTION_CALL:
			return translateFunctionCall((FunctionCallNode) expression, isVoid);
		case CONTRACT_VERIFY:
			return translateContractVerify((ContractVerifyNode) expression,
					isVoid);
		case GENERIC_SELECTION:
			return translateGenericSelection((GenericSelectionNode) expression);
		case OPERATOR:
			return translateOperatorExpression((OperatorNode) expression,
					isVoid);
		case QUANTIFIED_EXPRESSION:
			return translateQuantifiedExpression(
					(QuantifiedExpressionNode) expression, isVoid);
		case REGULAR_RANGE:
			return translateRegularRange((RegularRangeNode) expression, isVoid);
		case REMOTE_REFERENCE:
			return translateRemoteReference((RemoteExpressionNode) expression);
		case SCOPEOF:
			return translateScopeOf((ScopeOfNode) expression, isVoid);
		case SIZEOF:
			return translateSizeof((SizeofNode) expression, isVoid);
		case SPAWN:
			return translateSpawn((SpawnNode) expression, isVoid);
		case STATEMENT_EXPRESSION:
			return translateStatementExpression(
					(StatementExpressionNode) expression, isVoid);
		default:
			throw new ABCUnsupportedException("removing side-effects for "
					+ kind + " expression");
		}
	}

	// helper functions
	/**
	 * <p>
	 * Translates any AST node into a pure side-effect-free triple. Pure means
	 * the after clause will be empty and all expressions occurring within the
	 * resulting node will be side-effect-free. The kind of node returned in the
	 * triple will be the same kind given: e.g., if node is an instance of
	 * {@link DeclarationNode}, then the node component of the triple returned
	 * will also be an instance of {@link DeclarationNode}.
	 * </p>
	 * 
	 * <p>
	 * Specifically, what this method does: it explores the tree rooted at the
	 * given node in DFS order. Whenever it encounters an expression (so an
	 * expression that is not a sub-expression of another expression) it
	 * translates and purifies that expression. The before side-effects from the
	 * expression are appended to the before clause for the final result. The
	 * (sef) node component of the result replaces the original expression.
	 * </p>
	 * 
	 * @param node
	 *            any ASTNode
	 * @return a pure side-effect-free triple resulting from the translation of
	 *         the node
	 */
	private SETriple translateGenericNode(ASTNode node) {
		if (node instanceof ExpressionNode) {
			ExprTriple result = translate((ExpressionNode) node, false);

			purify(result);
			return result;
		} else {
			int numChildren = node.numChildren();
			SETriple result = new SETriple(node);

			for (int i = 0; i < numChildren; i++) {
				ASTNode child = node.child(i);

				if (child == null)
					continue;

				SETriple childTriple = translateGenericNode(child);

				result.addAllBefore(childTriple.getBefore());
				childTriple.getNode().remove();
				node.setChild(i, childTriple.getNode());
			}
			return result;
		}
	}

	// Declarations...

	/**
	 * Transforms an ordinary declaration into a list of statements whose
	 * execution are equivalent to it.
	 * 
	 * @param ordinaryDecl
	 * @return
	 */
	private List<BlockItemNode> translateOrdinaryDeclaration(
			OrdinaryDeclarationNode ordinaryDecl) {
		OrdinaryDeclarationKind kind = ordinaryDecl.ordinaryDeclarationKind();

		switch (kind) {
		case VARIABLE_DECLARATION:
			return this
					.translateVariableDeclaration((VariableDeclarationNode) ordinaryDecl);
		case FUNCTION_DEFINITION:
			this.normalizeFunctionDefinition((FunctionDefinitionNode) ordinaryDecl);
		case FUNCTION_DECLARATION:
		case ABSTRACT_FUNCTION_DEFINITION:
			return Arrays.asList((BlockItemNode) ordinaryDecl);
		default:
			throw new ABCUnsupportedException(
					"normalization of ordinary declaration of " + kind
							+ " kind in side-effect remover");
		}
	}

	/**
	 * Returns a triple in which the after clause is empty and the node is the
	 * variable declaration node, because we want the side-effects to complete
	 * before the initialization takes place.
	 * 
	 * @param decl
	 *            a variable declaration
	 * @return equivalent triple with empty after
	 */
	private List<BlockItemNode> translateVariableDeclaration(
			VariableDeclarationNode decl) {
		TypeNode typeNode = decl.getTypeNode();
		InitializerNode initNode = decl.getInitializer();
		SETriple typeTriple = translateGenericNode(typeNode);
		List<BlockItemNode> result = new LinkedList<>();

		result.addAll(typeTriple.getBefore());
		decl.setTypeNode((TypeNode) typeTriple.getNode());
		if (initNode != null) {
			SETriple initTriple;

			if (initNode instanceof ExpressionNode) {
				initTriple = translate((ExpressionNode) initNode, false);
				emptyAfter((ExprTriple) initTriple);
			} else {
				initTriple = translateCompoundInitializer(
						(CompoundInitializerNode) initNode, true);
				// true, since need side-effects to complete before
				// initialization happens
			}
			result.addAll(initTriple.getBefore());
			decl.setInitializer((InitializerNode) initTriple.getNode());
		}
		result.add(decl);
		return result;
	}

	/**
	 * Places a function definition into normal form.
	 * 
	 * @param function
	 *            a function definition node
	 */
	private void normalizeFunctionDefinition(FunctionDefinitionNode function) {
		function.setBody(transformCompound(function.getBody()));
	}

	// statements

	/**
	 * Given an expression which is going to be used essentially as a statement,
	 * i.e., only for its side-effects (for example, in an expression statement,
	 * or a for loop initializer or incrementer), returns an equivalent list of
	 * block items in normal form.
	 * 
	 * @param expr
	 *            a non-<code>null</code> expression
	 * @return list of block items in normal form the execution of which is
	 *         equivalent to the evaluation of the expression
	 */
	private List<BlockItemNode> translateExpressionAsStatement(
			ExpressionNode expr) {
		if (expr == null)
			return new LinkedList<BlockItemNode>();

		ExprTriple triple = translate(expr, true);
		List<BlockItemNode> result = triple.getBefore();

		result.addAll(triple.getAfter());
		return result;
	}

	/**
	 * Transforms an expression statement into a sequence of block items
	 * equivalent to the original expression but in normal form.
	 * 
	 * @param exprStmt
	 *            a non-<code>null</code> expression statement node
	 * @return list of block items in normal form equivalent to original
	 */
	private List<BlockItemNode> translateExpressionStatement(
			ExpressionStatementNode exprStmt) {
		return translateExpressionAsStatement(exprStmt.getExpression());
	}

	/**
	 * If the given statement is already a compound statement (instance of
	 * {@link CompoundStatementNode}), the given statement is removed from its
	 * parent and is returned immediately; otherwise, a new
	 * {@link CompoundStatementNode} is created with a single child which is the
	 * given statement.
	 * 
	 * Post-condition: the parent of the result statement node is null, i.e.,
	 * result.parent()==null.
	 * 
	 * @param stmt
	 *            any non-null statement
	 * @return a compound statement equivalent to the given one with parent
	 *         being null
	 */
	private CompoundStatementNode makeCompound(StatementNode stmt) {
		if (stmt instanceof CompoundStatementNode) {
			stmt.remove();
			return (CompoundStatementNode) stmt;
		} else {
			stmt.remove();
			return nodeFactory.newCompoundStatementNode(stmt.getSource(),
					Arrays.asList((BlockItemNode) stmt));
		}
	}

	/**
	 * Places a loop statement body into normal form.
	 * 
	 * @param loop
	 *            a non-<code>null</code> loop node
	 */
	private void normalizeLoopBody(LoopNode loop) {
		StatementNode body = loop.getBody();
		List<BlockItemNode> bodyList = translateStatement(body);

		removeNodes(bodyList);
		if (bodyList.size() == 1)
			loop.setBody((StatementNode) bodyList.get(0));
		else
			loop.setBody(nodeFactory.newCompoundStatementNode(body.getSource(),
					bodyList));
	}

	/**
	 * Normalizes the initializer node of for loop by placing it in normal form
	 * and moving before the for loop if necessary. This may modify the for
	 * loop.
	 * 
	 * @param forLoop
	 *            a for loop node
	 * @return the sequence of statements to insert before the for loop
	 *         (possibly empty)
	 */
	private List<BlockItemNode> normalizeForLoopInitializer(ForLoopNode forLoop) {
		ForLoopInitializerNode init = forLoop.getInitializer();

		if (init == null)
			return new LinkedList<BlockItemNode>();
		if (init instanceof ExpressionNode) {
			List<BlockItemNode> initItems = translateExpressionAsStatement((ExpressionNode) init);

			// if initItems consists of one expression statement, keep it in for
			if (initItems.size() == 1) {
				BlockItemNode item = initItems.get(0);

				if (item instanceof ExpressionStatementNode) {
					ExpressionNode expr = ((ExpressionStatementNode) item)
							.getExpression();

					expr.remove();
					forLoop.setInitializer(expr);
					return new LinkedList<BlockItemNode>();
				}
			}
			forLoop.setInitializer(null);
			return initItems;
		} else if (init instanceof DeclarationListNode) {
			// make all declarations normal. if there are any side
			// effects, move them to an outer scope?
			DeclarationListNode declList = (DeclarationListNode) init;
			int numDecls = declList.numChildren();
			List<BlockItemNode> result = new LinkedList<>();

			declList.remove();
			for (int i = 0; i < numDecls; i++) {
				VariableDeclarationNode decl = declList.getSequenceChild(i);

				result.addAll(translateVariableDeclaration(decl));
			}
			return result;
		} else
			throw new ABCRuntimeException(
					"Unexpected kind of for loop initializer: " + init);
	}

	/**
	 * Transforms a for-loop to an equivalent form in which the incrementer
	 * expression has been normalized. May involve modifications to the loop
	 * body as well as to the incrementer.
	 * 
	 * @param forLoop
	 *            a non-<code>null</code> for-loop node
	 */
	private void normalizeForLoopIncrementer(ForLoopNode forLoop) {
		// incrementer: if normal statement, leave alone, otherwise:
		// for (...; ...; ;) { ... incrementer }
		ExpressionNode incrementer = forLoop.getIncrementer();
		List<BlockItemNode> incItems = translateExpressionAsStatement(incrementer);

		if (incItems.size() == 1
				&& incItems.get(0) instanceof ExpressionStatementNode) {
			// nothing to do
			ExpressionNode newIncrementer = ((ExpressionStatementNode) incItems
					.get(0)).getExpression();

			newIncrementer.remove();
			forLoop.setIncrementer(newIncrementer);
		} else {
			CompoundStatementNode body = makeCompound(forLoop.getBody());

			forLoop.setBody(body);
			body.insertChildren(body.numChildren(), incItems);
			forLoop.setIncrementer(null);
		}
	}

	/**
	 * removes all direct null children node of a given compound statement.
	 * 
	 * Post-condition: all child nodes of the compound statement node are
	 * non-null.
	 * 
	 * @param compound
	 * @return
	 */
	private CompoundStatementNode normalizeCompoundStatement(
			CompoundStatementNode compound) {
		LinkedList<BlockItemNode> items = new LinkedList<>();
		boolean hasNull = false;

		for (BlockItemNode child : compound) {
			if (child == null)
				hasNull = true;
			else
				items.add(child);
		}
		if (hasNull) {
			for (BlockItemNode child : items)
				child.remove();
			return this.nodeFactory.newCompoundStatementNode(
					compound.getSource(), items);
		} else
			return compound;
	}

	/**
	 * Transforms a loop node to an equivalent form in which the loop condition
	 * expression has been placed in normal form. This may involve modifications
	 * to the loop body.
	 * 
	 * @param loop
	 *            a non-<code>null</code> loop node
	 */
	private void normalizeLoopCondition(LoopNode loop) {
		// cond: purify. if before is non-trivial then transform to
		// while (1) { befores; if (!expr) break; body}
		ExpressionNode cond = loop.getCondition();

		if (cond == null)
			return;

		ExprTriple condTriple = translate(cond, false);

		purify(condTriple);

		List<BlockItemNode> condItems = condTriple.getBefore();

		if (!condItems.isEmpty()) {
			Source condSource = cond.getSource();
			CompoundStatementNode body = makeCompound(loop.getBody());

			loop.setBody(body);
			condItems.add(nodeFactory.newIfNode(condSource, nodeFactory
					.newOperatorNode(condSource, Operator.NOT,
							condTriple.getNode()), nodeFactory
					.newBreakNode(condSource)));
			body.insertChildren(0, condItems);
			loop.setCondition(newOneNode(condSource));
		} else
			loop.setCondition(condTriple.getNode());
	}

	/**
	 * Produces a list of block items in normal form that is equivalent to the
	 * given for-loop node. The loop node may be modified.
	 * 
	 * @param loop
	 *            a non-<code>null</code> for loop node
	 * @return list of block items in normal form equivalent to original loop
	 *         node
	 */
	private List<BlockItemNode> translateForLoop(ForLoopNode forLoop) {
		normalizeLoopBody(forLoop);

		List<BlockItemNode> newItems = normalizeForLoopInitializer(forLoop);
		List<BlockItemNode> result = new LinkedList<>();

		newItems.add(forLoop);
		normalizeLoopCondition(forLoop);
		normalizeForLoopIncrementer(forLoop);
		if (newItems.size() > 1) {
			removeNodes(newItems);
			result.add(makeOneBlockItem(forLoop.getSource(), newItems));
		} else
			result = newItems;
		return result;
	}

	/**
	 * Produces a list of block items in normal form that is equivalent to the
	 * given while-loop node. The loop node may be modified.
	 * 
	 * Give the following while statement,
	 * 
	 * <pre>
	 * while(e){
	 * 	S;
	 * }
	 * </pre>
	 * 
	 * Let <code>S_be</code>, <code>S_af</code>, <code>x</code> be the
	 * side-effect-free triple of <code>e</code>, and <code>e'</code> is the
	 * side-effect-free translation of <code>e</code>. This function return the
	 * following result:
	 * 
	 * <pre>
	 * while(1){
	 *  var x;
	 * 	S_be;
	 * 	x=e';
	 * 	S_af;
	 * 	if(!x)
	 * 	  break;
	 * 	S;
	 * }
	 * </pre>
	 * 
	 * @param loop
	 *            a non-<code>null</code> while loop node
	 * @return list of block items in normal form equivalent to original loop
	 *         node
	 */
	private List<BlockItemNode> translateWhileLoop(LoopNode whileLoop) {
		normalizeLoopBody(whileLoop);
		normalizeLoopCondition(whileLoop);

		List<BlockItemNode> result = new LinkedList<>();

		result.add(whileLoop);
		return result;
	}

	/**
	 * Produces a list of block items in normal form that is equivalent to the
	 * given do-while-loop node. The loop node may be modified.
	 * 
	 * Give the following do-while statement,
	 * 
	 * <pre>
	 * do{
	 * 	S;
	 * }while(e);
	 * </pre>
	 * 
	 * Let <code>S_be</code>, <code>S_af</code>, <code>x</code> be the
	 * side-effect-free triple of <code>e</code>, and <code>e'</code> is the
	 * side-effect-free translation of <code>e</code>. This function return the
	 * following result:
	 * 
	 * <pre>
	 * var x;
	 * do{
	 * 	S;
	 * 	S_be;
	 * 	x=e';
	 * 	S_af;
	 * }while(x);
	 * </pre>
	 * 
	 * @param loop
	 *            a non-<code>null</code> do loop node
	 * @return list of block items in normal form equivalent to original loop
	 *         node
	 */
	private List<BlockItemNode> translateDoLoop(LoopNode doLoop) {
		normalizeLoopBody(doLoop);

		// do {... befores} while (e);
		ExprTriple condTriple = translate(doLoop.getCondition(), false);

		purify(condTriple);
		doLoop.setCondition(condTriple.getNode());

		List<BlockItemNode> condItems = condTriple.getBefore();
		List<BlockItemNode> result = new LinkedList<>();

		if (!condItems.isEmpty()) {
			CompoundStatementNode body = makeCompound(doLoop.getBody());
			List<BlockItemNode> newCondItems = new LinkedList<>();

			for (BlockItemNode item : condItems) {
				if (item instanceof VariableDeclarationNode) {
					VariableDeclarationNode variable = (VariableDeclarationNode) item;
					StatementNode assign = initializer2Assignment(variable);

					result.add(pureDeclaration(variable));
					if (assign != null)
						newCondItems.add(assign);
				} else
					newCondItems.add(item);
			}

			body.insertChildren(body.numChildren(), newCondItems);
			doLoop.setBody(body);
			// doLoop.setCondition(condTriple.getNode());
		}
		result.add(doLoop);
		if (result.size() > 1) {
			removeNodes(result);
			StatementNode compound = nodeFactory.newCompoundStatementNode(
					doLoop.getSource(), result);

			result.clear();
			result.add(compound);
		}
		return result;
	}

	/**
	 * Creates an assignment statement node equivalent to the initializer of a
	 * variable declaration. If the variable declaration has no initializer,
	 * returns true.
	 * 
	 * @param variable
	 * @return
	 */
	private StatementNode initializer2Assignment(
			VariableDeclarationNode variable) {
		InitializerNode initializer = variable.getInitializer();

		if (initializer == null)
			return null;
		assert initializer instanceof ExpressionNode;

		ExpressionNode rhs = ((ExpressionNode) initializer).copy();
		ExpressionNode lhs = nodeFactory.newIdentifierExpressionNode(
				variable.getSource(), variable.getIdentifier().copy());
		ExpressionNode assign = nodeFactory.newOperatorNode(
				variable.getSource(), Operator.ASSIGN, Arrays.asList(lhs, rhs));

		return nodeFactory.newExpressionStatementNode(assign);
	}

	/**
	 * Returns a variable declaration without initializer for a given variable
	 * declaration. If the variable declaration has no initializer, returns the
	 * variable declaration immediately.
	 * 
	 * @param variable
	 * @return
	 */
	private VariableDeclarationNode pureDeclaration(
			VariableDeclarationNode variable) {
		if (variable.getInitializer() == null)
			return variable;
		return this.nodeFactory.newVariableDeclarationNode(
				variable.getSource(), variable.getIdentifier().copy(), variable
						.getTypeNode().copy());
	}

	/**
	 * Produces a list of block items in normal form that is equivalent to the
	 * given loop node. The loop node may be modified.
	 * 
	 * @param loop
	 *            a non-<code>null</code> loop node
	 * @return list of block items in normal form equivalent to original loop
	 *         node
	 */
	private List<BlockItemNode> translateLoop(LoopNode loop) {
		switch (loop.getKind()) {
		case DO_WHILE:
			return translateDoLoop(loop);
		case FOR:
			return translateForLoop((ForLoopNode) loop);
		case WHILE:
			return translateWhileLoop(loop);
		default:
			throw new ABCRuntimeException("Unknown kind of loop: "
					+ loop.getKind());
		}
	}

	/**
	 * Transforms an atomic statement into a sequence of block items equivalent
	 * to the original statement but in normal form.
	 * 
	 * @param statement
	 * @return list of block items in normal form equivalent to original
	 */
	private List<BlockItemNode> translateAtomic(AtomicNode statement) {
		StatementNode body = statement.getBody();
		List<BlockItemNode> bodyItems = translateStatement(body);
		List<BlockItemNode> result = new LinkedList<>();

		result.add(statement);
		removeNodes(bodyItems);
		if (bodyItems.size() == 1) {
			BlockItemNode item = bodyItems.get(0);

			if (item instanceof StatementNode) {
				statement.setBody((StatementNode) item);
				return result;
			}
		}
		statement.setBody(nodeFactory.newCompoundStatementNode(
				body.getSource(), bodyItems));
		return result;
	}

	/**
	 * Returns a list of block items equivalent to the list of block items in a
	 * given compound statement, but all in normal form. May modify any node in
	 * the compound statement.
	 * 
	 * @param compound
	 *            a non-<code>null</code> compound statement node
	 * @return list of block items equivalent to the sequence of items in the
	 *         original compound statement
	 */
	private List<BlockItemNode> translateCompound(CompoundStatementNode compound) {
		List<BlockItemNode> blockItems = new LinkedList<>();
		List<BlockItemNode> result = new LinkedList<>();

		for (BlockItemNode item : compound) {
			List<BlockItemNode> tmp = translateBlockItem(item);

			blockItems.addAll(tmp);
		}
		removeNodes(blockItems);
		result.add(makeOneBlockItem(compound.getSource(), blockItems));
		if (result.size() == 1) {
			BlockItemNode node = result.get(0);

			if (!(node instanceof CompoundStatementNode))
				result = Arrays
						.asList((BlockItemNode) this.nodeFactory
								.newCompoundStatementNode(compound.getSource(),
										result));
		}
		return result;
	}

	/**
	 * Transforms a compound statement into an equivalent compound statement in
	 * which all the items are in normal form.
	 * 
	 * @param compound
	 *            a non-<code>null</code> compound statement node
	 * @return a compound statement node equivalent to original but in which all
	 *         items are in normal form
	 */
	private CompoundStatementNode transformCompound(
			CompoundStatementNode compound) {
		List<BlockItemNode> blockItems = translateCompound(compound);

		removeNodes(blockItems);
		if (blockItems.size() == 1) {
			BlockItemNode item = blockItems.get(0);

			if (item instanceof CompoundStatementNode)
				return (CompoundStatementNode) item;
		}
		return nodeFactory.newCompoundStatementNode(compound.getSource(),
				blockItems);
	}

	/**
	 * Given a statement, computes a list of block items whose execution is
	 * equivalent to the execution of the statement, but which are all in normal
	 * form. May result in the modification of the statement.
	 * 
	 * @param statement
	 *            a non-<code>null</code> statement node
	 * @return list of block items in normal form equivalent to given statement
	 */
	private List<BlockItemNode> translateStatement(StatementNode statement) {
		switch (statement.statementKind()) {
		case ATOMIC:
			return translateAtomic((AtomicNode) statement);
		case CHOOSE:
			return translateChoose((ChooseStatementNode) statement);
		case CIVL_FOR:
			return translateCivlFor((CivlForNode) statement);
		case COMPOUND:
			return translateCompound((CompoundStatementNode) statement);
		case EXPRESSION:
			return translateExpressionStatement((ExpressionStatementNode) statement);
		case IF:
			return translateIf((IfNode) statement);
		case JUMP:
			return translateJump((JumpNode) statement);
		case LABELED:
			return translateLabeledStatement((LabeledStatementNode) statement);
		case LOOP:
			return translateLoop((LoopNode) statement);
			// code review stops here on 04/06/2016
		case NULL:
			return Arrays.asList((BlockItemNode) statement);
		case OMP:
			return translateOmpExecutable((OmpExecutableNode) statement);
		case PRAGMA:
			throw new ABCUnsupportedException(
					"removing side-effects for pragmas");
		case SWITCH:
			return translateSwitch((SwitchNode) statement);
		case WHEN:
			return translateWhen((WhenNode) statement);
		default:
			throw new ABCUnsupportedException("removing side-effects for "
					+ statement.statementKind() + " statement");

		}
	}

	/**
	 * Transforms a jump statement into list of statements whose execution are
	 * equivalent to the jump statement.
	 * 
	 * <p>
	 * If the jump statement is NOT a return statement with an expression, then
	 * the jump node is returned immediately.
	 * </p>
	 * 
	 * @param compound
	 *            a non-<code>null</code> compound statement node
	 * @return a compound statement node equivalent to original but in which all
	 *         items are in normal form
	 */
	private List<BlockItemNode> translateJump(JumpNode jump) {
		List<BlockItemNode> result = new LinkedList<>();

		if (jump instanceof ReturnNode) {
			ReturnNode returnNode = (ReturnNode) jump;
			ExpressionNode expression = returnNode.getExpression();

			if (expression != null) {
				int exprIndex = expression.childIndex();
				ExprTriple exprTriple = translate(expression, false);

				purify(exprTriple);
				result.addAll(exprTriple.getBefore());
				returnNode.setChild(exprIndex, exprTriple.getNode());
				result.add(returnNode);
				return result;
			}
		}
		result.add(jump);
		return result;
	}

	/**
	 * Transforms a guarded statement into list of statements whose execution
	 * are equivalent to it. Note: the guard is not allowed to contain side
	 * effects and if so, an error should have been reported by the standard
	 * analyzer.
	 * 
	 * @param when
	 * @return
	 */
	private List<BlockItemNode> translateWhen(WhenNode when) {
		StatementNode body = when.getBody();
		List<BlockItemNode> bodyItems = this.translateStatement(body);
		List<BlockItemNode> result = new LinkedList<>();
		int bodyIndex = body.childIndex();

		assert when.getGuard().isSideEffectFree(false);
		this.removeNodes(bodyItems);
		when.setChild(bodyIndex,
				this.makeOneBlockItem(body.getSource(), bodyItems));
		result.add(when);
		return result;
	}

	/**
	 * Transforms a switch statement into list of statements whose execution are
	 * equivalent to it.
	 * 
	 * @param switchNode
	 * @return
	 */
	private List<BlockItemNode> translateSwitch(SwitchNode switchNode) {
		List<BlockItemNode> result = new LinkedList<>();
		ExpressionNode condition = switchNode.getCondition();
		int condIndex = condition.childIndex();
		ExprTriple condTriple = this.translate(condition, false);
		StatementNode body = switchNode.getBody();
		int bodyIndex = body.childIndex();
		List<BlockItemNode> bodyItems = this.translateStatement(body);

		purify(condTriple);
		result.addAll(condTriple.getBefore());
		switchNode.setChild(condIndex, condTriple.getNode());
		removeNodes(bodyItems);
		switchNode.setChild(bodyIndex,
				this.makeOneBlockItem(body.getSource(), bodyItems));
		result.add(switchNode);
		return result;
	}

	/**
	 * Transforms an OpenMP executable statement into list of statements whose
	 * execution are equivalent to it.
	 * 
	 * @param ompExec
	 * @return
	 */
	private List<BlockItemNode> translateOmpExecutable(OmpExecutableNode ompExec) {
		StatementNode body = ompExec.statementNode();
		List<BlockItemNode> result = new LinkedList<>();
		if (body != null) {
			int bodyIndex = body.childIndex();
			List<BlockItemNode> bodyItems = translateStatement(body);

			removeNodes(bodyItems);
			ompExec.setChild(bodyIndex,
					makeOneBlockItem(body.getSource(), bodyItems));
		}
		result.add(ompExec);
		return result;
	}

	/**
	 * Transforms a labeled statement into list of statements whose execution
	 * are equivalent to it.
	 * 
	 * @param labeled
	 * @return
	 */
	private List<BlockItemNode> translateLabeledStatement(
			LabeledStatementNode labeled) {
		StatementNode body = labeled.getStatement();
		int bodyIndex = body.childIndex();
		List<BlockItemNode> bodyNormals = translateStatement(body);
		List<BlockItemNode> result = new LinkedList<>();

		removeNodes(bodyNormals);
		labeled.setChild(bodyIndex,
				makeOneBlockItem(body.getSource(), bodyNormals));
		result.add(labeled);
		return result;
	}

	/**
	 * Transforms a if (or if-else) statement into list of statements whose
	 * execution are equivalent to it.
	 * 
	 * @param ifNode
	 * @return
	 */
	private List<BlockItemNode> translateIf(IfNode ifNode) {
		ExpressionNode condition = ifNode.getCondition();
		StatementNode trueBranch = ifNode.getTrueBranch();
		StatementNode falseBranch = ifNode.getFalseBranch();
		int condIndex = condition.childIndex(), trueIndex = trueBranch
				.childIndex();
		ExprTriple condTriple = translate(condition, false);
		List<BlockItemNode> trueNormalItems = translateStatement(trueBranch);
		List<BlockItemNode> result = new LinkedList<>();

		purify(condTriple);
		result.addAll(condTriple.getBefore());
		ifNode.setChild(condIndex, condTriple.getNode());
		removeNodes(trueNormalItems);
		ifNode.setChild(trueIndex,
				makeOneBlockItem(trueBranch.getSource(), trueNormalItems));
		if (falseBranch != null) {
			int falseIndex = falseBranch.childIndex();
			List<BlockItemNode> falseNormalItems = translateStatement(falseBranch);

			removeNodes(falseNormalItems);
			ifNode.setChild(falseIndex,
					makeOneBlockItem(falseBranch.getSource(), falseNormalItems));
		}
		result.add(ifNode);
		return result;
	}

	/**
	 * Creates one single block item node from a list of block item nodes. If
	 * the given list contains exactly one block item, then that block item is
	 * returned; otherwise, a compound statement node created using the list is
	 * returned.
	 * 
	 * @param source
	 * @param nodes
	 * @return
	 */
	private BlockItemNode makeOneBlockItem(Source source,
			List<BlockItemNode> nodes) {
		if (nodes.size() == 1)
			return nodes.get(0);
		else
			return nodeFactory.newCompoundStatementNode(source, nodes);
	}

	/**
	 * Transforms a civl for statement into list of statements whose execution
	 * are equivalent to it.
	 * 
	 * TODO: is the domain expression allowed to have side-effects?
	 * 
	 * FIXME: the invariant shouldn't have side effects, make the expression
	 * analyzer report an error
	 * 
	 * @param civlFor
	 * @return
	 */
	private List<BlockItemNode> translateCivlFor(CivlForNode civlFor) {
		List<BlockItemNode> result = new LinkedList<>();
		ExpressionNode domain = civlFor.getDomain();
		ExpressionNode invariant = civlFor.getInvariant();
		StatementNode body = civlFor.getBody();
		int domIndex = domain.childIndex(), bodyIndex = body.childIndex();
		ExprTriple domTriple = translate(domain, false);
		List<BlockItemNode> normalBodyItems = translateStatement(body);

		purify(domTriple);
		result.addAll(domTriple.getBefore());
		civlFor.setChild(domIndex, domTriple.getNode());
		if (invariant != null) {
			int invIndex = invariant.childIndex();
			ExprTriple invTriple = translate(invariant, false);

			purify(invTriple);
			result.addAll(invTriple.getBefore());
			civlFor.setChild(invIndex, invTriple.getNode());
		}
		removeNodes(normalBodyItems);
		if (normalBodyItems.size() == 1)
			civlFor.setChild(bodyIndex, normalBodyItems.get(0));
		else
			civlFor.setChild(bodyIndex, nodeFactory.newCompoundStatementNode(
					body.getSource(), normalBodyItems));
		result.add(civlFor);
		return result;
	}

	/**
	 * Removes a collection of nodes from their parents.
	 * 
	 * @param nodes
	 */
	private void removeNodes(Collection<? extends ASTNode> nodes) {
		for (ASTNode node : nodes)
			node.remove();
	}

	/**
	 * Transforms a civl choose statement into list of statements whose
	 * execution are equivalent to it.
	 * 
	 * @param choose
	 * @return
	 */
	private List<BlockItemNode> translateChoose(ChooseStatementNode choose) {
		int numChildren = choose.numChildren();
		List<BlockItemNode> result = new LinkedList<>();

		result.add(choose);
		for (int i = 0; i < numChildren; i++) {
			StatementNode child = choose.getSequenceChild(i);
			List<BlockItemNode> normalItems = translateStatement(child);

			removeNodes(normalItems);
			choose.setChild(i,
					this.makeOneBlockItem(child.getSource(), normalItems));
		}
		return result;
	}

	/**
	 * TODO simplify me using translateGeneric? Returns a list of block items in
	 * normal form that is equivalent to the given enumeration type declaration.
	 * 
	 * @param enumeration
	 * @return
	 */
	private List<BlockItemNode> translateEnumeration(
			EnumerationTypeNode enumeration) {
		SequenceNode<EnumeratorDeclarationNode> enumerators = enumeration
				.enumerators();
		int numEnumerators = enumerators.numChildren();
		List<BlockItemNode> result = new ArrayList<>();

		for (int i = 0; i < numEnumerators; i++) {
			EnumeratorDeclarationNode enumerator = enumerators
					.getSequenceChild(i);
			ExpressionNode value = enumerator.getValue();

			if (value != null) {
				ExprTriple expr = this.translate(value, false);

				result.addAll(expr.getBefore());
				enumerator.setValue(expr.getNode());
			}
		}
		result.add(enumeration);
		return result;
	}

	/**
	 * Returns a list of block items in normal form that is equivalent to the
	 * given struct or union type declaration.
	 * 
	 * @param structOrUnion
	 * @return
	 */
	private List<BlockItemNode> translateStructOrUnion(
			StructureOrUnionTypeNode structOrUnion) {
		SequenceNode<FieldDeclarationNode> fieldDecls = structOrUnion
				.getStructDeclList();
		List<BlockItemNode> result = new LinkedList<>();

		if (fieldDecls != null) {
			int numFields = fieldDecls.numChildren();

			for (int i = 0; i < numFields; i++) {
				FieldDeclarationNode fieldDecl = fieldDecls.getSequenceChild(i);
				SETriple seTriple = this.translateGenericNode(fieldDecl);

				result.addAll(seTriple.getBefore());
				seTriple.getNode().remove();
				fieldDecls.setChild(i, seTriple.getNode());
			}
		}
		result.add(structOrUnion);
		return result;
	}

	/**
	 * Returns a list of block items in normal form that is equivalent to the
	 * given typedef declaration.
	 * 
	 * @param structOrUnion
	 * @return
	 */
	private List<BlockItemNode> translateTypedef(TypedefDeclarationNode typedef) {
		SETriple seTriple = this.translateGenericNode(typedef);
		List<BlockItemNode> result = new ArrayList<>();

		result.addAll(seTriple.getBefore());
		result.add((BlockItemNode) seTriple.getNode());
		return result;
	}

	/**
	 * Returns a list of block items in normal form that is equivalent to the
	 * given block item. May modify the given block item.
	 * 
	 * @param item
	 *            a non-<code>null</code> block item
	 * @return list of block items all in normal form and equivalent to original
	 *         item
	 */
	private List<BlockItemNode> translateBlockItem(BlockItemNode item) {
		BlockItemKind kind = item.blockItemKind();

		switch (kind) {
		case ENUMERATION:
			return translateEnumeration((EnumerationTypeNode) item);
		case ORDINARY_DECLARATION:
			return translateOrdinaryDeclaration((OrdinaryDeclarationNode) item);
		case PRAGMA:
			return Arrays.asList((BlockItemNode) item);
		case STATEMENT:
			return translateStatement((StatementNode) item);
		case STATIC_ASSERTION:
			throw new ABCUnsupportedException(
					"normalization of static assertions in side-effect remover");
		case STRUCT_OR_UNION:
			return translateStructOrUnion((StructureOrUnionTypeNode) item);
		case TYPEDEF:
			return translateTypedef((TypedefDeclarationNode) item);
		default:
			throw new ABCUnsupportedException("normalization of block item of "
					+ kind + " kind in side-effect remover");
		}
	}

	// special handling: short circuit expressions ...
	/**
	 * transforms short circuit expressions recursively.
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void transformShortCircuitWork(ASTNode node) throws SyntaxException {
		if ((node instanceof StatementNode)
				&& !(node instanceof CompoundStatementNode)) {
			List<BlockItemNode> items = new ArrayList<>();

			for (ASTNode child : node.children()) {
				if (child == null)
					continue;
				if (child instanceof ExpressionNode) {
					List<BlockItemNode> childItems = this
							.transformShortCircuitExpression((ExpressionNode) child);

					items.addAll(childItems);
				} else if (child instanceof StatementNode) {
					transformShortCircuitWork(child);
				}
			}
			if (items.size() > 0) {
				ASTNode parent = node.parent();
				int statementIndex = node.childIndex();

				node.remove();
				items.add((StatementNode) node);

				StatementNode compound = this.nodeFactory
						.newCompoundStatementNode(node.getSource(), items);
				parent.setChild(statementIndex, compound);
			}
		} else {
			for (ASTNode child : node.children()) {
				if (child != null)
					this.transformShortCircuitWork(child);
			}
		}
	}

	/**
	 * checks if the given expression node is the condition of a loop node
	 * 
	 * @param expression
	 * @return
	 */
	private boolean isConditionOfLoop(ExpressionNode expression) {
		ASTNode parent = expression.parent();

		if (parent instanceof LoopNode) {
			// return expression.equals(((LoopNode)parent).getCondition());
			return expression.childIndex() == 0;
		}
		return false;
	}

	/**
	 * Transforms short circuit expressions with side-effects in the right
	 * operand recursively.
	 * 
	 * A short circuit expression is an operator expression of logical and/or.
	 * 
	 * If the expression doesn't contain any short circuit sub-expression, then
	 * this is a no-op.
	 * 
	 * @param expression
	 *            the expression to be transform
	 * @return a sorted list of block item nodes which is an equivalent
	 *         representation of the expression; if no transformation is
	 *         applied, then an empty list is returned.
	 * @throws SyntaxException
	 */
	private List<BlockItemNode> transformShortCircuitExpression(
			ExpressionNode expression) throws SyntaxException {
		if (expression instanceof QuantifiedExpressionNode)
			return new ArrayList<>(0);

		List<BlockItemNode> result = new ArrayList<>();
		StatementNode ifElse = null;
		VariableDeclarationNode tmpVar = null;
		boolean isLoopCond = this.isConditionOfLoop(expression);
		ASTNode parent = expression.parent();

		for (ASTNode child : expression.children()) {
			if (child == null)
				continue;
			if (child instanceof ExpressionNode) {
				List<BlockItemNode> subResult = transformShortCircuitExpression((ExpressionNode) child);

				result.addAll(subResult);
			}
		}
		if (expression instanceof OperatorNode) {
			OperatorNode operator = (OperatorNode) expression;
			Operator op = operator.getOperator();

			if (op == Operator.LAND || op == Operator.LOR) {
				ExpressionNode rhs = operator.getArgument(1);
				boolean isAnd = op == Operator.LAND;
				ExpressionNode lhs = operator.getArgument(0);

				if (!rhs.isSideEffectFree(false)) {
					Source source = expression.getSource();
					Source rhsSource = rhs.getSource();
					Source lhsSource = lhs.getSource();
					Type rhsType = rhs.getConvertedType();

					tmpVar = newTempVariable(rhsSource, rhsType);

					IdentifierExpressionNode tmpId = this.nodeFactory
							.newIdentifierExpressionNode(rhsSource,
									this.nodeFactory.newIdentifierNode(
											rhsSource, tmpVar.getName()));
					ExpressionNode condition;
					ExpressionNode trueAssign, falseAssign;

					lhs.remove();
					if (isAnd)
						condition = this.nodeFactory.newOperatorNode(lhsSource,
								Operator.NOT, lhs);
					else
						condition = lhs;
					trueAssign = this.nodeFactory.newOperatorNode(lhsSource,
							Operator.ASSIGN, Arrays.asList(tmpId.copy(),
									nodeFactory.newIntegerConstantNode(
											lhsSource, isAnd ? "0" : "1")));
					rhs.remove();
					falseAssign = this.nodeFactory.newOperatorNode(rhsSource,
							Operator.ASSIGN, Arrays.asList(tmpId.copy(), rhs));
					ifElse = nodeFactory.newIfNode(source, condition,
							this.nodeFactory
									.newExpressionStatementNode(trueAssign),
							this.nodeFactory
									.newExpressionStatementNode(falseAssign));
					operator.parent().setChild(operator.childIndex(), tmpId);
				}
			}
		}

		if ((result.size() > 0 || ifElse != null) && isLoopCond) {
			Source condSource = expression.getSource();
			LoopNode loop = (LoopNode) parent;
			CompoundStatementNode body = makeCompound(loop.getBody());
			ExpressionNode newCond = loop.getCondition();
			List<BlockItemNode> newItems = new LinkedList<>();

			loop.setBody(body);
			if (loop.getKind() == LoopKind.DO_WHILE) {
				int loopIndex = loop.childIndex();
				ASTNode loopParent = loop.parent();
				VariableDeclarationNode condVar = this.newTempVariable(
						condSource, expression.getConvertedType());

				newItems.add(condVar);
				if (tmpVar != null)
					newItems.add(0, tmpVar);
				if (ifElse != null)
					result.add(ifElse);
				// insert new variable
				expression.remove();
				result.add(this.nodeFactory
						.newExpressionStatementNode(this.nodeFactory
								.newOperatorNode(condSource, Operator.ASSIGN,
										Arrays.asList(nodeFactory
												.newIdentifierExpressionNode(
														condSource,
														condVar.getIdentifier()
																.copy()),
												expression))));
				body.insertChildren(body.numChildren(), result);
				loop.setCondition(nodeFactory.newIdentifierExpressionNode(
						condSource, condVar.getIdentifier().copy()));
				newItems.add(loop);
				loop.remove();
				loopParent.setChild(loopIndex, nodeFactory
						.newCompoundStatementNode(loop.getSource(), newItems));
			} else {
				if (tmpVar != null)
					result.add(tmpVar);
				if (ifElse != null)
					result.add(ifElse);
				newCond.remove();
				result.add(nodeFactory.newIfNode(condSource, nodeFactory
						.newOperatorNode(condSource, Operator.NOT, newCond),
						nodeFactory.newBreakNode(condSource)));
				body.insertChildren(0, result);
				loop.setCondition(newOneNode(condSource));
			}
			result.clear();
		} else {
			if (tmpVar != null)
				result.add(tmpVar);
			if (ifElse != null)
				result.add(ifElse);
		}
		return result;
	}

	/**
	 * creates a new temporary variable with unique name.
	 * 
	 * @param source
	 * @param type
	 * @return
	 */
	private VariableDeclarationNode newTempVariable(Source source, Type type) {
		String tmpId = tempVariablePrefix + (tempVariableCounter++);

		return nodeFactory.newVariableDeclarationNode(source,
				nodeFactory.newIdentifierNode(source, tmpId),
				typeNode(source, type));
	}

	/* Public Methods */

	/**
	 * {@inheritDoc}
	 * 
	 * Transforms this AST by removing all side effects so the entire AST is in
	 * normal form. The result is an equivalent AST. This method is destructive:
	 * it may modify the given AST.
	 */
	@Override
	public AST transform(AST ast) throws SyntaxException {
		SequenceNode<BlockItemNode> rootNode = ast.getRootNode();
		AST newAST;
		List<BlockItemNode> newBlockItems = new ArrayList<>();

		assert this.astFactory == ast.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		ast.release();
		transformShortCircuitWork(rootNode);
		// rootNode.prettyPrint(System.out);
		for (int i = 0; i < rootNode.numChildren(); i++) {
			BlockItemNode node = rootNode.getSequenceChild(i);
			List<BlockItemNode> normalNodes = this.translateBlockItem(node);

			removeNodes(normalNodes);
			newBlockItems.addAll(normalNodes);
		}
		rootNode = nodeFactory.newTranslationUnitNode(rootNode.getSource(),
				newBlockItems);
		newAST = astFactory.newAST(rootNode, ast.getSourceFiles(),
				ast.isWholeProgram());
		// newAST.prettyPrint(System.out, true);
		return newAST;
	}
}
