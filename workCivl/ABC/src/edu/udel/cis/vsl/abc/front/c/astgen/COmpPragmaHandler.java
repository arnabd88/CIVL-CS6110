package edu.udel.cis.vsl.abc.front.c.astgen;

import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.AMPERSAND;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.ATOMIC;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.BARRIER;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.BITOR;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.BITXOR;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.CAPTURE;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.COLLAPSE;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.COPYIN;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.COPYPRIVATE;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.CRITICAL;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.DATA_CLAUSE;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.DEFAULT;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.DYNAMIC;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.FLUSH;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.FOR;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.FST_PRIVATE;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.GUIDED;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.IDENTIFIER;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.IF;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.LST_PRIVATE;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.MASTER;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.NONE;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.NOWAIT;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.NUM_THREADS;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.ORDERED;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.PARALLEL;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.PARALLEL_FOR;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.PARALLEL_SECTIONS;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.PLUS;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.PRIVATE;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.READ;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.REDUCTION;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.RUNTIME;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.SCHEDULE;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.SECTION;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.SECTIONS;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.SEQ_CST;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.SHARED;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.SINGLE;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.STAR;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.STATIC;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.SUB;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.THD_PRIVATE;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.UNIQUE_FOR;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.UNIQUE_PARALLEL;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.UPDATE;
import static edu.udel.cis.vsl.abc.front.c.parse.COmpParser.WRITE;

import java.util.ArrayList;
import java.util.List;

import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.TokenStream;
import org.antlr.runtime.tree.CommonTree;

import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.PragmaNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IntegerConstantNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.OperatorNode.Operator;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpExecutableNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpForNode.OmpScheduleKind;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpParallelNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpReductionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpSyncNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode;
import edu.udel.cis.vsl.abc.ast.node.IF.omp.OmpWorksharingNode.OmpWorksharingNodeKind;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.err.IF.ABCUnsupportedException;
import edu.udel.cis.vsl.abc.front.IF.ParseTree;
import edu.udel.cis.vsl.abc.front.c.parse.COmpParser;
import edu.udel.cis.vsl.abc.front.common.astgen.PragmaHandler;
import edu.udel.cis.vsl.abc.front.common.astgen.SimpleScope;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

/**
 * This is responsible for translating an OpenMP pragma into OpenMP AST nodes.
 * Note: the source is first parsed by the general parser (CivlCParser), and
 * then at the AST builder phase, the OMPPragmaHandler is triggered to translate
 * the OpenMP pragma.
 * 
 * The input is a general pragma node produced by applying the general parser
 * (CivlCParser) to the pragma source. Since the OpenMP parser uses extra tokens
 * provided by OmpLexer, it needs to mark those tokens explicitly, which are all
 * considered as "IDENTIFIER" by CivlCParser; see
 * {@link #markTokens(PragmaNode)}.
 * 
 * @author Manchun Zheng
 *
 */
public class COmpPragmaHandler extends PragmaHandler {

	private ParseTree parseTree;

	private CASTBuilderWorker worker;

	/**
	 * The node factory used to create new AST nodes.
	 */
	private NodeFactory nodeFactory;

	/**
	 * The token factory used to create new tokens.
	 */
	private TokenFactory tokenFactory;

	private COmpParser cOmpParser;

	public COmpPragmaHandler(CASTBuilder builder, ParseTree parseTree) {
		ASTFactory astFactory = builder.getASTFactory();

		this.parseTree = parseTree;
		this.worker = builder.getWorker(parseTree);
		this.nodeFactory = astFactory.getNodeFactory();
		this.tokenFactory = astFactory.getTokenFactory();
		this.cOmpParser = new COmpParser();
	}

	// Private methods...

	/**
	 * Translates C tokens into OpenMP tokens.
	 * 
	 * @param ctokens
	 *            The list of C tokens to be translated.
	 * @return
	 */
	private void markTokens(PragmaNode pragmaNode) {
		int number = pragmaNode.getNumTokens();

		for (CivlcToken token : pragmaNode.getTokens()) {
			int type = token.getType();

			if (type == IDENTIFIER) {
				switch (token.getText()) {
				case "atomic":
					token.setType(ATOMIC);
					break;
				case "barrier":
					token.setType(BARRIER);
					break;
				case "capture":
					token.setType(CAPTURE);
					break;
				case "collapse":
					token.setType(COLLAPSE);
					break;
				case "copyin":
					token.setType(COPYIN);
					break;
				case "copyprivate":
					token.setType(COPYPRIVATE);
					break;
				case "critical":
					token.setType(CRITICAL);
					break;
				case "default":
					token.setType(DEFAULT);
					break;
				case "dynamic":
					token.setType(DYNAMIC);
					break;
				case "firstprivate":
					token.setType(FST_PRIVATE);
					break;
				case "flush":
					token.setType(FLUSH);
					break;
				case "guided":
					token.setType(GUIDED);
					break;
				case "lastprivate":
					token.setType(LST_PRIVATE);
					break;
				case "master":
					token.setType(MASTER);
					break;
				case "none":
					token.setType(NONE);
					break;
				case "nowait":
					token.setType(NOWAIT);
					break;
				case "num_threads":
					token.setType(NUM_THREADS);
					break;
				case "ordered":
					token.setType(ORDERED);
					break;
				case "parallel":
					token.setType(PARALLEL);
					break;
				case "private":
					token.setType(PRIVATE);
					break;
				case "read":
					token.setType(READ);
					break;
				case "reduction":
					token.setType(REDUCTION);
					break;
				case "runtime":
					token.setType(RUNTIME);
					break;
				case "schedule":
					token.setType(SCHEDULE);
					break;
				case "sections":
					token.setType(SECTIONS);
					break;
				case "section":
					token.setType(SECTION);
					break;
				case "seq_cst":
					token.setType(SEQ_CST);
					break;
				case "shared":
					token.setType(SHARED);
					break;
				case "single":
					token.setType(SINGLE);
					break;
				case "static":
					token.setType(STATIC);
					break;
				case "threadprivate":
					token.setType(THD_PRIVATE);
					break;
				case "update":
					token.setType(UPDATE);
					break;
				case "write":
					token.setType(WRITE);
					break;
				default:
				}
			}
		}
		if (number >= 1)
			pragmaNode.getToken(number - 1).setNext(null);
	}

	private OmpWorksharingNode translateWorkshare(Source source,
			CommonTree workshareTree, OmpWorksharingNodeKind kind) {
		int numChildren = workshareTree.getChildCount();
		OmpWorksharingNode workshareNode = nodeFactory.newWorksharingNode(
				source, kind);
		boolean hasNowait = false;

		for (int i = 0; i < numChildren; i++) {
			CommonTree sectionsClause = (CommonTree) workshareTree.getChild(i);
			int type = sectionsClause.getType();

			switch (type) {
			case DATA_CLAUSE:
				this.translateDataClause(source, sectionsClause, workshareNode);
				break;
			case NOWAIT:
				if (!hasNowait) {
					hasNowait = true;
				} else {
					throw new ABCRuntimeException(
							"At most one nowait directive is allowed in an OpenMP construct.",
							(tokenFactory.newSource((CivlcToken) sectionsClause
									.getToken()).getSummary(false)));
				}
				workshareNode.setNowait(true);
				break;
			default:
				throw new ABCRuntimeException(
						"OMPPragmaHandler: unsupported token");
			}
		}
		return workshareNode;
	}

	private OmpForNode translateFor(Source source, CommonTree forTree)
			throws SyntaxException {
		int numChildren = forTree.getChildCount();
		OmpForNode forNode = nodeFactory.newOmpForNode(source, null);

		for (int i = 0; i < numChildren; i++) {
			CommonTree forClause = (CommonTree) (forTree.getChild(i))
					.getChild(0);
			int type = forClause.getType();

			switch (type) {
			case UNIQUE_FOR:
				translateUniqueForClause((CommonTree) forClause, forNode);
				break;
			case DATA_CLAUSE:
				this.translateDataClause(source, forClause, forNode);
				break;
			case NOWAIT:
				forNode.setNowait(true);
				break;
			default:
				throw new ABCRuntimeException("Unreachable");
			}
		}

		return forNode;
	}

	private void translateUniqueForClause(CommonTree forClause,
			OmpForNode forNode) throws SyntaxException {
		CommonTree uniqueForClause = (CommonTree) forClause.getChild(0);
		int type = uniqueForClause.getType();

		switch (type) {
		case ORDERED:
			break;
		case SCHEDULE:
			int scheduleType = uniqueForClause.getChild(0).getType();

			switch (scheduleType) {
			case STATIC:
				forNode.setSchedule(OmpScheduleKind.STATIC);
				break;
			case DYNAMIC:
				forNode.setSchedule(OmpScheduleKind.DYNAMIC);
				break;
			case GUIDED:
				forNode.setSchedule(OmpScheduleKind.GUIDED);
				break;
			default: // case RUNTIME:
				forNode.setSchedule(OmpScheduleKind.RUNTIME);
			}
			if (uniqueForClause.getChildCount() > 1) {
				CommonTree chunkSizeTree = (CommonTree) uniqueForClause
						.getChild(1);

				// TODO: is null acceptable for a SimpleScope?

				ExpressionNode chunkSizeNode = worker.translateExpression(
						chunkSizeTree, null);

				forNode.setChunsize(chunkSizeNode);
			}

			break;
		case COLLAPSE: {
			CommonTree constant = (CommonTree) uniqueForClause.getChild(0);
			IntegerConstantNode constantNode = nodeFactory
					.newIntegerConstantNode(null, constant.getText());

			forNode.setCollapse(constantNode.getConstantValue()
					.getIntegerValue().intValue());
			break;
		}
		default:
			throw new ABCRuntimeException("Unreachable");
		}
	}

	private OmpNode translateParallel(Source source, CommonTree paralle)
			throws SyntaxException {
		int numChildren = paralle.getChildCount();
		OmpParallelNode parallelNode = nodeFactory.newOmpParallelNode(source,
				null);
		boolean hasIf = false;
		boolean hasNumThreads = false;

		for (int i = 0; i < numChildren; i++) {
			CommonTree parallelClause = (CommonTree) paralle.getChild(i);
			int type = parallelClause.getType();

			switch (type) {
			case UNIQUE_PARALLEL:
				int result = this.translateUniqueParallel(parallelClause,
						parallelNode);

				if (result == IF) {
					if (!hasIf) {
						hasIf = true;
					} else {
						throw new ABCRuntimeException(
								"At most one if clause is allowed in an OpenMP parallel construct.",
								(tokenFactory.newSource((CivlcToken) parallelClause
										.getToken()).getSummary(false)));
					}
				} else if (result == NUM_THREADS) {
					if (!hasNumThreads) {
						hasNumThreads = true;
					} else {
						throw new ABCRuntimeException(
								"At most one num_threads() clause is allowed in an OpenMP parallel construct.",
								(tokenFactory.newSource((CivlcToken) parallelClause
										.getToken()).getSummary(false)));
					}
				}
				break;
			case DATA_CLAUSE:
				this.translateDataClause(source, parallelClause, parallelNode);
				break;
			default:
				throw new ABCRuntimeException("Unreachable");
			}
		}
		return parallelNode;
	}

	private int translateUniqueParallel(CommonTree parallelClause,
			OmpParallelNode parallelNode) throws SyntaxException {
		CommonTree child = (CommonTree) parallelClause.getChild(0);
		ExpressionNode expression;

		switch (child.getType()) {
		case IF:
			expression = worker.translateExpression(
					(CommonTree) child.getChild(0), null);
			parallelNode.setIfClause(expression);
			return IF;
		case NUM_THREADS:
			expression = worker.translateExpression(
					(CommonTree) child.getChild(0), null);
			parallelNode.setNumThreads(expression);
			return NUM_THREADS;
		default:
			throw new ABCRuntimeException("Unreachable");
		}
	}

	private OmpParallelNode translateParallelFor(Source source,
			CommonTree parallelFor) throws SyntaxException {
		int numChildren = parallelFor.getChildCount();
		OmpParallelNode parallelNode = nodeFactory.newOmpParallelNode(source,
				null);
		OmpForNode forNode = nodeFactory.newOmpForNode(source, null);

		for (int i = 0; i < numChildren; i++) {
			CommonTree parallelForClause = (CommonTree) parallelFor.getChild(i);
			int type = parallelForClause.getType();

			switch (type) {
			case UNIQUE_PARALLEL:
				this.translateUniqueParallel(parallelForClause, parallelNode);
				break;
			case UNIQUE_FOR:
				this.translateUniqueForClause(parallelForClause, forNode);
				break;
			case DATA_CLAUSE:
				this.translateDataClause(source, parallelForClause,
						parallelNode);
				break;
			default:
				throw new ABCRuntimeException("Unreachable");
			}
		}
		parallelNode.setStatementNode(forNode);
		return parallelNode;
	}

	private OmpParallelNode translateParallelSections(Source source,
			CommonTree parallelSections) throws SyntaxException {
		int numChildren = parallelSections.getChildCount();
		OmpParallelNode parallelNode = nodeFactory.newOmpParallelNode(source,
				null);
		OmpWorksharingNode sectionsNode = nodeFactory.newOmpSectionsNode(
				source, null);

		for (int i = 0; i < numChildren; i++) {
			CommonTree parallelSectionsClause = (CommonTree) parallelSections
					.getChild(i);
			int type = parallelSectionsClause.getType();

			switch (type) {
			case UNIQUE_PARALLEL:
				this.translateUniqueParallel(parallelSectionsClause,
						parallelNode);
				break;
			case DATA_CLAUSE:
				this.translateDataClause(source, parallelSectionsClause,
						parallelNode);
				break;
			default:
				throw new ABCRuntimeException("Unreachable");
			}
		}
		parallelNode.setStatementNode(sectionsNode);
		return parallelNode;
	}

	private void translateDataClause(Source source, CommonTree dataClause,
			OmpExecutableNode ompStatementNode) {
		int numChildren = dataClause.getChildCount();
		CommonTree dataClauseEle;
		int type;

		assert numChildren == 1;
		dataClauseEle = (CommonTree) dataClause.getChild(0);
		type = dataClauseEle.getType();
		switch (type) {
		case PRIVATE:
			ompStatementNode.setPrivateList(translateIdentifierList(source,
					"privateList", (CommonTree) dataClauseEle.getChild(0)));
			break;
		case FST_PRIVATE:
			ompStatementNode.setFirstprivateList(translateIdentifierList(
					source, "firstprivateList",
					(CommonTree) dataClauseEle.getChild(0)));
			break;
		case LST_PRIVATE:
			ompStatementNode.setLastprivateList(translateIdentifierList(source,
					"lastprivateList", (CommonTree) dataClauseEle.getChild(0)));
			break;
		case SHARED:
			ompStatementNode.setSharedList(translateIdentifierList(source,
					"sharedList", (CommonTree) dataClauseEle.getChild(0)));
			break;
		case COPYIN:
			ompStatementNode.setCopyinList(translateIdentifierList(source,
					"copyinList", (CommonTree) dataClauseEle.getChild(0)));
			break;
		case COPYPRIVATE:
			ompStatementNode.setCopyprivateList(translateIdentifierList(source,
					"copyprivateList", (CommonTree) dataClauseEle.getChild(0)));
			break;
		case DEFAULT:
			if (dataClause.getChild(0).getChild(0).getType() == NONE)
				((OmpParallelNode) ompStatementNode).setDefault(false);
			break;
		case REDUCTION:
			OmpReductionNode reductionNode = translateReductionClause(dataClauseEle);
			SequenceNode<OmpReductionNode> reductionList = ompStatementNode
					.reductionList();

			if (reductionList == null) {
				List<OmpReductionNode> nodes = new ArrayList<>(1);

				nodes.add(reductionNode);
				reductionList = nodeFactory.newSequenceNode(
						reductionNode.getSource(), "reductionList", nodes);
			}
			ompStatementNode.setReductionList(reductionList);
			break;
		default:
			throw new ABCRuntimeException("Invalid data clause");
		}
	}

	private OmpReductionNode translateReductionClause(CommonTree reduction) {
		int operatorType = reduction.getChild(0).getType();
		List<IdentifierExpressionNode> list = translateIdentifierList((CommonTree) reduction
				.getChild(1));
		Source rootSource = tokenFactory.newSource((CivlcToken) reduction
				.getToken());
		SequenceNode<IdentifierExpressionNode> nodes = nodeFactory
				.newSequenceNode(rootSource, "reductionList", list);

		if (operatorType == IDENTIFIER) {
			IdentifierExpressionNode function = this
					.translateIdentifierExpression((CommonTree) reduction
							.getChild(0));

			return this.nodeFactory.newOmpFunctionReductionNode(rootSource,
					function, nodes);
		} else {
			Operator operator = translateOperator(reduction.getChild(0)
					.getType());

			return this.nodeFactory.newOmpSymbolReductionNode(rootSource,
					operator, nodes);
		}
	}

	private Operator translateOperator(int type) {
		switch (type) {
		case PLUS:
			return Operator.PLUSEQ;
		case STAR:
			return Operator.TIMESEQ;
		case SUB:
			return Operator.MINUSEQ;
		case AMPERSAND:
			return Operator.BITANDEQ;
		case BITXOR:
			return Operator.BITXOREQ;
		case BITOR:
			return Operator.BITOREQ;
			// case AND:
			// return Operator.LANDEQ;
			// case OR:
			// return Operator.LOREQ;
		default:
			throw new ABCUnsupportedException("reduction operator of type "
					+ type);
		}
	}

	private SequenceNode<IdentifierExpressionNode> translateIdentifierList(
			Source source, String name, CommonTree identifierList) {
		List<IdentifierExpressionNode> list = translateIdentifierList(identifierList);

		return nodeFactory.newSequenceNode(source, name, list);
	}

	private List<IdentifierExpressionNode> translateIdentifierList(
			CommonTree identifierList) {
		int numChildren = identifierList.getChildCount();
		List<IdentifierExpressionNode> list = new ArrayList<>(numChildren);

		for (int i = 0; i < numChildren; i++) {
			list.add(translateIdentifierExpression((CommonTree) identifierList
					.getChild(i)));
		}
		return list;
	}

	private IdentifierExpressionNode translateIdentifierExpression(
			CommonTree identifier) {
		IdentifierNode identifierNode = translateIdentifier(identifier);

		return nodeFactory.newIdentifierExpressionNode(
				identifierNode.getSource(), identifierNode);
	}

	private IdentifierNode translateIdentifier(CommonTree identifier) {
		CivlcToken token = (CivlcToken) identifier.getToken();
		Source source = tokenFactory.newSource(token);

		return nodeFactory.newIdentifierNode(source, token.getText());
	}

	// Public methods....

	@Override
	public EntityKind getEntityKind() {
		return EntityKind.PRAGMA_HANDLER;
	}

	@Override
	public String getName() {
		return "omp";
	}

	@Override
	public ParseTree getParseTree() {
		return parseTree;
	}

	@Override
	public ASTNode processPragmaNode(PragmaNode pragmaNode, SimpleScope scope)
			throws SyntaxException {
		Source source = pragmaNode.getSource();
		CivlcTokenSource tokenSource;
		TokenStream tokens;
		CommonTree rootTree;
		int type;

		markTokens(pragmaNode);
		tokenSource = pragmaNode.newTokenSource();
		tokens = new CommonTokenStream(tokenSource);
		rootTree = this.cOmpParser.parse(source, tokens);
		type = rootTree.getType();
		switch (type) {
		case PARALLEL_FOR:
			return translateParallelFor(source, rootTree);
		case PARALLEL_SECTIONS:
			return translateParallelSections(source, rootTree);
		case PARALLEL:
			return translateParallel(source, rootTree);
		case FOR:
			return translateFor(source, rootTree);
		case SECTIONS:
			return translateWorkshare(source, rootTree,
					OmpWorksharingNodeKind.SECTIONS);
		case SINGLE:
			return translateWorkshare(source, rootTree,
					OmpWorksharingNodeKind.SINGLE);
		case MASTER:
			return nodeFactory.newOmpMasterNode(source, null);
		case CRITICAL: {
			OmpSyncNode criticalNode = nodeFactory.newOmpCriticalNode(source,
					null, null);

			if (rootTree.getChildCount() > 0) {
				criticalNode
						.setCriticalName(this
								.translateIdentifier((CommonTree) rootTree
										.getChild(0)));
			}
			return criticalNode;
		}
		case ORDERED:
			return nodeFactory.newOmpOrederedNode(source, null);
		case SECTION:
			return nodeFactory.newOmpSectionNode(source, null);
		case BARRIER:
			return nodeFactory.newOmpBarrierNode(source);
		case FLUSH:
			return nodeFactory.newOmpFlushNode(
					source,
					translateIdentifierList(source, "flushList",
							(CommonTree) rootTree.getChild(0)));
		case THD_PRIVATE:
			return nodeFactory.newOmpThreadprivateNode(
					source,
					translateIdentifierList(source, "threadprivateList",
							(CommonTree) rootTree.getChild(0)));
		case ATOMIC:
			return nodeFactory.newOmpAtomicNode(source, null);
		default:
			throw new ABCRuntimeException("Unreachable");
		}
	}
}
