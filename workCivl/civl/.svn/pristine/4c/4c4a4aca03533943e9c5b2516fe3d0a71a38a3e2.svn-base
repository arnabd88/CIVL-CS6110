package edu.udel.cis.vsl.civl.transform.common;

import java.util.ArrayList;
import java.util.List;

import edu.udel.cis.vsl.abc.ABCUnsupportedException;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.IdentifierNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StringLiteralNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.CompoundStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ExpressionStatementNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.ReturnNode;
import edu.udel.cis.vsl.abc.ast.value.IF.StringValue;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.BaseTransformer;

/**
 * The IO transformer transforms<br>
 * <ul>
 * <li>all function calls printf(...) into frpintf(stdout, ...)</li>
 * <li>all function calls scanf(...) into fscanf(stdin, ...)</li>
 * <li>all function calls fopen(...) into $fopen(...)</li>
 * </ul>
 * 
 * @author zmanchun
 * 
 */
public class IOTransformer extends BaseTransformer {

	public static String CODE = "io";
	public static String LONG_NAME = "IOTransformer";
	public static String SHORT_DESCRIPTION = "transforms C program with IO to CIVL-C";

	public static String PRINTF = "printf";
	public static String FPRINTF = "fprintf";
	public static String SCANF = "scanf";
	public static String FSCANF = "fscanf";
	public static String STD_OUT = "stdout";
	public static String STD_IN = "stdin";
	public static String FOPEN = "fopen";
	public static String FOPEN_NEW = "$fopen";
	public static String CIVL_FILE_SYSTEM = "CIVL_filesystem";
	public static String CIVL_FILE_MODE_R = "CIVL_FILE_MODE_R";// r
	public static String CIVL_FILE_MODE_W = "CIVL_FILE_MODE_W";// w
	public static String CIVL_FILE_MODE_WX = "CIVL_FILE_MODE_WX";// wx
	public static String CIVL_FILE_MODE_A = "CIVL_FILE_MODE_A";// a
	public static String CIVL_FILE_MODE_RB = "CIVL_FILE_MODE_RB";// rb
	public static String CIVL_FILE_MODE_WB = "CIVL_FILE_MODE_WB";// wb
	public static String CIVL_FILE_MODE_WBX = "CIVL_FILE_MODE_WBX";// wbx
	public static String CIVL_FILE_MODE_AB = "CIVL_FILE_MODE_AB";// ab
	public static String CIVL_FILE_MODE_RP = "CIVL_FILE_MODE_RP";// r+
	public static String CIVL_FILE_MODE_WP = "CIVL_FILE_MODE_WP";// w+
	public static String CIVL_FILE_MODE_WPX = "CIVL_FILE_MODE_WPX";// w+x
	public static String CIVL_FILE_MODE_AP = "CIVL_FILE_MODE_AP";// a+
	public static String CIVL_FILE_MODE_RPB = "CIVL_FILE_MODE_RPB";// r+b or rb+
	public static String CIVL_FILE_MODE_WPB = "CIVL_FILE_MODE_WPB";// w+b or wb+
	public static String CIVL_FILE_MODE_WPBX = "CIVL_FILE_MODE_WPBX";// w+bx or
																		// wb+x
	public static String CIVL_FILE_MODE_APB = "CIVL_FILE_MODE_APB";// a+b or ab+
	public static String FOPEN_R = "r";
	public static String FOPEN_W = "w";
	public static String FOPEN_WX = "wx";
	public static String FOPEN_A = "a";
	public static String FOPEN_RB = "rb";
	public static String FOPEN_WB = "wb";
	public static String FOPEN_WBX = "wbx";
	public static String FOPEN_AB = "ab";
	public static String FOPEN_RP = "r+";
	public static String FOPEN_WP = "w+";
	public static String FOPEN_WPX = "w+x";
	public static String FOPEN_AP = "a+";
	public static String FOPEN_RPB = "r+b";
	public static String FOPEN_RBP = "rb+";
	public static String FOPEN_WPB = "w+b";
	public static String FOPEN_WBP = "wb+";
	public static String FOPEN_WPBX = "w+bx";
	public static String FOPEN_WBPX = "wb+x";
	public static String FOPEN_APB = "a+b";
	public static String FOPEN_ABP = "ab+";

	public static String FILESYSTEM_DESTROY = "$filesystem_destroy";
	public static String CIVL_FILESYSTEM = "CIVL_filesystem";

	public IOTransformer(ASTFactory astFactory) {
		super(IOTransformer.CODE, IOTransformer.LONG_NAME,
				IOTransformer.SHORT_DESCRIPTION, astFactory);
	}

	@Override
	public AST transform(AST unit) throws SyntaxException {
		ASTNode rootNode = unit.getRootNode();

		assert this.astFactory == unit.getASTFactory();
		assert this.nodeFactory == astFactory.getNodeFactory();
		unit.release();
		this.renameFunctionCalls(rootNode);
		this.processFreeCall(rootNode);
		return astFactory.newTranslationUnit(rootNode);
	}

	private void processFreeCall(ASTNode node) {
		int numChildren = node.numChildren();

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = node.child(i);

			if (child instanceof FunctionDefinitionNode) {
				FunctionDefinitionNode function = (FunctionDefinitionNode) child;
				String functionName = function.getName();

				if (functionName.equals("main")) {
					ExpressionStatementNode functionCallStatement;
					FunctionCallNode functionCall;
					List<ExpressionNode> arguments = new ArrayList<>(1);
					CompoundStatementNode body = function.getBody();
					BlockItemNode lastStatement = body.getSequenceChild(body
							.numChildren() - 1);

					arguments.add(nodeFactory.newIdentifierExpressionNode(node
							.getSource(), nodeFactory.newIdentifierNode(
							node.getSource(), CIVL_FILESYSTEM)));
					functionCall = nodeFactory.newFunctionCallNode(node
							.getSource(), nodeFactory
							.newIdentifierExpressionNode(node.getSource(),
									nodeFactory.newIdentifierNode(
											node.getSource(),
											FILESYSTEM_DESTROY)), arguments,
							null);
					functionCallStatement = nodeFactory
							.newExpressionStatementNode(functionCall);
					if (!(lastStatement instanceof ReturnNode)) {
						body.addSequenceChild(functionCallStatement.copy());
					}
					this.addFreeBeforeReturn(body, functionCallStatement);
				}
			}
		}
	}

	/**
	 * Processes an AST node.
	 * 
	 * @param node
	 * @throws SyntaxException
	 */
	private void renameFunctionCalls(ASTNode node) throws SyntaxException {
		int numChildren = node.numChildren();

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = node.child(i);

			if (child != null)
				this.renameFunctionCalls(node.child(i));
			// if (child.getSource().getFirstToken().getSourceFile().getName()
			// .equals("stdio-c.cvl")) {
			// if (child instanceof ExpressionStatementNode) {
			// ExpressionStatementNode expressionStatement =
			// (ExpressionStatementNode) child;
			//
			// if (expressionStatement.getExpression() instanceof
			// FunctionCallNode) {
			// FunctionCallNode functionCall = (FunctionCallNode)
			// expressionStatement
			// .getExpression();
			// String functionName = ((IdentifierExpressionNode) functionCall
			// .getFunction()).getIdentifier().name();
			//
			// if (functionName.equals("$filesystem_destroy")) {
			// this.freeCall = expressionStatement;
			// node.removeChild(i);
			// }
			// }
			// }
			// }
		}
		if (node instanceof FunctionCallNode) {
			this.processFunctionCall((FunctionCallNode) node);
		}
	}

	private void addFreeBeforeReturn(ASTNode node,
			ExpressionStatementNode functionCallStatement) {
		int numChildren = node.numChildren();

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = node.child(i);

			if (child == null)
				continue;
			if (child instanceof ReturnNode) {
				List<BlockItemNode> statements = new ArrayList<>(2);

				statements.add(functionCallStatement.copy());
				statements.add((ReturnNode) child);
				node.removeChild(i);
				node.setChild(i, nodeFactory.newCompoundStatementNode(
						child.getSource(), statements));
			} else
				this.addFreeBeforeReturn(node.child(i), functionCallStatement);
		}
	}

	private void processFunctionCall(FunctionCallNode functionCall)
			throws SyntaxException {
		if (functionCall.getFunction().expressionKind() == ExpressionKind.IDENTIFIER_EXPRESSION) {
			IdentifierExpressionNode functionExpression = (IdentifierExpressionNode) functionCall
					.getFunction();
			String functionName = functionExpression.getIdentifier().name();
			String firstArgName = "";
			IdentifierNode functionNameIdentifer = functionExpression
					.getIdentifier();

			if (functionName.equals(PRINTF) || functionName.equals(SCANF)) {
				if (functionName.equals(PRINTF)) {
					functionNameIdentifer.setName(FPRINTF);
					firstArgName = STD_OUT;
				} else if (functionName.equals(SCANF)) {
					functionNameIdentifer.setName(FSCANF);
					firstArgName = STD_IN;
				}
				processPrintfOrScanf(functionCall, firstArgName);
			} else if (functionName.equals(FOPEN)) {
				functionNameIdentifer.setName(FOPEN_NEW);
				processFopen(functionCall);
			}
		}
	}

	/**
	 * fopen(filename, "mode") --> $fopen(CIVL_filesystem, filename,
	 * MODE_CONSTANT)
	 * 
	 * @param functionCall
	 * @throws SyntaxException
	 */
	private void processFopen(FunctionCallNode functionCall)
			throws SyntaxException {
		Source source = functionCall.getFunction().getSource();
		IdentifierExpressionNode civlFileSystem = nodeFactory
				.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, CIVL_FILE_SYSTEM));
		int oldCount = functionCall.getNumberOfArguments();
		List<ExpressionNode> arguments = new ArrayList<>(oldCount + 1);
		ExpressionNode modeArg = functionCall.getArgument(1);

		arguments.add(civlFileSystem);
		arguments.add(functionCall.getArgument(0));
		if (modeArg instanceof StringLiteralNode) {
			StringValue value = ((StringLiteralNode) modeArg)
					.getConstantValue();
			String modeString = this.processFopenMode(value.toString(),
					modeArg.getSource());

			source = modeArg.getSource();
			arguments.add(nodeFactory.newIdentifierExpressionNode(source,
					nodeFactory.newIdentifierNode(source, modeString)));
		} else {
			throw new ABCUnsupportedException(
					"non-string-literal file mode of fopen");
		}
		for (int i = 0; i < oldCount; i++) {
			ExpressionNode argument = functionCall.getArgument(i);

			argument.parent().removeChild(argument.childIndex());
		}
		functionCall.setChild(1, nodeFactory.newSequenceNode(source,
				"ActualParameterList", arguments));
	}

	private String processFopenMode(String mode, Source source)
			throws SyntaxException {
		if (mode.equals(FOPEN_R))
			return CIVL_FILE_MODE_R;
		if (mode.equals(FOPEN_W))
			return CIVL_FILE_MODE_W;
		if (mode.equals(FOPEN_WX))
			return CIVL_FILE_MODE_WX;
		if (mode.equals(FOPEN_A))
			return CIVL_FILE_MODE_A;
		if (mode.equals(FOPEN_RB))
			return CIVL_FILE_MODE_RB;
		if (mode.equals(FOPEN_WB))
			return CIVL_FILE_MODE_WB;
		if (mode.equals(FOPEN_WBX))
			return CIVL_FILE_MODE_WBX;
		if (mode.equals(FOPEN_AB))
			return CIVL_FILE_MODE_AB;
		if (mode.equals(FOPEN_RP))
			return CIVL_FILE_MODE_RP;
		if (mode.equals(FOPEN_WP))
			return CIVL_FILE_MODE_WP;
		if (mode.equals(FOPEN_WPX))
			return CIVL_FILE_MODE_WPX;
		if (mode.equals(FOPEN_AP))
			return CIVL_FILE_MODE_AP;
		if (mode.equals(FOPEN_RPB) || mode.equals(FOPEN_RBP))
			return CIVL_FILE_MODE_RPB;
		if (mode.equals(FOPEN_WPB) || mode.equals(FOPEN_WBP))
			return CIVL_FILE_MODE_WPB;
		if (mode.equals(FOPEN_WPBX) || mode.equals(FOPEN_WBPX))
			return CIVL_FILE_MODE_WPBX;
		if (mode.equals(FOPEN_APB) || mode.equals(FOPEN_ABP))
			return CIVL_FILE_MODE_APB;
		throw new SyntaxException("Invalid mode " + mode + " of fopen.", source);
	}

	private void processPrintfOrScanf(FunctionCallNode functionCall,
			String firstArgName) {
		Source source = functionCall.getFunction().getSource();
		IdentifierExpressionNode firstArg = nodeFactory
				.newIdentifierExpressionNode(source,
						nodeFactory.newIdentifierNode(source, firstArgName));
		int oldCount = functionCall.getNumberOfArguments();
		List<ExpressionNode> arguments = new ArrayList<>(oldCount + 1);

		arguments.add(firstArg);
		for (int i = 0; i < oldCount; i++) {
			ExpressionNode argument = functionCall.getArgument(i);

			argument.parent().removeChild(argument.childIndex());
			arguments.add(argument);
		}
		functionCall.setChild(1, nodeFactory.newSequenceNode(source,
				"ActualParameterList", arguments));
	}

	// private void processOperator(OperatorNode expression)
	// throws SyntaxException {
	// int count = expression.getNumberOfArguments();
	//
	// for (int i = 0; i < count; i++) {
	// processExpression(expression.getArgument(i));
	// }
	// }

}
