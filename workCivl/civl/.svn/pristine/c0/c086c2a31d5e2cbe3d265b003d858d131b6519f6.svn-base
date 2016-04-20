package edu.udel.cis.vsl.civl.transform.IF;

import java.io.PrintStream;
import java.util.List;

import edu.udel.cis.vsl.abc.antlr2ast.IF.ASTBuilder;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.PragmaNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.transform.common.AST2CIVL;
import edu.udel.cis.vsl.civl.transform.common.CIVLBaseTransformer;
import edu.udel.cis.vsl.civl.transform.common.CIVLPragmaTransformer;
import edu.udel.cis.vsl.civl.transform.common.GeneralTransformer;
import edu.udel.cis.vsl.civl.transform.common.IOTransformer;
import edu.udel.cis.vsl.civl.transform.common.MPI2CIVLTransformer;
import edu.udel.cis.vsl.civl.transform.common.OmpPragmaTransformer;
import edu.udel.cis.vsl.civl.transform.common.OpenMPSimplifier;
import edu.udel.cis.vsl.civl.transform.common.Pthread2CIVLTransformer;

/**
 * This class manages the set of transformations provided by CIVL.
 * 
 * It provides a static method
 * {@link #applyTransformer(Program, String, List, ASTBuilder)} to apply a
 * certain transformer to a given program.
 * 
 * @author Manchun Zheng
 * 
 */
public class CIVLTransform {
	/**
	 * A list of codes of transformers provided by CIVL. Add one entry here when
	 * you create a new transformer, following the same pattern as the others.
	 */
	public final static String GENERAL = GeneralTransformer.CODE;
	public final static String IO = IOTransformer.CODE;
	public final static String OMP_PRAGMA = OmpPragmaTransformer.CODE;
	public final static String OMP_SIMPLIFY = OpenMPSimplifier.CODE;
	public final static String MPI = MPI2CIVLTransformer.CODE;
	public final static String PTHREAD = Pthread2CIVLTransformer.CODE;
	public final static String CIVL_PRAGMA = CIVLPragmaTransformer.CODE;

	/**
	 * Applies a transformer to a program.
	 * 
	 * @param program
	 *            The program to be transformed.
	 * @param code
	 *            The code of a transformer, should be one of the following:<br>
	 *            <ul>
	 *            <li>"general": general transformer</li>
	 *            <li>"io": IO transformer</li>
	 *            <li>"mpi": MPI-to-CIVL transformer</li>
	 *            <li>"_omp_": OpenMP pragma transformer</li>
	 *            <li>"omp": OpenMP-to-CIVL transformer</li>
	 *            <li>"pthread": Pthread-to-CIVL transformer</li>
	 *            </ul>
	 * @param inputVars
	 *            The list of variable names that appear in "-input" options
	 *            specified by users in CIVL's command line.
	 * @param astBuilder
	 *            The AST builder to be reused in the transformer to parse
	 *            tokens. For example, the OpenMP pragma transformer uses the
	 *            AST builder to parse expressions.
	 * @param debug
	 *            The flag to turn on/off debugging. Useful for printing more
	 *            information in debug mode.
	 * @throws SyntaxException
	 */
	public static void applyTransformer(Program program, String code,
			List<String> inputVars, ASTBuilder astBuilder,
			CIVLConfiguration config) throws SyntaxException {
		CIVLBaseTransformer transformer;
		ASTFactory astFactory = program.getAST().getASTFactory();

		switch (code) {
		case CIVLTransform.GENERAL:
			transformer = new GeneralTransformer(astFactory, inputVars, config);
			break;
		case CIVLTransform.IO:
			transformer = new IOTransformer(astFactory, inputVars, config);
			break;
		case CIVLTransform.MPI:
			transformer = new MPI2CIVLTransformer(astFactory, inputVars, config);
			break;
		case CIVLTransform.OMP_PRAGMA:
			transformer = new OmpPragmaTransformer(astFactory, inputVars,
					astBuilder, config);
			break;
		case CIVLTransform.OMP_SIMPLIFY:
			transformer = new OpenMPSimplifier(astFactory, config);
			break;
		case CIVLTransform.PTHREAD:
			transformer = new Pthread2CIVLTransformer(astFactory, config);
			break;
		case CIVLTransform.CIVL_PRAGMA:
			transformer = new CIVLPragmaTransformer(astFactory, astBuilder,
					config);
			break;
		default:
			// try applying the transformer from ABC, might fail.
			program.applyTransformer(code);
			return;
		}
		program.apply(transformer);
	}

	/**
	 * Prints the AST of a given program in the representation of CIVL-C code.
	 * 
	 * @param out
	 *            The print stream to be used.
	 * @param program
	 *            The program to be printed.
	 */
	public static void printProgram2CIVL(PrintStream out, Program program) {
		AST2CIVL toCIVL = new AST2CIVL();

		toCIVL.astToCIVL(out, program.getAST());
	}

	public static boolean hasFunctionCalls(AST ast, List<String> functions) {
		ASTNode root = ast.getRootNode();

		return checkFunctionCalls(root, functions);
	}

	private static boolean checkFunctionCalls(ASTNode node,
			List<String> functions) {
		int numChildren = node.numChildren();
		boolean result = false;

		for (int i = 0; i < numChildren; i++) {
			ASTNode child = node.child(i);

			if (child != null) {
				result = checkFunctionCalls(child, functions);
				if (result)
					return true;
			}
		}
		if (node instanceof FunctionCallNode) {
			FunctionCallNode functionCall = (FunctionCallNode) node;

			if (functionCall.getFunction().expressionKind() == ExpressionKind.IDENTIFIER_EXPRESSION) {
				IdentifierExpressionNode functionExpression = (IdentifierExpressionNode) functionCall
						.getFunction();
				String functionName = functionExpression.getIdentifier().name();

				if (functions.contains(functionName))
					return true;
			}
		}
		return false;
	}

	public static boolean hasCIVLPragma(AST ast) {
		ASTNode root = ast.getRootNode();

		return checkCIVLPragma(root);
	}

	private static boolean checkCIVLPragma(ASTNode node) {
		if (node.nodeKind() == NodeKind.PRAGMA) {
			PragmaNode pragma = (PragmaNode) node;

			if (pragma.getPragmaIdentifier().name().equals("CIVL"))
				return true;
		} else {
			for (ASTNode child : node.children()) {
				if (child != null) {
					boolean childResult = checkCIVLPragma(child);

					if (childResult)
						return true;
				}
			}
		}
		return false;
	}
}
