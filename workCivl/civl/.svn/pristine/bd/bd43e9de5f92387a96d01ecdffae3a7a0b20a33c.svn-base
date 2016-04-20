package edu.udel.cis.vsl.civl.transform.IF;

import java.util.List;

import edu.udel.cis.vsl.abc.antlr2ast.IF.ASTBuilder;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.transform.IF.Transform;
import edu.udel.cis.vsl.abc.transform.IF.TransformRecord;
import edu.udel.cis.vsl.abc.transform.IF.Transformer;
import edu.udel.cis.vsl.civl.transform.common.GeneralTransformer;
import edu.udel.cis.vsl.civl.transform.common.IOTransformer;
import edu.udel.cis.vsl.civl.transform.common.MPI2CIVLTransformer;
import edu.udel.cis.vsl.civl.transform.common.MacroTransformer;
import edu.udel.cis.vsl.civl.transform.common.OpenMP2CIVLTransformer;
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
	public final static String MACRO = MacroTransformer.CODE;
	public final static String IO = IOTransformer.CODE;
	public final static String OMP_SIMPLIFY = OpenMPSimplifier.CODE;
	public final static String MPI = MPI2CIVLTransformer.CODE;
	public final static String OPENMP = OpenMP2CIVLTransformer.CODE;
	public final static String PTHREAD = Pthread2CIVLTransformer.CODE;

	/**
	 * Registers EACH CIVL transformer to ABC Transform interface, so that
	 * <code>program.applyTransformer(code)</code> will work for.
	 */
	static {
		Transform.addTransform(new TransformRecord(GeneralTransformer.CODE,
				GeneralTransformer.LONG_NAME,
				GeneralTransformer.SHORT_DESCRIPTION) {
			@Override
			public Transformer create(ASTFactory astFactory) {
				return new GeneralTransformer(astFactory);
			}
		});

		Transform
				.addTransform(new TransformRecord(MacroTransformer.CODE,
						MacroTransformer.LONG_NAME,
						MacroTransformer.SHORT_DESCRIPTION) {
					@Override
					public Transformer create(ASTFactory astFactory) {
						return new MacroTransformer(astFactory);
					}
				});

		Transform.addTransform(new TransformRecord(IOTransformer.CODE,
				IOTransformer.LONG_NAME, IOTransformer.SHORT_DESCRIPTION) {
			@Override
			public Transformer create(ASTFactory astFactory) {
				return new IOTransformer(astFactory);
			}
		});

		Transform
				.addTransform(new TransformRecord(OpenMPSimplifier.CODE,
						OpenMPSimplifier.LONG_NAME,
						OpenMPSimplifier.SHORT_DESCRIPTION) {
					@Override
					public Transformer create(ASTFactory astFactory) {
						return new OpenMPSimplifier(astFactory);
					}
				});

		Transform.addTransform(new TransformRecord(OpenMP2CIVLTransformer.CODE,
				OpenMP2CIVLTransformer.LONG_NAME,
				OpenMP2CIVLTransformer.SHORT_DESCRIPTION) {
			@Override
			public Transformer create(ASTFactory astFactory) {
				return new OpenMP2CIVLTransformer(astFactory);
			}
		});

		Transform.addTransform(new TransformRecord(MPI2CIVLTransformer.CODE,
				MPI2CIVLTransformer.LONG_NAME,
				MPI2CIVLTransformer.SHORT_DESCRIPTION) {
			@Override
			public Transformer create(ASTFactory astFactory) {
				return new MPI2CIVLTransformer(astFactory);
			}
		});

		Transform.addTransform(new TransformRecord(
				Pthread2CIVLTransformer.CODE,
				Pthread2CIVLTransformer.LONG_NAME,
				Pthread2CIVLTransformer.SHORT_DESCRIPTION) {
			@Override
			public Transformer create(ASTFactory astFactory) {
				return new Pthread2CIVLTransformer(astFactory);
			}
		});
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
}
