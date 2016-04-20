package edu.udel.cis.vsl.civl.transform.IF;

import java.util.List;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode.ExpressionKind;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.IdentifierExpressionNode;
import edu.udel.cis.vsl.abc.front.IF.ASTBuilder;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.transform.IF.Transformer;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;

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
public class TransformerFactory {

	private ASTFactory astFactory;

	private Transformer generalTransformer;

	private Transformer macroTransformer;

	private Transformer ioTransformer;

	private Transformer openMPSimplifier;

	private Transformer mpi2CivlTransformer;

	private Transformer openMP2CivlTransformer;

	private Transformer openMPOrphanTransformer;

	private Transformer pthread2CivlTransformer;

	private Transformer cuda2CivlTransformer;

	private Transformer svcompUnPPTransformer;

	private Transformer svcompTransformer;

	public TransformerFactory(ASTFactory astFactory) {
		this.astFactory = astFactory;
	}

	public Transformer getGeneralTransformer(CIVLConfiguration config) {
		if (generalTransformer == null)
			generalTransformer = new GeneralTransformer(astFactory, config);
		return generalTransformer;
	}

	public Transformer getMacroTransformer() {
		if (macroTransformer == null)
			macroTransformer = new MacroTransformer(astFactory);
		return macroTransformer;
	}

	public Transformer getIOTransformer() {
		if (ioTransformer == null)
			ioTransformer = new IOTransformer(astFactory);
		return ioTransformer;
	}

	public Transformer getOpenMPSimplifier() {
		if (openMPSimplifier == null)
			openMPSimplifier = new OpenMPSimplifier(astFactory);
		return openMPSimplifier;
	}

	public Transformer getMPI2CIVLTransformer() {
		if (mpi2CivlTransformer == null)
			mpi2CivlTransformer = new MPI2CIVLTransformer(astFactory);
		return mpi2CivlTransformer;
	}

	public Transformer getOpenMP2CIVLTransformer(CIVLConfiguration config) {
		if (openMP2CivlTransformer == null)
			openMP2CivlTransformer = new OpenMP2CIVLTransformer(astFactory,
					config);
		return openMP2CivlTransformer;
	}

	public Transformer getOpenMPOrphanTransformer() {
		if (openMPOrphanTransformer == null)
			openMPOrphanTransformer = new OpenMPOrphanTransformer(astFactory);
		return openMPOrphanTransformer;
	}

	public Transformer getPthread2CIVLTransformer() {
		if (pthread2CivlTransformer == null)
			pthread2CivlTransformer = new Pthread2CIVLTransformer(astFactory);
		return pthread2CivlTransformer;
	}

	public Transformer getCuda2CIVLTransformer() {
		if (cuda2CivlTransformer == null)
			cuda2CivlTransformer = new Cuda2CIVLTransformer(astFactory);
		return cuda2CivlTransformer;
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

	public Transformer getSvcompUnPPTransformer() {
		if (svcompUnPPTransformer == null)
			svcompUnPPTransformer = new SvcompUnPPTransformer(astFactory);
		return svcompUnPPTransformer;
	}

	public Transformer getSvcompTransformer() {
		if (svcompTransformer == null)
			svcompTransformer = new SvcompTransformer(astFactory);
		return svcompTransformer;
	}
}
