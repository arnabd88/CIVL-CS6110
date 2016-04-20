package edu.udel.cis.vsl.abc.analysis.entity;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.conversion.IF.Conversion;
import edu.udel.cis.vsl.abc.ast.conversion.IF.ConversionFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.ExpressionNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.FunctionCallNode;
import edu.udel.cis.vsl.abc.ast.node.IF.expression.StringLiteralNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.type.IF.TypeFactory;
import edu.udel.cis.vsl.abc.err.IF.ABCUnsupportedException;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * This class maintains the hard-coded information of analyzes the variable
 * parameters of some specific functions, like <code>scanf, fscanf</code>, whose
 * variable arguments should all be of pointer type.
 * 
 * @author Manchun Zheng
 *
 */
public class SpecialFunctionCallAnalyzer {
	// names of special functions handled in this class
	private final static String SCANF = "scanf";
	private final static String FSCANF = "fscanf";
	private final static String PRINTF = "printf";
	private final static String FPRINTF = "fprintf";
	private final static String ACCESS = "$access";
	private final static String MODIFIED = "$write";
	private final static String READ = "$read";

	private EntityAnalyzer entityAnalyzer;

	/** the type factory, for generating types. */
	@SuppressWarnings("unused")
	private TypeFactory typeFactory;

	/** the void pointer type (void *) */
	private ObjectType voidPointerType;

	/**
	 * The names of functions handled by this analyzer
	 */
	private final Set<String> specialFunctioinNames = new HashSet<>(
			Arrays.asList(SCANF, FSCANF));

	private final Set<String> memoryTypeFunctionNames = new HashSet<>(
			Arrays.asList(ACCESS, MODIFIED, READ));

	private ConversionFactory conversionFactory;

	/**
	 * Creates a new instance of special function call analyzer.
	 * 
	 * @param typeFactory
	 *            The type factory to be used.
	 */
	public SpecialFunctionCallAnalyzer(EntityAnalyzer entityAnalyzer,
			TypeFactory typeFactory, ConversionFactory conversionFactory) {
		this.typeFactory = typeFactory;
		this.conversionFactory = conversionFactory;
		this.voidPointerType = typeFactory.pointerType(typeFactory.voidType());
		this.entityAnalyzer = entityAnalyzer;
	}

	/**
	 * Is the given function handled in this analyzer?
	 * 
	 * @param function
	 *            Name of the function
	 * @return true iff the given function is in this analyzer
	 */
	boolean isSpecialFunction(String function) {
		return this.specialFunctioinNames.contains(function);
	}

	/**
	 * checks if a fprintf/printf call has sufficient arguments as requested by
	 * the format string. An syntax exception is thrown if arguments are
	 * insufficient, otherwise, true is returned.
	 * 
	 * @param call
	 * @param function
	 * @param arguments
	 * @return true if the function is not a printf/fprintf call or there are
	 *         sufficient arguments.
	 * @throws SyntaxException
	 *             if arguments are insufficient
	 */
	boolean hasSufficientArgumentsForPrintf(FunctionCallNode call,
			String function, SequenceNode<ExpressionNode> arguments)
			throws SyntaxException {
		boolean isPrintf = false;
		boolean isFprintf = false;
		int formatIndex = 0;
		int numArgsForPrint = arguments.numChildren() - 1;
		ExpressionNode formatString;

		if (function.equals(FPRINTF))
			isFprintf = true;
		else if (function.equals(PRINTF))
			isPrintf = true;
		if (!isPrintf && !isFprintf)
			return true;
		if (isFprintf) {
			formatIndex++;
			numArgsForPrint--;
		}
		formatString = arguments.getSequenceChild(formatIndex);
		if (formatString instanceof StringLiteralNode) {
			String format = ((StringLiteralNode) formatString)
					.getStringRepresentation();
			int numFormats;
			String realFormat = format.replaceAll("%%", "");
			String formatArgumentsString = "arguments";
			String printArgumentsString = "are";

			numFormats = realFormat.split("%", -1).length - 1;
			if (numFormats == 1)
				formatArgumentsString = "argument";
			if (numArgsForPrint == 1)
				printArgumentsString = "is";
			if (numFormats > numArgsForPrint)
				throw this.entityAnalyzer.error("insufficient arguments for "
						+ function + ": the format string " + format
						+ " is requring " + numFormats + " subsequent "
						+ formatArgumentsString + " while only "
						+ numArgsForPrint + " " + printArgumentsString
						+ " provided.", call);
		}
		return true;
	}

	/**
	 * Returns the type of a variable parameter of a certain index of the given
	 * function.
	 * <p>
	 * Precondition: the given function is a special function handled in this
	 * analyzer and the index-th parameter is a variable one.
	 * 
	 * @param function
	 *            Name of the function
	 * @param index
	 *            index of the parameter whose type is to be obtained
	 * @return
	 */
	ObjectType variableParameterType(String function, int index) {
		assert this.isSpecialFunction(function);
		switch (function) {
		case SCANF:
			return this.variableParameterTypeOfScanf(index);
		case FSCANF:// fscanf has one more fixed parameter than scanf
			return this.variableParameterTypeOfScanf(index - 1);
		default:
			throw new ABCUnsupportedException("The function " + function
					+ " isn't a special function that needs "
					+ "type checking of its variable parameters");
		}
	}

	void addConversionsForSpecialFunctions(String functionName,
			ExpressionNode argument) throws SyntaxException {
		if (memoryTypeFunctionNames.contains(functionName)) {
			this.addMemoryConversion(argument);
		}
	}

	private void addMemoryConversion(ExpressionNode node)
			throws SyntaxException {
		Type oldType = node.getConvertedType();
		Conversion conversion = conversionFactory.memoryConversion(oldType);

		node.addConversion(conversion);

	}

	/**
	 * Returns the type of the parameter of the given index for
	 * <code>scanf</code>. <code>scanf</code> is expecting any parameter with
	 * index greater than 0 to be of pointer type, i.e.:
	 * <code>scanf(char*, (void*)+);</code>
	 * 
	 * @param index
	 *            The index of the parameter
	 * @return the type of the parameter of the given index for scanf, which is
	 *         always void*.
	 */
	private ObjectType variableParameterTypeOfScanf(int index) {
		assert index > 0;
		return this.voidPointerType;
	}

}
