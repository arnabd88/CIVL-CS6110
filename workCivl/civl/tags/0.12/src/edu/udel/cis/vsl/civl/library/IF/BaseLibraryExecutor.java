package edu.udel.cis.vsl.civl.library.IF;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.log.IF.CIVLErrorLogger;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NTReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicCompleteArrayType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;

/**
 * This class provides the common data and operations of library executors.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public abstract class BaseLibraryExecutor extends Library implements
		LibraryExecutor {

	/* ************************** Protected Types ************************** */

	protected enum ConversionType {
		INT, DOUBLE, CHAR, STRING, POINTER, VOID
	};

	protected class Format {
		public ConversionType type;
		public StringBuffer string;

		public Format(StringBuffer content, ConversionType conversion) {
			this.string = content;
			this.type = conversion;
		}

		@Override
		public String toString() {
			return this.string.toString();
		}
	}

	/* ************************** Instance Fields ************************** */

	/**
	 * The evaluator for evaluating expressions.
	 */
	protected Evaluator evaluator;

	/**
	 * The model factory of the system.
	 */
	protected ModelFactory modelFactory;

	/**
	 * The primary executor of the system.
	 */
	protected Executor primaryExecutor;

	/**
	 * The state factory for state-related computation.
	 */
	protected StateFactory stateFactory;

	/**
	 * The static model of the program.
	 */
	protected Model model;

	// protected boolean statelessPrintf;

	protected CIVLErrorLogger errorLogger;

	protected CIVLConfiguration civlConfig;

	/**
	 * The set of characters that are used to construct a number in a format
	 * string.
	 */
	protected Set<Character> numbers;

	/* **************************** Constructors *************************** */

	/**
	 * Creates a new instance of a library executor.
	 * 
	 * @param primaryExecutor
	 *            The executor for normal CIVL execution.
	 * @param output
	 *            The output stream to be used in the enabler.
	 * @param enablePrintf
	 *            If printing is enabled for the printf function.
	 * @param modelFactory
	 *            The model factory of the system.
	 */
	public BaseLibraryExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			CIVLConfiguration civlConfig) {
		super(name, primaryExecutor.evaluator().universe(), symbolicUtil);
		this.primaryExecutor = primaryExecutor;
		this.evaluator = primaryExecutor.evaluator();
		this.stateFactory = evaluator.stateFactory();
		this.civlConfig = civlConfig;
		this.modelFactory = modelFactory;
		this.model = modelFactory.model();
		this.errorLogger = primaryExecutor.errorLogger();
		numbers = new HashSet<Character>(10);
		for (int i = 0; i < 10; i++) {
			numbers.add(Character.forDigit(i, 10));
		}
	}

	/* ************************* Protected Methods ************************* */

	protected State executeAssert(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source, CallOrSpawnStatement statement)
			throws UnsatisfiablePathConditionException {
		BooleanExpression assertValue = (BooleanExpression) argumentValues[0];
		Reasoner reasoner;
		ValidityResult valid;
		ResultType resultType;

		reasoner = universe.reasoner(state.getPathCondition());
		valid = reasoner.valid(assertValue);
		resultType = valid.getResultType();
		if (resultType != ResultType.YES) {
			if (arguments.length > 1) {
				if (civlConfig.enablePrintf()) {
					Expression[] pArguments = Arrays.copyOfRange(arguments, 1,
							arguments.length);
					SymbolicExpression[] pArgumentValues = Arrays.copyOfRange(
							argumentValues, 1, argumentValues.length);

					state = this.execute_printf(source, state, pid, process,
							null, pArguments, pArgumentValues);
				}
			}
			state = errorLogger.logError(source, state, process,
					symbolicUtil.stateToString(state), assertValue, resultType,
					ErrorKind.ASSERTION_VIOLATION,
					"Cannot prove assertion holds: " + statement.toString()
							+ "\n  Path condition: " + state.getPathCondition()
							+ "\n  Assertion: " + assertValue + "\n");
		}
		return state;
	}

	protected State execute_printf(CIVLSource source, State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		StringBuffer stringOfSymbolicExpression;
		StringBuffer formatBuffer;
		List<StringBuffer> printedContents = new ArrayList<>();
		Pair<State, StringBuffer> concreteString;
		List<Format> formats;
		List<Format> nonVoidFormats = new ArrayList<>();

		concreteString = this.getString(arguments[0].getSource(), state,
				process, argumentValues[0]);
		formatBuffer = concreteString.right;
		state = concreteString.left;
		formats = this.splitFormat(arguments[0].getSource(), formatBuffer);
		for (Format format : formats) {
			if (format.type != ConversionType.VOID)
				nonVoidFormats.add(format);
		}
		assert nonVoidFormats.size() == argumentValues.length - 1;
		for (int i = 1; i < argumentValues.length; i++) {
			SymbolicExpression argumentValue = argumentValues[i];
			CIVLType argumentType = arguments[i].getExpressionType();

			if (argumentType instanceof CIVLPointerType
					&& ((CIVLPointerType) argumentType).baseType().isCharType()
					&& argumentValue.operator() == SymbolicOperator.CONCRETE) {
				Format myFormat = nonVoidFormats.get(i - 1);

				if (myFormat.type == ConversionType.STRING) {
					concreteString = this.getString(arguments[i].getSource(),
							state, process, argumentValue);
					stringOfSymbolicExpression = concreteString.right;
					state = concreteString.left;
					printedContents.add(stringOfSymbolicExpression);
				} else if (myFormat.type == ConversionType.POINTER) {
					printedContents.add(new StringBuffer(symbolicUtil
							.symbolicExpressionToString(
									arguments[i].getSource(), state,
									argumentValue)));
				} else {
					throw new CIVLSyntaxException("Array pointer unaccepted",
							arguments[i].getSource());
				}

			} else
				printedContents.add(new StringBuffer(this.symbolicUtil
						.symbolicExpressionToString(arguments[i].getSource(),
								state, argumentValue)));
		}
		this.printf(civlConfig.out(), arguments[0].getSource(), formats,
				printedContents);
		return state;
	}

	/**
	 * Prints to the standard output stream.
	 * 
	 * @param source
	 *            The source code information of the format argument.
	 * @param formatBuffer
	 *            The format string buffer.
	 * @param arguments
	 *            The list of arguments to be printed according to the format.
	 */
	protected void printf(PrintStream printStream, CIVLSource source,
			List<Format> formats, List<StringBuffer> arguments) {
		if (this.civlConfig.enablePrintf()) {
			int argIndex = 0;

			for (Format format : formats) {
				String formatString = format.toString();

				switch (format.type) {
				case VOID:
					printStream.print(formatString);
					break;
				default:
					printStream.printf("%s", arguments.get(argIndex++));
				}
			}
		}
	}

	/**
	 * Parses the format string, according to C11 standards. For example,
	 * <code>"This is process %d.\n"</code> will be parsed into a list of
	 * strings: <code>"This is process "</code>, <code>"%d"</code>,
	 * <code>".\n"</code>.<br>
	 * 
	 * In Paragraph 4, Section 7.21.6.1, C11 Standards:<br>
	 * Each conversion specification is introduced by the character %. After the
	 * %, the following appear in sequence:
	 * <ul>
	 * <li>Zero or more flags (in any order) that modify the meaning of the
	 * conversion specification.</li>
	 * <li>An optional minimum field width. If the converted value has fewer
	 * characters than the field width, it is padded with spaces (by default) on
	 * the left (or right, if the left adjustment flag, described later, has
	 * been given) to the field width. The field width takes the form of an
	 * asterisk * (described later) or a nonnegative decimal integer.</li>
	 * <li>An optional precision that gives the minimum number of digits to
	 * appear for the d, i, o, u, x, and X conversions, the number of digits to
	 * appear after the decimal-point character for a, A, e, E, f, and F
	 * conversions, the maximum number of significant digits for the g and G
	 * conversions, or the maximum number of bytes to be written for s
	 * conversions. The precision takes the form of a period (.) followed either
	 * by an asterisk * (described later) or by an optional decimal integer; if
	 * only the period is specified, the precision is taken as zero. If a
	 * precision appears with any other conversion specifier, the behavior is
	 * undefined.</li>
	 * <li>An optional length modifier that specifies the size of the argument.</li>
	 * <li>A conversion specifier character that specifies the type of
	 * conversion to be applied.</li>
	 * </ul>
	 * 
	 * @param source
	 *            The source code element of the format argument.
	 * @param formatBuffer
	 *            The string buffer containing the content of the format string.
	 * @return A list of string buffers by splitting the format by conversion
	 *         specifiers.
	 */
	protected List<Format> splitFormat(CIVLSource source,
			StringBuffer formatBuffer) {
		int count = formatBuffer.length();
		List<Format> result = new ArrayList<>();
		StringBuffer stringBuffer = new StringBuffer();
		boolean inConversion = false;
		boolean hasFieldWidth = false;
		boolean hasPrecision = false;

		for (int i = 0; i < count; i++) {
			Character current = formatBuffer.charAt(i);
			Character code;
			ConversionType type = ConversionType.VOID;

			if (current.equals('%')) {
				code = formatBuffer.charAt(i + 1);

				if (code.equals('%')) {
					stringBuffer.append("%%");
					i = i + 1;
					continue;
				}
				if (stringBuffer.length() > 0) {
					if (stringBuffer.charAt(0) == '%'
							&& stringBuffer.charAt(1) != '%') {
						throw new CIVLSyntaxException("The format %"
								+ stringBuffer + " is not allowed in fprintf",
								source);
					}
					result.add(new Format(stringBuffer, type));
					stringBuffer = new StringBuffer();
				}
				inConversion = true;
				stringBuffer.append('%');
				current = formatBuffer.charAt(++i);
			}
			if (inConversion) {
				// field width
				if (current.equals('*')) {
					stringBuffer.append('*');
					current = formatBuffer.charAt(++i);
				} else if (numbers.contains(current)) {
					Character next = current;

					if (hasFieldWidth) {
						stringBuffer.append(next);
						throw new CIVLSyntaxException(
								"Duplicate field width in \"" + stringBuffer
										+ "\"...", source);
					}
					hasFieldWidth = true;
					while (numbers.contains(next)) {
						stringBuffer.append(next);
						next = formatBuffer.charAt(++i);
					}
					current = next;
				}
				// precision
				if (current.equals('.')) {
					Character next;

					next = formatBuffer.charAt(++i);
					stringBuffer.append('.');
					if (hasPrecision) {
						throw new CIVLSyntaxException(
								"Duplicate precision detected in \""
										+ stringBuffer + "\"...", source);
					}
					hasPrecision = true;
					if (next.equals('*')) {
						stringBuffer.append(next);
						next = formatBuffer.charAt(++i);
					} else {
						while (numbers.contains(next)) {
							stringBuffer.append(next);
							next = formatBuffer.charAt(++i);
						}
					}
					current = next;
				}
				// length modifier
				switch (current) {
				case 'h':
				case 'l':
					stringBuffer.append(current);
					if (i + 1 >= count)
						throw new CIVLSyntaxException("The format "
								+ stringBuffer + " is not allowed.", source);
					else {
						Character next = formatBuffer.charAt(i + 1);

						if (next.equals(current)) {
							i++;
							stringBuffer.append(next);
						}
						current = formatBuffer.charAt(++i);
					}
					break;
				case 'j':
				case 'z':
				case 't':
				case 'L':
					stringBuffer.append(current);
					current = formatBuffer.charAt(++i);
					break;
				default:
				}
				// conversion specifier
				switch (current) {
				case 'c':
				case 'p':
				case 'n':
					if (hasFieldWidth || hasPrecision) {
						throw new CIVLSyntaxException(
								"Invalid precision for the format \"%"
										+ current + "\"...", source);
					}
				default:
				}
				switch (current) {
				case 'c':
					type = ConversionType.CHAR;
					break;
				case 'p':
				case 'n':
					type = ConversionType.POINTER;
					break;
				case 'd':
				case 'i':
				case 'o':
				case 'u':
				case 'x':
				case 'X':
					type = ConversionType.INT;
					break;
				case 'a':
				case 'A':
				case 'e':
				case 'E':
				case 'f':
				case 'F':
				case 'g':
				case 'G':
					type = ConversionType.DOUBLE;
					break;
				case 's':
					type = ConversionType.STRING;
					break;
				default:
					stringBuffer.append(current);
					throw new CIVLSyntaxException("The format %" + stringBuffer
							+ " is not allowed in fprintf", source);
				}
				stringBuffer.append(current);
				result.add(new Format(stringBuffer, type));
				inConversion = false;
				hasFieldWidth = false;
				hasPrecision = false;
				stringBuffer = new StringBuffer();
			} else {
				stringBuffer.append(current);
			}
		}
		if (stringBuffer.length() > 0)
			result.add(new Format(stringBuffer, ConversionType.VOID));
		return result;
	}

	/**
	 * Executes the function call "$free(*void)": removes from the heap the
	 * object referred to by the given pointer.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param arguments
	 *            The static representation of the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The dynamic representation of the arguments of the function
	 *            call.
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected State executeFree(State state, int pid, String process,
			Expression[] arguments, SymbolicExpression[] argumentValues,
			CIVLSource source) throws UnsatisfiablePathConditionException {
		SymbolicExpression firstElementPointer = argumentValues[0];

		if (this.symbolicUtil.isNullPointer(firstElementPointer))
			// does nothing for null pointer.
			return state;
		else if (!this.symbolicUtil.isHeapPointer(firstElementPointer)
				|| !this.symbolicUtil.isHeapObjectPointer(source,
						firstElementPointer)) {
			CIVLExecutionException err = new CIVLExecutionException(
					ErrorKind.MEMORY_LEAK, Certainty.PROVEABLE, process,
					"The argument of free "
							+ symbolicUtil.symbolicExpressionToString(source,
									state, firstElementPointer)
							+ " is not a pointer returned by a memory "
							+ "management method",
					symbolicUtil.stateToString(state), source);

			this.errorLogger.reportError(err);
			throw new UnsatisfiablePathConditionException();
		} else {
			CIVLHeapType heapType = modelFactory.heapType();
			SymbolicExpression heapObjectPointer;
			Evaluation eval;
			int index;
			SymbolicExpression undef;

			heapObjectPointer = this.symbolicUtil
					.heapCellPointer(firstElementPointer);
			eval = evaluator.dereference(source, state, process,
					heapObjectPointer, false);
			state = eval.state;
			if (eval.value instanceof SymbolicConstant) {
				SymbolicConstant value = (SymbolicConstant) eval.value;

				if (value.name().getString().equals("UNDEFINED")) {
					CIVLExecutionException err = new CIVLExecutionException(
							ErrorKind.MEMORY_LEAK,
							Certainty.PROVEABLE,
							process,
							"Attempt to free a memory space that is already freed or never allocated ",
							symbolicUtil.stateToString(state), source);

					this.errorLogger.reportError(err);
					throw new UnsatisfiablePathConditionException();
				}
			}
			index = getMallocIndex(firstElementPointer);
			undef = heapType.getMalloc(index).getUndefinedObject();
			state = primaryExecutor.assign(source, state, process,
					heapObjectPointer, undef);
			return state;
		}
	}

	/**
	 * * Only three types (represented differently in CIVL) of the symbolic
	 * expression "charPointer" is acceptable:<br>
	 * A pointer to char <br>
	 * A pointer to an element of array of char. (e.g. char a[N][M]; a[x] or
	 * &a[x][0] are acceptable. Address of an element of array of char or
	 * pointer to an array of char are same as this situation.)<br>
	 * A complete char array
	 * 
	 * @param source
	 *            The CIVL source of the pointer to char expression
	 * @param state
	 *            The current state
	 * @param process
	 *            The identifier of the process
	 * @param charPointer
	 *            The pointer to char
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	protected Pair<State, StringBuffer> getString(CIVLSource source,
			State state, String process, SymbolicExpression charPointer)
			throws UnsatisfiablePathConditionException {
		if (charPointer.operator() == SymbolicOperator.CONCRETE) {
			SymbolicSequence<?> originalArray = null;
			int int_arrayIndex = -1;
			StringBuffer result = new StringBuffer();
			ReferenceExpression ref = null;
			Evaluation eval;

			if (charPointer.type() instanceof SymbolicCompleteArrayType) {
				originalArray = (SymbolicSequence<?>) charPointer.argument(0);
				int_arrayIndex = 0;
			} else {
				ref = symbolicUtil.getSymRef(charPointer);
				if (ref instanceof ArrayElementReference) {
					SymbolicExpression pointerCharArray = symbolicUtil
							.parentPointer(source, charPointer);
					SymbolicExpression charArray;

					eval = evaluator.dereference(source, state, process,
							pointerCharArray, false);
					state = eval.state;
					charArray = eval.value;
					try {
						originalArray = (SymbolicSequence<?>) charArray
								.argument(0);
					} catch (ClassCastException e) {
						throw new CIVLUnimplementedFeatureException(
								"non-concrete strings", source);
					}
					int_arrayIndex = symbolicUtil.extractInt(source,
							((ArrayElementReference) ref).getIndex());

				} else {
					eval = evaluator.dereference(source, state, process,
							charPointer, false);
					state = eval.state;
					// A single character is not acceptable.
					if (eval.value.arguments().length <= 1)
						throw new CIVLExecutionException(ErrorKind.OTHER,
								Certainty.PROVEABLE, process,
								"Try to obtain a string from a sequence of char has length"
										+ " less than or equal to one", source);
					else {
						originalArray = (SymbolicSequence<?>) eval.value
								.argument(0);
						int_arrayIndex = 0;
					}
				}
			}
			result = symbolicUtil.charArrayToString(source, originalArray,
					int_arrayIndex, false);
			return new Pair<>(state, result);
		} else
			throw new CIVLUnimplementedFeatureException("non-concrete strings",
					source);
	}

	/* ************************** Private Methods ************************** */

	/**
	 * Obtains the field ID in the heap type via a heap-object pointer.
	 * 
	 * @param pointer
	 *            The heap-object pointer.
	 * @return The field ID in the heap type of the heap-object that the given
	 *         pointer refers to.
	 */
	private int getMallocIndex(SymbolicExpression pointer) {
		// ref points to element 0 of an array:
		NTReferenceExpression ref = (NTReferenceExpression) symbolicUtil
				.getSymRef(pointer);
		// objectPointer points to array:
		NTReferenceExpression objectPointer = (NTReferenceExpression) ref
				.getParent();
		// fieldPointer points to the field:
		TupleComponentReference fieldPointer = (TupleComponentReference) objectPointer
				.getParent();
		int result = fieldPointer.getIndex().getInt();

		return result;
	}

}
