package edu.udel.cis.vsl.civl.library.stdio;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryExecutor;
import edu.udel.cis.vsl.civl.log.IF.CIVLExecutionException;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.Certainty;
import edu.udel.cis.vsl.civl.model.IF.CIVLException.ErrorKind;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.LHSExpression;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.Format;
import edu.udel.cis.vsl.civl.semantics.IF.Format.ConversionType;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.civl.util.IF.Triple;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicSequence;

/**
 * Executor for stdio function calls. Some methods may be used elsewhere so this
 * executor may be loaded even if the user program has not included stdio. (See
 * "Other Public Methods".)
 * 
 * The following system functions are defined here:
 * <ul>
 * <li><code>$filesystem $filesystem_create($scope)</code></li>
 * <li><code>CIVL_File_mode CIVL_File_stringToMode(char *)</code></li>
 * <li><code>void $filesystem_destroy($filesystem)</code></li>
 * <li>
 * <code>FILE * $fopen($filesystem, const char * restrict, CIVL_File_mode)</code>
 * </li>
 * <li><code>int fclose(FILE *)</code></li>
 * <li><code>int fflush(FILE *)</code></li>
 * <li><code>int fprintf(FILE * restrict, const char * restrict, ...)</code></li>
 * <li><code>int fscanf(FILE * restrict, const char * restrict, ...)</code></li>
 * <li><code>void $filesystem_copy_output($filesystem, $file *)</code></li>
 * </ul>
 * 
 * Occurrences of functions <code>printf</code> and <code>scanf</code> in the
 * original source will already have been replaced by calls to
 * <code>fprintf</code> and <code>fscanf</code>, respectively.
 * 
 * fscanf: $assume $testFileLength("foo") == n*m+k; must appear before any
 * opening of the file.
 * 
 * C transformer: civl pragma's
 * 
 * @author Stephen F. Siegel (siegel)
 * @author Ziqing Luo (ziqing)
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class LibstdioExecutor extends BaseLibraryExecutor implements
		LibraryExecutor {

	// the different file modes; see stdio.cvl:
	public final static int CIVL_FILE_MODE_R = 0;
	public final static int CIVL_FILE_MODE_W = 1;
	public final static int CIVL_FILE_MODE_WX = 2;
	public final static int CIVL_FILE_MODE_A = 3;
	public final static int CIVL_FILE_MODE_RB = 4;
	public final static int CIVL_FILE_MODE_WB = 5;
	public final static int CIVL_FILE_MODE_WBX = 6;
	public final static int CIVL_FILE_MODE_AB = 7;
	public final static int CIVL_FILE_MODE_RP = 8;
	public final static int CIVL_FILE_MODE_WP = 9;
	public final static int CIVL_FILE_MODE_WPX = 10;
	public final static int CIVL_FILE_MODE_AP = 11;
	public final static int CIVL_FILE_MODE_RPB = 12;
	public final static int CIVL_FILE_MODE_WPB = 13;
	public final static int CIVL_FILE_MODE_WPBX = 14;
	public final static int CIVL_FILE_MODE_APB = 15;

	// file name of stdout/stdin
	public final static String STDOUT = "CIVL_stdout";
	public final static String STDIN = "CIVL_stdin";
	public final static String STDERR = "CIVL_stderr";

	/**
	 * The base type of the pointer type $filesystem; a structure type with
	 * fields (0) scope, and (1) files.
	 */
	private CIVLStructOrUnionType filesystemStructType;

	/**
	 * The symbolic type corresponding to filesystemStructType.
	 */
	private SymbolicTupleType filesystemStructSymbolicType;

	/**
	 * The CIVL struct type $file, defined in stdio.
	 */
	private CIVLStructOrUnionType fileType;

	/**
	 * The symbolic type corresponding to fileType.
	 */
	private SymbolicTupleType fileSymbolicType;

	/**
	 * The CIVL type FILE, defined in stdio.
	 */
	private CIVLStructOrUnionType FILEtype;

	/**
	 * The symbolic type array-of-char (char[]).
	 */
	private SymbolicArrayType stringSymbolicType;

	/**
	 * Empty file contents: array of string of length 0.
	 */
	private SymbolicExpression emptyContents;

	/**
	 * Abstract function for the initial content of a file. Different files
	 * should have different initial content.
	 */
	private SymbolicConstant initialContentsFunction;

	private SymbolicConstant fileLengthFunction;

	/**
	 * Abstract function to convert an integer into a string with a format:
	 * <code>char* intToString(char* format, int data)</code>.
	 */
	private SymbolicConstant intToStringFunction;

	/**
	 * Abstract function to convert a double into a string with a format:
	 * <code>char* doubleToString(char* format, double data)</code>.
	 */
	private SymbolicConstant doubleToStringFunction;

	/**
	 * Abstract function to convert a character into a string with a format:
	 * <code>char* charToString(char* format, char data)</code>.
	 */
	private SymbolicConstant charToStringFunction;

	/**
	 * Abstract function to convert a string into a string with a format:
	 * <code>char* stringDataToString(char* format, char* data)</code>.
	 */
	private SymbolicConstant stringDataToStringFunction;

	/**
	 * Abstract function to convert a pointer into a string with a format:
	 * <code>char* pointerToString(char* format, char data)</code>.
	 */
	private SymbolicConstant pointerToStringFunction;

	/**
	 * Abstract function to convert a string into an integer according to a
	 * format: <code>int stringToInt(char* format, char* string)</code>.
	 */
	private SymbolicConstant stringToIntFunction;

	/**
	 * Abstract function to convert a string into a double according to a
	 * format: <code>double stringToDouble(char* format, char* string)</code>.
	 */
	private SymbolicConstant stringToDoubleFunction;

	/**
	 * Abstract function to convert a string into a character according to a
	 * format: <code>char stringToChar(char* format, char* string)</code>.
	 */
	private SymbolicConstant stringToCharFunction;

	/**
	 * Abstract function to convert a string into a data of string type
	 * according to a format:
	 * <code>char* stringToStringData(char* format, char* string)</code>.
	 */
	private SymbolicConstant stringToStringDataFunction;

	/**
	 * Abstract function to convert a string into a pointer according to a
	 * format: <code>void* stringToPointer(char* format, char* string)</code>.
	 */
	private SymbolicConstant stringToPointerFunction;

	private SymbolicExpression EOF;

	private LibstdioEvaluator libevaluator;

	/* **************************** Constructors *************************** */

	/**
	 * Create a new instance of library executor for "stdio.h".
	 * 
	 * @param primaryExecutor
	 *            The main executor of the system.
	 * @param output
	 *            The output stream for printing.
	 * @param enablePrintf
	 *            True iff print is enabled, reflecting command line options.
	 */
	public LibstdioExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryExecutorLoader libExecutorLoader,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, primaryExecutor, modelFactory, symbolicUtil,
				symbolicAnalyzer, civlConfig, libExecutorLoader,
				libEvaluatorLoader);
		SymbolicType stringArrayType;

		EOF = universe.canonic(universe.integer(-100));
		stringSymbolicType = (SymbolicArrayType) universe.canonic(universe
				.arrayType(universe.characterType()));
		stringArrayType = (SymbolicArrayType) universe.canonic(universe
				.arrayType(stringSymbolicType));
		emptyContents = universe.canonic(universe
				.emptyArray(stringSymbolicType));
		initialContentsFunction = (SymbolicConstant) universe.canonic(universe
				.symbolicConstant(universe.stringObject("contents"), universe
						.functionType(Arrays.asList(stringSymbolicType),
								stringArrayType)));
		fileLengthFunction = (SymbolicConstant) universe.canonic(universe
				.symbolicConstant(universe.stringObject("fileLength"), universe
						.functionType(Arrays.asList(stringSymbolicType),
								universe.integerType())));
		createStringToDataFunctions();
		createDataToStringFunctions();
		this.filesystemStructType = (CIVLStructOrUnionType) typeFactory
				.systemType(ModelConfiguration.FILE_SYSTEM_TYPE);
		if (filesystemStructType != null)
			this.filesystemStructSymbolicType = (SymbolicTupleType) this.filesystemStructType
					.getDynamicType(universe);
		this.fileType = (CIVLStructOrUnionType) typeFactory
				.systemType(ModelConfiguration.REAL_FILE_TYPE);
		if (fileType != null)
			this.fileSymbolicType = (SymbolicTupleType) this.fileType
					.getDynamicType(universe);
		this.FILEtype = (CIVLStructOrUnionType) typeFactory
				.systemType(ModelConfiguration.FILE_STREAM_TYPE);
		this.libevaluator = new LibstdioEvaluator(name, evaluator,
				modelFactory, symbolicUtil, symbolicAnalyzer, civlConfig,
				this.libEvaluatorLoader);
	}

	/* ************************** Private Methods ************************** */

	/**
	 * This is a helper function of the constructor. It initializes all the
	 * abstract functions to convert a data of a certain type into a string.
	 */
	private void createDataToStringFunctions() {
		intToStringFunction = (SymbolicConstant) universe.canonic(universe
				.symbolicConstant(universe.stringObject("intToString"),
						universe.functionType(
								Arrays.asList(stringSymbolicType,
										universe.integerType()),
								stringSymbolicType)));
		doubleToStringFunction = (SymbolicConstant) universe.canonic(universe
				.symbolicConstant(universe.stringObject("doubleToString"),
						universe.functionType(
								Arrays.asList(stringSymbolicType,
										universe.realType()),
								stringSymbolicType)));
		charToStringFunction = (SymbolicConstant) universe.canonic(universe
				.symbolicConstant(universe.stringObject("charToString"),
						universe.functionType(
								Arrays.asList(stringSymbolicType,
										universe.characterType()),
								stringSymbolicType)));
		stringDataToStringFunction = (SymbolicConstant) universe
				.canonic(universe.symbolicConstant(universe
						.stringObject("stringDataToString"), universe
						.functionType(Arrays.asList(stringSymbolicType,
								stringSymbolicType), stringSymbolicType)));
		pointerToStringFunction = (SymbolicConstant) universe.canonic(universe
				.symbolicConstant(universe.stringObject("pointerToString"),
						universe.functionType(
								Arrays.asList(stringSymbolicType,
										typeFactory.pointerSymbolicType()),
								stringSymbolicType)));
	}

	/**
	 * This is a helper function of the constructor. It initializes all the
	 * abstract functions to convert a string to a data of certain type.
	 */
	private void createStringToDataFunctions() {
		stringToIntFunction = (SymbolicConstant) universe.canonic(universe
				.symbolicConstant(universe.stringObject("stringToInt"),
						universe.functionType(Arrays.asList(stringSymbolicType,
								stringSymbolicType), universe.integerType())));
		stringToDoubleFunction = (SymbolicConstant) universe.canonic(universe
				.symbolicConstant(universe.stringObject("stringToDouble"),
						universe.functionType(Arrays.asList(stringSymbolicType,
								stringSymbolicType), universe.realType())));
		stringToCharFunction = (SymbolicConstant) universe
				.canonic(universe.symbolicConstant(universe
						.stringObject("stringToChar"), universe.functionType(
						Arrays.asList(stringSymbolicType, stringSymbolicType),
						universe.characterType())));
		stringToStringDataFunction = (SymbolicConstant) universe
				.canonic(universe.symbolicConstant(universe
						.stringObject("stringToStringData"), universe
						.functionType(Arrays.asList(stringSymbolicType,
								stringSymbolicType), stringSymbolicType)));
		stringToPointerFunction = (SymbolicConstant) universe.canonic(universe
				.symbolicConstant(universe.stringObject("stringToPointer"),
						universe.functionType(Arrays.asList(stringSymbolicType,
								stringSymbolicType), typeFactory
								.pointerSymbolicType())));
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Returns the symbolic expression representing the initial contents of a
	 * file named filename. This is the array of length 1 whose sole element is
	 * the expression "initialContents(filename)", which is the application of
	 * the abstract function initialContentsFunction to the filename.
	 * 
	 * @param filename
	 *            symbolic expression of string type (i.e., an array of char)
	 * @return symbolic expression representing initial contents of that file
	 */
	private SymbolicExpression initialContents(SymbolicExpression filename) {
		return universe.apply(initialContentsFunction, Arrays.asList(filename));
	}

	private SymbolicExpression fileLength(SymbolicExpression filename) {
		return universe.apply(this.fileLengthFunction, Arrays.asList(filename));
	}

	/**
	 * $filesystem CIVL_filesystem = $filesystem_create($here); Creates a new
	 * empty file system, returning a handle to it. <br>
	 * $filesystem s$filesystem_create($scope scope);
	 * 
	 * typedef struct CIVL_filesystem { $scope scope; $file files[]; } *
	 * $filesystem;
	 * 
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_filesystem_create(CIVLSource source, State state,
			int pid, String process, LHSExpression lhs,
			Expression[] expressions, SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression scope = argumentValues[0];
		LinkedList<SymbolicExpression> filesystemComponents = new LinkedList<>();
		LinkedList<SymbolicExpression> fileArrayComponents = new LinkedList<>();
		SymbolicExpression filesArray = universe.array(fileSymbolicType,
				fileArrayComponents);
		SymbolicExpression filesystem;

		filesystemComponents.add(scope);
		filesystemComponents.add(filesArray);
		filesystem = universe.tuple(filesystemStructSymbolicType,
				filesystemComponents);
		state = primaryExecutor.malloc(source, state, pid, process, lhs,
				expressions[0], scope, filesystemStructType, filesystem);
		return state;
	}

	/**
	 * <pre>
	 * FILE * $fopen($filesystem fs, const char * restrict filename,
	 *               const char * restrict mode);
	 * </pre>
	 * 
	 */
	private State execute_fopen(CIVLSource source, State state, int pid,
			String process, LHSExpression lhs, Expression[] expressions,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression filesystemPointer = argumentValues[0];
		Evaluation eval = evaluator.dereference(expressions[0].getSource(),
				state, process, expressions[0], filesystemPointer, false);
		CIVLSource modeSource = expressions[2].getSource();
		int mode = symbolicUtil.extractInt(modeSource,
				(NumericExpression) argumentValues[2]);
		SymbolicExpression fileSystemStructure;
		SymbolicExpression fileArray;
		SymbolicExpression filename;
		SymbolicSequence<?> fileSequence;
		int numFiles;
		int fileIndex;
		SymbolicExpression length;
		NumericExpression isInput, isOutput, isBinary, isWide = this.zero;
		SymbolicExpression contents;
		SymbolicExpression theFile;
		NumericExpression pos0 = zero, pos1 = zero;
		boolean isInputFile = false;
		int filesystemDyscopeId = symbolicUtil.getDyscopeId(
				expressions[0].getSource(), filesystemPointer);
		int filesystemVid = symbolicUtil.getVariableId(
				expressions[0].getSource(), filesystemPointer);
		ReferenceExpression fileSystemRef = symbolicUtil
				.getSymRef(filesystemPointer);
		// Pair<State, StringBuffer> fileNameStringPair;
		// String fileNameString;

		state = eval.state;
		fileSystemStructure = eval.value;
		fileArray = universe.tupleRead(fileSystemStructure, oneObject);
		eval = evaluator.getStringExpression(state, process,
				expressions[1].getSource(), argumentValues[1]);
		state = eval.state;
		filename = eval.value;

		// fileNameStringPair = this.evaluator.getString(
		// expressions[1].getSource(), state, process,
		// argumentValues[1]);
		// state = fileNameStringPair.left;
		// fileNameString = fileNameStringPair.right.toString();
		// does a file by that name already exist in the filesystem?
		// assume all are concrete.
		if (fileArray.operator() != SymbolicOperator.CONCRETE)
			throw new CIVLUnimplementedFeatureException(
					"non-concrete file system", expressions[0]);
		fileSequence = (SymbolicSequence<?>) fileArray.argument(0);
		numFiles = fileSequence.size();
		for (fileIndex = 0; fileIndex < numFiles; fileIndex++) {
			SymbolicExpression tmpFile = fileSequence.get(fileIndex);
			SymbolicExpression tmpFilename = universe.tupleRead(tmpFile,
					zeroObject);

			if (tmpFilename.equals(filename)) {
				theFile = tmpFile;
				break;
			}
		}
		if (fileIndex == numFiles) {
			// file not found: create it.
			switch (mode) {
			case CIVL_FILE_MODE_R:
				// assume file exists with unconstrained contents
				isInput = this.one;
				isInputFile = true;
				isOutput = this.zero;
				isBinary = zero;
				contents = initialContents(filename);
				pos0 = pos1 = zero;
				break;
			case CIVL_FILE_MODE_W:
			case CIVL_FILE_MODE_WX:
				// assume file does not yet exist
				isInput = zero;
				isOutput = one;
				isBinary = zero;
				contents = emptyContents;
				pos0 = pos1 = zero;
				break;
			case CIVL_FILE_MODE_A:
				// assume file exists
				isInput = one;
				isInputFile = true;
				isOutput = one;
				isBinary = zero;
				contents = initialContents(filename);
				pos0 = one;
				pos1 = zero;
				break;
			case CIVL_FILE_MODE_RP:
				// assume file exists
				isInput = one;
				isInputFile = true;
				isOutput = one;
				isBinary = zero;
				contents = initialContents(filename);
				pos0 = pos1 = zero;
				break;
			default:
				throw new CIVLUnimplementedFeatureException(
						"FILE mode " + mode, modeSource);
			}
			length = this.fileLength(filename);
			theFile = universe.tuple(fileSymbolicType, Arrays.asList(filename,
					contents, isOutput, isInput, isBinary, isWide, length));
			fileArray = universe.append(fileArray, theFile);
			fileSystemStructure = universe.tupleWrite(fileSystemStructure,
					oneObject, fileArray);
			if (isInputFile && modelFactory.model().hasFscanf()) {
				BooleanExpression positiveLength = universe.lessThan(zero,
						(NumericExpression) length);

				state = state.setPathCondition(universe.and(
						state.getPathCondition(), positiveLength));
			}
			state = primaryExecutor.assign(expressions[1].getSource(), state,
					process, filesystemPointer, fileSystemStructure);
		}
		// now theFile is the new file and fileIndex is its index
		// malloc a new FILE object with appropriate pointers
		// create a pointer to theFile (array element reference)
		//
		{
			List<SymbolicExpression> streamComponents = new LinkedList<>();
			ReferenceExpression ref = universe.arrayElementReference(
					universe.tupleComponentReference(fileSystemRef, oneObject),
					universe.integer(fileIndex));
			SymbolicExpression filePointer = symbolicUtil.makePointer(
					filesystemDyscopeId, filesystemVid, ref);
			SymbolicExpression fileStream;
			// SymbolicExpression scope = modelFactory.scopeValue(state
			// .getProcessState(pid).getDyscopeId());

			streamComponents.add(filePointer);
			streamComponents.add(filesystemPointer);
			streamComponents.add(pos0);
			streamComponents.add(pos1);
			streamComponents.add(argumentValues[2]);
			streamComponents.add(universe.integer(1));
			fileStream = universe.tuple(
					(SymbolicTupleType) FILEtype.getDynamicType(universe),
					streamComponents);
			// do malloc, get pointer, do the assignments.
			// state = primaryExecutor.assign(state, pid, lhs, fileStream);
			state = primaryExecutor.malloc(source, state, pid, process, lhs,
					expressions[0],
					modelFactory.scopeValue(filesystemDyscopeId), FILEtype,
					fileStream);

		}
		return state;
	}

	/**
	 * Execute a function call statement for a certain process at a given state.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The Id of the process that the call statement belongs to.
	 * @param statement
	 *            The call statement to be executed.
	 * @return The new state after executing the call statement.
	 * @throws UnsatisfiablePathConditionException
	 */
	private State executeWork(State state, int pid,
			CallOrSpawnStatement statement, String functionName)
			throws UnsatisfiablePathConditionException {
		Expression[] arguments;
		SymbolicExpression[] argumentValues;
		int numArgs;
		CIVLSource source = statement.getSource();
		LHSExpression lhs = statement.lhs();
		int processIdentifier = state.getProcessState(pid).identifier();
		String process = "p" + processIdentifier + " (id = " + pid + ")";

		numArgs = statement.arguments().size();
		arguments = new Expression[numArgs];
		argumentValues = new SymbolicExpression[numArgs];
		for (int i = 0; i < numArgs; i++) {
			Evaluation eval;

			arguments[i] = statement.arguments().get(i);
			eval = evaluator.evaluate(state, pid, arguments[i]);
			argumentValues[i] = eval.value;
			state = eval.state;
		}
		switch (functionName) {
		case "$fopen":
			state = execute_fopen(source, state, pid, process, lhs, arguments,
					argumentValues);
			break;
		case "$filesystem_create":
			state = execute_filesystem_create(source, state, pid, process, lhs,
					arguments, argumentValues);
			break;
		case "$filesystem_destroy":
			state = executeFree(state, pid, process, arguments, argumentValues,
					source);
			break;
		case "fclose":
			state = executeFree(state, pid, process, arguments, argumentValues,
					source);
			break;
		case "fprintf":
			state = execute_fprintf(source, state, pid, process, lhs,
					arguments, argumentValues);
			break;
		case "printf":
			if (civlConfig.enablePrintf())
				state = this.primaryExecutor.execute_printf(source, state, pid,
						process, lhs, arguments, argumentValues);
			break;
		case "fscanf":
			state = execute_fscanf(source, state, pid, process, lhs, arguments,
					argumentValues);
			break;
		case "fflush":
		case "_fflush":
			break;
		case "$filesystem_copy_output":
			state = execute_filesystem_copy_output(source, state, pid, process,
					arguments, argumentValues);
			break;
		case "$textFileLength":
			state = execute_text_file_length(source, state, pid, process, lhs,
					arguments, argumentValues);
			break;
		case "sprintf":
			state = this.execute_fprintf(source, state, pid, process, lhs,
					arguments, argumentValues);
			break;
		default:
			throw new CIVLUnimplementedFeatureException(functionName, statement);

		}
		state = stateFactory.setLocation(state, pid, statement.target(),
				statement.lhs() != null);
		return state;
	}

	private State execute_text_file_length(CIVLSource source, State state,
			int pid, String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		Expression fileSystemExpression = modelFactory
				.civlFilesystemVariableExpression();
		Evaluation eval = evaluator.evaluate(state, pid, fileSystemExpression);
		SymbolicExpression filesystemPointer;
		SymbolicExpression fileSystemStructure;
		SymbolicExpression fileArray;
		SymbolicSequence<?> fileSequence;
		SymbolicExpression filename;
		int numFiles;
		int fileIndex;
		SymbolicExpression theFile = null;
		SymbolicExpression length;

		filesystemPointer = eval.value;
		state = eval.state;
		eval = evaluator.dereference(fileSystemExpression.getSource(), state,
				process, fileSystemExpression, filesystemPointer, false);
		state = eval.state;
		fileSystemStructure = eval.value;
		fileArray = universe.tupleRead(fileSystemStructure, oneObject);
		eval = evaluator.getStringExpression(state, process,
				arguments[0].getSource(), argumentValues[0]);
		state = eval.state;
		filename = eval.value;

		// does a file by that name already exist in the filesystem?
		// assume all are concrete.
		if (fileArray.operator() != SymbolicOperator.CONCRETE)
			throw new CIVLUnimplementedFeatureException(
					"non-concrete file system", arguments[0]);
		fileSequence = (SymbolicSequence<?>) fileArray.argument(0);
		numFiles = fileSequence.size();
		for (fileIndex = 0; fileIndex < numFiles; fileIndex++) {
			SymbolicExpression tmpFile = fileSequence.get(fileIndex);
			SymbolicExpression tmpFilename = universe.tupleRead(tmpFile,
					zeroObject);

			if (tmpFilename.equals(filename)) {
				theFile = tmpFile;
				break;
			}
		}
		if (fileIndex == numFiles) {
			// file not found: create it.
			NumericExpression isInput = this.zero;
			NumericExpression isOutput = this.zero;
			NumericExpression isBinary = zero;
			SymbolicExpression contents = initialContents(filename);
			length = this.fileLength(filename);
			SymbolicExpression isWide = this.zero;

			theFile = universe.tuple(fileSymbolicType, Arrays.asList(filename,
					contents, isOutput, isInput, isBinary, isWide, length));
			fileArray = universe.append(fileArray, theFile);
			fileSystemStructure = universe.tupleWrite(fileSystemStructure,
					oneObject, fileArray);
			state = primaryExecutor.assign(fileSystemExpression.getSource(),
					state, process, filesystemPointer, fileSystemStructure);
		} else {
			SymbolicExpression isBinary = universe.tupleRead(theFile,
					universe.intObject(4));

			if (!isBinary.equals(this.zero)) {
				throw new CIVLExecutionException(ErrorKind.OTHER,
						Certainty.CONCRETE, process, "The file "
								+ arguments[0].toString()
								+ " is not a text file.", source);
			}
			length = universe.tupleRead(theFile, universe.intObject(6));
		}
		if (lhs != null)
			state = primaryExecutor.assign(state, pid, process, lhs, length);
		return state;
	}

	private State execute_filesystem_copy_output(CIVLSource source,
			State state, int pid, String process, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression civlFileSystemPointer = argumentValues[0];
		SymbolicExpression arrayPointer = argumentValues[1];
		SymbolicExpression fileArray;
		Evaluation eval;
		NumericExpression length;
		int length_int;
		SymbolicExpression scopeField = universe.tupleRead(arrayPointer,
				zeroObject), varField = universe.tupleRead(arrayPointer,
				oneObject);
		CIVLSource arraySource = arguments[1].getSource();
		List<SymbolicExpression> files;
		SymbolicExpression outputArray;

		eval = evaluator.dereference(arguments[0].getSource(), state, process,
				arguments[0], civlFileSystemPointer, false);
		state = eval.state;
		fileArray = universe.tupleRead(eval.value, oneObject);
		length = universe.length(fileArray);
		length_int = symbolicUtil.extractInt(arguments[0].getSource(), length);
		files = new ArrayList<>(length_int);
		for (int i = 0; i < length_int; i++) {
			NumericExpression fileArrayIndex = universe.integer(i);

			files.add(universe.arrayRead(fileArray, fileArrayIndex));
		}
		outputArray = universe.array(this.fileSymbolicType, files);
		arrayPointer = universe.tuple(
				typeFactory.pointerSymbolicType(),
				Arrays.asList(scopeField, varField,
						universe.identityReference()));
		state = primaryExecutor.assign(arraySource, state, process,
				arrayPointer, outputArray);
		return state;
	}

	/**
	 * Execute the function call for fprintf
	 * <code>int fprintf(FILE * restrict stream,
	 * const char * restrict format, ...)</code>.
	 * 
	 * @param source
	 *            The source code element of the function call.
	 * @param state
	 *            The state where the function call happens.
	 * @param pid
	 *            The ID of the process that this function call belongs to.
	 * @param lhs
	 *            The left hand side of the function call.
	 * @param arguments
	 *            The list of CIVL expressions for the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The list of symbolic expressions representing the value of the
	 *            arguments of the function call.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_fscanf(CIVLSource source, State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression fileStream;
		SymbolicExpression filePointer;
		NumericExpression fileLength;
		Evaluation eval;
		SymbolicExpression fileObject;
		StringBuffer formatBuffer;
		Triple<State, StringBuffer, Boolean> formatString;
		NumericExpression position;
		Reasoner reasoner;

		// TODO: position is never cleared if another process open and read the
		// file.
		eval = evaluator.dereference(arguments[0].getSource(), state, process,
				arguments[0], argumentValues[0], false);
		fileStream = eval.value;
		state = eval.state;
		filePointer = universe.tupleRead(fileStream, zeroObject);
		position = (NumericExpression) universe
				.tupleRead(fileStream, twoObject);
		eval = evaluator.dereference(arguments[0].getSource(), state, process,
				null, filePointer, false);
		state = eval.state;
		fileObject = eval.value;
		{// checks file length
			BooleanExpression positionExceedFileLength;
			ResultType positionExceedFileLengthValid;

			fileLength = (NumericExpression) universe.tupleRead(fileObject,
					universe.intObject(6));
			positionExceedFileLength = universe.lessThanEquals(fileLength,
					position);
			reasoner = universe.reasoner(state.getPathCondition());
			positionExceedFileLengthValid = reasoner.valid(
					positionExceedFileLength).getResultType();

			if (positionExceedFileLengthValid == ResultType.YES) {
				if (lhs != null) {
					state = primaryExecutor.assign(state, pid, process, lhs,
							this.EOF);
				}
				return state;
			}
		}
		formatString = this.evaluator.getString(arguments[1].getSource(),
				state, process, arguments[1], argumentValues[1]);
		formatBuffer = formatString.second;
		state = formatString.first;
		{ // reads the file
			SymbolicExpression fileContents = universe.tupleRead(fileObject,
					oneObject);
			List<Format> formats = this.primaryExecutor.splitFormat(
					arguments[1].getSource(), formatBuffer);
			int numOfFormats = formats.size();
			// index of arguments of the fscanf() function
			int dataPointerIndex = 2;
			// number of arguments already assigned
			int count = 0;
			// number of data units read from file
			int dataLength = 1;

			for (int i = 0; i < numOfFormats; i++) {
				Format currentFormat = formats.get(i);
				String formatValue = currentFormat.string.toString();
				SymbolicExpression currentString = universe.arrayRead(
						fileContents, position);
				SymbolicExpression format, data;
				ConversionType conversion = currentFormat.type;
				SymbolicConstant conversionFunction = null;

				format = universe.stringExpression(formatValue);
				switch (conversion) {
				case INT:
					conversionFunction = this.stringToIntFunction;
					break;
				case DOUBLE:
					conversionFunction = this.stringToDoubleFunction;
					break;
				case POINTER:
					conversionFunction = this.stringToPointerFunction;
					break;
				case CHAR:
					conversionFunction = this.stringToCharFunction;
					break;
				case STRING:
					conversionFunction = this.stringToStringDataFunction;
					break;
				default:
				}
				if (conversionFunction != null) {
					SymbolicExpression assignedOutputArgPtr, origOutputArgPtr;
					Expression origOutputArgPtrExpr;

					// TODO: Improvement: Width specified by format is max width
					// which means the real width can be less than the given
					// width. But for symbolic execution here, we only care
					// about max width currently.
					data = universe.apply(conversionFunction,
							Arrays.asList(format, currentString));
					assignedOutputArgPtr = origOutputArgPtr = argumentValues[dataPointerIndex];
					origOutputArgPtrExpr = arguments[dataPointerIndex];
					// Only character array(or string) will make assigned
					// pointer different.
					// TODO: what about %[ ?
					if (conversion == ConversionType.CHAR
							|| conversion == ConversionType.STRING) {
						dataLength = this.getCharsLengthFromFormat(state,
								process, formatValue, conversion,
								arguments[1].getSource());
						if (dataLength > 1) {
							BooleanExpression positionExceedFileLength;
							NumericExpression charsLengthNumExpr = universe
									.integer(dataLength);
							SymbolicConstant charsToStringFunction;
							Pair<Evaluation, SymbolicExpression> eval_and_assignedPtr;

							// As long as charsLength > 1, data will be
							// represented with charsToStringFunction which has
							// an array of char type.
							charsToStringFunction = libevaluator
									.charsToString(charsLengthNumExpr);
							data = universe.apply(charsToStringFunction,
									Arrays.asList(format, currentString));
							// Special case: Checking if "position + dataLength"
							// exceeds "file length" or just reaches the end of
							// the file.
							positionExceedFileLength = universe.lessThanEquals(
									fileLength,
									universe.add(position,
											universe.integer(dataLength)));
							if (reasoner.isValid(positionExceedFileLength)) {
								// If exceeds file length, assigning the current
								// argument then directly return (break) TODO:
								// do we need report this error ?
								NumericExpression nowPosition = universe.add(
										position, universe.integer(dataLength));
								NumericExpression exceedLength = universe
										.subtract(nowPosition, fileLength);
								NumericExpression realDataLength = universe
										.subtract(charsLengthNumExpr,
												exceedLength);

								count++;
								data = symbolicAnalyzer.getSubArray(data, zero,
										realDataLength, state, process, source);
								libevaluator.setOutputArgument(state, process,
										data, origOutputArgPtrExpr,
										origOutputArgPtr, realDataLength,
										source);
								state = primaryExecutor.assign(source, state,
										process, assignedOutputArgPtr, data);
								position = fileLength;
								break;
							} else {
								eval_and_assignedPtr = libevaluator
										.setOutputArgument(state, process,
												data, origOutputArgPtrExpr,
												origOutputArgPtr,
												charsLengthNumExpr, source);
								eval = eval_and_assignedPtr.left;
								state = eval.state;
								data = eval.value;
								assignedOutputArgPtr = eval_and_assignedPtr.right;
							}
						}
					}
					state = primaryExecutor.assign(source, state, process,
							assignedOutputArgPtr, data);
					count++;
					dataPointerIndex++;
				}
				position = universe.add(position, universe.integer(dataLength));
			}
			fileObject = universe.tupleWrite(fileObject, oneObject,
					fileContents);
			state = primaryExecutor.assign(source, state, process, filePointer,
					fileObject);
			fileStream = universe.tupleWrite(fileStream, twoObject, position);
			state = primaryExecutor.assign(source, state, process,
					argumentValues[0], fileStream);
			if (lhs != null) {
				SymbolicExpression countValue = universe.integer(count);

				state = primaryExecutor.assign(state, pid, process, lhs,
						countValue);
			}
		}
		return state;
	}

	/**
	 * Execute the function call for fprintf
	 * <code>int fprintf(FILE * restrict stream,
	 * const char * restrict format, ...)</code>.
	 * 
	 * @param source
	 *            The source code element of the function call.
	 * @param state
	 *            The state where the function call happens.
	 * @param pid
	 *            The ID of the process that this function call belongs to.
	 * @param lhs
	 *            The left hand side of the function call.
	 * @param arguments
	 *            The list of CIVL expressions for the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The list of symbolic expressions representing the value of the
	 *            arguments of the function call.
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private State execute_fprintf(CIVLSource source, State state, int pid,
			String process, LHSExpression lhs, Expression[] arguments,
			SymbolicExpression[] argumentValues)
			throws UnsatisfiablePathConditionException {
		SymbolicExpression fileStream;
		SymbolicExpression filePointer;
		Evaluation eval;
		SymbolicExpression fileObject;
		SymbolicExpression fileName;
		Triple<State, StringBuffer, Boolean> stringResult;
		String fileNameString;
		StringBuffer stringOfSymbolicExpression;
		StringBuffer formatBuffer;
		List<StringBuffer> printedContents = new ArrayList<>();
		List<Integer> sIndexes = new LinkedList<>();
		int sCount = 2;
		Triple<State, StringBuffer, Boolean> concreteString;
		List<Format> formats;

		eval = evaluator.dereference(arguments[0].getSource(), state, process,
				arguments[0], argumentValues[0], false);
		fileStream = eval.value;
		state = eval.state;
		filePointer = universe.tupleRead(fileStream, zeroObject);
		eval = evaluator.dereference(arguments[0].getSource(), state, process,
				null, filePointer, false);
		fileObject = eval.value;
		state = eval.state;
		fileName = universe.tupleRead(fileObject, zeroObject);
		stringResult = this.evaluator.getString(source, state, process, null,
				fileName);
		state = stringResult.first;
		fileNameString = stringResult.second.toString();
		concreteString = this.evaluator.getString(arguments[1].getSource(),
				state, process, arguments[1], argumentValues[1]);
		formatBuffer = concreteString.second;
		state = concreteString.first;
		formats = this.primaryExecutor.splitFormat(arguments[1].getSource(),
				formatBuffer);
		for (Format format : formats) {
			if (format.type == ConversionType.STRING)
				sIndexes.add(sCount++);
			else if (format.type != ConversionType.VOID)
				sCount++;
		}
		for (int i = 2; i < argumentValues.length; i++) {
			SymbolicExpression argumentValue = argumentValues[i];
			CIVLType argumentType = arguments[i].getExpressionType();

			if (argumentType instanceof CIVLPointerType
					&& ((CIVLPointerType) argumentType).baseType().isCharType()
					&& argumentValue.operator() == SymbolicOperator.CONCRETE) {
				// also check format code is %s before doing this
				if (!sIndexes.contains(i)) {
					throw new CIVLSyntaxException("Array pointer unaccepted",
							arguments[i].getSource());
				}
				concreteString = this.evaluator.getString(
						arguments[i].getSource(), state, process, arguments[i],
						argumentValue);
				stringOfSymbolicExpression = concreteString.second;
				state = concreteString.first;
				printedContents.add(stringOfSymbolicExpression);
			} else
				printedContents.add(new StringBuffer(this.symbolicAnalyzer
						.symbolicExpressionToString(arguments[i].getSource(),
								state, argumentValue)));
		}
		if (fileNameString.compareTo(STDOUT) == 0) {
			if (civlConfig.enablePrintf())
				this.primaryExecutor.printf(civlConfig.out(),
						arguments[1].getSource(), formats, printedContents);
			if (civlConfig.statelessPrintf())
				return state;
		} else if (fileNameString.compareTo(STDIN) == 0) {
			// TODO: stdin
		} else if (fileNameString.equals(STDERR)) {
			if (civlConfig.enablePrintf())
				this.primaryExecutor.printf(civlConfig.err(),
						arguments[1].getSource(), formats, printedContents);
		}
		{ // updates the file
			SymbolicExpression fileContents = universe.tupleRead(fileObject,
					oneObject);

			int newContentCount = formats.size();
			int dataIndex = 2;

			for (int i = 0; i < newContentCount; i++) {
				Format currentFormat = formats.get(i);
				SymbolicExpression newStringExpression = null;
				ConversionType conversion = currentFormat.type;
				String formatString = currentFormat.string.toString();
				SymbolicConstant conversionFunction = null;

				switch (conversion) {
				case INT:
					conversionFunction = this.intToStringFunction;
					break;
				case DOUBLE:
					conversionFunction = this.doubleToStringFunction;
					break;
				case CHAR:
					conversionFunction = this.charToStringFunction;
					break;
				case STRING:
					conversionFunction = this.stringDataToStringFunction;
					break;
				case POINTER:
					conversionFunction = this.pointerToStringFunction;
					break;
				default:// VOID
					newStringExpression = universe
							.stringExpression(formatString
									.replaceAll("%%", "%"));
				}
				if (conversionFunction != null)
					newStringExpression = universe.apply(conversionFunction,
							Arrays.asList(
									universe.stringExpression(formatString),
									argumentValues[dataIndex++]));
				fileContents = universe.append(fileContents,
						newStringExpression);
			}
			fileObject = universe.tupleWrite(fileObject, oneObject,
					fileContents);
			state = primaryExecutor.assign(source, state, process, filePointer,
					fileObject);
		}
		return state;
	}

	/**
	 * Analysis a given format which should be guaranteed to matching a string
	 * or an array of characters. Returns the number of characters of the
	 * matched argument (string or array of char) specified by the format.
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The information of the process
	 * @param formatValue
	 *            The value of the format (must be concrete string literal)
	 * @param conversion
	 *            The type of the conversion of the format value.
	 * @param source
	 *            The CIVL source of the statement.
	 * @return The number of characters should be in the matching string or char
	 *         array.
	 */
	// "%s" will include an extra termination sign while "%c" excludes it.
	private Integer getCharsLengthFromFormat(State state, String process,
			String formatValue, ConversionType conversion, CIVLSource source) {
		assert (conversion != ConversionType.STRING || conversion != ConversionType.CHAR) : "Cannot return characters when the format isn't expecting a string or char";
		// TODO: what about "%[" ?
		Pattern charOrStrPattern; // regex used to matching "%c" and "%s"
		Matcher matcher;
		String lengthStr;
		int length; // width is always concrete becasue it's from a string
					// literal.

		// TODO: suppression assignment * and length modifier is not supported
		// yet.
		charOrStrPattern = Pattern.compile("%[0-9]+");
		matcher = charOrStrPattern.matcher(formatValue);
		if (matcher.find()) {
			lengthStr = matcher.group();
			lengthStr = lengthStr.substring(1); // get rid of the "%"
			try {
				length = Integer.parseInt(lengthStr);
			} catch (NumberFormatException e) {
				throw new CIVLUnimplementedFeatureException("Format :"
						+ formatValue
						+ " is not supported yet or it's not a valid format.");
			}
		} else
			length = 1;
		// If conversion type is STRING, width add one.
		if (conversion == ConversionType.STRING)
			length++;
		if (length <= 0) {
			errorLogger.reportError(new CIVLExecutionException(ErrorKind.OTHER,
					Certainty.CONCRETE, process, "Invalid format", source));
			return 0;
		} else if (length == 1)
			return 1;
		else
			return length;
	}

	/* ******************** Methods from LibraryExecutor ******************* */

	@Override
	public State execute(State state, int pid, CallOrSpawnStatement statement,
			String functionName) throws UnsatisfiablePathConditionException {
		return executeWork(state, pid, (CallOrSpawnStatement) statement,
				functionName);
	}
}
