package edu.udel.cis.vsl.civl.run.IF;

import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.bar;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.macroO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showProverQueriesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.showQueriesO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.sysIncludePathO;
import static edu.udel.cis.vsl.civl.config.IF.CIVLConstants.userIncludePathO;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.abc.FrontEnd;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode.NodeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.config.IF.Configuration.Language;
import edu.udel.cis.vsl.abc.parse.IF.ParseException;
import edu.udel.cis.vsl.abc.parse.IF.ParseTree;
import edu.udel.cis.vsl.abc.preproc.IF.Preprocessor;
import edu.udel.cis.vsl.abc.preproc.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.token.IF.CTokenSource;
import edu.udel.cis.vsl.abc.token.IF.Macro;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelBuilder;
import edu.udel.cis.vsl.civl.model.IF.Models;
import edu.udel.cis.vsl.civl.transform.IF.TransformerFactory;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;

public class ModelTranslator {

	private static final String CIVL_MACRO = "_CIVL";

	private final static File[] emptyFileArray = new File[0];

	private final static File[] civlSysPathArray = new File[] { CIVLConstants.CIVL_INCLUDE_PATH };

	GMCConfiguration cmdConfig;// = commandLine.configuration();
	CIVLConfiguration config;// = new CIVLConfiguration(cmdConfig);
	String[] filenames;// = commandLine.files();
	Preprocessor preprocessor;// = this.frontEnd.getPreprocessor();
	private File[] systemIncludes;// = this.getSysIncludes(cmdConfig),
	private File[] userIncludes;// = this.getUserIncludes(cmdConfig);
	private Map<String, Macro> macroMaps;// = getMacroMaps(preprocessor,
											// cmdConfig);
	private FrontEnd frontEnd;
	private PrintStream err = System.err;
	private PrintStream out = System.out;
	String userFileName;
	private TransformerFactory transformerFactory;
	SymbolicUniverse universe;
	String userFileCoreName;
	File userFile;

	ModelTranslator(TransformerFactory transformerFactory, FrontEnd frontEnd,
			GMCConfiguration cmdConfig, String[] filenames, String coreName,
			File coreFile) {
		this(transformerFactory, frontEnd, frontEnd.getPreprocessor(),
				cmdConfig, filenames, coreName, coreFile, SARL
						.newStandardUniverse());
	}

	ModelTranslator(TransformerFactory transformerFactory, FrontEnd frontEnd,
			Preprocessor preprocessor, GMCConfiguration cmdConfig,
			String[] filenames, String coreName, File coreFile,
			SymbolicUniverse universe) {
		this.transformerFactory = transformerFactory;
		this.cmdConfig = cmdConfig;
		this.userFileCoreName = coreName;
		this.universe = universe;
		if (cmdConfig.isTrue(showProverQueriesO))
			universe.setShowProverQueries(true);
		if (cmdConfig.isTrue(showQueriesO))
			universe.setShowQueries(true);
		config = new CIVLConfiguration(cmdConfig);
		this.filenames = filenames;
		userFileName = filenames[0];
		this.userFile = coreFile;
		this.frontEnd = frontEnd;
		this.preprocessor = preprocessor;
		systemIncludes = this.getSysIncludes(cmdConfig);
		userIncludes = this.getUserIncludes(cmdConfig);
		macroMaps = getMacroMaps(preprocessor, cmdConfig);
	}

	Program buildProgram() throws PreprocessorException {
		CTokenSource[] tokenSources;
		List<AST> asts = null;
		Program program = null;
		long startTime, endTime;
		long totalTime;

		startTime = System.currentTimeMillis();
		tokenSources = this.preprocess();
		endTime = System.currentTimeMillis();
		if (config.showTime()) {
			totalTime = (endTime - startTime);// / 1000;
			out.println(totalTime
					+ "ms:\tSUMARRY ANTLR preprocessor parsing to form preproc tree for "
					+ tokenSources.length + " translation units");
		}
		if (tokenSources != null) {
			// startTime = System.currentTimeMillis();
			asts = this.parseTokens(tokenSources);
			// endTime = System.currentTimeMillis();
			// if (config.showTime()) {
			// totalTime = (endTime - startTime) / 1000;
			// out.println(totalTime + "s:\tSUMARRY parsing "
			// + tokenSources.length + " preproc trees into ASTs");
			// }
		}
		if (asts != null) {
			program = this.link(asts);
		}
		if (program != null) {
			startTime = System.currentTimeMillis();
			if (!this.applyAllTransformers(program))
				return null;
			endTime = System.currentTimeMillis();
			if (config.showTime()) {
				totalTime = (endTime - startTime);// / 1000;
				out.println(totalTime + "ms:\tSUMARRY applying transformers");
			}
			if (config.debugOrVerbose() || config.showAST()) {
				out.println(bar
						+ "The AST after linking and applying transformer is:"
						+ bar);
				program.getAST().print(out);
				out.println();
				out.flush();
			}
			if (config.debugOrVerbose() || config.showProgram()) {
				out.println(bar
						+ "The program after linking and applying transformer is:"
						+ bar);
				program.prettyPrint(out);
				out.println();
				out.flush();
			}
			if (config.debugOrVerbose() || config.showInputVars())
				this.printInputVariableNames(program);
			return program;
		}
		return null;
	}

	private void printInputVariableNames(Program program) {
		ASTNode root = program.getAST().getRootNode();

		out.println(bar + " input variables of " + this.userFileCoreName + " "
				+ bar);
		for (ASTNode child : root.children()) {
			if (child != null
					&& child.nodeKind() == NodeKind.VARIABLE_DECLARATION) {
				VariableDeclarationNode variable = (VariableDeclarationNode) child;

				if (variable.getTypeNode().isInputQualified()) {
					variable.prettyPrint(out);
					out.println();
				}
			}
		}
		out.flush();
	}

	Model translate() throws PreprocessorException {
		long startTime = System.currentTimeMillis();
		Program program = this.buildProgram();
		long endTime = System.currentTimeMillis();
		long totalTime;

		if (config.showTime()) {
			totalTime = (endTime - startTime);// / 1000;
			out.println(totalTime
					+ "ms: total time for building the whole program");
		}
		if (program != null) {
			Model model;

			startTime = System.currentTimeMillis();
			model = this.buildModel(program);
			endTime = System.currentTimeMillis();
			if (config.showTime()) {
				totalTime = (endTime - startTime);// / 1000;
				out.println(totalTime
						+ "ms: CIVL model builder builds model from program");
			}
			return model;
		}
		return null;
	}

	/**
	 * Extracts from a string the "core" part of a filename by removing any
	 * directory prefixes and removing any file suffix. For example, invoking on
	 * "users/siegel/gcd/gcd1.cvl" will return "gcd1". This is the name used to
	 * name the model and other structures; it is used in the log, to name
	 * generated files, and for error reporting.
	 * 
	 * @param filename
	 *            a filename
	 * @return the core part of that filename
	 */
	private static String coreName(String filename) {
		String result = filename;
		char sep = File.separatorChar;
		int lastSep = filename.lastIndexOf(sep);
		int lastDot;

		if (lastSep >= 0)
			result = result.substring(lastSep + 1);
		lastDot = result.lastIndexOf('.');
		if (lastDot >= 0)
			result = result.substring(0, lastDot);
		return result;
	}

	Model buildModel(Program program) {
		Model model;
		ModelBuilder modelBuilder = Models.newModelBuilder(this.universe);
		String modelName = coreName(userFileName);

		try {
			boolean hasFscanf = TransformerFactory.hasFunctionCalls(
					program.getAST(), Arrays.asList("scanf", "fscanf"));

			model = modelBuilder.buildModel(cmdConfig, program, modelName,
					config.debugOrVerbose(), out);
			model.setHasFscanf(hasFscanf);
		} catch (CommandLineException e) {
			err.println("errors encountered when building model for "
					+ modelName + ":");
			err.println(e.getMessage());
			err.flush();
			return null;
		}
		if (config.debugOrVerbose() || config.showModel()) {
			out.println(bar + "The CIVL model is:" + bar);
			model.print(out, config.debugOrVerbose());
			out.println();
			out.flush();
		}
		return model;
	}

	/**
	 * Applies default transformers (pruner and side-effect remover) of the
	 * given program.
	 * 
	 * @param program
	 *            The result of compiling, linking and applying CIVL-specific
	 *            transformers to the input program.
	 * @param config
	 *            The CIVL configuration.
	 * @throws SyntaxException
	 */
	private void applyDefaultTransformers(Program program)
			throws SyntaxException {
		// always apply pruner and side effect remover
		if (config.debugOrVerbose())
			this.out.println("Apply pruner...");
		program.applyTransformer("prune");
		if (config.debugOrVerbose())
			program.prettyPrint(out);
		if (config.debugOrVerbose())
			this.out.println("Apply side-effect remover...");
		program.applyTransformer("sef");
		if (config.debugOrVerbose())
			program.prettyPrint(out);
	}

	/**
	 * Applies CIVL-specific transformers (such as general, mpi, omp, io, etc)
	 * to a given program. The transformers to be applied are selected by
	 * analyzing the program. Currently, the rules are as follows.
	 * <ul>
	 * <li>
	 * io: stdio.h is present;</li>
	 * <li>
	 * omp: omp.h is present or there is some OpenMP pragma;</li>
	 * <li>
	 * mpi: mpi.h is present;</li>
	 * <li>
	 * pthread: pthread.h is present.</li>
	 * </ul>
	 * 
	 * @param fileName
	 *            The file name of the source program.
	 * @param program
	 *            The result of compiling and linking the source program.
	 * @param config
	 *            The CIVL configuration.
	 * @throws SyntaxException
	 */
	private void applyTranslationTransformers(Program program)
			throws SyntaxException {
		// ASTFactory astFactory = program.getAST().getASTFactory();
		Set<String> headers = new HashSet<>();
		boolean isC = userFileName.endsWith(".c");
		boolean hasStdio = false, hasOmp = false, hasMpi = false, hasPthread = false, hasCuda = false;

		for (SourceFile sourceFile : program.getAST().getSourceFiles()) {
			String filename = sourceFile.getName();

			if (filename.endsWith(".h")) {
				headers.add(filename);
			}
		}
		if (headers.contains("stdio.h"))
			hasStdio = true;
		if (headers.contains("omp.h") || program.hasOmpPragma())
			hasOmp = true;
		if (isC && headers.contains("pthread.h"))
			hasPthread = true;
		if (isC && headers.contains("mpi.h"))
			hasMpi = true;
		if (headers.contains("cuda.h"))
			hasCuda = true;
		// always apply general transformation.
		if (config.debugOrVerbose())
			this.out.println("Apply general transformer...");
		program.apply(transformerFactory.getGeneralTransformer());
		if (config.debugOrVerbose()) {
			program.prettyPrint(out);
		}
		if (hasStdio) {
			if (config.debugOrVerbose())
				this.out.println("Apply IO transformer...");
			program.apply(transformerFactory.getIOTransformer());
			if (config.debugOrVerbose()) {
				program.prettyPrint(out);
			}
		}
		if (hasOmp) {
			if (!config.ompNoSimplify()) {
				if (config.debugOrVerbose())
					this.out.println("Apply OpenMP simplifier...");
				program.apply(transformerFactory.getOpenMPSimplifier());
			}
			if (config.debugOrVerbose())
				this.out.println("Apply OpenMP transformer...");
			program.apply(transformerFactory.getOpenMP2CIVLTransformer(config));
			if (config.debugOrVerbose())
				program.prettyPrint(out);
		}
		if (hasPthread) {
			if (config.svcomp()) {
				if (config.debugOrVerbose())
					this.out.println("Apply Macro transformer for svcomp programs ...");
				program.apply(transformerFactory.getMacroTransformer());
				if (config.debugOrVerbose())
					program.prettyPrint(out);
			}
			if (config.debugOrVerbose())
				this.out.println("Apply Pthread transformer...");
			program.apply(transformerFactory.getPthread2CIVLTransformer());
			if (config.debugOrVerbose())
				program.prettyPrint(out);
		}
		if (hasMpi) {
			if (config.debugOrVerbose())
				this.out.println("Apply MPI transformer...");
			program.apply(transformerFactory.getMPI2CIVLTransformer());
			if (config.debugOrVerbose())
				program.prettyPrint(out);
		}
		if (hasCuda) {
			if (config.debugOrVerbose())
				this.out.println("Apply Cuda transformer...");
			program.apply(transformerFactory.getCuda2CIVLTransformer());
			if (config.debugOrVerbose())
				program.prettyPrint(out);
		}
	}

	/**
	 * Apply transformers of the program.
	 * 
	 * @param fileName
	 *            The file name of the input program.
	 * @param program
	 *            The result of compiling and linking the input program.
	 * @throws SyntaxException
	 */
	private boolean applyAllTransformers(Program program) {
		try {
			this.applyTranslationTransformers(program);
			this.applyDefaultTransformers(program);
		} catch (SyntaxException e) {
			err.println("errors encountered when applying transformers:");
			err.println(e.getMessage());
			err.flush();
			return false;
		}
		return true;
	}

	/**
	 * Links an AST with the system implementations of libraries used in the
	 * AST.
	 * 
	 * @param preprocessor
	 *            The preprocessor to be used for preprocessing all system
	 *            implementation of libraries used by the given AST.
	 * @param userAST
	 *            The AST to be linked.
	 * @return The program which is the result of linking the given AST and the
	 *         ASTs of system implementation of libraries used.
	 * @throws PreprocessorException
	 * @throws SyntaxException
	 * @throws ParseException
	 * @throws IOException
	 */
	private Program link(List<AST> userASTs) {
		ArrayList<AST> asts = new ArrayList<>();
		AST[] TUs;
		Program program;

		try {
			asts.addAll(this.systemImplASTs(userASTs));
		} catch (PreprocessorException | SyntaxException | ParseException
				| IOException e) {
			err.println("errors encountered when parsing implementation "
					+ "of system libraries:");
			err.println(e.getMessage());
			err.flush();
			return null;
		}
		asts.addAll(userASTs);
		TUs = new AST[asts.size()];
		asts.toArray(TUs);
		if (config.debugOrVerbose()) {
			out.println("Linking: ");
			for (AST ast : TUs)
				out.println("  " + ast);
			out.flush();
		}
		try {
			long startTime, endTime;
			long totalTime;

			startTime = System.currentTimeMillis();
			program = frontEnd.link(TUs, Language.CIVL_C);
			endTime = System.currentTimeMillis();
			if (config.showTime()) {
				totalTime = (endTime - startTime);// / 1000;
				out.println(totalTime + "ms:\tSUMARRY linking " + TUs.length
						+ " ASTs");
			}
		} catch (SyntaxException e) {
			// the following is inaccurate and I think not helpful.
			// this is the first time the translation units get analyzed,
			// so this may report an error that is in a single translation unit
			// and has nothing to do with linking.
			// err.println("errors encountered when linking input program with"
			// + " the implementation of system libraries:");
			err.println("Compilation error: " + e.getMessage());
			err.flush();
			return null;
		}
		return program;
	}

	/**
	 * Parses a given token source into an AST.
	 * 
	 * @param tokenSource
	 *            The token source to be parsed.
	 * @return The unanalyzed AST which is the result of parsing the given token
	 *         source.
	 * @throws SyntaxException
	 * @throws ParseException
	 */
	private AST parse(CTokenSource tokenSource) throws SyntaxException,
			ParseException {
		ParseTree tree;
		AST ast;
		long startTime;
		long endTime;
		long totalTime;

		if (config.debugOrVerbose()) {
			out.println("Generating AST for " + tokenSource);
			// out.println();
			// out.flush();
		}
		startTime = System.currentTimeMillis();
		tree = frontEnd.getParser().parse(tokenSource);
		endTime = System.currentTimeMillis();
		if (config.showTime()) {
			totalTime = (endTime - startTime);// / 1000;
			out.println(totalTime
					+ "ms:\t\tANTLR parsing to form ANTLR tree for TU "
					+ tokenSource);
		}
		startTime = System.currentTimeMillis();
		ast = frontEnd.getASTBuilder().getTranslationUnit(tree);
		endTime = System.currentTimeMillis();
		if (config.showTime()) {
			totalTime = (endTime - startTime);// / 1000;
			out.println(totalTime
					+ "ms:\t\tconverting ANTLR tree to AST for TU "
					+ tokenSource);
		}
		return ast;
	}

	public List<AST> parseTokens(CTokenSource[] tokenSources) {
		List<AST> asts = new ArrayList<>(tokenSources.length);

		for (CTokenSource tokens : tokenSources) {
			try {
				AST ast = parse(tokens);

				asts.add(ast);
			} catch (SyntaxException | ParseException e) {
				err.println("errors encountered when parsing "
						+ tokens.getSourceName() + ":");
				err.println(e.getMessage());
				err.flush();
				return null;
			}
		}
		return asts;
	}

	public CTokenSource[] preprocess() throws PreprocessorException {
		List<CTokenSource> tokenSources = new ArrayList<>(filenames.length);

		for (String filename : filenames) {
			File file = new File(filename);

			try {
				CTokenSource tokens = preprocessor.outputTokenSource(
						systemIncludes, userIncludes, macroMaps, new File(
								filename));

				tokenSources.add(tokens);
			} catch (PreprocessorException e) {
				err.println("errors encountered when preprocessing " + filename
						+ ":");
				err.println(e.getMessage());
				err.flush();
				return null;
			}
			if (config.showPreproc() || config.debugOrVerbose()) {
				out.println(bar + " Preprocessor output for " + filename + " "
						+ bar);
				preprocessor.printOutputDebug(systemIncludes, userIncludes,
						macroMaps, out, file);
				out.println();
				out.flush();
			}
		}
		return tokenSources.toArray(new CTokenSource[filenames.length]);
	}

	private Map<String, Macro> getMacroMaps(Preprocessor preprocessor,
			GMCConfiguration config) {
		Map<String, Object> macroDefMap = config.getMapValue(macroO);
		Map<String, String> macroDefs = new HashMap<String, String>();

		macroDefs.put(CIVL_MACRO, "");
		if (macroDefMap != null) {
			for (String name : macroDefMap.keySet()) {
				macroDefs.put(name, (String) macroDefMap.get(name));
			}
		}
		try {
			return preprocessor.getMacros(macroDefs);
		} catch (PreprocessorException e) {
			this.err.println("invalid macro definitions found in the command line:");
			err.println(e.getMessage());
		}
		return new HashMap<String, Macro>();
	}

	/**
	 * Given a colon-separated list of filenames as a single string, this splits
	 * it up and returns an array of File objects, one for each name.
	 * 
	 * @param string
	 *            null or colon-separated list of filenames
	 * @return array of File
	 */
	private File[] extractPaths(String string) {
		if (string == null)
			return new File[0];
		else {
			String[] pieces = string.split(":");
			int numPieces = pieces.length;
			File[] result = new File[numPieces];

			for (int i = 0; i < numPieces; i++)
				result[i] = new File(pieces[i]);
			return result;
		}
	}

	private File[] getUserIncludes(GMCConfiguration config) {
		return extractPaths((String) config.getValue(userIncludePathO));
	}

	/**
	 * This adds the default CIVL include path to the list of system includes.
	 *
	 * @param config
	 * @return list of system include directories specified in the (command
	 *         line) config object with the default CIVL include directory
	 *         tacked on at the end
	 */
	private File[] getSysIncludes(GMCConfiguration config) {
		File[] sysIncludes = extractPaths((String) config
				.getValue(sysIncludePathO));
		int numIncludes = sysIncludes.length;
		File[] newSysIncludes = new File[numIncludes + 1];

		System.arraycopy(sysIncludes, 0, newSysIncludes, 0, numIncludes);
		newSysIncludes[numIncludes] = CIVLConstants.CIVL_INCLUDE_PATH;
		return newSysIncludes;
	}

	/**
	 * Finds all system libraries that are needed by the given AST, and compiles
	 * them into ASTs.
	 * 
	 * @param preprocessor
	 *            the preprocessor for preprocessing tokens.
	 * @param userAST
	 *            the AST of the input program, which is considered as the
	 *            "user" code, compared to libraries.
	 * @return The list of ASTs each of which corresponds to the implementation
	 *         of a library used by the input AST.
	 * @throws PreprocessorException
	 * @throws SyntaxException
	 * @throws ParseException
	 * @throws IOException
	 */
	private List<AST> systemImplASTs(List<AST> userASTs)
			throws PreprocessorException, SyntaxException, ParseException,
			IOException {
		List<AST> result = new ArrayList<>();
		Set<String> processedSystemFilenames = new HashSet<>();
		Stack<AST> workList = new Stack<>();

		workList.addAll(userASTs);
		while (!workList.isEmpty()) {
			AST ast = workList.pop();

			for (SourceFile sourceFile : ast.getSourceFiles()) {
				String systemFilename = getSystemImplementationName(sourceFile
						.getFile());

				if (systemFilename != null
						&& processedSystemFilenames.add(systemFilename)) {
					// the following ensures the file found will be
					// /include/civl/name.cvl, not something in the
					// current directory or elsewhere in the path.
					// It also ensures any file included will also
					// be found in either /include/civl or /include/abc.

					// File systemFile = new
					// File(CIVLConstants.CIVL_INCLUDE_PATH,
					// systemFilename);

					CTokenSource tokens = preprocessor.outputTokenSource(
							civlSysPathArray, emptyFileArray, macroMaps,
							systemFilename);
					AST newAST = parse(tokens);

					workList.add(newAST);
					result.add(newAST);
				}
			}
		}
		return result;
	}

	// /**
	// * Parses a given file into an AST.
	// *
	// * @param preprocessor
	// * The preprocessor that will extracts token source from the
	// * given file.
	// * @param filename
	// * The name of the file that is to be parsed.
	// * @return The AST which is the result of parsing the given file.
	// * @throws SyntaxException
	// * @throws ParseException
	// * @throws PreprocessorException
	// */
	// private AST parseFile(String filename) throws SyntaxException,
	// ParseException, PreprocessorException, IOException {
	//
	// CTokenSource tokens = preprocessor.outputTokenSource(systemIncludes,
	// userIncludes, macroMaps, filename);
	//
	// return parse(tokens);
	// }

	/**
	 * Finds out the file name of the system implementation of a header file,
	 * which stands for a certain system library, such as civlc.cvh, mpi.h,
	 * omp.h, stdio.h, etc.
	 * 
	 * @param file
	 * @return The file name of the system implementation of the given header
	 *         file, or null if there is no implementation of the header file.
	 */
	private String getSystemImplementationName(File file) {
		String name = file.getName();

		switch (name) {
		case "civlc.cvh":
			return "civlc.cvl";
		case "civl-mpi.cvh":
			return "civl-mpi.cvl";
		case "civl-pthread.cvh":
			return "civl-pthread.cvl";
		case "comm.cvh":
			return "comm.cvl";
		case "concurrency.cvh":
			return "concurrency.cvl";
		case "civl-omp.cvh":
			return "civl-omp.cvl";
		case "mpi.h":
			return "mpi.cvl";
		case "math.h":
			return "math.cvl";
		case "omp.h":
			return "omp.cvl";
		case "pthread.h":
			return "pthread.cvl";
		case "seq.cvh":
			return "seq.cvl";
		case "string.h":
			return "string.cvl";
		case "svcomp.h":
			return "svcomp.cvl";
		case "stdlib.h":
			return "stdlib.cvl";
		case "sys/time.h":
			return "sys-time.cvl";
		case "time.h":
			return "time.cvl";
		case "cuda.h":
			return "cuda.cvl";
		case "civl-cuda.cvh":
			return "civl-cuda.cvl";
		default:
			return null;
		}
	}

}
