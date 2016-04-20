package edu.udel.cis.vsl.abc.front.c.preproc;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;

import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.front.IF.Preprocessor;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.IF.Macro;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.abc.token.IF.Tokens;

/**
 * This is the worker of the preprocessor, which is instantiated each time when
 * a preprocessing is requested. The purpose is to make the preprocessor
 * stateless and re-usable.
 * 
 * @author Manchun Zheng
 * 
 */
public class CPreprocessorWorker {

	/* ******************* Package-private static fields ******************* */

	/**
	 * The preprocessor which created this worker.
	 */
	private CPreprocessor preprocessor;

	/**
	 * The system include paths to search for included system headers
	 */
	private File[] systemIncludePaths;

	/**
	 * The user include paths to search for included user headers
	 */
	private File[] userIncludePaths;

	/**
	 * The predefined macros, including those specified by command line
	 * specification.
	 */
	private Map<String, Macro> implicitMacros;

	/**
	 * The token factory.
	 */
	private TokenFactory tokenFactory = Tokens.newTokenFactory();

	/**
	 * The configuration of the translation task
	 */
	private Configuration config;

	/* ******************* Package-private static fields ******************* */

	/**
	 * Default value for implicit macros, which is just an empty map.
	 */
	static Map<String, Macro> defaultImplicitMacros = new HashMap<>();

	/**
	 * Default value for system include path list.
	 */
	static File[] defaultSystemIncludes = new File[] {};

	/**
	 * Default value for user include path list. Currently, it consists of one
	 * directory, namely, the working directory.
	 */
	static File[] defaultUserIncludes = new File[] { new File(
			System.getProperty("user.dir")) };

	/* *************************** Constructors **************************** */

	/**
	 * Creates a new instance of preprocessor worker.
	 * 
	 * @param systemIncludePaths
	 *            the system include paths to search for included system headers
	 * @param userIncludePaths
	 *            the user include paths to search for included user headers
	 * @param macros
	 *            the predefined macros, including those specified in command
	 *            line
	 */
	public CPreprocessorWorker(Configuration config,
			CPreprocessor preprocessor, File[] systemIncludePaths,
			File[] userIncludePaths, Map<String, Macro> macros) {
		this.preprocessor = preprocessor;
		this.config = config;
		if (systemIncludePaths == null)
			this.systemIncludePaths = defaultSystemIncludes;
		else
			this.systemIncludePaths = systemIncludePaths;
		if (userIncludePaths == null)
			this.userIncludePaths = defaultUserIncludes;
		else
			this.userIncludePaths = userIncludePaths;
		if (macros == null || macros.size() == 0)
			this.implicitMacros = defaultImplicitMacros;
		else
			this.implicitMacros = new HashMap<>(macros);
	}

	/* ************************ Private methods ************************* */

	/**
	 * Given a preprocessor source file, this returns a Token Source that emits
	 * the tokens resulting from preprocessing the file.
	 * 
	 * @param file
	 * @param macroMap
	 * @param tokenFactory
	 * @param preprocessor
	 * @return
	 * @throws PreprocessorException
	 */
	private PreprocessorTokenSource outputTokenSource(File file,
			Map<String, Macro> macroMap, TokenFactory tokenFactory,
			boolean tmpFile) throws PreprocessorException {
		PreprocessorParser parser = preprocessor.parser(file);
		PreprocessorTokenSource tokenSource = new PreprocessorTokenSource(
				this.config, file, parser, systemIncludePaths,
				userIncludePaths, macroMap, tokenFactory, this, tmpFile);

		return tokenSource;
	}

	/* ************************ Package methods ************************* */

	/**
	 * Looks to see if a {@link SourceFile} object has already been created for
	 * the given {@link File}. If so, returns that one. Else creates a new one,
	 * assigns it the next index, and stores it.
	 * 
	 * @param file
	 *            a file that is being read to produce this token source
	 * @return the {@link SourceFile} corresponding to the given file
	 */
	SourceFile getOrMakeSourceFile(File file, boolean tmpFile) {
		return preprocessor.getOrMakeSourceFile(file, tmpFile);
	}

	/**
	 * Find the file with the given name by looking through the directories in
	 * the given list. Go through list from first to last. Returns first
	 * instance found.
	 * 
	 * Note: the filename may itself containing directory structure, e.g.,
	 * "sys/stdio.h".
	 * 
	 * @param paths
	 *            list of directories to search
	 * @param filename
	 *            name of file
	 * @return file named filename, or null if not found
	 */
	File findFile(File[] paths, String filename) {
		for (File path : paths) {
			File result = new File(path, filename);

			if (result.isFile())
				return result;
		}
		return null;
	}

	CharStream findInternalSystemFile(File path, String filename) {
		File file = new File(path, filename);

		if (file.getAbsoluteFile().equals(Preprocessor.ABC_INCLUDE_PATH))
			return null;
		try {
			CharStream charStream = PreprocessorUtils
					.newFilteredCharStreamFromResource(filename,
							file.getAbsolutePath());

			return charStream;
		} catch (IOException e) {
			return null;
		}
	}

	CharStream findInternalSystemFile(String filename) {
		for (File systemPath : systemIncludePaths) {
			CharStream charStream = findInternalSystemFile(systemPath, filename);

			if (charStream != null)
				return charStream;
		}
		// look in directory "abc" in the class path:
		return findInternalSystemFile(Preprocessor.ABC_INCLUDE_PATH, filename);
	}

	/**
	 * Given a preprocessor source file, this returns a Token Source that emits
	 * the tokens resulting from preprocessing the file.
	 * 
	 * @param file
	 *            the file to be preprocessed
	 * @param preprocessor
	 * @return a token source for the token resulting from preprocessing the
	 *         file
	 * @throws PreprocessorException
	 *             if an I/O error occurs
	 */
	PreprocessorTokenSource outputTokenSource(File file, boolean tmpFile)
			throws PreprocessorException {
		Map<String, Macro> macroMap = new HashMap<String, Macro>();

		if (implicitMacros != null)
			macroMap.putAll(implicitMacros);
		return outputTokenSource(file, macroMap, tokenFactory, tmpFile);
	}

	/**
	 * Given a preprocessor source file, this returns a Token Source that emits
	 * the tokens resulting from preprocessing the file.
	 * 
	 * @param filename
	 *            the name of the file to be preprocessed
	 * @param preprocessor
	 * @return a token source for the token resulting from preprocessing the
	 *         file
	 * @throws PreprocessorException
	 *             if an I/O error occurs
	 */
	CivlcTokenSource outputTokenSource(boolean isSystem, String filename)
			throws PreprocessorException, IOException {
		Map<String, Macro> macroMap = new HashMap<String, Macro>();

		if (implicitMacros != null)
			macroMap.putAll(implicitMacros);

		File file = null;
		CharStream charStream;
		PreprocessorParser parser;
		PreprocessorLexer lexer;
		int numErrors;

		try {
			file = new File(filename);
			if (isSystem) {
				charStream = getCharStreamFromSystem(filename);
				// no such file:
				if (charStream == null)
					return null;
			} else
				charStream = PreprocessorUtils
						.newFilteredCharStreamFromFile(file);
		} catch (FileNotFoundException fof) {
			// If the target file is not in the current directory, search as a
			// system library file
			charStream = getCharStreamFromSystem(filename);
		}
		lexer = new PreprocessorLexer(charStream);
		parser = new PreprocessorParser(new CommonTokenStream(lexer));
		numErrors = parser.getNumberOfSyntaxErrors();
		if (numErrors != 0)
			throw new PreprocessorException(numErrors
					+ " syntax errors occurred while scanning included file "
					+ file);

		PreprocessorTokenSource tokenSource = new PreprocessorTokenSource(
				this.config, file, parser, systemIncludePaths,
				userIncludePaths, macroMap, tokenFactory, this, false);

		return tokenSource;
	}

	/**
	 * This method loads char stream for system implementation files. Paths are
	 * searched with following rules:
	 * <ol>
	 * <li>
	 * The first priority is user defined include paths and system paths (which
	 * is outside of the jar file)</li>
	 * <li>The second priority is internal resources in the jar file</li>
	 * <li>The lowest priority is the current path</li>
	 * </ol>
	 * 
	 * @param filename
	 * @return
	 * @throws IOException
	 */
	private CharStream getCharStreamFromSystem(String filename)
			throws IOException {
		File file = findFile(userIncludePaths, filename);
		CharStream charStream;

		if (file == null)
			file = findFile(systemIncludePaths, filename);
		if (file == null) {
			charStream = findInternalSystemFile(filename);
			if (charStream == null)
				return null;
			file = new File(filename);
		} else {
			charStream = PreprocessorUtils.newFilteredCharStreamFromFile(file);
		}
		return charStream;
	}

	CivlcTokenSource tokenSourceOfLibrary(String name) {
		File file = new File(Preprocessor.ABC_INCLUDE_PATH, name);

		try {
			CharStream charStream = PreprocessorUtils
					.newFilteredCharStreamFromResource(name,
							file.getAbsolutePath());
			PreprocessorLexer lexer = new PreprocessorLexer(charStream);
			PreprocessorParser parser = new PreprocessorParser(
					new CommonTokenStream(lexer));

			return new PreprocessorTokenSource(this.config, file, parser,
					new File[0], new File[0], new HashMap<String, Macro>(),
					Tokens.newTokenFactory(), this, false);

		} catch (IOException | PreprocessorException e) {
			throw new ABCRuntimeException(
					"errors encountered when preprocessing library " + name);
		}
	}

}
