package edu.udel.cis.vsl.abc.front.fortran.preproc;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.antlr.runtime.Parser;

import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.front.IF.Preprocessor;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.Macro;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

public class FortranPreprocessor implements Preprocessor {

	private Map<File, SourceFile> sourceFileMap = new LinkedHashMap<>();

	private ArrayList<SourceFile> sourceFiles = new ArrayList<>();

	@SuppressWarnings("unused")
	private Configuration config;

	private TokenFactory tokenFactory;

	public FortranPreprocessor(Configuration config, TokenFactory tokenFactory) {
		this.config = config;
		this.tokenFactory = tokenFactory;
	}

	/**
	 * Returns a FortranLexer for the given preprocessor source file. The lexer
	 * removes all occurrences of backslash-newline, scans and tokenizes the
	 * input to produce a sequence of tokens in the preprocessor grammar. It
	 * does not execute the preprocessor directives.
	 * 
	 * @param file
	 *            a preprocessor source file
	 * @return a FortranLexer for the given file
	 * @throws IOException
	 *             if an I/O error occurs while reading the file
	 */
	@Override
	public FortranLexer lexer(File file) throws PreprocessorException {
		try {
			FortranStream fortranStream = new FortranStream(
					file.getAbsolutePath());

			return new FortranLexer(fortranStream);
		} catch (IOException e) {
			throw new PreprocessorException(
					"I/O error occurred while scanning " + file + ":\n" + e);
		}
	}

	/**
	 * Prints the results of lexical analysis of the source file. Mainly useful
	 * for debugging. (The printing method is unimplemented currently for
	 * Fortran.)
	 * 
	 * @param out
	 *            a PrintStream to which the output should be sent
	 * @param file
	 *            a preprocessor source file
	 * @throws PreprocessorException
	 *             if any kind of exception comes from ANTLR's lexer, including
	 *             a file which does not conform lexically to the preprocessor
	 *             grammar
	 */
	@Override
	public void lex(PrintStream out, File file) throws PreprocessorException {
		out.println("Lexical analysis of " + file + ":");
		try {
			FortranStream fortranStream = new FortranStream(
					file.getAbsolutePath());
			FortranLexer fortranLexer = new FortranLexer(fortranStream);
			int numErrors = fortranLexer.getNumberOfSyntaxErrors();

			// PreprocessorUtils.printTokenSource(out, lexer);
			if (numErrors != 0)
				throw new PreprocessorException(numErrors
						+ " syntax errors occurred while scanning " + file);
		} catch (IOException e) {
			throw new PreprocessorException(e.getMessage());
		}
	}

	@Deprecated
	public Parser parser(File file) throws PreprocessorException {
		// Unimplemented
		return null;
	}

	@Deprecated
	public void parse(PrintStream out, File file) throws PreprocessorException {
		// Unimplemented
	}

	@Override
	public Map<String, Macro> getMacros(Map<String, String> macroDefs)
			throws PreprocessorException {
		// No Macro implementation for Fortran
		return new HashMap<String, Macro>();
	}

	@SuppressWarnings({ "unchecked", "unused" })
	@Override
	public CivlcTokenSource outputTokenSource(File[] systemIncludePaths,
			File[] userIncludePaths, Map<String, Macro> implicitMacros,
			File file) throws PreprocessorException {
		// TODO:
		File[] sysIncludePaths = systemIncludePaths == null ? new File[] {}
				: systemIncludePaths;
		File[] usrIncludePaths = userIncludePaths == null ? new File[] { new File(
				System.getProperty("user.dir")) } : userIncludePaths;
		Map<String, Macro> impMacros = (implicitMacros == null || implicitMacros
				.size() == 0) ? new HashMap<String, Macro>() : implicitMacros;
		FortranStream fortranStream = null;
		Formation inclusionFormation = tokenFactory
				.newInclusion(new SourceFile(file, 0));// FIXME make it work for
														// included files

		try {
			fortranStream = new FortranStream(file.getAbsolutePath());
		} catch (IOException e) {
			throw new PreprocessorException(e.getMessage());
		}

		FortranLexer lexer = new FortranLexer(fortranStream);
		FortranTokenStream tokenStream = new FortranTokenStream(lexer);
		FortranLexicalPrepass prepass = new FortranLexicalPrepass(lexer,
				tokenStream);

		// determine whether the file is fixed or free form and
		// set the source form in the prepass so it knows how to handle lines.
		prepass.setSourceForm(fortranStream.getSourceForm());
		prepass.performPrepass();
		tokenStream.finalizeTokenStream();

		return new FortranTokenSource(
				(List<CivlcToken>) tokenStream.getTokens(), this.tokenFactory,
				tokenStream);
	}

	@Override
	public CivlcTokenSource outputTokenSource(File[] systemIncludePaths,
			File[] userIncludePaths, Map<String, Macro> implicitMacros,
			String filename, boolean isSystem) throws PreprocessorException,
			IOException {
		File file = new File(filename);

		return outputTokenSource(systemIncludePaths, userIncludePaths,
				implicitMacros, file);
	}

	@Override
	public void printOutputTokens(File[] systemIncludePaths,
			File[] userIncludePaths, Map<String, Macro> implicitMacros,
			PrintStream out, File file) throws PreprocessorException {
		// TODO Auto-generated method stub

	}

	@Override
	public void printOutput(File[] systemIncludePaths, File[] userIncludePaths,
			Map<String, Macro> implicitMacros, PrintStream out, File file)
			throws PreprocessorException {
		// TODO Auto-generated method stub

	}

	@Deprecated
	public void printOutputDebug(File[] systemIncludePaths,
			File[] userIncludePaths, Map<String, Macro> implicitMacros,
			PrintStream out, File file) throws PreprocessorException {
		// Unimplemented
	}

	@Deprecated
	public void debug(File[] systemIncludePaths, File[] userIncludePaths,
			Map<String, Macro> implicitMacros, PrintStream out, File file)
			throws PreprocessorException {
		// Unimplemented
	}

	@Override
	public Collection<SourceFile> getSourceFiles() {
		return sourceFiles;
	}

	@Override
	public SourceFile getSourceFile(File file) {
		return sourceFileMap.get(file);
	}

	@Override
	public int getNumSourceFiles() {
		return sourceFiles.size();
	}

	@Override
	public SourceFile getSourceFile(int index) {
		return sourceFiles.get(index);
	}

	@Override
	public void printSourceFiles(PrintStream out) {
		out.println("Source files:");
		for (SourceFile sourceFile : sourceFiles) {
			out.println(sourceFile.getIndexName() + "\t: "
					+ sourceFile.getPath());
		}
		out.println();
		out.flush();
	}

}
