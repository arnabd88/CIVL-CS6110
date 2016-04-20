package edu.udel.cis.vsl.abc.front.c.preproc;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonToken;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.antlr.runtime.tree.Tree;

import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.front.IF.Preprocessor;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.front.c.preproc.PreprocessorParser.file_return;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.IF.Macro;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.util.IF.ANTLRUtils;

/**
 * The class provides easy access to all services exported by the preproc module
 * (a la Facade Pattern). It includes a main method which preprocesses the file
 * and sends result to stdout.
 * 
 * @author Stephen F. Siegel, University of Delaware
 */
public class CPreprocessor implements Preprocessor {

	public final static String SHORT_FILE_NAME_PREFIX = "f";

	public final static boolean debug = true;

	private Map<File, SourceFile> sourceFileMap = new LinkedHashMap<>();

	private ArrayList<SourceFile> sourceFiles = new ArrayList<>();

	private Configuration config;

	public CPreprocessor(Configuration config) {
		this.config = config;
	}

	@Override
	public Map<String, Macro> getMacros(Map<String, String> macroDefs)
			throws PreprocessorException {
		if ((this.config != null && this.config.svcomp())
				|| (macroDefs != null && macroDefs.size() > 0)) {
			try {
				// use temporary file to store the macro definitions
				String tmpDirBase = System.getProperty("java.io.tmpdir");
				// when -Duser.home=$HOME is used, this returns $HOME
				if (tmpDirBase.startsWith("$")) {
					tmpDirBase = System.getenv(tmpDirBase.substring(1));
				}

				File temp = new File(tmpDirBase, "tmp"
						+ System.currentTimeMillis() + ".h");
				// Write to temp file
				FileWriter tmpWriter = new FileWriter(temp);
				BufferedWriter tmpOut = new BufferedWriter(tmpWriter);
				CPreprocessorWorker worker;
				PreprocessorTokenSource tokenSource;
				Token token;

				// macros for GNU C features
				// for now, put this here. Find a better place:
				if (this.config != null && this.config.svcomp())
					tmpOut.write("#define __attribute__(X)\r\n");
				for (String macro : macroDefs.keySet())
					tmpOut.write("#define " + macro + " "
							+ macroDefs.get(macro) + "\r\n");
				tmpOut.write("\r\n");
				tmpOut.flush();
				tmpOut.close();
				tmpWriter.close();
				worker = new CPreprocessorWorker(config, this,
						CPreprocessorWorker.defaultSystemIncludes,
						CPreprocessorWorker.defaultSystemIncludes,
						new HashMap<String, Macro>());
				tokenSource = worker.outputTokenSource(temp, true);
				do {
					token = tokenSource.nextToken();
				} while (token.getType() != PreprocessorLexer.EOF);
				// delete the temporary file
				temp.delete();
				return tokenSource.macroMap;
			} catch (IOException e) {
				// TODO Auto-generated catch block
				// why doesn't this throw an exception????????
				return new HashMap<String, Macro>();
			}
		} else
			return new HashMap<String, Macro>();
	}

	/**
	 * Returns a lexer for the given preprocessor source file. The lexer removes
	 * all occurrences of backslash-newline, scans and tokenizes the input to
	 * produce a sequence of tokens in the preprocessor grammar. It does not
	 * execute the preprocessor directives.
	 * 
	 * @param file
	 *            a preprocessor source file
	 * @return a lexer for the given file
	 * @throws IOException
	 *             if an I/O error occurs while reading the file
	 */
	@Override
	public PreprocessorLexer lexer(File file) throws PreprocessorException {
		try {
			CharStream charStream = PreprocessorUtils
					.newFilteredCharStreamFromFile(file);

			return new PreprocessorLexer(charStream);
		} catch (IOException e) {
			throw new PreprocessorException(
					"I/O error occurred while scanning " + file + ":\n" + e);
		}
	}

	/**
	 * Prints the results of lexical analysis of the source file. Mainly useful
	 * for debugging.
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
			PreprocessorLexer lexer = lexer(file);
			int numErrors;

			PreprocessorUtils.printTokenSource(out, lexer);
			numErrors = lexer.getNumberOfSyntaxErrors();

			if (numErrors != 0)
				throw new PreprocessorException(numErrors
						+ " syntax errors occurred while scanning " + file);
		} catch (RuntimeException e) {
			throw new PreprocessorException(e.getMessage());
		}
	}

	/**
	 * Returns a parser for the given preprocessor source file.
	 * 
	 * @param file
	 *            a preprocessor source file
	 * @return a parser for that file
	 * @throws PreprocessorException
	 *             if an I/O error occurs in attempting to open the file
	 */
	@SuppressWarnings("unchecked")
	@Override
	public PreprocessorParser parser(File file) throws PreprocessorException {
		PreprocessorLexer lexer = lexer(file);
		CommonTokenStream tokenStream = new CommonTokenStream(lexer);

		if (config != null && config.svcomp()) {
			int numTokens = tokenStream.getNumberOfOnChannelTokens();
			// the second last token is the token before EOF
			Token secondLastToken = tokenStream.get(numTokens - 2);

			if (secondLastToken.getType() != PreprocessorParser.NEWLINE) {
				Token newLineToken = new CommonToken(
						secondLastToken.getInputStream(),
						PreprocessorParser.NEWLINE,
						secondLastToken.getChannel(), -1, -1);

				newLineToken.setText("\n");
				((List<Token>) tokenStream.getTokens()).add(numTokens - 1,
						newLineToken);
			}
		}
		return new PreprocessorParser(tokenStream);
	}

	/**
	 * Scans and parses the given preprocessor source file, sending a textual
	 * description of the resulting tree to out. This does not execute any
	 * preprocessor directives. It is useful mainly for debugging.
	 * 
	 * @param out
	 *            print stream to which the tree representation of the file will
	 *            be sent
	 * @param file
	 *            a preprocessor source file.
	 * @throws PreprocessorException
	 *             if the file does not conform to the preprocessor grammar, or
	 *             an I/O error occurs in reading the file
	 */
	@Override
	public void parse(PrintStream out, File file) throws PreprocessorException {
		try {
			PreprocessorParser parser = parser(file);
			file_return fileReturn = parser.file();
			int numErrors = parser.getNumberOfSyntaxErrors();
			Tree tree;

			if (numErrors != 0)
				throw new PreprocessorException(numErrors
						+ " syntax errors occurred while scanning " + file);
			out.println("AST for " + file + ":");
			out.flush();
			tree = (Tree) fileReturn.getTree();
			ANTLRUtils.printTree(out, tree);
		} catch (RecognitionException e) {
			throw new PreprocessorException(
					"Recognition error while preprocessing:\n" + e);
		} catch (RuntimeException e) {
			e.printStackTrace(System.err);
			throw new PreprocessorException(e.toString());
		}
	}

	/**
	 * Given a preprocessor source file, this returns a Token Source that emits
	 * the tokens resulting from preprocessing the file.
	 * 
	 * @param file
	 * @return a token source for the token resulting from preprocessing the
	 *         file
	 * @throws PreprocessorException
	 *             if an I/O error occurs
	 */
	@Override
	public PreprocessorTokenSource outputTokenSource(File[] systemIncludePaths,
			File[] userIncludePaths, Map<String, Macro> implicitMacros,
			File file) throws PreprocessorException {
		CPreprocessorWorker worker = new CPreprocessorWorker(config, this,
				systemIncludePaths, userIncludePaths, implicitMacros);

		return worker.outputTokenSource(file, false);
	}

	@Override
	public CivlcTokenSource outputTokenSource(File[] systemIncludePaths,
			File[] userIncludePaths, Map<String, Macro> implicitMacros,
			String filename, boolean isSystem) throws PreprocessorException,
			IOException {
		CPreprocessorWorker worker = new CPreprocessorWorker(config, this,
				systemIncludePaths, userIncludePaths, implicitMacros);

		return worker.outputTokenSource(isSystem, filename);
	}

	/**
	 * Prints the list of tokens that result from preprocessing the file. One
	 * token is printed per line, along with information on the origin of that
	 * token. Useful mainly for debugging.
	 * 
	 * @param out
	 *            where to send output list
	 * @param file
	 *            a preprocessor source file
	 * @throws PreprocessorException
	 *             if the file fails to adhere to the preprocessor grammar, or
	 *             an I/O occurs
	 */
	@Override
	public void printOutputTokens(File[] systemIncludePaths,
			File[] userIncludePaths, Map<String, Macro> implicitMacros,
			PrintStream out, File file) throws PreprocessorException {
		CPreprocessorWorker worker = new CPreprocessorWorker(config, this,
				systemIncludePaths, userIncludePaths, implicitMacros);
		PreprocessorTokenSource source = worker.outputTokenSource(file, false);

		out.println("Post-preprocessing token stream for " + file + ":\n");
		PreprocessorUtils.printTokenSource(out, source);
		out.flush();
	}

	@Override
	public void printOutput(File[] systemIncludePaths, File[] userIncludePaths,
			Map<String, Macro> implicitMacros, PrintStream out, File file)
			throws PreprocessorException {
		CPreprocessorWorker worker = new CPreprocessorWorker(config, this,
				systemIncludePaths, userIncludePaths, implicitMacros);
		PreprocessorTokenSource source = worker.outputTokenSource(file, false);

		PreprocessorUtils.sourceTokenSource(out, source);
		out.flush();
	}

	@Override
	public void printOutputDebug(File[] systemIncludePaths,
			File[] userIncludePaths, Map<String, Macro> implicitMacros,
			PrintStream out, File file) throws PreprocessorException {
		out.println("Post-preprocessing output for " + file + ":\n");
		out.println("----------------------------------->");
		printOutput(systemIncludePaths, userIncludePaths, implicitMacros, out,
				file);
		out.println("<-----------------------------------");
		out.flush();
	}

	@Override
	public void debug(File[] systemIncludePaths, File[] userIncludePaths,
			Map<String, Macro> implicitMacros, PrintStream out, File file)
			throws PreprocessorException {
		PreprocessorUtils.source(out, file);
		out.println();
		lex(out, file);
		out.println();
		parse(out, file);
		out.println();
		printOutputTokens(systemIncludePaths, userIncludePaths, implicitMacros,
				out, file);
		out.println();
		printOutputDebug(systemIncludePaths, userIncludePaths, implicitMacros,
				out, file);
		out.println();
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
		SourceFile result = sourceFileMap.get(file);

		if (result == null) {
			result = new SourceFile(file, sourceFiles.size());
			if (!tmpFile) {
				// don't keep track of temp files created by parsing command
				// line macros
				sourceFiles.add(result);
				sourceFileMap.put(file, result);
			}
		}
		return result;
	}

	public CivlcTokenSource tokenSourceOfLibrary(String name) {
		CPreprocessorWorker worker = new CPreprocessorWorker(config, this,
				new File[0], new File[0], new HashMap<String, Macro>());

		return worker.tokenSourceOfLibrary(name);
	}

	/**
	 * This main method is just here for simple tests. The real main method is
	 * in the main class, ABC.java.
	 */
	public final static void main(String[] args) throws PreprocessorException {
		String filename = args[0];
		CPreprocessor p = new CPreprocessor(null);
		File file = new File(filename);

		if (debug)
			p.debug(CPreprocessorWorker.defaultSystemIncludes,
					CPreprocessorWorker.defaultUserIncludes,
					CPreprocessorWorker.defaultImplicitMacros, System.out, file);
		else
			p.printOutput(CPreprocessorWorker.defaultSystemIncludes,
					CPreprocessorWorker.defaultUserIncludes,
					CPreprocessorWorker.defaultImplicitMacros, System.out, file);
	}

}
