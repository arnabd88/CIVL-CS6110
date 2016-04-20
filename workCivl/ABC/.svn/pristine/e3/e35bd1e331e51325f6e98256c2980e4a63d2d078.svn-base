package edu.udel.cis.vsl.abc.front.c.preproc;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonToken;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.antlr.runtime.TokenSource;
import org.antlr.runtime.tree.CommonTree;
import org.antlr.runtime.tree.Tree;

import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.front.IF.IllegalMacroArgumentException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorRuntimeException;
import edu.udel.cis.vsl.abc.front.c.preproc.PreprocessorParser.file_return;
import edu.udel.cis.vsl.abc.front.common.preproc.CTokenIterator;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.FunctionMacro;
import edu.udel.cis.vsl.abc.token.IF.Macro;
import edu.udel.cis.vsl.abc.token.IF.ObjectMacro;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.StringToken;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;
import edu.udel.cis.vsl.abc.token.IF.TokenUtils;
import edu.udel.cis.vsl.abc.util.IF.Pair;
import edu.udel.cis.vsl.abc.util.IF.StringPredicate;

/**
 * A PreprocessorTokenSource is created by opening a file, scanning that file
 * and executing the preprocessor directives to produce a stream of (output)
 * tokens. The directives may include #include directives, which cause
 * additional files to be opened and scanned.
 * 
 * The tokens produced are instances of CToken.
 * 
 * TODO: add some options: (1) filter out white space, comments? (2) filter out
 * pragmas?, (3) output #line tokens?, (4) parse formatted comments that use
 * '@'?
 * 
 * TODO: deal with '#' and '##'.
 * 
 * @author Stephen F. Siegel
 */
public class PreprocessorTokenSource implements CivlcTokenSource {

	// Fields...

	// /**
	// * For performance analysis: the number of calls to method
	// * {@link #nextToken()}.
	// */
	// public static long nextToken_calls = 0;

	private SourceFile originalSourceFile;

	/**
	 * The source files used to build this token stream only. These do not
	 * necessarily include all of the source files seen by the preprocessor
	 * creating this token source, because the preprocessor can be re-used
	 * multiple times to create many token sources.
	 */
	private Set<SourceFile> sourceFiles = new LinkedHashSet<>();

	private TokenFactory tokenFactory;

	/**
	 * Stack of included source file information objects. When a #include
	 * directive is executed, an element is pushed on to this stack. When the
	 * EOF of a file is reached, the stack is popped. The stack is initialized
	 * with the initial given source file.
	 */
	private Stack<PreprocessorSourceFileInfo> sourceStack = new Stack<PreprocessorSourceFileInfo>();

	/**
	 * The directories which should be searched for files that are included
	 * using
	 * 
	 * <pre>
	 * #include <filename>
	 * </pre>
	 * 
	 * syntax.
	 */
	private File[] systemIncludePaths;

	/**
	 * The directories which should be searched for files that are included
	 * using
	 * 
	 * <pre>
	 * #include "filename"
	 * </pre>
	 * 
	 * syntax. If the file is not found in one of these directories, the system
	 * paths are then searched.
	 */
	private File[] userIncludePaths;

	/**
	 * Should we save all output tokens in some kind of array?
	 */
	private boolean saveTokens = true;

	/**
	 * The output tokens, if we are saving them, else null.
	 */
	private ArrayList<CivlcToken> theTokens = null;

	/**
	 * Adjacent string literal tokens will be accumulated in a buffer before
	 * being added to the output stream because adjacent string literal must be
	 * concatenated to form one token.
	 */
	private LinkedList<CivlcToken> stringLiteralBuffer = new LinkedList<CivlcToken>();

	/**
	 * The last token, which will be the EOF token, once it is reached.
	 */
	private CivlcToken finalToken = null;

	/**
	 * The expression analyzer is used to analyze and evaluate integer
	 * expressions in preprocessor conditionals.
	 */
	private PreprocessorExpressionAnalyzer expressionAnalyzer;

	/**
	 * A mapping of macro names to the Macro object. An entry is created and
	 * added to this map whenever a '#define' directive is processed. An entry
	 * is removed by a '#undef'
	 */
	Map<String, Macro> macroMap;

	/** Is the current node inside a text block ? */
	private boolean inTextBlock = false;

	/** Is the current node inside a pragma line ? */
	private boolean inPragma = false;

	/**
	 * First and last elements of the output buffer, which forms a linked list.
	 * This is where tokens stay temporarily until they are removed by an
	 * invocation of nextToken().
	 */
	private CivlcToken firstOutput, lastOutput;

	/**
	 * The number of tokens that have been output.
	 */
	private int outputTokenCount = 0;

	/**
	 * The worker who created this token source.
	 */
	private CPreprocessorWorker worker;

	// Constructors...

	/**
	 * Instantiates new CTokenSource object. The give source file is parsed, a
	 * file info object is created for it and pushed onto the stack. The output
	 * tokens are not generated; this does not begin until "getToken" is called.
	 * 
	 * @param source
	 *            original C source file (before preprocessing)
	 * @param systemIncludePaths
	 *            the directories where files included with angle brackets are
	 *            searched
	 * @param userIncludePaths
	 *            the directories where files included with double quotes are
	 *            searched
	 * @throws PreprocessorException
	 *             if and IOException or RecognitionException occurs while
	 *             scanning and parsing the source file
	 */
	public PreprocessorTokenSource(Configuration config, File source,
			PreprocessorParser parser, File[] systemIncludePaths,
			File[] userIncludePaths, Map<String, Macro> macroMap,
			TokenFactory tokenFactory, CPreprocessorWorker worker,
			boolean tmpFile) throws PreprocessorException {
		assert systemIncludePaths != null;
		assert userIncludePaths != null;
		this.tokenFactory = tokenFactory;
		this.worker = worker;
		this.originalSourceFile = getOrMakeSourceFile(source, tmpFile);
		try {
			CommonTree tree = (CommonTree) parser.file().getTree();

			// public CommonToken(CharStream input, int type, int channel, int
			// start, int stop) {

			if (!tmpFile && (config != null && config.svcomp())) {
				CommonToken svcomp = new CommonToken(tree.getToken()
						.getInputStream(), PreprocessorLexer.HEADER_NAME, 0,
						-1, -1);
				CommonToken include = new CommonToken(tree.getToken()
						.getInputStream(), PreprocessorLexer.PINCLUDE, 0, -1,
						-1);

				svcomp.setText("<svcomp.h>");
				include.setText("#include");

				CommonTree includeSvcomp = new CommonTree(include);

				includeSvcomp.addChild(new CommonTree(svcomp));
				tree.insertChild(0, includeSvcomp);
			}

			Formation history = tokenFactory.newInclusion(originalSourceFile);
			StringPredicate macroDefinedPredicate = new MacroDefinedPredicate(
					macroMap);

			addEofNodeToTree(tree, source.getName());
			this.macroMap = macroMap;
			sourceStack.push(new PreprocessorSourceFileInfo(history, parser,
					tree, tree));
			incrementNextNode(); // skip root "FILE" node
			this.systemIncludePaths = systemIncludePaths;
			this.userIncludePaths = userIncludePaths;
			this.expressionAnalyzer = new PreprocessorExpressionAnalyzer(
					macroDefinedPredicate);
		} catch (RecognitionException e) {
			throw new PreprocessorException("Preprocessing " + source
					+ " failed: " + e);
		} catch (RuntimeException e) {
			throw new PreprocessorException(e.getMessage());
		}
		if (saveTokens)
			theTokens = new ArrayList<CivlcToken>();
	}

	public PreprocessorTokenSource(File source, PreprocessorParser parser,
			File[] systemIncludePaths, File[] userIncludePaths,
			TokenFactory tokenFactory, CPreprocessorWorker worker,
			boolean tmpFile) throws PreprocessorException {
		this(null, source, parser, systemIncludePaths, userIncludePaths,
				new HashMap<String, Macro>(), tokenFactory, worker, tmpFile);
	}

	// Helper

	private void addEofNodeToTree(Tree tree, String filename) {
		Formation eofFormation = tokenFactory.newSystemFormation("EOF");
		CivlcToken eofToken = tokenFactory.newCivlcToken(Token.EOF, "EndOfFile<"
				+ filename + ">", eofFormation);
		CommonTree eofNode = new CommonTree(eofToken);

		tree.addChild(eofNode);
	}

	// Implementation of methods from CTokenSource...

	@Override
	public void printShorterFileNameMap(PrintStream out) {
		out.println();
		out.println("File name list:");
		for (SourceFile sourceFile : sourceFiles)
			out.println(sourceFile.getIndex() + "\t: " + sourceFile.getName());
	}

	@Override
	public TokenFactory getTokenFactory() {
		return tokenFactory;
	}

	/**
	 * Returns current file being processed or null if file is not known.
	 * 
	 * @return current file or null
	 */
	private SourceFile getCurrentSource() {
		if (sourceStack.isEmpty()) {
			// only way this could happen is before initial push...
			return originalSourceFile;
		} else
			return sourceStack.peek().getFile();
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
	private SourceFile getOrMakeSourceFile(File file, boolean tmpFile) {
		SourceFile result = worker.getOrMakeSourceFile(file, tmpFile);

		sourceFiles.add(result);
		return result;
	}

	/**
	 * Returns name of current file being scanned. I.e., the name returned by
	 * this method will change dynamically as new files are included.
	 */
	@Override
	public String getSourceName() {
		SourceFile sourceFile = getCurrentSource();

		if (sourceFile != null)
			return sourceFile.getPath();
		return "<unknown source>";
	}

	/**
	 * Returns the next token in the post-preprocessing stream. This is the main
	 * method that must be implemented in order to implement ANTLR's TokenSource
	 * interface.
	 * 
	 * EOF will be the last token returned, and if subsequent calls to this
	 * method are made, it will continue to return EOF forever. This seems to be
	 * what ANTLR's parsers expect.
	 * 
	 * @exception PreprocessorRuntimeException
	 *                if anything goes wrong in trying to find the next token
	 */
	@Override
	public CivlcToken nextToken() {
		// nextToken_calls++;
		if (finalToken != null)
			return finalToken;
		while (firstOutput == null
				|| firstOutput.getType() != PreprocessorLexer.EOF
				&& firstOutput == lastOutput)
			try {
				processNextNode();
			} catch (PreprocessorException e) {
				throw new PreprocessorRuntimeException(e);
			} catch (PreprocessorRuntimeException e) {
				throw e;
			} catch (RuntimeException e) {
				throw new PreprocessorRuntimeException(e.toString(),
						firstOutput);
			}
		if (firstOutput.getType() == PreprocessorLexer.EOF)
			finalToken = firstOutput;
		return removeOutput();
	}

	// Options...

	@Override
	public int getNumTokens() {
		return theTokens.size();
	}

	@Override
	public CivlcToken getToken(int index) {
		return theTokens.get(index);
	}

	// The implementation methods...

	/**
	 * Process the next node in the CPP AST. This may actually involve
	 * processing more nodes, but it will at least involve processing one node
	 * and incrementing the current position by at least one token.
	 * 
	 * @throws PreprocessorException
	 */
	private void processNextNode() throws PreprocessorException {
		CommonTree node = (CommonTree) getNextInputNode();

		if (inTextBlock()) {
			// If you are in a TEXT_BLOCK, you don't have to check for any
			// directives.
			processText(node);
		} else {
			Token token = node.getToken();
			int type = token.getType();

			switch (type) {
			case PreprocessorParser.EOF:
				processEOF(node);
				break;
			case PreprocessorParser.TEXT_BLOCK:
				processTextBlock(node);
				break;
			case PreprocessorParser.PDEFINE:
				processMacroDefinition(node);
				break;
			case PreprocessorLexer.PERROR:
				processError(node);
				break;
			case PreprocessorLexer.PELIF:
			case PreprocessorLexer.PIF:
				processIf(node);
				break;
			case PreprocessorLexer.PIFDEF:
				processIfdef(node);
				break;
			case PreprocessorLexer.PIFNDEF:
				processIfndef(node);
				break;
			case PreprocessorLexer.PINCLUDE:
				processInclude(node);
				break;
			case PreprocessorLexer.PRAGMA:
				processPragma(node);
				break;
			case PreprocessorLexer.PUNDEF:
				processUndef(node);
				break;
			case PreprocessorParser.HASH:
				processNondirective(node);
				break;
			case PreprocessorParser.PLINE:
				processLine(node);
				break;
			default:
				processText(node);
			}
		}
	}

	// processText...

	/**
	 * Process a text node, i.e., a node for a token which is not a preprocessor
	 * directive and does not have any special meaning to the preprocessor,
	 * though it may be a macro invocation. This node may or may not be in a
	 * text block.
	 * 
	 * Precondition: This method should be called only from the outermost scope
	 * of expansion, i.e., we are not currently in a macro expansion.
	 * 
	 * Postcondition: if the node is not an identifier for a macro, a CToken for
	 * it is created and added to the output buffer. If it is a macro, macro
	 * expansion takes place. For a function macro, this involves consuming more
	 * input tokens (the tokens comprising the left parenthesis, the arguments,
	 * and the final right parenthesis). The current position in the input AST
	 * is moved to the point just after that last token. The CTokens resulting
	 * from the expansion are added to the output buffer.
	 * 
	 * @param textNode
	 * @throws PreprocessorException
	 */
	private void processText(Tree textNode) throws PreprocessorException {
		Token token = ((CommonTree) textNode).getToken();

		if (PreprocessorUtils.isIdentifier(token)) {
			processIdentifier(textNode);
		} else {
			shiftToOutput(textNode);
			incrementNextNode();
		}
	}

	/**
	 * If the identifier is a macro, do macro expansion. Else, it's just a
	 * regular token that gets shifted to output.
	 * 
	 * @throws PreprocessorException
	 */
	private void processIdentifier(Tree identifierNode)
			throws PreprocessorException {
		String name = identifierNode.getText();
		Macro macro = macroMap.get(name);

		if (macro != null
				&& (macro instanceof ObjectMacro || peekAheadSkipWSHasType(PreprocessorLexer.LPAREN)
				// peekAheadHasType(PreprocessorLexer.LPAREN)
				)) {
			processInvocation(macro, identifierNode);
		} else {
			shiftToOutput(identifierNode);
			incrementNextNode();
		}
	}

	// Macro Expansion...

	/**
	 * Processes a macro invocation node. Continues walking the input tree to
	 * find the macro arguments (if the macro is a function macro). Then expands
	 * the macro using the macro's definition. The resulting token sequence is
	 * added to the end of the outputBuffer and the position in the input
	 * sequence is moved to the point just after the complete macro invocation.
	 * 
	 * This method is recursive: if any macro expansions occur within arguments,
	 * they are also expanded, following the rules laid out in the C11
	 * specification.
	 * 
	 * Implementation notes: calls findInvocationAguments(...) then calls
	 * processInvocation(macro, arguments);
	 * 
	 * @param macro
	 *            a Macro object
	 * @param invocationNode
	 *            the node containing the identifier token whose string value is
	 *            the name of the macro
	 * @throws PreprocessorException
	 *             if something goes wrong expanding the macro, such as the
	 *             wrong number of arguments is provided
	 */
	private void processInvocation(Macro macro, Tree invocationNode)
			throws PreprocessorException {
		Token token = ((CommonTree) invocationNode).getToken();
		CivlcToken cToken = tokenFactory.newCivlcToken(token, getIncludeHistory());
		Pair<CivlcToken, CivlcToken> result;

		if (macro instanceof ObjectMacro) {
			result = processInvocation((ObjectMacro) macro, cToken);
			incrementNextNode();
		} else {
			CivlcToken[] arguments = findInvocationArguments((FunctionMacro) macro,
					invocationNode);

			// note the call to findInvocationArguments updated
			// position correctly.
			result = processInvocation((FunctionMacro) macro, cToken, arguments);
		}
		addOutputList(result);
	}

	/**
	 * Performs expansion of an object macro. Returns a list of tokens obtained
	 * from the macro's replacement list.
	 * 
	 * The list of tokens returned consists entirely of newly created tokens
	 * (i.e., tokens which did not exist upon entry to this method). They will
	 * have correct include and expansion histories.
	 * 
	 * Following the C Standard, the list of replacement tokens are expanded a
	 * second time, after marking all tokens corresponding to the given macro
	 * identifier as "do not expand".
	 * 
	 * @param macro
	 *            the object macro
	 * @param origin
	 *            the expansion history of the identifier before getting to the
	 *            current expansion.
	 * @return a pair consisting of the first and last elements of the new list
	 *         of tokens
	 * @throws PreprocessorException
	 *             if something goes wrong while expanding the list of
	 *             replacement tokens (i.e., the second expansion)
	 */
	private Pair<CivlcToken, CivlcToken> processInvocation(ObjectMacro macro,
			CivlcToken origin) throws PreprocessorException {
		return performSecondExpansion(instantiate(macro, origin), macro);
	}

	/**
	 * Processes a function macro invocation, given the macro and the actual
	 * arguments. Each actual argument is given as a null-terminated list of
	 * tokens. This returns the list of tokens which is the result of expanding
	 * the macros. This procedure is recursive: if any macro invocations occur
	 * within the arguments, they are also expanded.
	 * 
	 * It is assumed that the input argument tokens will have the correct
	 * expansion histories, i.e., for all expansions up to but not including the
	 * current one.
	 * 
	 * The list of tokens returned consists entirely of newly created tokens
	 * (i.e., tokens which did not exist upon entry to this method). They will
	 * have correct include and expansion histories.
	 * 
	 * Implementation notes: for an invocation of function macro M: for each
	 * argument: call expand(). That modifies the argument (which is a list).
	 * Then invoke substitute, yielding a new List of CToken, B. Then mark all
	 * occurrences of identifier M in B as "do not expand". Then expand B. This
	 * is the recipe straight from the C11 Standard.
	 * 
	 * @param macro
	 * @param arguments
	 * @throws PreprocessorException
	 */
	private Pair<CivlcToken, CivlcToken> processInvocation(FunctionMacro macro,
			CivlcToken origin, CivlcToken[] arguments) throws PreprocessorException {
		for (int i = 0; i < arguments.length; i++)
			arguments[i] = expandList(arguments[i]).left;
		return performSecondExpansion(instantiate(macro, origin, arguments),
				macro);
	}

	/**
	 * In the second expansion of a macro, the result of the first expansion is
	 * first scanned for instances of the macro being expanded. Any such
	 * instances are marked to not be re-expanded, to prevent an infinite
	 * recursion.
	 * 
	 * @param tokenList
	 *            a list of tokens to be expanded given as pair consisting of
	 *            first and last elements
	 * @param macro
	 *            the macro being expanded
	 * @return result of second expansion of tokenList
	 * @throws PreprocessorException
	 *             any improper macro invocations occur in the token list
	 */
	private Pair<CivlcToken, CivlcToken> performSecondExpansion(
			Pair<CivlcToken, CivlcToken> tokenList, Macro macro)
			throws PreprocessorException {
		String name = macro.getName();

		// mark all occurrences of identifier M as "do not expand"...
		for (CivlcToken token = tokenList.left; token != null; token = token
				.getNext()) {
			if (PreprocessorUtils.isIdentifier(token)
					&& name.equals(token.getText()))
				token.makeNonExpandable();
		}
		return expandList(tokenList.left);
	}

	/**
	 * Creates a new instance of the function macro's body, substituting actual
	 * arguments for formal parameters.
	 * 
	 * The result is a linked list of CToken using the "next" field of CToken.
	 * The elements of the Pair returned are the first and last element of the
	 * list.
	 * 
	 * The arguments will not be modified and will not be re-used in the
	 * returned result. I.e., each node in the result will be a fresh new
	 * CToken.
	 * 
	 * The histories of the new tokens will all be set appropriately. The
	 * history of a new token generated from a replacement token which was not a
	 * formal parameter is obtained by appending a new expansion record (macro,
	 * replacement-index) to the history of the origin. The history of a new
	 * token generated from an argument token (which is substituted for a formal
	 * parameter) is obtained by appending the new expansion record to the
	 * history of the argument token.
	 * 
	 * The reason the arguments can't be re-used: an argument can be used more
	 * than once since the formal parameter may occur more than once in the
	 * macro body.
	 * 
	 * @param macro
	 *            a function macro
	 * @param origin
	 *            the original CToken which is an identifier for the macro's
	 *            name which led to its expansion
	 * @param arguments
	 *            array of length number of formal parameters for macro. Element
	 *            in position i is the first element of a null-terminated list
	 *            of the tokens comprising the i-th argument
	 * @return first and last element in a new list which is the result of
	 *         performing substitution of actual arguments for formal parameters
	 *         in the macro body
	 */
	private Pair<CivlcToken, CivlcToken> instantiate(FunctionMacro macro,
			CivlcToken origin, CivlcToken[] arguments) {
		int numTokens = macro.getNumReplacementTokens();
		CivlcToken first = null, previous = null, current = null;

		for (int i = 0; i < numTokens; i++) {
			Token token = macro.getReplacementToken(i);
			int formalIndex = macro.getReplacementFormalIndex(i);

			if (formalIndex < 0) {
				current = tokenFactory.newCivlcToken(token,
						tokenFactory.newMacroExpansion(origin, macro, i));
				if (previous != null)
					previous.setNext(current);
				if (first == null)
					first = current;
				previous = current;
			} else { // splice in argument
				CivlcToken argument = arguments[formalIndex];

				while (argument != null) {
					current = tokenFactory.newCivlcToken(argument,
							tokenFactory.newMacroExpansion(argument, macro, i));
					if (previous != null)
						previous.setNext(current);
					if (first == null)
						first = current;
					previous = current;
					argument = argument.getNext();
				}
			}
		}
		return new Pair<>(first, current);
	}

	/**
	 * Creates a new instance of the object macro's body. Creates a sequence of
	 * CTokens corresponding to the sequence of input tokens in the macro's
	 * replacement list.
	 * 
	 * The result is a linked list of CToken using the "next" field of CToken.
	 * The elements of the Pair returned are the first and last element of the
	 * list.
	 * 
	 * @param macro
	 *            any object macro
	 * @param origin
	 *            the original expansion history for the identifier which is the
	 *            macro's name and led to its expansion
	 * @return first and last element in a null-terminated linked list of fresh
	 *         CTokens obtained from the macro's body
	 */
	private Pair<CivlcToken, CivlcToken> instantiate(ObjectMacro macro, CivlcToken origin) {
		int numTokens = macro.getNumReplacementTokens();
		CivlcToken first = null, previous = null, current = null;

		for (int i = 0; i < numTokens; i++) {
			Token token = macro.getReplacementToken(i);

			current = tokenFactory.newCivlcToken(token,
					tokenFactory.newMacroExpansion(origin, macro, i));
			if (previous != null)
				previous.setNext(current);
			if (first == null)
				first = current;
			previous = current;
		}
		return new Pair<>(first, current);
	}

	/**
	 * Expands all macro invocations in a list of CToken, modifying the list in
	 * the process. Does not care about preprocessor directives, or anything
	 * else other than macro invocations. Even if this method comes across a
	 * directive, it does not treat the directive as a directive---it is treated
	 * as just another token.
	 * 
	 * Exception: do not expand macros if they occur within a "defined"
	 * operator!
	 * 
	 * Note that the token returned by this method MAY be the first token in the
	 * given list. It also may NOT be the first token in the given list, because
	 * that token was a macro invocation and was replaced.
	 * 
	 * Implementation: iterate over the tokens looking for macro invocations.
	 * When you find one, call processInvocation and insert its output into
	 * list, in place of the the invocation.
	 * 
	 * ... X X X M ( A0 A0 A1 A2 A2 A2 ) X X X ... ->
	 * 
	 * ... X X X R R R ... R X X X ...
	 * 
	 * @param token
	 *            the first element in a null-terminated list of tokens; may be
	 *            null for empty list
	 * @return first element in expanded list; may be null for empty list
	 * @throws PreprocessorException
	 */
	private Pair<CivlcToken, CivlcToken> expandList(CivlcToken first)
			throws PreprocessorException {
		CivlcToken current = first, previous = null;

		while (current != null) {
			if (!current.isExpandable()) {
				previous = current;
				current = current.getNext();
				continue;
			}

			int type = current.getType();

			if (type == PreprocessorLexer.DEFINED) {
				// ignore it and next token
				previous = current.getNext();
				current = previous.getNext();
				continue;
			}

			Macro macro = null;
			boolean isInvocation = false;

			if (PreprocessorUtils.isIdentifier(current)) {
				macro = macroMap.get(current.getText());

				if (macro == null) {
					isInvocation = false;
				} else if (macro instanceof ObjectMacro) {
					isInvocation = true;
				} else {
					CivlcToken next = current.getNext();

					isInvocation = (next != null && next.getType() == PreprocessorLexer.LPAREN);
				}
			}
			if (!isInvocation) { // ignore it
				previous = current;
				current = current.getNext();
				continue;
			}

			Pair<CivlcToken, CivlcToken> replacements;

			if (macro instanceof ObjectMacro) {
				replacements = processInvocation((ObjectMacro) macro, current);
				current = current.getNext();
			} else {
				Iterator<CivlcToken> iter = new CTokenIterator(current.getNext());
				CivlcToken[] arguments = findInvocationArguments(
						(FunctionMacro) macro, iter);

				replacements = processInvocation((FunctionMacro) macro,
						current, arguments);
				// move current to the token just after the closing ')'
				// of the invocation, or null if the ')' was the last token:
				if (iter.hasNext())
					current = iter.next();
				else
					current = null;
			}
			if (replacements.left == null) {
				if (previous == null)
					first = current;
				else
					previous.setNext(current);
			} else {
				if (previous == null)
					first = replacements.left;
				else
					previous.setNext(replacements.left);
				previous = replacements.right;
				previous.setNext(current);
			}
		}
		return new Pair<>(first, previous);
	}

	/**
	 * Given a function macro invocation node, parses input stream to find the
	 * actual arguments in the macro invocation and creates new CTokens for the
	 * tokens occurring in those arguments. Returns an array (whose length is
	 * the number of inputs to the macro) in which element i is first element in
	 * the list of CTokens for the tokens which comprise argument i.
	 * 
	 * The new CTokens will have the correct include history. They will have the
	 * "trivial" expansion history of length 0.
	 * 
	 * From C11 Sec. 6.10.3.11:
	 * 
	 * "If there are sequences of preprocessing tokens within the list of
	 * arguments that would otherwise act as preprocessing directives, the
	 * behavior is undefined."
	 * 
	 * This method will throw a PreprocessorException if this occurs.
	 * 
	 * Updates position to point just after closing right parenthesis.
	 * 
	 * Implementation notes: creates an Iterator of PreprocessorNode by
	 * iterating over the Tree nodes starting from the node immediately
	 * following the invocationNode in DFS order and creating new
	 * PreprocessorNodes. Feeds this to method findInvocationArguments(Macro ,
	 * Iterator<CToken> ).
	 * 
	 * 
	 * @param macro
	 * @param invocationNode
	 * @return array of length number of formal parameters of macro; i-th
	 *         element of array is the first element of a list of tokens that
	 *         comprise the i-th argument
	 * @throws PreprocessorException
	 *             if a sequence of tokens that would otherwise act as
	 *             preprocessing directives occurs in the argument list
	 */
	private CivlcToken[] findInvocationArguments(FunctionMacro macro,
			Tree invocationNode) throws PreprocessorException {
		Iterator<CivlcToken> iter;

		incrementNextNode();
		iter = new Iterator<CivlcToken>() {
			@Override
			public boolean hasNext() {
				return getNextInputNode() != null;
			}

			@Override
			public CivlcToken next() {
				Tree node = getNextInputNode();
				Token inputToken = ((CommonTree) node).getToken();
				CivlcToken result = tokenFactory.newCivlcToken(inputToken,
						getIncludeHistory());

				if (node.getChildCount() > 0)
					throw new IllegalMacroArgumentException(result);
				incrementNextNode();
				return result;
			}

			@Override
			public void remove() { // should never be called
				throw new UnsupportedOperationException();
			}
		};
		return findInvocationArguments(macro, iter);
	}

	private CivlcToken[] findInvocationArguments(FunctionMacro macro,
			Iterator<CivlcToken> argumentIterator) throws PreprocessorException {
		try {
			return findInvocationArgumentsWorker(macro, argumentIterator);
		} catch (IllegalMacroArgumentException e) {
			throw new PreprocessorException(e.getMessage());
		}
	}

	/**
	 * Given an iterator of CTokens which comprise the arguments to a macro,
	 * parses the list to separate the arguments.
	 * 
	 * This method does NOT create any new tokens. It DOES modify the tokens
	 * coming out of the iterator by setting their "next" fields appropriately.
	 * [DOES THIS MESS WITH THE ITERATOR?] The "next" field in the last token
	 * for each argument is set to null, in order to terminate the new list. The
	 * commas separating arguments are spliced out of the list.
	 * 
	 * Note that any or all of the entries in the array returned may be null.
	 * This is because a macro argument can be empty, as in "f()" or "f(1,,3)".
	 * 
	 * The first token in the given argumentIterator had better be LPAREN (left
	 * parenthesis). Otherwise this is not an invocation of a function macro.
	 * The arguments finish when the matching RPAREN is reached.
	 * 
	 * It is guaranteed that this method will invoke next() on the
	 * argumentIterator until it reaches the final ')' (unless that is not
	 * possible for some reason, in which case an exception is thrown). The
	 * method will not iterate beyond that point. In other words, after this
	 * method returns, the "cursor" in the iterator will be at the point just
	 * after the ')'.
	 * 
	 * Implementation notes: doing a little parsing here. Scan the tokens
	 * dividing into the following classes: LPAREN, RPAREN, COMMA, and OTHER.
	 * 
	 * @param macro
	 * @param argumentIterator
	 * @exception PreprocessorException
	 *                if the number of actual arguments does not match the
	 *                number of formals in the macro definition
	 * @return
	 */
	private CivlcToken[] findInvocationArgumentsWorker(FunctionMacro macro,
			Iterator<CivlcToken> argumentIterator) throws PreprocessorException {
		int numFormals = macro.getNumFormals();
		CivlcToken[] result = new CivlcToken[numFormals];
		int argCount = 0, type, parenDepth;
		CivlcToken token, previousToken;

		// first, skip through all the white space to get to the '(':
		while (true) {
			if (!argumentIterator.hasNext())
				throw new PreprocessorException("Macro invocation " + macro
						+ " does not contain any arguments");
			token = argumentIterator.next();
			if (!PreprocessorUtils.isWhiteSpace(token))
				break;
		}
		if (token.getType() != PreprocessorLexer.LPAREN)
			throw new PreprocessorException(
					"Invocation of function macro does not begin with '(': "
							+ macro, token);
		if (numFormals == 0) {
			if (!argumentIterator.hasNext())
				throw new PreprocessorException("Macro invocation " + macro
						+ " does not end in ')'", token);
			token = argumentIterator.next();
			if (token.getType() != PreprocessorLexer.RPAREN)
				throw new PreprocessorException(
						"Invocation of function macro with 0 arguments"
								+ "must have form f() with no spaces between the parentheses",
						token);
			return result;
		}
		parenDepth = 1;
		while (true) {
			if (!argumentIterator.hasNext())
				throw new PreprocessorException(
						"Not enough arguments to macro " + macro, token);
			previousToken = token;
			token = argumentIterator.next();
			type = token.getType();
			if (parenDepth == 1 && type == PreprocessorLexer.COMMA) {
				if (result[argCount] != null)
					previousToken.setNext(null);
				argCount++;
				if (argCount >= numFormals)
					throw new PreprocessorException(
							"Number of arguments to macro " + macro
									+ " exceeds " + "expected number "
									+ numFormals, token);

			} else {
				if (type == PreprocessorLexer.LPAREN)
					parenDepth++;
				else if (type == PreprocessorLexer.RPAREN) {
					parenDepth--;
					if (parenDepth < 0)
						throw new PreprocessorException("Extra ')'", token);
					if (parenDepth == 0) {
						if (result[argCount] != null)
							previousToken.setNext(null);
						argCount++;
						break;
					}
				}
				if (result[argCount] != null)
					previousToken.setNext(token);
				else
					result[argCount] = token;
			}
		}
		if (argCount != numFormals)
			throw new PreprocessorException("Invocation of macro "
					+ macro.getName() + ": expected " + numFormals
					+ " arguments but saw " + argCount, token);
		return result;
	}

	// processEOF...

	/**
	 * Process and End-of-file token. If this is the root file, you are all
	 * done, and the EOF token is moved to the output buffer. Otherwise, you pop
	 * stack and throw away the EOF token---it does not get output.
	 * 
	 * @throws PreprocessorException
	 */
	private void processEOF(Tree node) throws PreprocessorException {
		Token eof = ((CommonTree) node).getToken();
		PreprocessorSourceFileInfo o = sourceStack.pop();

		if (sourceStack.isEmpty()) {
			CivlcToken myEof = tokenFactory.newCivlcToken(eof, o.getIncludeHistory());

			// myEof.setText(text)
			addOutput(myEof);
		} else {
			// you were at the include node. jump to next node ignoring
			// children of include node.
			jumpNextNode();
		}
	}

	// processTextBlock...

	/**
	 * Processes a text block node by moving the current position to the first
	 * child (the first token in the text block).
	 * 
	 * A text block consists of a sequence of tokens that do not contain any
	 * preprocessor directives. The sequence may, however, contains macro
	 * invocations which need to be expanded.
	 * 
	 * @param node
	 *            a node in the tree with TEXT_BLOCK token
	 */
	private void processTextBlock(Tree textBlockNode) {
		int numChildren = textBlockNode.getChildCount();

		if (numChildren != 0)
			inTextBlock = true;
		incrementNextNode();
	}

	/**
	 * Processes a '#define' for an (object or function) macro. For an object
	 * macro, child 0 is the identifier being defined. Child 1 is the "body"
	 * node, whose children form a (possibly empty) list of tokens.
	 * 
	 * For a function macro. Child 0 is the idenitifer being defined. Child 1 is
	 * the formal parameter list node. Child 2 is the body.
	 * 
	 * @param node
	 *            A node in the tree with token of type PDEFINE.
	 * @throws PreprocessorException
	 *             if the macro has already been defined differently
	 */
	private void processMacroDefinition(Tree node) throws PreprocessorException {
		SourceFile sourceFile = getCurrentSource();

		if (node.getChildCount() == 3)
			processMacroDefinition(tokenFactory.newFunctionMacro(node,
					sourceFile));
		else
			processMacroDefinition(tokenFactory
					.newObjectMacro(node, sourceFile));
	}

	/**
	 * Takes a newly created Macro object and checks whether it has been defined
	 * previously. If it has, checks that the two definitions are equivalent. If
	 * the checks pass, an entry for the macro is added to the macroMap.
	 * 
	 * @param newMacro
	 *            a new Macro object
	 * @throws PreprocessorException
	 *             if a macro with the same name has been defined previously
	 *             (and not undefined) in a different way
	 */
	private void processMacroDefinition(Macro newMacro)
			throws PreprocessorException {
		String name = newMacro.getName();
		Macro oldMacro = macroMap.get(name);

		if (oldMacro != null) {
			if (!oldMacro.equals(newMacro))
				throw new PreprocessorException(
						"Attempt to redefine macro in new way: " + newMacro
								+ "\nOriginal defintion was at: "
								+ oldMacro.getDefinitionNode());
		} else {
			macroMap.put(name, newMacro);
		}
		jumpNextNode();
	}

	/**
	 * Processes a "#error" node. Always throws an exception with a message
	 * formed from the error node's list of tokens.
	 * 
	 * @param errorNode
	 *            a node of type "#error"
	 * @throws PreprocessorException
	 *             always, with a message formed from the #error line's tokens
	 */
	private void processError(Tree errorNode) throws PreprocessorException {
		String message = "Preprocessor #error directive encountered:\n";
		int numChildren = errorNode.getChildCount();
		Token errorToken = ((CommonTree) errorNode).getToken();
		Token betterErrorToken = tokenFactory.newCivlcToken(errorToken,
				getIncludeHistory());

		for (int i = 0; i < numChildren; i++) {
			Tree child = errorNode.getChild(i);
			String text = child.getText();

			message += text;
		}
		throw new PreprocessorException(message, betterErrorToken);
	}

	private void processIf(Tree ifNode) throws PreprocessorException {
		CommonTree expressionNode = (CommonTree) ifNode.getChild(0);
		CivlcToken first, expandedFirst;
		TokenSource source;
		int result;

		assert expressionNode.getType() == PreprocessorParser.EXPR;
		// form a list of new non-whitespace tokens from the expression node...
		first = nonWhiteSpaceTokenListFromChildren(expressionNode);
		// expand all macro invocations in the expression...
		expandedFirst = expandList(first).left;
		// form a TokenSource from this list...

		// TODO: somehow the line number is not right. It is set to one.

		source = TokenUtils.makeTokenSourceFromList(expandedFirst);
		// evaluate to get integer result...
		result = expressionAnalyzer.evaluate(source);
		// move to the appropriate point based on result...
		processConditional(ifNode, result != 0);
	}

	private void processIfdef(Tree ifdefNode) {
		processDefOrNdefNode(ifdefNode, true);
	}

	private void processIfndef(Tree ifndefNode) {
		processDefOrNdefNode(ifndefNode, false);
	}

	private void processDefOrNdefNode(Tree node, boolean isIfDef) {
		String macroName = node.getChild(0).getText();
		Macro macro = macroMap.get(macroName);
		boolean trueBranch = (isIfDef ? macro != null : macro == null);

		processConditional(node, trueBranch);
	}

	private void processConditional(Tree node, boolean takeTrueBranch) {
		if (takeTrueBranch) {
			Tree next = node.getChild(1); // TRUE_BRANCH node

			if (next.getChildCount() > 0)
				setNextInputNode(next.getChild(0));
			else
				jumpNextNode();
		} else if (node.getChildCount() > 2) {
			Tree next = node.getChild(2);

			if (next.getChildCount() > 0)
				setNextInputNode(next.getChild(0));
			else
				jumpNextNode();
		} else
			jumpNextNode();
	}

	/**
	 * Given a node in the tree, this method creates a list of new CTokens
	 * formed from children of the given node. It returns the first element in
	 * the list. White space tokens (including new lines) are filtered out.
	 * 
	 * @param root
	 *            a node in the AST of a preprocessor source file
	 * @return the first node in a list of new CTokens formed from the children
	 *         of root, or null if the root has 0 children
	 * @throws PreprocessorException
	 *             if one of the children has a null token
	 */
	private CivlcToken nonWhiteSpaceTokenListFromChildren(CommonTree root)
			throws PreprocessorException {
		int numChildren = root.getChildCount();
		CivlcToken first = null, prev = null;

		for (int i = 0; i < numChildren; i++) {
			Token token = ((CommonTree) root.getChild(i)).getToken();

			if (token == null)
				throw new PreprocessorException(
						"Encountered null token as child " + i + " of node "
								+ root);
			if (!PreprocessorUtils.isWhiteSpace(token)) {
				CivlcToken newToken = tokenFactory.newCivlcToken(token,
						getIncludeHistory());

				if (prev == null)
					first = newToken;
				else
					prev.setNext(newToken);
				prev = newToken;
			}
		}
		return first;
	}

	/**
	 * Processes a #include directive. Locates the file by searching the
	 * appropriate paths, parses it, creates a source file info for it and
	 * pushes it onto the sourceStack.
	 * 
	 * @param includeNode
	 *            node in source tree of type PINCLUDE
	 * @throws PreprocessorException
	 *             if the file can't be found, or if it does not conform to the
	 *             Preprocessor grammar
	 */
	private void processInclude(Tree includeNode) throws PreprocessorException {
		Token filenameToken = ((CommonTree) includeNode.getChild(0)).getToken();
		String fullName = filenameToken.getText();
		int numChars = fullName.length();
		String name;
		boolean system;
		PreprocessorSourceFileInfo newInfo;
		int firstChar, lastChar;

		if (numChars < 3)
			throw new PreprocessorException("Improper file name in #include: "
					+ fullName, filenameToken);
		firstChar = fullName.charAt(0);
		lastChar = fullName.charAt(numChars - 1);
		if (firstChar == '<') {
			if (lastChar != '>')
				throw new PreprocessorException(
						"Improper file name in #include: " + fullName,
						filenameToken);
			name = fullName.substring(1, numChars - 1);
			system = true;
		} else if (firstChar == '"') {
			if (lastChar != '"')
				throw new PreprocessorException(
						"Improper file name in #include: " + fullName,
						filenameToken);
			name = fullName.substring(1, numChars - 1);
			system = false;
		} else {
			throw new PreprocessorException("Improper file name in #include: "
					+ fullName, filenameToken);
		}
		try {
			CivlcToken amplifiedFilenameToken = tokenFactory.newCivlcToken(
					filenameToken, getIncludeHistory());

			newInfo = findInclude(amplifiedFilenameToken, name, system);
		} catch (IOException e) {
			throw new PreprocessorException(
					"I/O error when attempting to include " + name + ":\n" + e,
					filenameToken);
		} catch (RecognitionException e) {
			throw new PreprocessorException(
					"Preprocessor could not parse included file " + name
							+ ":\n" + e, filenameToken);
		}
		if (newInfo == null)
			throw new PreprocessorException(
					"Cannot find included file " + name, filenameToken);
		sourceStack.push(newInfo);
	}

	/**
	 * Locates an include file, parses it, and creates a
	 * PreprocessorSourceFileInfo record for it.
	 * 
	 * @param filenameToken
	 *            the token in the #include line in the original source file
	 *            with the name of the file, used for error reporting
	 * @param filename
	 *            the name of the file, as extracted from the token
	 * @param system
	 *            true if angular brackes were used around the filename in the
	 *            #include directive, false if double quotes were used
	 * @return the PreprocessorSourceFileInfo record for the parsed file
	 * @throws IOException
	 *             if something goes wrong trying to read or open the file
	 * @throws RecognitionException
	 *             if the file does not conform to the Preprocessor grammar
	 * @throws PreprocessorException
	 *             if some other syntax error occurs in processing the file
	 */
	private PreprocessorSourceFileInfo findInclude(CivlcToken filenameToken,
			String filename, boolean system) throws IOException,
			RecognitionException, PreprocessorException {
		File file = null;
		CharStream charStream;
		Tree tree;
		PreprocessorParser parser;
		PreprocessorLexer lexer;
		int numErrors;

		if (!system) {
			// first look in dir containing current file, then
			// user's include paths
			File currentDir = sourceStack.peek().getFile().getFile()
					.getParentFile();

			file = new File(currentDir, filename);
			if (!file.isFile())
				file = worker.findFile(userIncludePaths, filename);
		}
		if (file == null)
			file = worker.findFile(systemIncludePaths, filename);
		if (file == null) {
			// last but not least: look internally in the class path
			// directories:
			charStream = worker.findInternalSystemFile(filename);
			if (charStream == null)
				return null;
			file = new File(filename);
		} else {
			charStream = PreprocessorUtils.newFilteredCharStreamFromFile(file);
		}
		lexer = new PreprocessorLexer(charStream);
		parser = new PreprocessorParser(new CommonTokenStream(lexer));
		file_return fileReturn = parser.file();
		numErrors = parser.getNumberOfSyntaxErrors();
		if (numErrors != 0)
			throw new PreprocessorException(numErrors
					+ " syntax errors occurred while scanning included file "
					+ file);
		tree = (Tree) fileReturn.getTree();
		addEofNodeToTree(tree, filename);
		return new PreprocessorSourceFileInfo(tokenFactory.newInclusion(
				getOrMakeSourceFile(file, false), filenameToken), parser, tree,
				tree.getChild(0));
	}

	/**
	 * Processes a #pragma node. For now, the whole pragma is just going to be
	 * sent to the output stream. Macro replacement will take place in the
	 * pragma tokens as usual.
	 * 
	 * This method sends the #pragma node to the output list, and moves the
	 * current position to the first child (or the next token if there are no
	 * children).
	 * 
	 * It sets inPragma to true. This is so that when the newline is reached
	 * that terminates the pragma, that newline will not have its channel set to
	 * the hidden channel. Hence the newline will be visible to an ANTLR parser
	 * that consumes from this source. The newline is necessary to know where
	 * the pragma ends.
	 * 
	 * @param pragmaNode
	 *            A #pragma node in the preprocessor tree
	 * @throws PreprocessorException
	 */
	private void processPragma(Tree pragmaNode) throws PreprocessorException {
		Token token = ((CommonTree) pragmaNode).getToken();
		CivlcToken pragmaToken = tokenFactory.newCivlcToken(token, getIncludeHistory());

		addOutput(pragmaToken);
		inTextBlock = true; // don't have to check for directives
		inPragma = true;
		incrementNextNode();
	}

	/**
	 * Processes a "#undef" node. This node has 1 child, which is the identifier
	 * of the macro which is to be undefined. This removes the macro from the
	 * macroMap. According to C11 Sec. 6.10.3.5.2, the operation is just ignored
	 * if the macro is not already defined, so this cannot lead to an error.
	 * 
	 * @param undefNode
	 *            the #undef node
	 */
	private void processUndef(Tree undefNode) {
		Tree identifierNode = undefNode.getChild(0);
		String name = identifierNode.getText();

		macroMap.remove(name);
		jumpNextNode();
	}

	/**
	 * Ignoring all non-directives for now.
	 * 
	 * @param nondirectiveNode
	 */
	private void processNondirective(Tree nondirectiveNode) {
		// ignoring all nondirectives for now
		jumpNextNode();
	}

	/**
	 * Process a #line directive.
	 * 
	 * Ignored, for now.
	 * 
	 * @param lineNode
	 */
	private void processLine(Tree lineNode) {
		jumpNextNode();
	}

	// Utility methods...

	private static boolean isConditional(CommonTree node) {
		Token token = node.getToken();

		if (token == null)
			return false;
		else {
			int type = token.getType();

			return type == PreprocessorParser.PIF
					|| type == PreprocessorParser.PIFDEF
					|| type == PreprocessorParser.PIFNDEF
					|| type == PreprocessorParser.PELIF;
		}
	}

	/**
	 * Returns next input tree node, or null if end of file has been reached.
	 * Does not modify anything. This is the nextNode field for top element of
	 * fileStack. reads: fileStack
	 * 
	 * @return
	 */
	private Tree getNextInputNode() {
		if (sourceStack.isEmpty())
			return null;
		return sourceStack.peek().getPosition();
	}

	private void setNextInputNode(Tree node) {
		sourceStack.peek().setPosition(node);
	}

	/**
	 * Move next node to next node in Tree in DFS order, or null if at last
	 * node.
	 * 
	 * When backtracking through a conditional node, this method will skip over
	 * the alternative branch. In other words, if we start in the "true" branch
	 * and then backtrack, we will NOT go down the false branch. This is because
	 * we only want to traverse one of the two branches when we preprocess a
	 * file.
	 * 
	 * The inTextBlock flag is turned off when we exit a block.
	 * 
	 * If given null this method is a no-op. If we are at the last node, it
	 * returns null. It should never throw an exception.
	 */
	private void incrementNextNode() {
		Tree node = getNextInputNode();

		if (node != null) {
			if (node.getChildCount() > 0)
				setNextInputNode(node.getChild(0));
			else
				jumpNextNode();
		}
	}

	/**
	 * Move next node to the next sibling. If there is no next sibling, proceed
	 * as in DFS. In other words, this is the same as DFS after removing all
	 * children of the current next node.
	 * 
	 * When backtracking through a conditional node, this method will skip over
	 * the alternative branch. In other words, if we start in the "true" branch
	 * and then backtrack, we will NOT go down the false branch. This is because
	 * we only want to traverse one of the two branches when we preprocess a
	 * file.
	 * 
	 * The inTextBlock flag is turned off when we exit a block.
	 * 
	 * If given null this method is a no-op. If there is no node to jump to, it
	 * returns null. It should never throw an exception.
	 */
	private void jumpNextNode() {
		CommonTree node = (CommonTree) getNextInputNode();

		if (node != null) {
			while (true) {
				int index = node.getChildIndex() + 1;

				node = (CommonTree) node.getParent();
				if (node == null)
					break;
				if (!isConditional(node) && index < node.getChildCount()) {
					// move to next sibling
					node = (CommonTree) node.getChild(index);
					break;
				}
				// a nontrivial backtrack is taking place
				// if you were in a TEXT_BLOCK or PRAGMA, now you're not
				if (inTextBlock) {
					inTextBlock = false;
				}
				if (inPragma) {
					inPragma = false;
				}
			}
			setNextInputNode(node);
		}
	}

	// /**
	// * Returns the token for node that follows the next node in DFS order, or
	// * null if there is no such node.
	// *
	// * @return the token of the node that follows the next node
	// */
	// private Token peek() {
	// CommonTree node = (CommonTree) getSuccessorNode(getNextInputNode());
	//
	// if (node == null)
	// return null;
	// return node.getToken();
	// }

	// /**
	// * Determines whether the token that follows the next node in DFS order
	// has
	// * the given type. If the token is null, returns false.
	// *
	// * @param tokenType
	// * a token type
	// * @return true iff the token of the node that follows the next node has
	// * type tokenType
	// */
	// private boolean peekAheadHasType(int tokenType) {
	// Token token = peek();
	//
	// return token != null && token.getType() == tokenType;
	// }

	private boolean peekAheadSkipWSHasType(int tokenType) {
		CommonTree node = (CommonTree) getSuccessorNode(getNextInputNode());

		while (node != null) {
			Token token = node.getToken();

			if (!PreprocessorUtils.isWhiteSpace(token)) {
				return token != null && token.getType() == tokenType;
			}
			node = (CommonTree) getSuccessorNode(node);
		}
		return false;
	}

	/**
	 * Returns the node that follows the given node in DFS order without
	 * modifying the state. Alternative conditional branches are skipped, as
	 * usual. It is useful for peeking ahead.
	 * 
	 * @param node
	 *            any node in the tree.
	 * @return the next node in the DFS traversal
	 */
	private Tree getSuccessorNode(Tree node) {
		if (node == null)
			return null;
		else {
			int numChildren = node.getChildCount();

			if (numChildren > 0)
				return node.getChild(0);
			while (true) {
				int index = node.getChildIndex() + 1;

				node = node.getParent();
				if (node == null)
					return null;
				if (!isConditional((CommonTree) node)
						&& index < node.getChildCount()) {
					return node.getChild(index);
				}
			}
		}
	}

	private Formation getIncludeHistory() {
		return sourceStack.peek().getIncludeHistory();
	}

	private boolean inTextBlock() {
		return inTextBlock;
	}

	// Methods modifying the output list...

	/**
	 * Adds a single token to output buffer.
	 * 
	 * @param token
	 *            a token to add to output buffer
	 * @throws PreprocessorException
	 */
	private void addOutput(CivlcToken token) throws PreprocessorException {
		int type = token.getType();

		// The string literals will be separated by some white
		// space tokens, and this would break the concatenation here, so...

		// if this is white space (other than \n at end of #pragma)
		// and stringLiteralBuffer is not empty, add the token
		// to the string literal buffer and return.

		// string literal buffer will consists of string literal token
		// followed by sequence of white space and string literal tokens.

		// process string literal buffer: result will be a single
		// string literal token and a sequence of white space tokens
		// which must be added to the output stream in that order.

		if (type == PreprocessorParser.STRING_LITERAL) {
			// first remove any white space tokens at the end of the list
			while (!stringLiteralBuffer.isEmpty()
					&& PreprocessorUtils.isWhiteSpace(stringLiteralBuffer
							.getLast()))
				stringLiteralBuffer.removeLast();
			stringLiteralBuffer.add(token);
			return;
		}
		if (!stringLiteralBuffer.isEmpty()) {
			if (PreprocessorUtils.isWhiteSpace(token)
					&& !(inPragma && type == PreprocessorParser.NEWLINE)) {
				stringLiteralBuffer.add(token);
				return;
			} else {
				List<CivlcToken> pureStringTokens = new LinkedList<>();
				List<CivlcToken> extraWhiteSpaces = new LinkedList<>();

				for (CivlcToken stringToken : stringLiteralBuffer) {
					if (PreprocessorUtils.isWhiteSpace(stringToken))
						extraWhiteSpaces.add(stringToken);
					else
						pureStringTokens.add(stringToken);
				}
				stringLiteralBuffer.clear();
				try {
					StringToken result;

					if (pureStringTokens.size() != 1) {
						result = tokenFactory.newStringToken(pureStringTokens);
					} else {
						result = tokenFactory.newStringToken(pureStringTokens
								.get(0));
					}
					addOutputHelper(result);
				} catch (SyntaxException e) {
					throw new PreprocessorException(e.getMessage(),
							pureStringTokens.get(0));
				}
				for (CivlcToken ws : extraWhiteSpaces)
					addOutputHelper(ws);
			}
		}
		addOutputHelper(token);
	}

	private void addOutputHelper(CivlcToken token) throws PreprocessorException {
		int type = token.getType();

		if (type == PreprocessorParser.CHARACTER_CONSTANT) {
			try {
				token = tokenFactory.characterToken(token);
			} catch (SyntaxException e) {
				throw new PreprocessorException(e.getMessage(), e.getSource()
						.getFirstToken());
			}
		} else if (PreprocessorUtils.isWhiteSpace(token)
				&& !(inPragma && type == PreprocessorParser.NEWLINE))
			token.setChannel(Token.HIDDEN_CHANNEL);
		token.setIndex(outputTokenCount);
		if (saveTokens)
			theTokens.add(token);
		outputTokenCount++;
		if (firstOutput == null) {
			firstOutput = lastOutput = token;
		} else {
			lastOutput.setNext(token);
			token.setNext(null);
			lastOutput = token;
		}
	}

	private void addOutputList(Pair<CivlcToken, CivlcToken> list)
			throws PreprocessorException {
		CivlcToken previous = null, current = list.left;

		while (current != null) {
			previous = current;
			current = current.getNext();
			addOutput(previous);
		}
	}

	/**
	 * Creates a new CToken from the give Tree node and adds the token to the
	 * end of the output list.
	 * 
	 * @param node
	 *            a CommonTree node
	 * @throws PreprocessorException
	 */
	private void shiftToOutput(Tree node) throws PreprocessorException {
		Token token = ((CommonTree) node).getToken();
		CivlcToken output = tokenFactory.newCivlcToken(token, getIncludeHistory());

		addOutput(output);
	}

	/**
	 * Removes a token from the front of the output list.
	 * 
	 * @return the first token, i.e., the one removed
	 */
	private CivlcToken removeOutput() {
		CivlcToken result = firstOutput;

		if (result == null)
			throw new PreprocessorRuntimeException(
					"Internal error: no output to remove");
		firstOutput = result.getNext();
		if (firstOutput == null)
			lastOutput = null;
		return result;
	}

	@Override
	public Collection<SourceFile> getSourceFiles() {
		return sourceFiles;
	}

	@Override
	public String toString() {
		return originalSourceFile.getName();
	}

}

class MacroDefinedPredicate implements StringPredicate {
	private Map<String, Macro> macroMap;

	MacroDefinedPredicate(Map<String, Macro> macroMap) {
		this.macroMap = macroMap;
	}

	@Override
	public boolean holds(String string) {
		return macroMap.containsKey(string);
	}
}
