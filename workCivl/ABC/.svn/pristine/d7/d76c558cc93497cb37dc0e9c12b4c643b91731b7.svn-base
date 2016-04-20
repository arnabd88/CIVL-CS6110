package edu.udel.cis.vsl.abc.front.c.preproc;

import java.io.PrintStream;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.antlr.runtime.TokenSource;
import org.antlr.runtime.TokenStream;
import org.antlr.runtime.tree.CommonTree;

import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorExpressionException;
import edu.udel.cis.vsl.abc.util.IF.StringPredicate;

/**
 * A class for parsing conditional expressions in preprocessor conditionals
 * after macro expansion has taken place. The resulting expression should be an
 * integer expression using literals. Any identifiers are interpreted as 0.
 * 
 * @author Stephen F. Siegel, University of Delaware, All rights reserved
 */
public class PreprocessorExpressionAnalyzer {

	/**
	 * A predicate on strings which returns true on string s iff there is a
	 * macro named s which is defined. This is needed in order to evaluate
	 * subexpressions of the form "defined(X)".
	 */
	private StringPredicate macroDefinedPredicate;

	/**
	 * Create a new expression analyzer using the given predicate to determine
	 * which macros are defined. The analyzer can be used to evaluate multiple
	 * expressions.
	 * 
	 * @param macroDefinedPredicate
	 *            a predicate on strings which returns true on string s iff
	 *            there is a macro named s which is defined. This is needed in
	 *            order to evaluate subexpressions of the form "defined(X)".
	 */
	public PreprocessorExpressionAnalyzer(StringPredicate macroDefinedPredicate) {
		this.macroDefinedPredicate = macroDefinedPredicate;
	}

	/**
	 * Creates a new expression analyzer, assuming that no macros are defined.
	 * Hence "defined(X)" will always return false. Useful mostly for simple
	 * tests.
	 */
	public PreprocessorExpressionAnalyzer() {
		this(new StringPredicate() {
			@Override
			public boolean holds(String string) {
				return false;
			}
		});
	}

	public void spewString(PrintStream out, String string)
			throws PreprocessorException {
		CharStream stream = new ANTLRStringStream(string);
		PreprocessorLexer cppLexer = new PreprocessorLexer(stream);

		cppLexer.inCondition = true;
		PreprocessorUtils.printTokenSource(out, cppLexer);
	}

	/**
	 * Given a source of tokens that form a preprocessor expression, this method
	 * parses the source to form an AST of the expression, returning the root
	 * node. The incoming tokens must not include white space tokens. They may
	 * not include any macro invocations, although subexpressions of the form
	 * "defined(X)" are fine; for those subexpressions the macroDefinedPredicate
	 * will be used.
	 * 
	 * @param tokenSource
	 * @return root of AST of parsed expression
	 * @throws PreprocessorExpressionException
	 */
	public CommonTree parse(TokenSource tokenSource)
			throws PreprocessorExpressionException {
		try {
			TokenStream stream = new CommonTokenStream(tokenSource);
			PreprocessorExpressionParser parser = new PreprocessorExpressionParser(
					stream);
			CommonTree tree = (CommonTree) parser.start().getTree();
			int numParseErrors = parser.getNumberOfSyntaxErrors();

			if (numParseErrors > 0)
				throw new PreprocessorExpressionException(
						"There were syntax errors while parsing expression.");
			return tree;
		} catch (RecognitionException e) {
			// This is thrown by parser.start(). I don't know
			// what input would cause it to get thrown or if it is even
			// possible...
			throw new PreprocessorExpressionException(e.getMessage());
		} catch (RuntimeException e) {
			throw new PreprocessorExpressionException(e.getMessage());
		}
	}

	public CommonTree parse(String expressionString)
			throws PreprocessorExpressionException {
		CharStream stream = new ANTLRStringStream(expressionString);
		PreprocessorLexer cppLexer = new PreprocessorLexer(stream);

		cppLexer.inCondition = true;

		TokenSource source = PreprocessorUtils.filterWhiteSpace(cppLexer);
		CommonTree result = parse(source);
		int numErrors = cppLexer.getNumberOfSyntaxErrors();

		if (numErrors > 0)
			throw new PreprocessorExpressionException(
					"There were syntax errors when scanning expression: "
							+ expressionString);
		return result;
	}

	/**
	 * Given an AST for a preprocessor expression (produced by the
	 * PreprocessorExpressionParser), this method evaluates the expression,
	 * returning the integer value.
	 * 
	 * @param tree
	 * @return
	 * @throws PreprocessorExpressionException
	 */
	private int evaluate(CommonTree tree)
			throws PreprocessorExpressionException {
		CommonTree node = (CommonTree) tree;
		Token token = node.getToken();
		int type = token.getType();

		if (PreprocessorUtils.isPpNumber(token)) {
			String text = token.getText();

			return PreprocessorUtils.convertStringToInt(text);
		} else if (PreprocessorUtils.isIdentifier(token)) {
			return 0;
			// issue warning?
		} else if (tree.getChildCount() == 1) {
			CommonTree child = (CommonTree) tree.getChild(0);

			if (type == PreprocessorLexer.DEFINED) {
				return macroDefinedPredicate.holds(child.getText()) ? 1 : 0;
			} else {
				int childValue = evaluate(child);

				if (type == PreprocessorLexer.SUB)
					return -childValue;
				else if (type == PreprocessorLexer.PLUS)
					return childValue;
				else if (type == PreprocessorLexer.NOT)
					return (childValue == 0 ? 1 : 0);
			}
		} else if (tree.getChildCount() == 2) {
			CommonTree child0 = (CommonTree) tree.getChild(0);
			CommonTree child1 = (CommonTree) tree.getChild(1);
			int value0 = evaluate(child0);

			if (type == PreprocessorLexer.PLUS)
				return value0 + evaluate(child1);
			else if (type == PreprocessorLexer.SUB)
				return value0 - evaluate(child1);
			else if (type == PreprocessorLexer.STAR)
				return value0 * evaluate(child1);
			else if (type == PreprocessorLexer.DIV)
				return value0 / evaluate(child1);
			else if (type == PreprocessorLexer.MOD)
				return value0 % evaluate(child1);
			else if (type == PreprocessorLexer.AND)
				return (value0 == 0 ? 0 : (evaluate(child1) == 0 ? 0 : 1));
			else if (type == PreprocessorLexer.OR)
				return (value0 != 0 ? 1 : (evaluate(child1) != 0 ? 1 : 0));
			else if (type == PreprocessorLexer.GT)
				return (value0 > evaluate(child1) ? 1 : 0);
			else if (type == PreprocessorLexer.GTE)
				return (value0 >= evaluate(child1) ? 1 : 0);
			else if (type == PreprocessorLexer.LT)
				return (value0 < evaluate(child1) ? 1 : 0);
			else if (type == PreprocessorLexer.LTE)
				return (value0 <= evaluate(child1) ? 1 : 0);
			else if (type == PreprocessorLexer.EQUALS)
				return (value0 == evaluate(child1) ? 1 : 0);
			else if (type == PreprocessorLexer.NEQ)
				return (value0 != evaluate(child1) ? 1 : 0);
		}
		throw new PreprocessorExpressionException(
				"Unknown expression in preprocessor: " + tree);
	}

	/**
	 * Given a (linear) source of tokens which form a preprocessor expression,
	 * this method parses and then evaluates the expression, returning the
	 * integer value. The token source must already have been macro expanded. It
	 * may contain white space (which will just be ignored). It may contain
	 * subexpressions of the form "defined(X)"; in those cases the
	 * macroDefinedPredicate associated to this PreprocessorExpressionAnalyzer
	 * will be used to evaluate the subexpression.
	 * 
	 * @param source
	 *            a source of preprocessor tokens that form a preprocessor
	 *            expression
	 * @return the result of evaluating the expression
	 * @throws PreprocessorExpressionException
	 */
	public int evaluate(TokenSource source)
			throws PreprocessorExpressionException {
		TokenSource filteredSource = PreprocessorUtils.filterWhiteSpace(source);
		CommonTree root = parse(filteredSource);
		int result = evaluate(root);

		return result;
	}

	/**
	 * Parses and evaluates an expression given as a string. Returns the integer
	 * value resulting from the evaluation.
	 * 
	 * @param string
	 *            a preprocessor expression expressed as a string
	 * @return the integer value of that expression
	 * @throws PreprocessorExpressionException
	 *             if the string is not a syntactically valid preprocess
	 *             expression
	 */
	public int evaluate(String string) throws PreprocessorExpressionException {
		return evaluate(parse(string));
	}

	/**
	 * This method is really just for testing. It takes one argument, a string.
	 * The string should be an (integer-valued) preproessor expression. It
	 * evaluates the expression and returns the result. It assumes no macros are
	 * defined, so any identifiers will be interpreted as 0.
	 * 
	 * @param args
	 *            array of length 1: a string which is the expression
	 * @throws PreprocessorException
	 *             if the string does not form a valid preprocessor expression
	 */
	public static void main(String[] args) throws PreprocessorException {
		PrintStream out = System.out;
		String expressionString = args[0];
		PreprocessorExpressionAnalyzer analyzer = new PreprocessorExpressionAnalyzer();
		int value = analyzer.evaluate(expressionString);

		out.println(value);
		out.flush();
	}
}
