package edu.udel.cis.vsl.abc.front.c.preproc;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;

import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonToken;
import org.antlr.runtime.Token;
import org.antlr.runtime.TokenSource;

import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorExpressionException;
import edu.udel.cis.vsl.abc.util.IF.ANTLRUtils;

public class PreprocessorUtils {

	private static int identifierMinIndex, identifierMaxIndex;
	private static boolean[] identifierPredicate = initIdentifierPredicate();

	private static boolean[] initIdentifierPredicate() {
		int[] identifierIndexes = new int[] { PreprocessorLexer.AUTO,
				PreprocessorLexer.BREAK, PreprocessorLexer.CASE,
				PreprocessorLexer.CHAR, PreprocessorLexer.CONST,
				PreprocessorLexer.CONTINUE, PreprocessorLexer.DEFAULT,
				PreprocessorLexer.DO, PreprocessorLexer.DOUBLE,
				PreprocessorLexer.ELSE, PreprocessorLexer.ENUM,
				PreprocessorLexer.EXTERN, PreprocessorLexer.FLOAT,
				PreprocessorLexer.FOR, PreprocessorLexer.GOTO,
				PreprocessorLexer.IF, PreprocessorLexer.INLINE,
				PreprocessorLexer.INT, PreprocessorLexer.LONG,
				PreprocessorLexer.REGISTER, PreprocessorLexer.RESTRICT,
				PreprocessorLexer.RETURN, PreprocessorLexer.SHORT,
				PreprocessorLexer.SIGNED, PreprocessorLexer.SIZEOF,
				PreprocessorLexer.STATIC, PreprocessorLexer.STRUCT,
				PreprocessorLexer.SWITCH, PreprocessorLexer.TYPEDEF,
				PreprocessorLexer.UNION, PreprocessorLexer.UNSIGNED,
				PreprocessorLexer.VOID, PreprocessorLexer.VOLATILE,
				PreprocessorLexer.WHILE, PreprocessorLexer.ALIGNAS,
				PreprocessorLexer.ALIGNOF, PreprocessorLexer.ATOMIC,
				PreprocessorLexer.BOOL, PreprocessorLexer.COMPLEX,
				PreprocessorLexer.GENERIC, PreprocessorLexer.IMAGINARY,
				PreprocessorLexer.NORETURN, PreprocessorLexer.STATICASSERT,
				PreprocessorLexer.THREADLOCAL };
		boolean[] result;
		int length;
		int min = identifierIndexes[0], max = identifierIndexes[0];

		for (int index : identifierIndexes) {
			if (index < min)
				min = index;
			if (index > max)
				max = index;
		}
		length = max - min + 1;
		result = new boolean[length];
		for (int index : identifierIndexes)
			result[index - min] = true;
		identifierMinIndex = min;
		identifierMaxIndex = max;
		return result;
	}

	/**
	 * Is the token a preprocessor identifier. That would be any C identifier
	 * (type IDENTIFIER) or any C keyword.
	 * 
	 * @param token
	 *            any token
	 * @return true iff the token's type is either IDENTIFIER or any of the
	 *         types in the list of C keywords.
	 */
	public static boolean isIdentifier(Token token) {
		int type = token.getType();

		if (type == PreprocessorLexer.IDENTIFIER)
			return true;
		return type >= identifierMinIndex && type <= identifierMaxIndex
				&& identifierPredicate[type - identifierMinIndex];
	}

	public static boolean isPpNumber(Token token) {
		int type = token.getType();

		return type == PreprocessorLexer.INTEGER_CONSTANT
				|| type == PreprocessorLexer.FLOATING_CONSTANT
				|| type == PreprocessorLexer.PP_NUMBER;
	}

	/**
	 * Is the preprocessor token considered a white space token? Spaces, tabs,
	 * newlines, comments are all white space.
	 * 
	 * @param token
	 *            any token defined in the PreprocessorLexer
	 * @return true iff token is a form of white space
	 */
	public static boolean isWhiteSpace(Token token) {
		int type = token.getType();

		return type == PreprocessorLexer.WS
				|| type == PreprocessorLexer.COMMENT
				|| type == PreprocessorLexer.NEWLINE;
	}

	/**
	 * This convenience method transforms a TokenSource by filtering out the
	 * white space tokens. The TokenSource returned is equivalent to the given
	 * TokenSource, except that all white space tokens (spaces, tabs, newlines)
	 * have been removed.
	 * 
	 * @param oldSource
	 *            a token source that might have white space
	 * @return a new token source equivalent to old but with white space tokens
	 *         removed
	 */
	public static TokenSource filterWhiteSpace(final TokenSource oldSource) {
		TokenSource newSource = new TokenSource() {
			@Override
			public String getSourceName() {
				return oldSource.getSourceName();
			}

			@Override
			public Token nextToken() {
				while (true) {
					Token token = oldSource.nextToken();

					if (!isWhiteSpace(token))
						return token;
				}
			}
		};
		return newSource;
	}

	public static Integer convertStringToInt(String text)
			throws PreprocessorExpressionException {
		String stripped, root;
		// String suffix;
		int length = text.length();
		Integer result;

		while (length >= 1) {
			char c = text.charAt(length - 1);

			if (c != 'U' && c != 'u' && c != 'l' && c != 'L')
				break;
			length--;
		}
		stripped = text.substring(0, length);
		// TODO: do anything with suffix?
		// suffix = text.substring(length);
		try {
			if (stripped.startsWith("0")) {
				if (stripped.startsWith("0x") || stripped.startsWith("0X")) {
					// hexadecimal
					root = stripped.substring(2);
					result = Integer.parseInt(root, 16);
				} else {
					// octal
					result = Integer.parseInt(stripped, 8);
				}
			} else {
				// decimal
				result = Integer.valueOf(stripped);
			}
		} catch (NumberFormatException e) {
			throw new PreprocessorExpressionException(
					"Unable to extract integer value from " + text + ":\n" + e);
		}
		return result;
	}

	public static Double convertStringToDouble(String text)
			throws PreprocessorExpressionException {
		// TODO: fix
		return new Double(text);
	}

	/**
	 * Prints the stream of tokens emanating from a token source. Used mainly
	 * for debugging. Uses the tokens' "toString" method.
	 * 
	 * @param out
	 *            a print stream to which the output is sent
	 * @param source
	 *            any instance of TokenSource
	 * @throws PreprocessorException
	 *             if any exception is thrown while printing a token or getting
	 *             the next token. CommonToken's toString method can throw all
	 *             manner of exceptions
	 */
	public static void printTokenSource(PrintStream out, TokenSource source)
			throws PreprocessorException {
		try {
			CommonToken token;

			do {
				token = (CommonToken) source.nextToken();
				out.println(token.toString());
				out.flush();
			} while (token.getType() != PreprocessorLexer.EOF);
		} catch (RuntimeException e) {
			e.printStackTrace(System.err);
			throw new PreprocessorException(e.toString());
		}
	}

	public static void sourceTokenSource(PrintStream out, TokenSource source)
			throws PreprocessorException {
		try {
			CommonToken token;
			int type;

			while (true) {
				token = (CommonToken) source.nextToken();
				type = token.getType();
				if (type == PreprocessorParser.EOF)
					break;
				if (type == PreprocessorParser.COMMENT)
					out.print(" ");
				else
					out.print(token.getText());
				out.flush();
			}
		} catch (RuntimeException e) {
			e.printStackTrace(out);
			throw new PreprocessorException(e.getMessage());
		}
	}

	public static void source(PrintStream out, File file)
			throws PreprocessorException {
		try {
			ANTLRUtils.source(out, file);
		} catch (IOException e) {
			e.printStackTrace(out);
			throw new PreprocessorException(e.toString());
		}
	}

	public static CharStream newFilteredCharStreamFromFile(File file)
			throws IOException {
		return new FilteredANTLRFileStream(file);
	}

	public static CharStream newFilteredCharStreamFromResource(String name,
			String resource) throws IOException {
		InputStream inputStream = PreprocessorUtils.class
				.getResourceAsStream(resource);

		if (inputStream == null)
			return null;
		return new FilteredANTLRInputStream(name, inputStream);
	}

}
