package edu.udel.cis.vsl.abc.preproc;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.util.HashMap;
import java.util.Map;

import org.antlr.runtime.Token;
import org.antlr.runtime.TokenSource;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorRuntimeException;
import edu.udel.cis.vsl.abc.front.c.preproc.CPreprocessor;
import edu.udel.cis.vsl.abc.front.c.preproc.PreprocessorParser;
import edu.udel.cis.vsl.abc.front.c.preproc.PreprocessorUtils;
import edu.udel.cis.vsl.abc.token.IF.Macro;

public class PreprocessorTest {

	private static boolean debug = false;

	private static File root = new File(new File("examples"), "preproc");

	private static File dir1 = new File(root, "dir1");

	private static File dir11 = new File(dir1, "dir1.1");

	private static File dir2 = new File(root, "dir2");

	private static File[] systemIncludes = new File[] { dir2 };

	private static File[] userIncludes = new File[] { dir1, dir11 };

	private static Map<String, Macro> implicitMacros = new HashMap<>();

	private CPreprocessor p;

	@Before
	public void setUp() throws Exception {
		p = new CPreprocessor(null);
	}

	private void readSource(TokenSource source) throws PreprocessorException {
		try {
			while (true) {
				Token token = source.nextToken();

				if (token.getType() == PreprocessorParser.EOF)
					break;
			}
		} catch (PreprocessorRuntimeException e) {
			throw new PreprocessorException(e.toString());
		}
	}

	private void check(String rootName) throws PreprocessorException {
		File sourceFile = new File(root, rootName + ".txt");
		TokenSource source;

		if (debug)
			p.debug(systemIncludes, userIncludes, implicitMacros, System.out,
					sourceFile);
		source = p.outputTokenSource(systemIncludes, userIncludes,
				implicitMacros, sourceFile);
		readSource(source);
	}

	/**
	 * Compares the two token sources for equivalence modulo white space.
	 * 
	 * @param actualSource
	 * @param expectedSource
	 */
	private void compare(TokenSource actualSource, TokenSource expectedSource)
			throws PreprocessorException {
		try {
			while (true) {
				Token token1, token2;
				int type1, type2;

				do {
					token1 = actualSource.nextToken();
					type1 = token1.getType();
				} while (PreprocessorUtils.isWhiteSpace(token1));
				do {
					token2 = expectedSource.nextToken();
					type2 = token2.getType();
				} while (PreprocessorUtils.isWhiteSpace(token2));
				assertEquals(type2, type1);
				if (type1 == PreprocessorParser.EOF)
					break;
				assertEquals(token2.getText(), token1.getText());

			}
		} catch (PreprocessorRuntimeException e) {
			throw new PreprocessorException(e.toString());
		}
	}

	private void checkPair(String rootName) throws PreprocessorException {
		File sourceFile = new File(root, rootName + ".txt");
		File solutionFile = new File(root, rootName + ".sol.txt");

		if (debug)
			p.debug(systemIncludes, userIncludes, implicitMacros, System.out,
					sourceFile);

		TokenSource actualSource = p.outputTokenSource(systemIncludes,
				userIncludes, implicitMacros, sourceFile);
		TokenSource expectedSource = p.lexer(solutionFile);

		compare(actualSource, expectedSource);
	}

	@Test
	public void backslashNewline1() throws PreprocessorException {
		checkPair("backslashNewline1");
	}

	@Test
	public void backslashNewline2() throws PreprocessorException {
		checkPair("backslashNewline2");
	}

	@Test
	public void conditions1() throws PreprocessorException {
		checkPair("conditions1");
	}

	@Test
	public void conditions2() throws PreprocessorException {
		checkPair("conditions2");
	}

	@Test
	public void expressions() throws PreprocessorException {
		checkPair("expressions");
	}

	@Test
	public void nondirectives() throws PreprocessorException {
		checkPair("nondirectives");
	}

	@Test(expected = PreprocessorException.class)
	public void badIfTest() throws PreprocessorException {
		check("badIf");
	}

	@Test
	public void ifdef() throws PreprocessorException {
		checkPair("ifdef");
	}

	@Test
	public void objectMacros() throws PreprocessorException {
		checkPair("objectMacros");
	}

	@Test
	public void functionMacros() throws PreprocessorException {
		checkPair("functionMacros");
	}

	@Test
	public void functionMacros2() throws PreprocessorException {
		checkPair("functionMacros2");
	}

	/**
	 * One function macro invokes another function macro in its replacement
	 * list.
	 * 
	 * @throws PreprocessorException
	 */
	@Test
	public void functionMacros3() throws PreprocessorException {
		checkPair("functionMacros3");
	}

	/**
	 * One function macro invokes another function macro in its replacement
	 * list, and the second function macro has empty replacement list.
	 * 
	 * @throws PreprocessorException
	 */
	@Test
	public void functionMacros4() throws PreprocessorException {
		checkPair("functionMacros4");
	}

	@Test
	public void emptyMacros() throws PreprocessorException {
		checkPair("emptyMacros");
	}

	@Test
	public void selfRefMacros() throws PreprocessorException {
		checkPair("selfRefMacros");
	}

	/**
	 * Checks that an exception is thrown when a sequence of tokens that can be
	 * interpreted as a preprocessor directive occurs in an argument of a macro
	 * invocation. According to C11, the behavior in this case is undefined, so
	 * we choose to report it as error.
	 * 
	 * @throws PreprocessorException
	 *             always
	 */
	@Test(expected = PreprocessorException.class)
	public void badMacroArguments() throws PreprocessorException {
		check("badMacroArguments");
	}

	/**
	 * Checks that an exception occurs when a 0-argument function macro is
	 * invoked with an argument.
	 * 
	 * @throws PreprocessorException
	 *             always
	 */
	@Test(expected = PreprocessorException.class)
	public void badMacroArguments2() throws PreprocessorException {
		check("badMacroArguments2");
	}

	/**
	 * Checks that an exception occurs when a 0-argument function macro is
	 * invoked incorrectly, with an open '(' but no matching ')'.
	 * 
	 * @throws PreprocessorException
	 *             always
	 */
	@Test(expected = PreprocessorException.class)
	public void badMacroArguments3() throws PreprocessorException {
		check("badMacroArguments3");
	}

	/**
	 * Checks that an exception is thrown when a 1-argument function macro is
	 * invoked with 2 arguments.
	 * 
	 * @throws PreprocessorException
	 *             always
	 */
	@Test(expected = PreprocessorException.class)
	public void tooManyArguments() throws PreprocessorException {
		check("tooManyArguments");
	}

	/**
	 * Checks that #include directives work as expected, for both system
	 * includes and user includes.
	 * 
	 * @throws PreprocessorException
	 *             never
	 */
	@Test
	public void includes() throws PreprocessorException {
		checkPair("includes");
	}

	/**
	 * Checks that when a #error directive is processed, an exception is thrown.
	 * 
	 * @throws PreprocessorException
	 *             always
	 */
	@Test(expected = PreprocessorException.class)
	public void error() throws PreprocessorException {
		check("error");
	}

	/**
	 * This just tests that the pragma is preserved in the output, except that
	 * macro substitution does occur.
	 * 
	 * @throws PreprocessorException
	 *             never
	 */
	@Test
	public void pragmas() throws PreprocessorException {
		checkPair("pragmas");
	}

	/**
	 * Checks that #undef works as expected---results in the macro becoming
	 * undefined.
	 * 
	 * @throws PreprocessorException
	 *             never
	 */
	@Test
	public void undef() throws PreprocessorException {
		check("undef");
	}

	/**
	 * Checks that an error occurs if one attempts to re-define an object macro
	 * in a different way. See C11 Sec 6.10.3.
	 * 
	 * @throws PreprocessorException
	 *             always
	 */
	@Test(expected = PreprocessorException.class)
	public void badDef() throws PreprocessorException {
		check("badDef");
	}

	/**
	 * Checks that no error is generated when a macro is defined twice using
	 * identical definitions. See C11 Sec 6.10.3.
	 * 
	 * @throws PreprocessorException
	 *             never
	 */
	@Test
	public void doubleDef() throws PreprocessorException {
		check("doubleDef");
	}

	/**
	 * Checks that an error occurs if one attempts to #include a file that is
	 * not in any of the search paths.
	 * 
	 * @throws PreprocessorException
	 *             always
	 */
	@Test(expected = PreprocessorException.class)
	public void badInclude() throws PreprocessorException {
		check("badInclude");
	}

	/**
	 * Checks that an error occurs if one attempts to #include a file named "".
	 * 
	 * @throws PreprocessorException
	 *             always
	 */
	@Test(expected = PreprocessorException.class)
	public void badIncludeName() throws PreprocessorException {
		check("badIncludeName");
	}

	/**
	 * Checks that "#if 1" followed immediately by "#endif" yields nothing--when
	 * all alone.
	 * 
	 * @throws PreprocessorException
	 *             never
	 */
	@Test
	public void trivialConditional() throws PreprocessorException {
		checkPair("trivialConditional");
	}

	/**
	 * Checks that "#if 1" followed immediately by "#endif" yields nothing--when
	 * inserted in the middle of some lines.
	 * 
	 * @throws PreprocessorException
	 *             never
	 */
	@Test
	public void trivialConditional2() throws PreprocessorException {
		checkPair("trivialConditional2");
	}

	/**
	 * Checks that two adjacent string literals are concatenated.
	 * 
	 * @throws PreprocessorException
	 */
	@Test
	public void concat() throws PreprocessorException {
		checkPair("concat");
	}
}
