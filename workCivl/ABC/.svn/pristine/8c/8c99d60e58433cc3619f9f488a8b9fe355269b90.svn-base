package edu.udel.cis.vsl.abc.preproc;

import static org.junit.Assert.assertEquals;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import org.antlr.runtime.CommonToken;
import org.antlr.runtime.Token;
import org.antlr.runtime.TokenSource;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorExpressionException;
import edu.udel.cis.vsl.abc.front.c.preproc.PreprocessorExpressionAnalyzer;
import edu.udel.cis.vsl.abc.front.c.preproc.PreprocessorExpressionParser;
import edu.udel.cis.vsl.abc.util.IF.StringPredicate;

/**
 * As the name suggests, these tests check the preprocessor expression analyzer,
 * used by the preprocessor to determine conditional values in conditional
 * directives.
 * 
 * @author siegel
 * 
 */
public class PreprocessorExpressionAnalyzerTest {

	/**
	 * An analyzer in which there are no defined macros.
	 */
	PreprocessorExpressionAnalyzer a1 = new PreprocessorExpressionAnalyzer();

	/**
	 * An analyzer with exactly 2 defined macros named "M1" and "M2".
	 */
	PreprocessorExpressionAnalyzer a2 = new PreprocessorExpressionAnalyzer(
			new StringPredicate() {
				@Override
				public boolean holds(String string) {
					return "M1".equals(string) || "M2".equals(string);
				}
			});

	/**
	 * Tests binary "+" is addition.
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testAdd1() throws PreprocessorExpressionException {
		assertEquals(3, a1.evaluate("1+2"));
	}

	/**
	 * Tests that the value of identifier which has not been defined is 0. This
	 * is what the C11 standard says to do.
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testUndefinedMacro() throws PreprocessorExpressionException {
		assertEquals(0, a1.evaluate("HELLO"));
		assertEquals(0, a2.evaluate("HELLO"));
	}

	/**
	 * Check the "defined" operator acts as expected in a variety of contexts.
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testDefined() throws PreprocessorExpressionException {
		assertEquals(0, a1.evaluate("defined(M1)"));
		assertEquals(1, a2.evaluate("defined(M1)"));
		assertEquals(1, a2.evaluate("defined(M2)"));
		assertEquals(0, a2.evaluate("defined(HELLO)"));
		assertEquals(1, a2.evaluate("defined M1"));
		assertEquals(0, a2.evaluate("defined HELLO"));
	}

	/**
	 * Tests unary minus applied to an expression yields the negative of the
	 * value of the expression.
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testNegative() throws PreprocessorExpressionException {
		assertEquals(-5, a1.evaluate("-(2+3)"));
	}

	/**
	 * Tests unary + is the identity.
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testPlus() throws PreprocessorExpressionException {
		assertEquals(5, a1.evaluate("+(2+3)"));
	}

	/**
	 * Tests ! applied to a non-zero number is 0.
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testNot1() throws PreprocessorExpressionException {
		assertEquals(0, a1.evaluate("!-5"));
	}

	/**
	 * Tests !0==1.
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testNot2() throws PreprocessorExpressionException {
		assertEquals(1, a1.evaluate("!0"));
	}

	/**
	 * Tests binary - is subtraction.
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testSubtraction() throws PreprocessorExpressionException {
		assertEquals(-1, a1.evaluate("2-3"));
	}

	/**
	 * Tests binary * is multiplication.
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testMultiplication() throws PreprocessorExpressionException {
		assertEquals(6, a1.evaluate("2*3"));
	}

	/**
	 * Tests / is integer division in case where numerator and denominator are
	 * both position and numerator is greater than denominator.
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testDivision1() throws PreprocessorExpressionException {
		assertEquals(2, a1.evaluate("7/3"));
	}

	/**
	 * Tests / is integer division in case where numerator and denominator are
	 * both positive and denominator is greater than nuemrator.
	 * 
	 * TODO: what if one or both are negative? Is C11 different from Java?
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testDivision2() throws PreprocessorExpressionException {
		assertEquals(0, a1.evaluate("2/3"));
	}

	/**
	 * Tests % is integer modulus.
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testModulus() throws PreprocessorExpressionException {
		assertEquals(1, a1.evaluate("7%3"));
	}

	/**
	 * Tests && is logical and.
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testAnd() throws PreprocessorExpressionException {
		assertEquals(1, a1.evaluate("10 && 5"));
		assertEquals(0, a1.evaluate("0 && 1"));
		assertEquals(0, a1.evaluate("-5 && 0"));
		assertEquals(0, a1.evaluate("0 && 0"));
	}

	/**
	 * Tests || is logical or.
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testOr() throws PreprocessorExpressionException {
		assertEquals(1, a1.evaluate("10 || 5"));
		assertEquals(1, a1.evaluate("0 || 1"));
		assertEquals(1, a1.evaluate("-5 || 0"));
		assertEquals(0, a1.evaluate("0 || 0"));
	}

	/**
	 * Test the comparators ==, !=, <, <=, >, >= in a variety of contexts on
	 * integer constants.
	 * 
	 * @throws PreprocessorExpressionException
	 *             never
	 */
	@Test
	public void testComparators() throws PreprocessorExpressionException {
		assertEquals(1, a1.evaluate("-5==-5"));
		assertEquals(0, a1.evaluate("1==2"));
		assertEquals(1, a1.evaluate("1!=2"));
		assertEquals(0, a1.evaluate("1!=1"));
		assertEquals(1, a1.evaluate("0<1"));
		assertEquals(0, a1.evaluate("-1<-2"));
		assertEquals(1, a1.evaluate("5<=5"));
		assertEquals(1, a1.evaluate("4<=5"));
		assertEquals(0, a1.evaluate("-1<=-2"));
		assertEquals(1, a1.evaluate("2>1"));
		assertEquals(0, a1.evaluate("1>1"));
		assertEquals(0, a1.evaluate("0>1"));
		assertEquals(1, a1.evaluate("0>=0"));
		assertEquals(1, a1.evaluate("-3>=-4"));
		assertEquals(0, a1.evaluate("0>=1"));
	}

	/**
	 * Tests an exception is thrown on invalid input.
	 * 
	 * @throws PreprocessorExpressionException
	 *             always
	 */
	@Test(expected = PreprocessorException.class)
	public void testBadInput1() throws PreprocessorExpressionException {
		a1.evaluate("*5");
	}

	@Test
	public void testSpewString() throws PreprocessorException {
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		PrintStream out = new PrintStream(baos);
		// CommonToken(CharStream input, int type, int channel, int start, int
		// stop)
		Token token = new CommonToken(null,
				PreprocessorExpressionParser.INTEGER_CONSTANT, 0, 0, 2);
		Token eof = new CommonToken(null, PreprocessorExpressionParser.EOF, 0,
				3, 3);
		String expected, result;

		token.setText("999");
		token.setLine(1);
		token.setCharPositionInLine(0);
		eof.setText("<EOF>");
		eof.setLine(1);
		eof.setCharPositionInLine(3);
		expected = token + "\n" + eof + "\n";
		a1.spewString(out, "999");
		result = new String(baos.toByteArray());
		assertEquals(expected, result);
	}

	@Test
	public void testMain() throws PreprocessorException {
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		PrintStream out = new PrintStream(baos);
		String expression = "1<2 && X==0 && (4!=3 || 1+1==2)";
		String result, expected = "1\n";

		System.setOut(out);
		PreprocessorExpressionAnalyzer.main(new String[] { expression });
		result = new String(baos.toByteArray());
		assertEquals(expected, result);
	}

	@Ignore
	@Test(expected = PreprocessorException.class)
	public void testParseError() throws PreprocessorException {
		TokenSource badSource1 = new TokenSource() {
			@Override
			public Token nextToken() {
				return new CommonToken(Token.EOF);
			}

			@Override
			public String getSourceName() {
				return "badSource";
			}
		};

		a1.parse(badSource1);
	}

	@Test(expected = PreprocessorException.class)
	public void testParseError2() throws PreprocessorException {
		a1.parse("\"x");
	}

}
