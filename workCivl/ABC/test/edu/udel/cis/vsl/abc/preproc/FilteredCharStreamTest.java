package edu.udel.cis.vsl.abc.preproc;

import static org.junit.Assert.assertEquals;

import java.io.IOException;
import java.io.PrintStream;

import org.antlr.runtime.CharStream;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.abc.front.c.preproc.FilteredANTLRFileStream;
import edu.udel.cis.vsl.abc.front.c.preproc.FilteredANTLRInputStream;

/**
 * Tests the removal of backslash-newline sequences from character streams in
 * the two classes {@link FilteredANTLRFileStream} and
 * {@link FilteredANTLRInputStream}.
 * 
 * @author siegel
 *
 */
public class FilteredCharStreamTest {

	private static boolean debug = false;

	private static PrintStream out = System.out;

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	private String filter(CharStream output) throws IOException {
		String result = "";
		int index0 = 0;

		while (index0 == output.index()) {
			int number = output.LA(1);
			char c = (char) number;

			if (number == CharStream.EOF)
				break;
			result += c;
			output.consume();
			index0++;
		}
		if (debug) {
			out.print("Output--->" + result + "<--");
			out.println(" (size=" + output.size() + ")");
			out.println();
		}
		return result;
	}

	String fileFilter(String original) throws IOException {
		return filter(new FilteredANTLRFileStream(original));
	}

	String streamFilter(String original, int chunkSize) throws IOException {
		return filter(new FilteredANTLRInputStream("test", original, chunkSize));
	}

	private void test(String expected, String original) throws IOException {
		if (debug) {
			out.print("Input---->" + original + "<--");
			out.println(" (size=" + original.length() + ")");
			out.println();
		}
		assertEquals(expected, fileFilter(original));
		assertEquals(expected, streamFilter(original, 1));
		assertEquals(expected, streamFilter(original, 2));
		assertEquals(expected, streamFilter(original, 8192));
	}

	@Test
	public void testNone() throws IOException {
		test("abc", "abc");
	}

	@Test
	public void testMiddle() throws IOException {
		test("ab", "a\\\nb");
	}

	@Test
	public void testBegin() throws IOException {
		test("ab", "\\\nab");
	}

	@Test
	public void testEnd() throws IOException {
		test("ab", "ab\\\n");
	}

	@Test
	public void testEmpty() throws IOException {
		test("", "\\\n");
	}

	@Test
	public void testDouble() throws IOException {
		test("ab", "a\\\n\\\nb");
	}

	@Test
	public void testBackslashOnly() throws IOException {
		test("a\\b", "a\\b");
	}

	@Test
	public void testNewlineOnly() throws IOException {
		test("a\nb", "a\nb");
	}

	@Test
	public void testDoubleBegin() throws IOException {
		test("x", "\\\n\\\nx");
	}
}
