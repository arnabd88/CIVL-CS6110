package edu.udel.cis.vsl.abc;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configurations;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.main.FrontEnd;
import edu.udel.cis.vsl.abc.main.TranslationTask;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * Checks a number of simple C programs to make sure they pass on the parsing
 * and analysis stages, while also applying the prune and side-effect-free
 * transformations.
 * 
 * @author siegel
 * 
 */
public class CTranslationTest {

	/**
	 * Turn on a lot of output for debugging? Set this to true only in your
	 * local copy. Be sure to set it back to false before committing!
	 */
	private static boolean debug = false;

	private static File root = new File("examples");

	private static List<String> codes = Arrays.asList("prune", "sef");

	private static Configuration config = Configurations
			.newMinimalConfiguration();

	private static FrontEnd fe = new FrontEnd(config);

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	private void check(String filenameRoot) throws ABCException, IOException {
		File file = new File(root, filenameRoot + ".c");

		if (debug) {
			TranslationTask config = new TranslationTask(Language.C, file);

			config.addAllTransformCodes(codes);
			fe.showTranslation(config);
		} else {
			fe.compileAndLink(new File[] { file }, Language.CIVL_C)
					.applyTransformers(codes);
		}
	}

	@Test
	public void constants() throws ABCException, IOException {
		check("constants");
	}

	@Test
	public void adder_seq() throws ABCException, IOException {
		check("adder_seq");
	}

	@Test
	public void useNull() throws ABCException, IOException {
		check("parse/useNull");
	}

	@Test
	public void pointer1() throws ABCException, IOException {
		check("parse/pointer1");
	}

	@Test
	public void pointer2() throws ABCException, IOException {
		check("parse/pointer2");
	}

	@Test
	public void varargs() throws ABCException, IOException {
		check("varargs");
	}

	@Test
	public void printf() throws ABCException, IOException {
		check("printf");
	}

	@Test
	public void compound() throws ABCException, IOException {
		check("compound");
	}

	@Test
	public void compound2() throws ABCException, IOException {
		check("compound2");
	}

	@Test
	public void enum1() throws ABCException, IOException {
		check("enum1");
	}

	@Test
	public void enum2() throws ABCException, IOException {
		check("enum2");
	}

	@Test(expected = ABCException.class)
	public void tagBad1() throws ABCException, IOException {
		check("tagBad1");
	}

	@Test
	public void tagGood1() throws ABCException, IOException {
		check("tagGood1");
	}

	@Test
	public void a2d() throws ABCException, IOException {
		check("a2d");
	}

	@Test
	public void labels() throws ABCException, IOException {
		check("labels");
	}

	@Test
	public void completeStruct() throws ABCException, IOException {
		check("completeStruct");
	}

	@Test
	public void forcomma() throws ABCException, IOException {
		check("forcomma");
	}

	@Test
	public void funcPointer() throws ABCException, IOException {
		check("funcPointer");
	}

	@Test
	public void comma() throws ABCException, IOException {
		check("comma");
	}

	@Test
	public void intChar() throws ABCException, IOException {
		check("c/intChar");
	}

	@Test(expected = ABCException.class)
	public void scanf() throws ABCException, IOException {
		check("c/scanf");
	}

	@Test
	public void fscanf() throws ABCException, IOException {
		check("c/fscanf");
	}

	@Test(expected = SyntaxException.class)
	public void printfBad() throws ABCException, IOException {
		check("c/printfBad");
	}

	@Test
	public void chars() throws ABCException, IOException {
		check("chars");
	}

	@Test
	public void struct() throws ABCException, IOException {
		check("c/struct");
	}

	@Test(expected = SyntaxException.class)
	public void assigns() throws ABCException, IOException {
		check("c/assigns");
	}

	@Test
	public void identifier() throws ABCException, IOException {
		check("c/ident");
	}

	@Test
	public void identifier2() throws ABCException, IOException {
		check("c/ident2");
	}
}
