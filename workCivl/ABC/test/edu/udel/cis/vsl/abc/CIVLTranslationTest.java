package edu.udel.cis.vsl.abc;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;

import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configurations;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.main.FrontEnd;
import edu.udel.cis.vsl.abc.main.TranslationTask;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

public class CIVLTranslationTest {

	private static boolean debug = false;

	private static List<String> codes = Arrays.asList("prune", "sef");

	private File root = new File(new File("examples"), "civl");

	private static Configuration config = Configurations
			.newMinimalConfiguration();

	private static FrontEnd f = new FrontEnd(config);

	private void check(String filenameRoot) throws ABCException, IOException {
		File file = new File(root, filenameRoot + ".cvl");

		if (debug) {
			TranslationTask config = new TranslationTask(Language.CIVL_C, file);

			config.addAllTransformCodes(codes);
			f.showTranslation(config);
		} else {
			f.compileAndLink(new File[] { file }, Language.CIVL_C)
					.applyTransformers(codes);
		}
	}

	@Test
	public void assertForall() throws ABCException, IOException {
		check("forall");
	}

	@Test
	public void spawn() throws ABCException, IOException {
		check("spawn");
	}

	@Test
	public void choose() throws ABCException, IOException {
		check("choose");
	}

	@Test
	public void duffs() throws ABCException, IOException {
		check("duffs");
	}

	@Test
	public void sideEffects() throws ABCException, IOException {
		check("sideEffects");
	}

	@Test
	public void malloc() throws ABCException, IOException {
		check("malloc");
	}

	// Ignoring because scope-qualified pointers are going away
	@Ignore
	@Test
	public void pointerScopes() throws ABCException, IOException {
		check("pointerScopes");
	}

	@Test
	public void atomicBlock() throws ABCException, IOException {
		check("atomicStatement");
	}

	@Test
	public void potentialBug() throws ABCException, IOException {
		check("potentialBug");
	}

	// ignoring because for now CIVL follows the C11 Standard
	// in that all functions have internal or external linkage
	@Test
	public void nestedFunctions() throws ABCException, IOException {
		check("nestedFunctions");
	}

	@Test
	public void domain() throws ABCException, IOException {
		check("domain");
	}

	@Test
	public void dollarFor() throws ABCException, IOException {
		check("dollarFor");
	}

	@Test
	public void parfor() throws ABCException, IOException {
		check("parfor");
	}

	@Test(expected = SyntaxException.class)
	public void parfor_bad() throws ABCException, IOException {
		check("parfor_bad");
	}

	@Test(expected = SyntaxException.class)
	public void parfor_bad2() throws ABCException, IOException {
		check("parfor_bad2");
	}

	@Test
	public void domainDecomp() throws ABCException, IOException {
		check("domainDecomposition");
	}

	@Test
	public void cond() throws ABCException, IOException {
		check("cond");
	}

	@Test
	public void externalDefs() throws ABCException, IOException {
		check("externaldefs");
	}
}
