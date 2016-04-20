package edu.udel.cis.vsl.abc.fortran;

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

public class SimpleFortranTest {
	/**
	 * Turn on a lot of output for debugging? Set this to true only in your
	 * local copy. Be sure to set it back to false before committing!
	 */
	private static boolean debug = false;

	private static File root = new File("examples/fortran/simple-test");

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
		File file = new File(root, filenameRoot + ".f");

		if (debug) {
			TranslationTask config = new TranslationTask(Language.FORTRAN77, file);

			config.addAllTransformCodes(codes);
			fe.showTranslation(config);
		} else {
			fe.compileAndLink(new File[] { file }, Language.FORTRAN77)
					.applyTransformers(codes);
		}
	}

	@Test
	public void simpleSample() throws ABCException, IOException {
		check("simpleSample");
	}
}
