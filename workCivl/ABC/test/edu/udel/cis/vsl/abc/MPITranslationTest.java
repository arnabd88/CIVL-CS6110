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
import edu.udel.cis.vsl.abc.program.IF.Program;

/**
 * Checks a number of simple C programs to make sure they pass on the parsing
 * and analysis stages, while also applying the prune and side-effect-free
 * transformations.
 * 
 * @author siegel
 * 
 */
public class MPITranslationTest {

	/**
	 * Turn on a lot of output for debugging? Set this to true only in your
	 * local copy. Be sure to set it back to false before committing!
	 */
	private static boolean debug = false;

	private static File root = new File(new File("examples"), "mpi");

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
			TranslationTask config = new TranslationTask(Language.CIVL_C, file);

			config.addAllTransformCodes(codes);
			fe.showTranslation(config);
		} else {
			Program p = fe.compileAndLink(new File[] { file }, Language.CIVL_C);

			p.applyTransformers(codes);
		}
	}

	@Test
	public void adder_par() throws ABCException, IOException {
		check("adder_par");
	}

	@Test
	public void datatype() throws ABCException, IOException {
		check("datatype");
	}

	@Test
	public void matmat_mw() throws ABCException, IOException {
		check("matmat_mw");
	}

	@Test
	public void mpi_pi_send() throws ABCException, IOException {
		check("mpi_pi_send");
	}

	@Test
	public void mpithreads_mpi() throws ABCException, IOException {
		check("mpithreads_mpi");
	}

	@Test
	public void reduce() throws ABCException, IOException {
		check("reduce");
	}

	@Test
	public void rowcol() throws ABCException, IOException {
		check("rowcol");
	}

	@Test
	public void ring1() throws ABCException, IOException {
		check("ring1");
	}

	@Test
	public void diffusion1d() throws ABCException, IOException {
		check("diffusion1d_spec_revision");
	}
}
