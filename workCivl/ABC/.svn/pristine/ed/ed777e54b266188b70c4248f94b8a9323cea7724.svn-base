package edu.udel.cis.vsl.abc;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;

import org.junit.Test;

import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configurations;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.main.FrontEnd;
import edu.udel.cis.vsl.abc.main.TranslationTask;
import edu.udel.cis.vsl.abc.program.IF.Program;

public class ContractTest {

	private static boolean debug = false;

	private static List<String> codes = Arrays.asList("prune", "sef");

	private File root = new File(new File("examples"), "contract");

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
			Program p = f.compileAndLink(new File[] { file }, Language.CIVL_C);

			p.applyTransformers(codes);
			// p.prettyPrint(System.out);
		}
	}

	@Test
	public void por() throws ABCException, IOException {
		check("por");
	}

	@Test
	public void por2() throws ABCException, IOException {
		check("por2");
	}

	@Test
	public void contracts() throws ABCException, IOException {
		check("contracts");
	}
}
