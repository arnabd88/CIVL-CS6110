package edu.udel.cis.vsl.abc;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;

import org.junit.Test;

import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configurations;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.main.FrontEnd;
import edu.udel.cis.vsl.abc.program.IF.Program;

public class EquivASTTest {

	private static boolean debug = false;

	private static List<String> codes = Arrays.asList("prune", "sef");

	private File root = new File(new File("examples"), "equiv");

	private static Configuration config = Configurations
			.newMinimalConfiguration();

	private static FrontEnd f = new FrontEnd(config);

	private boolean isEquiv(String filenameRoot1, String filenameRoot2)
			throws ABCException, IOException {
		File file1 = new File(root, filenameRoot1 + ".c");
		File file2 = new File(root, filenameRoot2 + ".c");
		Program program1, program2;
		DifferenceObject diff;

		program1 = f.compileAndLink(new File[] { file1 }, Language.C);
		program1.applyTransformers(codes);

		program2 = f.compileAndLink(new File[] { file2 }, Language.C);
		program2.applyTransformers(codes);
		if (debug) {
			System.out.println("First program is: ");
			program1.prettyPrint(System.out);
			System.out.println("Second program is: ");
			program2.prettyPrint(System.out);
		}
		diff = program1.getAST().diff(program2.getAST());
		if (diff == null)
			return true;
		else {
			if (debug)
				diff.print(System.out);
			return false;
		}
	}

	@Test
	public void test1() throws ABCException, IOException {
		assertTrue(isEquiv("test1_0", "test1_1"));
	}

	@Test
	public void test2() throws ABCException, IOException {
		assertFalse(isEquiv("test2_0", "test2_1"));
	}

	@Test
	public void test3() throws ABCException, IOException {
		assertFalse(isEquiv("test3_0", "test3_1"));
	}

	@Test
	public void test4() throws ABCException, IOException {
		assertFalse(isEquiv("test4_0", "test4_1"));
	}
}
