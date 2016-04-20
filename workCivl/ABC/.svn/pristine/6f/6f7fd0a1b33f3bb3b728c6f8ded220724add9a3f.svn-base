package edu.udel.cis.vsl.abc;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import org.junit.Test;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configurations;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.main.FrontEnd;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.transform.IF.Transform;

public class CompareTest {
	private static boolean debug = false;

	private File root = new File(new File("examples"), "compare");

	private PrintStream out = System.out;

	private static Configuration config = Configurations
			.newMinimalConfiguration();

	private static FrontEnd f = new FrontEnd(config);

	private void check(String filename0, String filename1) throws ABCException,
			IOException {
		File file0 = new File(root, filename0 + ".cvl"), file1 = new File(root,
				filename1 + ".cvl");
		Program program0, program1, compositeProgram;
		AST combinedAST;

		program0 = f.compileAndLink(new File[] { file0 }, Language.CIVL_C);
		if (debug)
			program0.prettyPrint(out);
		program1 = f.compileAndLink(new File[] { file1 }, Language.CIVL_C);
		if (debug)
			program1.prettyPrint(out);
		combinedAST = Transform.compareCombiner().combine(program0.getAST(),
				program1.getAST());
		if (debug)
			combinedAST.prettyPrint(out, false);
		compositeProgram = f.getProgramFactory(
				f.getStandardAnalyzer(Language.CIVL_C)).newProgram(combinedAST);
		if (debug)
			compositeProgram.prettyPrint(out);
	}

	@Test
	public void adder() throws ABCException, IOException {
		check("adder_spec", "adder_impl");
	}
}
