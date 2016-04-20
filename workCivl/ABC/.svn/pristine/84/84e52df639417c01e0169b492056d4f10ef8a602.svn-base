package edu.udel.cis.vsl.abc;

import static org.junit.Assert.assertTrue;

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
import edu.udel.cis.vsl.abc.program.IF.Program;

public class SideEffectRemoverTest {

	private static boolean debug = false;

	private static List<String> codes = Arrays.asList("prune", "sef");

	private File root = new File(new File("examples"), "side-effects");

	private static Configuration config = Configurations
			.newMinimalConfiguration();

	private static FrontEnd f = new FrontEnd(config);

	private void check(String filename) throws ABCException, IOException {
		File file = new File(root, filename);
		File outputFile = new File(root, "out_" + filename);
		Program program = f
				.compileAndLink(new File[] { file }, Language.CIVL_C);

		program.applyTransformers(codes);
		if (debug)
			program.prettyPrint(System.out);

		Program outputProgram = f.compileAndLink(new File[] { outputFile },
				Language.CIVL_C);
		boolean equiv = program.getAST().equiv(outputProgram.getAST());

		if (debug) {
			if (!equiv) {
				System.out.println(program.getAST()
						.diff(outputProgram.getAST()));
				outputProgram.prettyPrint(System.out);
			}
		}
		assertTrue(equiv);
	}

	@Test
	public void assign1() throws ABCException, IOException {
		check("assign1.c");
	}

	@Test
	public void assign2() throws ABCException, IOException {
		check("assign2.c");
	}

	@Test
	public void assign3() throws ABCException, IOException {
		check("assign3.c");
	}

	@Test
	public void comma() throws ABCException, IOException {
		check("comma.c");
	}

	@Test
	public void enums() throws ABCException, IOException {
		check("enums.c");
	}

	@Test
	public void for_se() throws ABCException, IOException {
		check("for-se.c");
	}

	@Test
	public void inc() throws ABCException, IOException {
		check("inc.c");
	}

	@Test
	public void recurse() throws ABCException, IOException {
		check("recurse.c");
	}

	@Test
	public void returns() throws ABCException, IOException {
		check("returns.c");
	}

	@Test
	public void types() throws ABCException, IOException {
		check("types.c");
	}

	@Test
	public void doWhile() throws ABCException, IOException {
		check("doWhile.c");
	}

	@Test
	public void cond() throws ABCException, IOException {
		check("cond.c");
	}

	@Test
	public void dereference() throws ABCException, IOException {
		check("dereference.c");
	}

	@Test
	public void stmtExpr() throws ABCException, IOException {
		check("stmtExpression.c");
	}

	@Test
	public void shortCircuit() throws ABCException, IOException {
		check("shortCircuit.c");
	}

	@Test
	public void loopShortCircuit() throws ABCException, IOException {
		check("loopShortCircuit.c");
	}

	@Test
	public void nestedLoop() throws ABCException, IOException {
		check("nestedLoop.c");
	}

}
