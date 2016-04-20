package edu.udel.cis.vsl.civl.bench;

import java.io.File;
import java.util.Arrays;
import java.util.List;

import edu.udel.cis.vsl.abc.config.IF.Configurations;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.front.IF.ParseException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.main.FrontEnd;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * java -classpath ${WORKING_DIR}/civl.jar:${WORKING_DIR}/bin
 * edu.udel.cis.vsl.civl.bench.ParserMemoryTest $arg0 $arg1
 * 
 * where $arg0 is the full path to the test file and $arg1 is the number of
 * iteration, ${WORKING_DIR} is your CIVL directory.
 * 
 * @author zmanchun
 *
 */
public class ParserMemoryTest {
	private static Runtime runtime = Runtime.getRuntime();
	private static long mb = 1024 * 1024;
	private static FrontEnd frontEnd = new FrontEnd(
			Configurations.newMinimalConfiguration());
	private static List<String> codes = Arrays.asList("prune", "sef");

	public static void main(String[] args) throws SyntaxException,
			PreprocessorException, ParseException {
		File testFile = new File(args[0]);
		int n = Integer.parseInt(args[1]);

		for (int i = 0; i < n; i++) {
			System.out.println("i is " + i);
			frontEnd.compileAndLink(new File[] { testFile }, Language.CIVL_C)
					.applyTransformers(codes);
			System.gc();
			System.out.println("Number of types = "
					+ frontEnd.getASTFactory().getTypeFactory().getNumTypes());
			System.out.println("##### Heap utilization statistics [MB] #####");
			System.out.println("Used Memory:"
					+ (runtime.totalMemory() - runtime.freeMemory()) / mb);
			System.out.println("Free Memory:" + runtime.freeMemory() / mb);
			System.out.flush();
		}
	}
}
