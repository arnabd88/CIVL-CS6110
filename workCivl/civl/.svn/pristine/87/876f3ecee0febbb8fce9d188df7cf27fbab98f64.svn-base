package edu.udel.cis.vsl.civl.bench;

import edu.udel.cis.vsl.abc.front.IF.ParseException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;

/**
 * java -classpath ${WORKING_DIR}/civl.jar:${WORKING_DIR}/bin
 * edu.udel.cis.vsl.civl.bench.VerifyMemoryTest $arg0 $arg1
 * 
 * where $arg0 is the full path to the test file and $arg1 is the number of
 * iteration, ${WORKING_DIR} is your CIVL directory.
 * 
 * @author zmanchun
 *
 */
public class VerifyMemoryTest {
	private static UserInterface ui = new UserInterface();

	public static void main(String[] args) throws SyntaxException,
			PreprocessorException, ParseException {
		String testFile = args[0];
		int n = Integer.parseInt(args[1]);

		for (int i = 0; i < n; i++) {
			System.out.println("i is " + i);
			ui.run("verify", "-svcomp", testFile);
		}
	}
}
