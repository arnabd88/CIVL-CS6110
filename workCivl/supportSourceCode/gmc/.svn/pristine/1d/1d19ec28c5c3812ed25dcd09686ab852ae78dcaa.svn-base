package edu.udel.cis.vsl.gmc;

import java.util.Arrays;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.gmc.Option.OptionType;

public class ParserTest {

	private static Option option1;

	private static Option option2;

	private static Option option3;

	private CommandLineParser parser;

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
		option1 = Option.newScalarOption("verbose", OptionType.BOOLEAN,
				"print verbose output", false);
		option2 = Option.newScalarOption("errBound", OptionType.INTEGER,
				"bound on number of errors logged before quitting", 10);
		option3 = Option.newMapOption("input",
				"specify initial value of input variable");
	}

	@Before
	public void setUp() throws Exception {
		parser = new CommandLineParser(Arrays.asList(option1, option2, option3));
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void print() {
		parser.printUsage(System.out);
	}

	@Test
	public void parse1() throws CommandLineException {
		GMCConfiguration config = parser.parse(Arrays.asList("-errBound=2",
				"-inputX=10", "-inputY=20", "foo.c"));

		config.print(System.out);
	}
}
