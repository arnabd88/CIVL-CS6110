package edu.udel.cis.vsl.abc;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configurations;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.front.IF.ParseException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.main.FrontEnd;
import edu.udel.cis.vsl.abc.token.IF.Macro;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * Tests the "copy" method in nodes, which performs deep cloning.
 * 
 * @author siegel
 * 
 */
public class CloneTest {

	private static File[] systemIncludes = new File[0];

	private static File[] userIncludes = new File[0];

	private static File root = new File("examples");

	private static Configuration config = Configurations
			.newMinimalConfiguration();

	private static FrontEnd fe = new FrontEnd(config);

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	private void check(String filenameRoot) throws PreprocessorException,
			ParseException, SyntaxException, IOException {
		AST ast1, ast2;
		SequenceNode<BlockItemNode> root1, root2;

		ast1 = fe.compile(new File(root, filenameRoot + ".c"), Language.C,
				systemIncludes, userIncludes, new HashMap<String, Macro>());
		root1 = ast1.getRootNode();
		root2 = root1.copy();
		ast2 = fe.getASTFactory().newAST(root2, ast1.getSourceFiles(),
				ast1.isWholeProgram());
		assertEquals(ast1.getNumberOfNodes(), ast2.getNumberOfNodes());
	}

	@Test
	public void adder_seq() throws PreprocessorException, ParseException,
			SyntaxException, IOException {
		check("adder_seq");
	}

	@Test
	public void useNull() throws PreprocessorException, ParseException,
			SyntaxException, IOException {
		check("parse/useNull");
	}

	@Test
	public void pointer1() throws PreprocessorException, ParseException,
			SyntaxException, IOException {
		check("parse/pointer1");
	}

	@Test
	public void pointer2() throws PreprocessorException, ParseException,
			SyntaxException, IOException {
		check("parse/pointer2");
	}
}
