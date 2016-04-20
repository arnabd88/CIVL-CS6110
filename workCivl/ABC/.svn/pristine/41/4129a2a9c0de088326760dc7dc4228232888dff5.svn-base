package edu.udel.cis.vsl.abc;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.util.HashMap;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.entity.IF.OrdinaryEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configurations;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.front.IF.ParseException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.main.FrontEnd;
import edu.udel.cis.vsl.abc.token.IF.Macro;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * Tests linkage issues: internal, external, or "none".
 * 
 * @author siegel
 * 
 */
public class CLinkageTest {

	private File root = new File("examples");

	private static Configuration config = Configurations
			.newMinimalConfiguration();

	private static FrontEnd fe = new FrontEnd(config);

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	private AST getAST(File file) throws ParseException, SyntaxException,
			PreprocessorException {
		AST ast = fe.compile(file, Language.C, new File[0], new File[0],
				new HashMap<String, Macro>());

		return ast;
	}

	@Test
	public void inner_func() throws ParseException, SyntaxException,
			PreprocessorException {
		File file = new File(root, "inner_func.c");
		AST ast = getAST(file);
		OrdinaryEntity entity = ast.getInternalOrExternalEntity("f");
		FunctionDeclarationNode prototype = null;
		FunctionDefinitionNode fDefn = null;
		FunctionDeclarationNode innerPrototype = null;

		// check there is an entity in the AST with internal
		// linkage called "f". It should be a function...
		assertNotNull(entity);
		assertTrue(entity instanceof Function);
		assertEquals(ProgramEntity.LinkageKind.EXTERNAL, entity.getLinkage());
		for (ASTNode exDef : ast.getRootNode().children()) {
			switch (exDef.nodeKind()) {
			case FUNCTION_DECLARATION: {
				FunctionDeclarationNode decl = (FunctionDeclarationNode) exDef;

				if ("f".equals(decl.getName()))
					prototype = decl;
				break;
			}
			case FUNCTION_DEFINITION: {
				FunctionDefinitionNode defn = (FunctionDefinitionNode) exDef;
				String name = defn.getName();

				if ("f".equals(name))
					fDefn = defn;
				else if ("main".equals(name)) {
					for (ASTNode stmt : defn.getBody().children()) {
						if (stmt instanceof FunctionDeclarationNode
								&& ((FunctionDeclarationNode) stmt).getName()
										.equals("f")) {
							innerPrototype = (FunctionDeclarationNode) stmt;
							break;
						}
					}
				}
				break;
			}
			default:
			}
		}
		// check the function prototype which is an external defn
		// for f has that as its entity...
		assertNotNull(prototype);
		assertEquals(entity, prototype.getEntity());
		// check the function definition which is an external defn
		// for f has f as its entity...
		assertNotNull(fDefn);
		assertEquals(entity, fDefn.getEntity());
		// get the body of main and find within it a declaration
		// for a function named f. Check that it has the same entity.
		assertNotNull(innerPrototype);
		assertEquals(entity, innerPrototype.getEntity());
	}
}
