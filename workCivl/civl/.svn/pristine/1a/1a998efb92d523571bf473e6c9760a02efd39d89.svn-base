package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.LinkedList;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import edu.udel.cis.vsl.abc.ABC;
import edu.udel.cis.vsl.abc.ABC.Language;
import edu.udel.cis.vsl.abc.ABCException;
import edu.udel.cis.vsl.abc.Activator;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.transform.Transform;
import edu.udel.cis.vsl.abc.transform.IF.TransformRecord;
import edu.udel.cis.vsl.abc.transform.IF.Transformer;
import edu.udel.cis.vsl.abc.transform.common.Pruner;
import edu.udel.cis.vsl.abc.transform.common.SideEffectRemover;
import edu.udel.cis.vsl.civl.run.UserInterface;
import edu.udel.cis.vsl.civl.transform.common.OmpPragmaTransformer;
import edu.udel.cis.vsl.civl.transform.common.OpenMPTransformer;

public class OmpTransformerTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "omp");

	private static UserInterface ui = new UserInterface();

	private File[] systemIncludes, userIncludes;

	private PrintStream out = System.out;

	private File root = new File(new File("examples"), "omp");

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	@Before
	public void setUp() throws Exception {
		if (!Transform.getCodes().contains(OpenMPTransformer.CODE)) {
			Transform.addTransform(new TransformRecord(OpenMPTransformer.CODE,
					OpenMPTransformer.LONG_NAME,
					OpenMPTransformer.SHORT_DESCRIPTION) {
				@Override
				public Transformer create(ASTFactory astFactory) {
					return new OpenMPTransformer(astFactory);
				}
			});
		}
		if (!Transform.getCodes().contains(OmpPragmaTransformer.CODE)) {
			Transform
					.addTransform(new TransformRecord(OmpPragmaTransformer.CODE,
							OmpPragmaTransformer.LONG_NAME,
							OmpPragmaTransformer.SHORT_DESCRIPTION) {
						@Override
						public Transformer create(ASTFactory astFactory) {
							return new OmpPragmaTransformer(astFactory);
						}
					});
		}
		ABC.language = Language.CIVL_C;
	}

	@After
	public void tearDown() throws Exception {
	}

	private void check(String filenameRoot) throws ABCException, IOException {
		Activator a;
		List<String> codes = new LinkedList<String>();

		codes.add(Pruner.CODE);
		codes.add(SideEffectRemover.CODE);
		codes.add(OmpPragmaTransformer.CODE);
		codes.add(OpenMPTransformer.CODE);
		this.systemIncludes = new File[0];
		this.userIncludes = new File[0];
		a = ABC.activator(new File(root, filenameRoot + ".c"), systemIncludes,
				userIncludes);
		a.showTranslation(out, codes);
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void dotProduct_critical1() throws ABCException, IOException {
		assertTrue(ui.run("parse", "-echo", filename("dotProduct_critical.c")));
	}

	@Test
	public void nested() throws ABCException, IOException {
		//this.check("nested");
		assertTrue(ui.run("parse", "-echo", filename("nested.c")));
	}

	@Test
	public void dotProduct_critical() throws ABCException, IOException {
		check("dotProduct_critical");
	}

	@Test
	public void dotProduct_orphan() throws ABCException, IOException {
		check("dotProduct_orphan");
	}

	@Test
	public void dotProduct1() throws ABCException, IOException {
		check("dotProduct1");
	}

	@Test
	public void matProduct1() throws ABCException, IOException {
		check("matProduct1");
	}

	@Test
	public void matProduct2() throws ABCException, IOException {
		check("matProduct2");
	}

	@Test
	public void raceCond1() throws ABCException, IOException {
		check("raceCond1");
	}

	@Test
	public void raceCond2() throws ABCException, IOException {
		check("raceCond2");
	}

	@Test
	public void vecAdd_deadlock() throws ABCException, IOException {
		check("vecAdd_deadlock");
	}

	@Test
	public void vecAdd_fix() throws ABCException, IOException {
		check("vecAdd_fix");
	}

	@Test
	public void fig310_mxv_omp() throws ABCException, IOException {
		check("fig3.10-mxv-omp");
	}

	@Test
	public void fig498_threadprivate() throws ABCException, IOException {
		check("fig4.98-threadprivate");
	}

	@Test
	public void parallelfor() throws ABCException, IOException {
		check("parallelfor");
	}
}
