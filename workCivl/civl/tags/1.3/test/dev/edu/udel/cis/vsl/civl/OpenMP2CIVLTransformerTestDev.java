package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.AfterClass;
import org.junit.Ignore;
import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class OpenMP2CIVLTransformerTestDev {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File("examples"), "omp");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void vecAdd_fix() {
		assertTrue(ui.run("verify ", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("vecAdd_fix.c")));
	}
	
	@Ignore
	@Test
	public void dotProduct1() {
		assertTrue(ui.run("verify ", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("dotProduct1.c")));
	}
	
	@Ignore
	@Test
	public void dotProduct1Simplify() {
		assertTrue(ui.run("verify ",
				"-inputTHREAD_MAX=2", filename("dotProduct1.c")));
	}

	@Ignore
	@Test
	public void dotProductCritical() {
		assertTrue(ui.run("verify ", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("dotProduct_critical.c")));
	}
	
	@Ignore
	@Test
	public void dotProductCriticalSimplify() {
		assertTrue(ui.run("verify ",
				"-inputTHREAD_MAX=2", filename("dotProduct_critical.c")));
	}

	@Ignore
	@Test
	public void matProduct1() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("matProduct1.c")));
	}
	
	@Ignore
	@Test
	public void matProduct1Simplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("matProduct1.c")));
	}

	@Ignore
	@Test
	public void parallelfor() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("parallelfor.c")));
	}
	
	@Ignore
	@Test
	public void parallelforSimplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("parallelfor.c")));
	}

	@Ignore
	@Test
	public void raceCond1() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("raceCond1.c")));
	}
	
	@Ignore
	@Test
	public void raceCond1Simplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("raceCond1.c")));
	}
	
	@Ignore
	@Test
	public void fft() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("fft_openmp.c")));
	}
	
	@Ignore
	@Test
	public void fftSimplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("fft_openmp.c")));
	}
	
	@Ignore
	@Test
	public void poisson() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("poisson_openmp.c")));
	}
	
	@Ignore
	@Test
	public void poissonSimplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("poisson_openmp.c")));
	}

	@Ignore
	@Test
	public void quad() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("quad_openmp.c")));
	}

	@Ignore
	@Test
	public void quadSimplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("quad_openmp.c")));
	}

	@Ignore
	@Test
	public void md() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("md_openmp.c")));
	}

	@Ignore
	@Test
	public void mdSimplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("md_openmp.c")));
	}


	@Ignore
	@Test
	public void heatedplateAllDecomp() {
		assertTrue(ui.run("verify", "-ompNoSimplify -ompLoopDecomp=ALL", "-DMATH_NO_ASSUMPTIONS",
				"-inputTHREAD_MAX=2", filename("heated_plate_openmp.c")));
	}

	@Ignore
	@Test
	public void heatedplateRoundRobinDecomp() {
		assertTrue(ui.run("verify", "-ompNoSimplify -ompLoopDecomp=ROUND_ROBIN", "-DMATH_NO_ASSUMPTIONS",
				"-inputTHREAD_MAX=2", filename("heated_plate_openmp.c")));
	}

	@Ignore
	@Test
	public void heatedplateSimplify() {
		assertTrue(ui.run("verify", "-ompLoopDecomp=ALL", "-DMATH_NO_ASSUMPTIONS",
				"-inputTHREAD_MAX=2", filename("heated_plate_openmp.c")));
	}

	@Ignore
	@Test
	public void heatedplateAllDecomp4() {
		assertTrue(ui.run("verify", "-ompNoSimplify -ompLoopDecomp=ALL", "-DMATH_NO_ASSUMPTIONS",
				"-inputTHREAD_MAX=4", filename("heated_plate_openmp.c")));
	}

	@Ignore
	@Test
	public void heatedplateSimplify4() {
		assertTrue(ui.run("verify", "-ompLoopDecomp=ALL", "-DMATH_NO_ASSUMPTIONS",
				"-inputTHREAD_MAX=4", filename("heated_plate_openmp.c")));
	}

	@Ignore
	@Test
	public void heatedplateRoundRobinDecomp4() {
		assertTrue(ui.run("verify", "-ompNoSimplify -ompLoopDecomp=ROUND_ROBIN", "-DMATH_NO_ASSUMPTIONS",
				"-inputTHREAD_MAX=4", filename("heated_plate_openmp.c")));
	}

	@Ignore
	@Test
	public void prime() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("prime_openmp.c")));
	}

	@Ignore
	@Test
	public void primeSimplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("prime_openmp.c")));
	}

	@Ignore
	@Test
	public void fig310_mxv_omp() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("fig310-mxv-omp.c")));
	}

	@Ignore
	@Test
	public void fig310_mxv_ompSimplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("fig310-mxv-omp.c")));
	}


	@Test
	public void pi() {
		assertTrue(ui.run("verify", "-ompNoSimplify", "-showProgram",
				"-inputTHREAD_MAX=2", filename("pi.c")));
	}

	@Test
	public void piSimplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("pi.c")));
	}

	@Ignore
	@Test
	public void cmandel() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("c_mandel.c")));
	}

	@Ignore 
	@Test
	public void cmandelSimplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("c_mandel.c")));
	}

	@Ignore
	@Test
	public void cmd() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("c_md.c")));
	}

	@Ignore 
	@Test
	public void cmdSimplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("c_md.c")));
	}

	@Ignore
	@Test
	public void cpi() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("c_pi.c")));
	}

	@Ignore 
	@Test
	public void cpiSimplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("c_pi.c")));
	}

	@Ignore
	@Test
	public void cfft() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("c_fft.c")));
	}

	@Ignore 
	@Test
	public void cfftSimplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("c_fft.c")));
	}

	@Ignore
	@Test        public void cfft6() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("c_fft6.c")));
	}

	@Ignore 
	@Test
	public void cfft6Simplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("c_fft6.c")));
	}

	@Ignore
	@Test
	public void cjacobi01() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("c_jacobi01.c")));
	}

	@Ignore
	@Test
	public void cjacobi01Simplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("c_jacobi01.c")));
	}

	@Ignore
	@Test
	public void cjacobi02() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("c_jacobi02.c")));
	}

	@Ignore
	@Test
	public void cjacobi02Simplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("c_jacobi02.c")));
	}

	@Ignore
	@Test
	public void cjacobi03() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("c_jacobi03.c")));
	}

	@Ignore
	@Test
	public void cjacobi03Simplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("c_jacobi03.c")));
	}

	@Ignore
	@Test
	public void clu() {
		assertTrue(ui.run("verify", "-ompNoSimplify",
				"-inputTHREAD_MAX=2", filename("c_lu.c")));
	}

	@Ignore
	@Test
	public void cluSimplify() {
		assertTrue(ui.run("verify",
				"-inputTHREAD_MAX=2", filename("c_lu.c")));
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
		ui = null;
		rootDir = null;
	}
}
