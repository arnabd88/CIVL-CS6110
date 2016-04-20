package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Test;

import edu.udel.cis.vsl.civl.run.IF.UserInterface;

public class AMGTest {

	/* *************************** Static Fields *************************** */

	private static File rootDir = new File(new File(new File("examples"),
			"mpi-omp"), "AMG2013");

	private static UserInterface ui = new UserInterface();

	/* *************************** Helper Methods ************************** */

	private static String filename(String name) {
		return new File(rootDir, name).getPath();
	}

	/* **************************** Test Methods *************************** */

	@Test
	public void Utils() {
		assertTrue(ui
				.run("show",
						"-ompNoSimplify",
						"-input_mpi_nprocs=1",
						"-input_omp_thread_max=1",
						"-DTIMER_USE_MPI",
						"-DHYPRE_USING_OPENMP",
						"-DHYPRE_TIMING",
						"-userIncludePath=examples/mpi-omp/AMG2013/utilities:examples/mpi-omp/AMG2013:examples/mpi-omp/AMG2013/parcsr_mv:examples/mpi-omp/AMG2013/seq_mv:examples/mpi-omp/AMG2013/sstruct_mv:examples/mpi-omp/AMG2013/struct_mv:examples/mpi-omp/AMG2013/IJ_mv:examples/mpi-omp/AMG2013/parcsr_ls:examples/mpi-omp/AMG2013/krylov",
						filename("test/amg2013.c"),
						filename("utilities/amg_linklist.c "),
						filename("utilities/binsearch.c"),
						filename("utilities/exchange_data.c "),
						filename("utilities/hypre_memory.c "),
						filename("utilities/hypre_qsort.c "),
						filename("utilities/memory_dmalloc.c "),
						filename("utilities/mpistubs.c "),
						filename("utilities/qsplit.c "),
						filename("utilities/thread_mpistubs.c "),
						filename("utilities/threading.c "),
						filename("utilities/timer.c "),
						filename("utilities/timing.c "),
						filename("utilities/umalloc_local.c ")));

	}

	@Test
	public void IJ_mv() {
		assertTrue(ui
				.run("show",
						"-ompNoSimplify",
						"-input_mpi_nprocs=1",
						"-input_omp_thread_max=1",
						"-DTIMER_USE_MPI",
						"-DHYPRE_USING_OPENMP",
						"-DHYPRE_TIMING",
						"-userIncludePath=examples/mpi-omp/AMG2013/utilities:examples/mpi-omp/AMG2013:examples/mpi-omp/AMG2013/parcsr_mv:examples/mpi-omp/AMG2013/seq_mv:examples/mpi-omp/AMG2013/sstruct_mv:examples/mpi-omp/AMG2013/struct_mv:examples/mpi-omp/AMG2013/IJ_mv:examples/mpi-omp/AMG2013/parcsr_ls:examples/mpi-omp/AMG2013/krylov",
						filename("test/amg2013.c"),
						filename("IJ_mv/aux_par_vector.c "),
						filename("IJ_mv/aux_parcsr_matrix.c"),
						filename("IJ_mv/HYPRE_IJMatrix.c "),
						filename("IJ_mv/HYPRE_IJVector.c "),
						filename("IJ_mv/IJMatrix_parcsr.c "),
						filename("IJ_mv/IJMatrix.c "),
						filename("IJ_mv/IJVector_parcsr.c "),
						filename("IJ_mv/IJVector.c ")));

	}

	@Test
	public void Krylov() {
		assertTrue(ui
				.run("show",
						"-ompNoSimplify",
						"-input_mpi_nprocs=1",
						"-input_omp_thread_max=1",
						"-DTIMER_USE_MPI",
						"-DHYPRE_USING_OPENMP",
						"-DHYPRE_TIMING",
						"-userIncludePath=examples/mpi-omp/AMG2013/utilities:examples/mpi-omp/AMG2013:examples/mpi-omp/AMG2013/parcsr_mv:examples/mpi-omp/AMG2013/seq_mv:examples/mpi-omp/AMG2013/sstruct_mv:examples/mpi-omp/AMG2013/struct_mv:examples/mpi-omp/AMG2013/IJ_mv:examples/mpi-omp/AMG2013/parcsr_ls:examples/mpi-omp/AMG2013/krylov",
						filename("test/amg2013.c"),
						filename("krylov/gmres.c "),
						filename("krylov/HYPRE_gmres.c"),
						filename("krylov/HYPRE_pcg.c "),
						filename("krylov/pcg.c ")));

	}

	@Test
	public void Parcsr_mv() {
		assertTrue(ui
				.run("show",
						"-ompNoSimplify",
						"-input_mpi_nprocs=1",
						"-input_omp_thread_max=1",
						"-DTIMER_USE_MPI",
						"-DHYPRE_USING_OPENMP",
						"-DHYPRE_TIMING",
						"-userIncludePath=examples/mpi-omp/AMG2013/utilities:examples/mpi-omp/AMG2013:examples/mpi-omp/AMG2013/parcsr_mv:examples/mpi-omp/AMG2013/seq_mv:examples/mpi-omp/AMG2013/sstruct_mv:examples/mpi-omp/AMG2013/struct_mv:examples/mpi-omp/AMG2013/IJ_mv:examples/mpi-omp/AMG2013/parcsr_ls:examples/mpi-omp/AMG2013/krylov",
						filename("test/amg2013.c"),
						filename("parcsr_mv/HYPRE_parcsr_matrix.c "),
						filename("parcsr_mv/HYPRE_parcsr_vector.c"),
						filename("parcsr_mv/new_commpkg.c "),
						filename("parcsr_mv/par_csr_assumed_part.c "),
						filename("parcsr_mv/par_csr_communication.c "),
						filename("parcsr_mv/par_csr_matop_marked.c "),
						filename("parcsr_mv/par_csr_matop.c "),
						filename("parcsr_mv/par_csr_matrix.c "),
						filename("parcsr_mv/par_csr_matvec.c "),
						filename("parcsr_mv/par_vector.c ")));

	}

	@Test
	public void Seq_mv() {
		assertTrue(ui
				.run("show",
						"-ompNoSimplify",
						"-input_mpi_nprocs=1",
						"-input_omp_thread_max=1",
						"-DTIMER_USE_MPI",
						"-DHYPRE_USING_OPENMP",
						"-DHYPRE_TIMING",
						"-userIncludePath=examples/mpi-omp/AMG2013/utilities:examples/mpi-omp/AMG2013:examples/mpi-omp/AMG2013/parcsr_mv:examples/mpi-omp/AMG2013/seq_mv:examples/mpi-omp/AMG2013/sstruct_mv:examples/mpi-omp/AMG2013/struct_mv:examples/mpi-omp/AMG2013/IJ_mv:examples/mpi-omp/AMG2013/parcsr_ls:examples/mpi-omp/AMG2013/krylov",
						filename("test/amg2013.c"),
						filename("seq_mv/big_csr_matrix.c "),
						filename("seq_mv/csr_matop.c"),
						filename("seq_mv/csr_matrix.c "),
						filename("seq_mv/csr_matvec.c "),
						filename("seq_mv/genpart.c "),
						filename("seq_mv/HYPRE_csr_matrix.c "),
						filename("seq_mv/HYPRE_vector.c "),
						filename("seq_mv/vector.c ")));

	}

	@Test
	public void Parcsr_ls() {
		assertTrue(ui
				.run("show",
						"-showProgram",
						"-ompNoSimplify",
						"-input_mpi_nprocs=1",
						"-input_omp_thread_max=1",
						"-DTIMER_USE_MPI",
						"-DHYPRE_USING_OPENMP",
						"-DHYPRE_TIMING",
						"-userIncludePath=examples/mpi-omp/AMG2013/utilities:examples/mpi-omp/AMG2013:examples/mpi-omp/AMG2013/parcsr_mv:examples/mpi-omp/AMG2013/seq_mv:examples/mpi-omp/AMG2013/sstruct_mv:examples/mpi-omp/AMG2013/struct_mv:examples/mpi-omp/AMG2013/IJ_mv:examples/mpi-omp/AMG2013/parcsr_ls:examples/mpi-omp/AMG2013/krylov",
						filename("test/amg2013.c"),
						filename("parcsr_ls/aux_interp.c "),
						filename("parcsr_ls/gen_redcs_mat.c"),
						filename("parcsr_ls/HYPRE_parcsr_amg.c "),
						filename("parcsr_ls/HYPRE_parcsr_gmres.c "),
						filename("parcsr_ls/HYPRE_parcsr_pcg.c "),
						filename("parcsr_ls/par_amg_setup.c "),
						filename("parcsr_ls/par_amg_solve.c "),
						filename("parcsr_ls/par_amg.c "),
						filename("parcsr_ls/par_cg_relax_wt.c "),
						filename("parcsr_ls/par_coarse_parms.c "),
						filename("parcsr_ls/par_coarsen.c "),
						filename("parcsr_ls/par_cycle.c "),
						filename("parcsr_ls/par_difconv.c "),
						filename("parcsr_ls/par_indepset.c "),
						filename("parcsr_ls/par_interp.c "),
						filename("parcsr_ls/par_jacobi_interp.c "),
						filename("parcsr_ls/par_laplace_27pt.c "),
						filename("parcsr_ls/par_laplace.c "),
						filename("parcsr_ls/par_lr_interp.c "),
						filename("parcsr_ls/par_multi_interp.c "),
						filename("parcsr_ls/par_nodal_systems.c "),
						filename("parcsr_ls/par_rap_communication.c "),
						filename("parcsr_ls/par_rap.c "),
						filename("parcsr_ls/par_relax_interface.c "),
						filename("parcsr_ls/par_relax_more.c "),
						filename("parcsr_ls/par_relax.c "),
						filename("parcsr_ls/par_scaled_matnorm.c "),
						filename("parcsr_ls/par_stats.c "),
						filename("parcsr_ls/par_strength.c "),
						filename("parcsr_ls/par_vardifconv.c "),
						filename("parcsr_ls/partial.c "),
						filename("parcsr_ls/pcg_par.c ")));

	}

	@Test
	public void Sstruct_mv() {
		assertTrue(ui
				.run("show",
						"-ompNoSimplify",
						"-input_mpi_nprocs=1",
						"-input_omp_thread_max=1",
						"-DTIMER_USE_MPI",
						"-DHYPRE_USING_OPENMP",
						"-DHYPRE_TIMING",
						"-userIncludePath=examples/mpi-omp/AMG2013/utilities:examples/mpi-omp/AMG2013:examples/mpi-omp/AMG2013/parcsr_mv:examples/mpi-omp/AMG2013/seq_mv:examples/mpi-omp/AMG2013/sstruct_mv:examples/mpi-omp/AMG2013/struct_mv:examples/mpi-omp/AMG2013/IJ_mv:examples/mpi-omp/AMG2013/parcsr_ls:examples/mpi-omp/AMG2013/krylov",
						filename("test/amg2013.c"),
						filename("sstruct_mv/box_map.c "),
						filename("sstruct_mv/HYPRE_sstruct_graph.c"),
						filename("sstruct_mv/HYPRE_sstruct_grid.c "),
						filename("sstruct_mv/HYPRE_sstruct_matrix.c "),
						filename("sstruct_mv/HYPRE_sstruct_stencil.c "),
						filename("sstruct_mv/HYPRE_sstruct_vector.c "),
						filename("sstruct_mv/sstruct_axpy.c "),
						filename("sstruct_mv/sstruct_copy.c "),
						filename("sstruct_mv/sstruct_graph.c "),
						filename("sstruct_mv/sstruct_grid.c "),
						filename("sstruct_mv/sstruct_innerprod.c "),
						filename("sstruct_mv/sstruct_matrix.c "),
						filename("sstruct_mv/sstruct_matvec.c "),
						filename("sstruct_mv/sstruct_overlap_innerprod.c "),
						filename("sstruct_mv/sstruct_scale.c "),
						filename("sstruct_mv/sstruct_stencil.c "),
						filename("sstruct_mv/sstruct_vector.c ")));

	}

	@Test
	public void Struct_mv() {
		assertTrue(ui
				.run("show",
						"-ompNoSimplify",
						"-input_mpi_nprocs=1",
						"-input_omp_thread_max=1",
						"-DTIMER_USE_MPI",
						"-DHYPRE_USING_OPENMP",
						"-DHYPRE_TIMING",
						"-userIncludePath=examples/mpi-omp/AMG2013/utilities:examples/mpi-omp/AMG2013:examples/mpi-omp/AMG2013/parcsr_mv:examples/mpi-omp/AMG2013/seq_mv:examples/mpi-omp/AMG2013/sstruct_mv:examples/mpi-omp/AMG2013/struct_mv:examples/mpi-omp/AMG2013/IJ_mv:examples/mpi-omp/AMG2013/parcsr_ls:examples/mpi-omp/AMG2013/krylov",
						filename("test/amg2013.c"),
						filename("struct_mv/assumed_part.c "),
						filename("struct_mv/box_algebra.c"),
						filename("struct_mv/box_alloc.c "),
						filename("struct_mv/box_boundary.c "),
						filename("struct_mv/box_manager.c "),
						filename("struct_mv/box_neighbors.c "),
						filename("struct_mv/box.c "),
						filename("struct_mv/communication_info.c "),
						filename("struct_mv/computation.c "),
						filename("struct_mv/grow.c "),
						filename("struct_mv/HYPRE_struct_grid.c "),
						filename("struct_mv/HYPRE_struct_matrix.c "),
						filename("struct_mv/HYPRE_struct_stencil.c "),
						filename("struct_mv/HYPRE_struct_vector.c "),
						filename("struct_mv/new_assemble.c "),
						filename("struct_mv/new_box_neighbors.c "),
						filename("struct_mv/project.c "),
						filename("struct_mv/struct_axpy.c "),
						filename("struct_mv/struct_communication.c "),
						filename("struct_mv/struct_copy.c "),
						filename("struct_mv/struct_grid.c "),
						filename("struct_mv/struct_innerprod.c "),
						filename("struct_mv/struct_io.c "),
						filename("struct_mv/struct_matrix_mask.c "),
						filename("struct_mv/struct_matrix.c "),
						filename("struct_mv/struct_matvec.c "),
						filename("struct_mv/struct_overlap_innerprod.c "),
						filename("struct_mv/struct_scale.c "),
						filename("struct_mv/struct_stencil.c "),
						filename("struct_mv/struct_vector.c ")));
	}

}
