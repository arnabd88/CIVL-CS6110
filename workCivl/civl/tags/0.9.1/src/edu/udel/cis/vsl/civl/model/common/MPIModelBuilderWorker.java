package edu.udel.cis.vsl.civl.model.common;

import java.io.PrintStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.civl.err.CIVLException;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.Fragment;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.MPIModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.GMCConfiguration;

public class MPIModelBuilderWorker extends ModelBuilderWorker {

	/* *************************** Static Fields ************************** */

	/**
	 * The name of the input variable for specifying the number of MPI
	 * processes. e.g., a corresponding command line option may be
	 * -inputNPROCS=3.
	 */
	static final String NPROCS = "NPROCS";

	/* ************************** Instance Fields ************************** */

	/**
	 * The unique MPI model factory used by the system.
	 */
	private MPIModelFactory mpiFactory;

	/**
	 * The main function of each MPI process.
	 */
	private CIVLFunction processMainFunction;

	/* **************************** Constructors *************************** */

	/**
	 * Create a new instance of MPI model builder worker.
	 * 
	 * @param config
	 *            The configuration of the system.
	 * @param factory
	 *            The MPI model factory to be used.
	 * @param program
	 *            The program to be translated.
	 * @param name
	 *            The name of the CIVL model, i.e., the file name without the
	 *            file extension.
	 * @param debugOut
	 * @param debugging
	 */
	public MPIModelBuilderWorker(GMCConfiguration config,
			MPIModelFactory factory, Program program, String name,
			boolean debugging, PrintStream debugOut) {
		super(config, factory, program, name, debugging, debugOut);
		this.mpiFactory = factory;
	}

	/* ****************** Methods from ModelBuilderWorker ****************** */

	/**
	 * Build the MPI model from the AST tree.
	 * 
	 * @throws CommandLineException
	 *             if command line input has errors.
	 */
	@Override
	public void buildModel() throws CommandLineException {
		Identifier systemID = mpiFactory.identifier(mpiFactory.systemSource(),
				"_MPI_system");
		CIVLFunction system = mpiFactory.function(
				mpiFactory.sourceOf(program.getAST().getRootNode()), systemID,
				new ArrayList<Variable>(), null, null, null);
		ASTNode rootNode = program.getAST().getRootNode();
		MPIFunctionTranslator systemFunctionTranslator = new MPIFunctionTranslator(
				this, mpiFactory, system);
		Expression nprocsExpression;
		Fragment initialization;
		MPIFunctionTranslator processMainFunctionTranslator;

		initialization(system);
		if (inputInitMap == null || !inputInitMap.containsKey(NPROCS)) {
			throw new CommandLineException(
					"NPROCS must be specified for running or verifying MPI programs.");
		}
		initializedInputs.add(NPROCS);
		nprocsExpression = nprocsExpression();
		this.mpiFactory.setNumberOfProcs(nprocsExpression);
		this.processMainFunction = systemFunctionTranslator
				.processMainFunction(systemScope, rootNode);
		initialization = systemFunctionTranslator.translateRootFunction(
				systemScope, rootNode, this.processMainFunction.outerScope());
		if (inputInitMap != null) {
			// if commandline specified input variables that do not
			// exist, throw exception...
			Set<String> commandLineVars = new HashSet<String>(
					inputInitMap.keySet());

			commandLineVars.removeAll(initializedInputs);
			if (!commandLineVars.isEmpty()) {
				String msg = "Program contains no input variables named ";
				boolean first = true;

				for (String name : commandLineVars) {
					if (first)
						first = false;
					else
						msg += ", ";
					msg += name;
				}
				throw new CommandLineException(msg);
			}
		}
		if (mainFunctionNode == null) {
			throw new CIVLException("A MPI program must have a main function.",
					mpiFactory.sourceOf(rootNode));
		}
		processMainFunctionTranslator = new MPIFunctionTranslator(this,
				mpiFactory, processMainFunction,
				this.mainFunctionNode.getBody());
		this.functionMap.put(mainFunctionNode.getEntity(), processMainFunction);
		processMainFunctionTranslator
				.translateProcessMainFunction(initialization);
		translateUndefinedFunctions();
		completeCallOrSpawnStatements();
		mpiFactory.completeHeapType(heapType, mallocStatements);
		completeBundleType();
		completeModel(system);
		this.staticAnalysis();
	}

	/* ********************** Package-private Methods ********************** */

	/**
	 * Obtain the value of the number of processes, i.e., NPROCS, specified in
	 * the command line.
	 * 
	 * @return The integer literal expression of the number of processes.
	 * @throws CommandLineException
	 *             if no input variable NPROCS can be found.
	 */
	Expression nprocsExpression() throws CommandLineException {
		Object nprocs = inputInitMap.get(NPROCS);

		if (nprocs != null) {
			initializedInputs.add(NPROCS);
			if (nprocs instanceof Integer)
				return mpiFactory.integerLiteralExpression(mpiFactory
						.systemSource(),
						new BigInteger(((Integer) nprocs).toString()));
			if (nprocs instanceof String)
				return mpiFactory.integerLiteralExpression(mpiFactory
						.systemSource(), new BigInteger((String) nprocs));
			else
				throw new CommandLineException(
						"Expected integer value for variable " + NPROCS
								+ " but saw " + nprocs);
		} else {
			throw new CommandLineException(
					"NPROCS must be specified for running or verifying MPI programs.");
		}
	}

	/**
	 * 
	 * @return The main function of MPI processes.
	 */
	CIVLFunction processMainFunction() {
		return this.processMainFunction;
	}
}
