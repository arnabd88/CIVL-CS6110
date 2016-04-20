package edu.udel.cis.vsl.civl;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.io.PrintWriter;

import org.junit.Test;

import edu.udel.cis.vsl.abc.Activator;
import edu.udel.cis.vsl.abc.ast.unit.IF.TranslationUnit;
import edu.udel.cis.vsl.abc.parse.IF.ParseException;
import edu.udel.cis.vsl.abc.preproc.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.civl.kripke.Enabler;
import edu.udel.cis.vsl.civl.kripke.StateManager;
import edu.udel.cis.vsl.civl.log.ErrorLog;
import edu.udel.cis.vsl.civl.model.Models;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelBuilder;
import edu.udel.cis.vsl.civl.predicate.Deadlock;
import edu.udel.cis.vsl.civl.semantics.Evaluator;
import edu.udel.cis.vsl.civl.semantics.Executor;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.civl.state.StateFactory;
import edu.udel.cis.vsl.civl.state.StateFactoryIF;
import edu.udel.cis.vsl.civl.transition.Transition;
import edu.udel.cis.vsl.civl.transition.TransitionFactory;
import edu.udel.cis.vsl.civl.transition.TransitionSequence;
import edu.udel.cis.vsl.gmc.DfsSearcher;
import edu.udel.cis.vsl.gmc.EnablerIF;
import edu.udel.cis.vsl.gmc.StateManagerIF;
import edu.udel.cis.vsl.gmc.StatePredicateIF;
import edu.udel.cis.vsl.sarl.SARL;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicArrayType;

public class ArraysTest {

	private static File rootDir = new File("examples");
	private static SymbolicUniverse universe = SARL.newIdealUniverse();
	private static ModelBuilder modelBuilder = Models.newModelBuilder();
	private PrintStream out = System.out;

	@Test
	public void testArrays() throws IOException, PreprocessorException,
			ParseException, SyntaxException {
		File[] systemIncludes = new File[0];
		File[] userIncludes = new File[0];
		Activator a = new Activator(new File(rootDir, "arrays.cvl"),
				systemIncludes, userIncludes);
		TranslationUnit unit = a.getSideEffectFreeTranslationUnit();
		StateFactoryIF stateFactory = new StateFactory(universe);
		Model model;
		TransitionFactory transitionFactory = new TransitionFactory();
		ErrorLog log = new ErrorLog(new PrintWriter(System.out),
				new java.io.File("."));
		Evaluator evaluator = new Evaluator(universe, log);
		EnablerIF<State, Transition, TransitionSequence> enabler = new Enabler(
				transitionFactory, universe, evaluator);
		StatePredicateIF<State> predicate = new Deadlock(universe, evaluator);
		Executor executor;
		StateManagerIF<State, Transition> stateManager;
		DfsSearcher<State, Transition, TransitionSequence> searcher;
		State initialState;
		double startTime = System.currentTimeMillis(), endTime;
		boolean result;
		String bar = "===================";

		model = modelBuilder.buildModel(unit);
		out.println(bar + " Model " + bar + "\n");
		model.print(out);
		initialState = stateFactory.initialState(model);
		executor = new Executor(model, universe, stateFactory, log);
		stateManager = new StateManager(executor);
		searcher = new DfsSearcher<State, Transition, TransitionSequence>(
				enabler, stateManager, predicate);
		searcher.setDebugOut(new PrintWriter(out));
		result = searcher.search(initialState);
		endTime = System.currentTimeMillis();
		out.println(bar + " Stats " + bar + "\n");
		CIVL.printStats(out, searcher, universe, startTime, endTime,
				((StateManager) stateManager).maxProcs());
		if (result || log.numReports() > 0) {
			out.println("The program MAY NOT be correct.");
		} else {
			out.println("The specified properties hold for all executions.");
		}
		out.flush();
		assertFalse(result);
	}

	private SymbolicExpression write2d(SymbolicExpression array,
			SymbolicExpression i, SymbolicExpression j, SymbolicExpression value) {
		SymbolicExpression row = universe.arrayRead(array,
				(NumericExpression) i);
		SymbolicExpression newRow = universe.arrayWrite(row,
				(NumericExpression) j, value);

		return universe.arrayWrite(array, (NumericExpression) i, newRow);
	}

	private SymbolicExpression read2d(SymbolicExpression array,
			SymbolicExpression i, SymbolicExpression j) {
		SymbolicExpression row = universe.arrayRead(array,
				(NumericExpression) i);

		return universe.arrayRead(row, (NumericExpression) j);
	}

	/**
	 * Write and read a 2d array.
	 */
	@Test
	public void array2d() {
		SymbolicArrayType t = universe.arrayType(universe.arrayType(universe
				.integerType()));
		SymbolicExpression a = universe.symbolicConstant(
				universe.stringObject("a"), t);
		SymbolicExpression zero = universe.zeroInt();
		SymbolicExpression twoInt = universe.integer(2);
		SymbolicExpression read;

		a = write2d(a, zero, zero, twoInt);
		read = read2d(a, zero, zero);
		assertEquals(twoInt, read);
		// for the heck of it...
		out.println("array2d: new row is: "
				+ universe.arrayRead(a, (NumericExpression) zero));
	}

}