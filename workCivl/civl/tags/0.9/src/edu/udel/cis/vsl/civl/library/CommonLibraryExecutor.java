package edu.udel.cis.vsl.civl.library;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.err.CIVLExecutionException.Certainty;
import edu.udel.cis.vsl.civl.err.CIVLExecutionException.ErrorKind;
import edu.udel.cis.vsl.civl.err.CIVLStateException;
import edu.udel.cis.vsl.civl.err.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.library.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.semantics.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.StateFactory;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.ValidityResult.ResultType;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NTReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;

/**
 * This class implements the common logic of library executors.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public abstract class CommonLibraryExecutor extends Library implements
		LibraryExecutor {

	/* ************************** Instance Fields ************************** */

	/**
	 * Enable or disable printing. By default true, i.e., enable printing.
	 */
	protected boolean enablePrintf;

	/**
	 * The evaluator for evaluating expressions.
	 */
	protected Evaluator evaluator;

	/**
	 * The model factory of the system.
	 */
	protected ModelFactory modelFactory;

	/**
	 * The symbolic expression of one.
	 */
	protected NumericExpression one;

	/**
	 * The symbolic object of integer one.
	 */
	protected IntObject oneObject;

	/**
	 * The output stream to be used for printing.
	 */
	protected PrintStream output = System.out;

	/**
	 * The primary executor of the system.
	 */
	protected Executor primaryExecutor;

	/**
	 * The state factory for state-related computation.
	 */
	protected StateFactory stateFactory;

	/**
	 * The symbolic universe for symbolic computations.
	 */
	protected SymbolicUniverse universe;

	/**
	 * The symbolic expression of zero.
	 */
	protected NumericExpression zero;

	/**
	 * The symbolic object of integer zero.
	 */
	protected IntObject zeroObject;

	/* **************************** Constructors *************************** */

	/**
	 * Creates a new instance of a library executor.
	 * 
	 * @param primaryExecutor
	 *            The executor for normal CIVL execution.
	 * @param output
	 *            The output stream to be used in the enabler.
	 * @param enablePrintf
	 *            If printing is enabled for the printf function.
	 * @param modelFactory
	 *            The model factory of the system.
	 */
	protected CommonLibraryExecutor(Executor primaryExecutor,
			PrintStream output, boolean enablePrintf, ModelFactory modelFactory) {
		this.primaryExecutor = primaryExecutor;
		this.evaluator = primaryExecutor.evaluator();
		this.universe = evaluator.universe();
		this.stateFactory = evaluator.stateFactory();
		this.zero = universe.zeroInt();
		this.one = universe.oneInt();
		this.zeroObject = universe.intObject(0);
		this.oneObject = universe.intObject(1);
		this.enablePrintf = enablePrintf;
		this.output = output;
		this.modelFactory = modelFactory;
	}

	/* ************************* Protected Methods ************************* */

	/**
	 * Executes the function call "$free(*void)": removes from the heap the
	 * object referred to by the given pointer.
	 * 
	 * @param state
	 *            The current state.
	 * @param pid
	 *            The ID of the process that the function call belongs to.
	 * @param arguments
	 *            The static representation of the arguments of the function
	 *            call.
	 * @param argumentValues
	 *            The dynamic representation of the arguments of the function
	 *            call.
	 * @param source
	 *            The source code element to be used for error report.
	 * @return The new state after executing the function call.
	 * @throws UnsatisfiablePathConditionException
	 */
	protected State executeFree(State state, int pid, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source)
			throws UnsatisfiablePathConditionException {
		Expression pointerExpression = arguments[0];
		SymbolicExpression firstElementPointer = argumentValues[0];
		CIVLHeapType heapType = modelFactory.heapType();
		SymbolicExpression heapScopeID = universe.tupleRead(
				firstElementPointer, universe.intObject(0));
		SymbolicExpression heapObjectPointer;
		Evaluation eval;
		int index;
		SymbolicExpression undef;
		SymbolicExpression heapPointer = evaluator.heapPointer(source, state,
				heapScopeID);

		eval = getAndCheckHeapObjectPointer(heapPointer, firstElementPointer,
				pointerExpression.getSource(), state);
		state = eval.state;
		heapObjectPointer = eval.value;
		index = getMallocIndex(firstElementPointer);
		undef = heapType.getMalloc(index).getUndefinedObject();
		state = primaryExecutor.assign(source, state, heapObjectPointer, undef);
		return state;
	}

	/* ************************** Private Methods ************************** */

	/**
	 * Obtain a heap object via a certain heap object pointer.
	 * 
	 * @param heapPointer
	 *            The heap pointer.
	 * @param pointer
	 *            The heap object pointer.
	 * @param pointerSource
	 *            The source code element of the pointer.
	 * @param state
	 *            The current state
	 * @return The heap object pointer and the new state if any side effect.
	 */
	private Evaluation getAndCheckHeapObjectPointer(
			SymbolicExpression heapPointer, SymbolicExpression pointer,
			CIVLSource pointerSource, State state) {
		SymbolicExpression objectPointer = evaluator.getParentPointer(pointer);

		if (objectPointer != null) {
			SymbolicExpression fieldPointer = evaluator
					.getParentPointer(objectPointer);

			if (fieldPointer != null) {
				SymbolicExpression actualHeapPointer = evaluator
						.getParentPointer(fieldPointer);

				if (actualHeapPointer != null) {
					BooleanExpression pathCondition = state.getPathCondition();
					BooleanExpression claim = universe.equals(
							actualHeapPointer, heapPointer);
					ResultType valid = universe.reasoner(pathCondition)
							.valid(claim).getResultType();
					ReferenceExpression symRef;

					if (valid != ResultType.YES) {
						Certainty certainty = valid == ResultType.NO ? Certainty.PROVEABLE
								: Certainty.MAYBE;
						CIVLStateException e = new CIVLStateException(
								ErrorKind.MALLOC, certainty,
								"Invalid pointer for heap", state,
								pointerSource);

						evaluator.reportError(e);
						state = state.setPathCondition(universe.and(
								pathCondition, claim));
					}
					symRef = evaluator.getSymRef(pointer);
					if (symRef instanceof ArrayElementReference) {
						NumericExpression index = ((ArrayElementReference) symRef)
								.getIndex();

						if (index.isZero()) {
							return new Evaluation(state, objectPointer);
						}
					}

				}
			}
		}
		{
			CIVLStateException e = new CIVLStateException(ErrorKind.MALLOC,
					Certainty.PROVEABLE, "Invalid pointer for heap", state,
					pointerSource);

			evaluator.reportError(e);
			state = state.setPathCondition(universe.falseExpression());
			return new Evaluation(state, objectPointer);
		}
	}

	/**
	 * Obtains the field ID in the heap type via a heap-object pointer.
	 * 
	 * @param pointer
	 *            The heap-object pointer.
	 * @return The field ID in the heap type of the heap-object that the given
	 *         pointer refers to.
	 */
	private int getMallocIndex(SymbolicExpression pointer) {
		// ref points to element 0 of an array:
		NTReferenceExpression ref = (NTReferenceExpression) evaluator
				.getSymRef(pointer);
		// objectPointer points to array:
		NTReferenceExpression objectPointer = (NTReferenceExpression) ref
				.getParent();
		// fieldPointer points to the field:
		TupleComponentReference fieldPointer = (TupleComponentReference) objectPointer
				.getParent();
		int result = fieldPointer.getIndex().getInt();

		return result;
	}
}
