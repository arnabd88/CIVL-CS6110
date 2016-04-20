package edu.udel.cis.vsl.civl.library.bundle;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEvaluator;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

public class LibbundleEvaluator extends BaseLibraryEvaluator implements
		LibraryEvaluator {

	public LibbundleEvaluator(String name, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, evaluator, modelFactory, symbolicUtil, symbolicAnalyzer,
				civlConfig, libEvaluatorLoader);
	}

	/* ********************* Package protected Function *********************** */
	/**
	 * Evaluating for bundle_unpack execution. This function returns the value
	 * of the object and the pointer to that object(the return type is a Pair).
	 * The reason that why this function need. <br>
	 * Note: Data in bundle is in the form of a unrolled one dimensional array.
	 * 
	 * Implementation details: First, it's guaranteed that the data in bundle is
	 * always in the form of a one dimensional array(also can be understood as a
	 * unrolled array or a sequence of data).<br>
	 * Second, inside this function, it contains a cast from the one dimensional
	 * array mentioned above to another type specified by the parameter
	 * "pointer". A correct CIVL program or C program should make sure that cast
	 * is legal, otherwise an error will be reported.<br>
	 * Third, the object used to store the data in bundle can have a larger size
	 * than the data itself.
	 * 
	 * 
	 * @param state
	 *            The current state
	 * @param process
	 *            The identifier of the process
	 * @param bundle
	 *            The bundle type object
	 * @param pointer
	 *            The pointer to the address of the object which will be
	 *            assigned by bundle data
	 * @param civlsource
	 *            The CIVL Source of the bundle_unpack statement
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	Pair<Evaluation, SymbolicExpression> bundleUnpack(State state,
			String process, SymbolicExpression bundleData,
			Expression pointerExpr, SymbolicExpression pointer,
			CIVLSource civlsource) throws UnsatisfiablePathConditionException {
		SymbolicExpression data = bundleData;
		NumericExpression dataSize;
		Evaluation eval;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		Pair<Evaluation, SymbolicExpression> eval_and_pointer;

		// Since bundle unpack is called by executeBundleUnpack, it has no need
		// to check pointer validation here.
		dataSize = universe.length(data);
		// If data size is zero, do nothing.
		if (reasoner.isValid(universe.equals(dataSize, zero))) {
			eval = evaluator.dereference(civlsource, state, process, null,
					pointer, false);
			return new Pair<Evaluation, SymbolicExpression>(eval, pointer);
		} else if (reasoner.isValid(universe.equals(dataSize, one))) {
			ReferenceExpression ref;

			// If data size is one, reading array to get the element
			eval = new Evaluation(state, universe.arrayRead(data, zero));
			ref = symbolicAnalyzer.getMemBaseReference(state, pointer,
					civlsource);
			pointer = symbolicUtil.makePointer(pointer, ref);
			return new Pair<Evaluation, SymbolicExpression>(eval, pointer);
		}
		// If data size larger than one, return an array and the corresponding
		// pointer.
		eval_and_pointer = this.setDataFrom(state, process, pointerExpr,
				pointer, dataSize, data, false, civlsource);
		return eval_and_pointer;
	}
}
