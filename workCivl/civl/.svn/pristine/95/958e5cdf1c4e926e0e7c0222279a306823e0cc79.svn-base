package edu.udel.cis.vsl.civl.semantics.IF;

import java.util.Iterator;
import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.PointerSetExpression;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.expr.BooleanExpression;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * ContractConditionGenerator provides a set of interfaces for deriving contract
 * clauses. <br>
 * 
 * Terms:
 * <ol>
 * <li>Verifying function: the function which is being verified using contracts.
 * </li>
 * </ol>
 * Abstract interpretation:
 * <ol>
 * conditions: All conditions expressed in contracts are evaluate to boolean
 * expression. The evaluation of all kinds of expressions is not guaranteed to
 * have a absolute boolean value (true or false), but they shall have canonical
 * forms so that they can be used to do reasoing and derivation.
 * </ol>
 * 
 * Pointer abstract representations:
 * <ol>
 * <li>lambda: Pointer type parameters and global variables will be initialized
 * as an lambda expression: <code> lambda offset : ptr(XP, offset);</code> where
 * XP is an uninterpreted function whose duo inputs are scope ID and variable ID
 * of the parameter or global variable, the output is a unique pointer type
 * expression.</li>
 * <li>\valid: This class will evaluate \valid expressions to canonical boolean
 * abstract functions.</li>
 * <li>\remote:This class will evaluate \remote expressions to canonical
 * abstract functions.</li>
 * <li>lazy initialization: current pointers are initialized at the beginning of
 * verifying a function. Lazy initialization will be considered in the future.</li>
 * </ol>
 * 
 * 
 * miscellaneous:
 * <ol>
 * <li>Multiple-level pointers: multiple level pointers are pointers point to
 * pointers. Since contract clauses don't have orders, they are parallel
 * conditions. CIVL should be able to figure out dependencies among pointers.</li>
 * </ol>
 * 
 * @author ziqingluo
 *
 */
public interface ContractConditionGenerator {

	/******************* General main methods ************************/
	/**
	 * Given an expression in a contract clause, returns the derived result
	 * which is able to be used for reasoning.
	 * 
	 * @param state
	 *            The current state
	 * @param expression
	 *            The expression will be derived.
	 * @return
	 */
	Evaluation deriveExpression(State state, int pid, Expression expression)
			throws UnsatisfiablePathConditionException;

	/**
	 * Returns an {@link Iterator} for all \valid clauses that is proved as a
	 * consequence of all requirements.
	 * 
	 * @return
	 */
	Iterator<List<Integer>> validPointersIterator();

	/**************** Encoding abstract interpretation method ******************/
	/**
	 * Encodes a symbolic pointer expression as an uninterpreted function.
	 * 
	 * @param pointer
	 *            The {@link SymbolicExpression} of the pointer
	 * @param pointerExpr
	 *            The {@link Expression} of the pointer
	 * @return
	 */
	SymbolicExpression derefOnPointer(SymbolicExpression pointer,
			Expression pointerExpr);

	/**
	 * Encodes a \valid predicate on a symbolic pointer expression p with a
	 * lower and a higher bound. The predicate states that:
	 * <code> For all integer i; lower <= i < higher such that \valid(p+i)</code>
	 * 
	 * @param lambdaPointer
	 *            A pointer symbolic expression.
	 * @param low
	 *            The lower bound of a valid offset
	 * 
	 * @param high
	 *            The higher bound of a valid offset
	 * @return A quantified boolean predicate
	 */
	BooleanExpression pointerIsValidForall(SymbolicExpression basePointer,
			NumericExpression low, NumericExpression high);

	/**
	 * Encodes a \valid predicate on a symbolic pointer expression p. The
	 * predicate states that <code>\valid(p)</code>
	 * 
	 * @param pointer
	 * @return A boolean predicate
	 */
	BooleanExpression pointerIsValid(SymbolicExpression pointer);

	/**
	 * Initialize a pointer type variable v. v can only be the parameter of the
	 * function that is been verifying. v will be initialize as a lambda
	 * expression: <code> v = lambda(i) ;
	 * lambda(i) := ptr(pointer, i)</code> where the "pointer" is pointer stands
	 * for the base address and "i" is the input which stands for an offset.
	 * More details can be found at the specification of the class
	 * {@link ContractConditionGenerator}
	 * 
	 * @param pointerVar
	 *            The pointer type variable
	 * @return
	 */
	SymbolicExpression initializePointer(Variable pointerVar);

	/**************** Decoding abstract interpretation method ******************/
	/**
	 * This method extends {@link super#pointerAdd(State, int, String,
	 * BinaryExpression, SymbolicExpression, NumericExpression)} to be able to
	 * handle symbolic pointers.
	 * 
	 * @param state
	 *            The current state
	 * @param pid
	 *            The PID of the process
	 * @param process
	 *            The string identifier of the process
	 * @param expression
	 *            The addition expression
	 * @param pointer
	 *            The symbolic pointer value
	 * @param offset
	 *            The numeric offset value
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation pointerAdd(State state, int pid, String process,
			BinaryExpression expression, SymbolicExpression pointer,
			NumericExpression offset)
			throws UnsatisfiablePathConditionException;

	/******************* Setter and getter methods **********************/
	/**
	 * Saves a proved \valid axiom. proved \valid axiom must be a consequence of
	 * all requirements.
	 * 
	 * @param validConsequences
	 */
	void setValidConsequences(
			List<Pair<PointerSetExpression, Integer>> validConsequences);

	/**
	 * Return a "malloc" id for a \valid operand by a pair of vid and pointer
	 * depth
	 * 
	 * @param vid
	 *            The ID of an variable
	 * @param pointerLevels
	 *            The number of levels of pointers.
	 * @return
	 */
	List<Integer> getOrderedMallocId(int vid, int pointerLevels);

	/**
	 * TODO: experimental only
	 * 
	 * @param state
	 * @param pid
	 * @param numProcess
	 * @param collectiveBehavior
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	Evaluation deriveMPICollectiveBehavior(State state, int pid,
			int numProcess, MPICollectiveBehavior collectiveBehavior)
			throws UnsatisfiablePathConditionException;
}
