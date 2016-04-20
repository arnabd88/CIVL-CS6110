package edu.udel.cis.vsl.civl.semantics.common;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.CIVLTypeFactory;
import edu.udel.cis.vsl.civl.model.IF.CIVLUnimplementedFeatureException;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.expression.MemoryUnitExpression;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.ArraySliceReference;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.ArraySliceReference.ArraySliceKind;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.MemoryUnitReference;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.MemoryUnitReference.MemoryUnitReferenceKind;
import edu.udel.cis.vsl.civl.model.IF.expression.reference.StructOrUnionFieldReference;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLCompleteArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluation;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.MemoryUnitExpressionEvaluator;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnit;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitFactory;
import edu.udel.cis.vsl.civl.state.IF.MemoryUnitSet;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.state.IF.UnsatisfiablePathConditionException;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.object.SymbolicObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.collections.IF.SymbolicCollection;

/**
 * This is responsible for evaluating memory unit expressions. (IN PROGRESS)
 * 
 * @author Manchun Zheng
 *
 */
public class CommonMemoryUnitEvaluator implements MemoryUnitExpressionEvaluator {

	private ModelFactory modelFactory;

	private CIVLTypeFactory typeFactory;

	/**
	 * The symbolic utility to be used.
	 */
	private SymbolicUtility symbolicUtil;

	/**
	 * The evaluator to be used for evaluating parameters of memory unit
	 * expressions, e.g, index of an array.
	 */
	private CommonEvaluator evaluator;

	/**
	 * The symbolic universe to be used.
	 */
	private SymbolicUniverse universe;

	private MemoryUnitFactory muFactory;

	public CommonMemoryUnitEvaluator(SymbolicUtility symbolicUtil,
			Evaluator evaluator, MemoryUnitFactory muFactory,
			SymbolicUniverse universe) {
		this.symbolicUtil = symbolicUtil;
		this.evaluator = (CommonEvaluator) evaluator;
		this.universe = universe;
		this.muFactory = muFactory;
		this.modelFactory = evaluator.modelFactory();
		this.typeFactory = this.modelFactory.typeFactory();
	}

	/**
	 * Evaluates a memory unit expression.
	 * 
	 * @param state
	 * @param pid
	 * @param memUnit
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	public MemoryUnitSet evaluates(State state, int pid,
			MemoryUnitExpression memUnit, MemoryUnitSet muSet)
			throws UnsatisfiablePathConditionException {
		MemoryUnitSet result = muSet;
		int scopeID = memUnit.scopeId();
		int dyscopeID = state.getDyscope(pid, scopeID);
		Set<ReferenceExpression> referenceValues;

		if (dyscopeID < 0)
			return result;
		referenceValues = this.evaluatesMemoryUnitReference(
				memUnit.getSource(), state, pid, memUnit.objectType(),
				memUnit.reference(), null).right;
		for (ReferenceExpression reference : referenceValues) {
			MemoryUnit newMemUnit = muFactory.newMemoryUnit(dyscopeID,
					memUnit.variableId(), reference);

			muFactory.add(result, newMemUnit);
			if (memUnit.deref()) {
				SymbolicExpression pointer = state.getVariableValue(dyscopeID,
						memUnit.variableId());

				if (pointer.type().equals(
						this.typeFactory.pointerSymbolicType()))
					muFactory.add(result, this.muFactory.newMemoryUnit(
							this.symbolicUtil.getDyscopeId(null, pointer),
							this.symbolicUtil.getVariableId(null, pointer),
							symbolicUtil.getSymRef(pointer)));
			}
			// result.add(pointer);
			// this.findPointersInExpression(
			// this.symbolicUtil.makePointer(dyscopeID,
			// memUnit.variableId(), reference), result,
			// state, state.getProcessState(pid).name());
			// result.add(symbolicUtil.makePointer(dyscopeID,
			// memUnit.variableId(), reference));
		}
		return result;

	}

	/**
	 * Evaluates reference of memory unit expressions.
	 * 
	 * @param state
	 * @param pid
	 * @param reference
	 * @param parent
	 * @return
	 * @throws UnsatisfiablePathConditionException
	 */
	private Pair<State, Set<ReferenceExpression>> evaluatesMemoryUnitReference(
			CIVLSource source, State state, int pid, CIVLType objType,
			MemoryUnitReference reference, Set<ReferenceExpression> parents)
			throws UnsatisfiablePathConditionException {
		MemoryUnitReferenceKind refKind = reference.memoryUnitKind();
		MemoryUnitReference child = reference.child();
		Set<ReferenceExpression> myRefValues = new HashSet<>();
		CIVLType myObjType = objType;
		// ReferenceExpression myRefValue = null;

		switch (refKind) {
		case SELF:
			myRefValues.add(universe.identityReference());
			break;
		case ARRAY_SLICE:// TODO to be finished
		{
			ArraySliceReference arraySlice = (ArraySliceReference) reference;
			ArraySliceKind sliceKind = arraySlice.sliceKind();
			Expression indexExpression = arraySlice.index();
			Evaluation eval = null;

			assert parents != null && parents.size() > 0;
			if (indexExpression != null) {
				eval = evaluator.evaluate(state, pid, indexExpression);
				state = eval.state;
			}
			switch (sliceKind) {
			case ELEMENT:
				for (ReferenceExpression parent : parents)
					myRefValues.add(universe.arrayElementReference(parent,
							(NumericExpression) eval.value));
				break;
			case WILDCARD: {
				CIVLCompleteArrayType arrayType = (CIVLCompleteArrayType) objType;
				Expression extent = arrayType.extent();
				int extentInt;
				Reasoner reasoner = universe.reasoner(state.getPathCondition());
				IntegerNumber length_number;

				eval = evaluator.evaluate(state, pid, extent);
				state = eval.state;
				length_number = (IntegerNumber) reasoner
						.extractNumber((NumericExpression) eval.value);
				extentInt = length_number.intValue();
				for (int i = 0; i < extentInt; i++)
					for (ReferenceExpression parent : parents)
						myRefValues.add(universe.arrayElementReference(parent,
								universe.integer(i)));
				break;
			}
			case REG_RANGE:
				// TODO to be finished
				break;
			default:
				throw new CIVLUnimplementedFeatureException(
						"evaluating array slice reference of " + sliceKind
								+ " kind", source);
			}

			break;
		}
		case STRUCT_OR_UNION_FIELD: {
			StructOrUnionFieldReference fieldRef = (StructOrUnionFieldReference) reference;
			int fieldIndex = fieldRef.fieldIndex();

			assert parents != null && parents.size() > 0;
			myObjType = ((CIVLStructOrUnionType) objType).getField(fieldIndex)
					.type();
			for (ReferenceExpression parent : parents)
				myRefValues.add(universe.tupleComponentReference(parent,
						universe.intObject(fieldRef.fieldIndex())));
			break;
		}
		default:
			throw new CIVLUnimplementedFeatureException(
					"evaluating memory unit reference of " + refKind + " kind",
					source);
		}
		assert myRefValues.size() > 0;
		if (child != null)
			return evaluatesMemoryUnitReference(source, state, pid, myObjType,
					child, myRefValues);
		else {
			// result.addAll(myRefValues);
			return new Pair<>(state, myRefValues);
		}
	}

	/**
	 * Finds pointers contained in a given expression recursively.
	 * 
	 * @param expr
	 * @param set
	 * @param state
	 */
	private void findPointersInExpression(SymbolicExpression expr,
			MemoryUnitSet set, State state, String process) {
		SymbolicType type = expr.type();

		// TODO check comm type
		if (type != null && !type.equals(typeFactory.heapSymbolicType())
				&& !type.equals(typeFactory.bundleSymbolicType())) {
			// need to eliminate heap type as well. each proc has its own.
			if (typeFactory.pointerSymbolicType().equals(type)) {
				SymbolicExpression pointerValue;
				Evaluation eval;

				this.muFactory.add(set, this.muFactory.newMemoryUnit(
						this.symbolicUtil.getDyscopeId(null, expr),
						this.symbolicUtil.getVariableId(null, expr),
						symbolicUtil.getSymRef(expr)));
				// set.add(expr);
				try {
					if (expr.operator() == SymbolicOperator.CONCRETE
							&& symbolicUtil.getDyscopeId(null, expr) >= 0) {
						/*
						 * If the expression is an arrayElementReference
						 * expression, and finally it turns that the array type
						 * has length 0, return immediately. Because we can not
						 * dereference it and the dereference exception
						 * shouldn't report here.
						 */
						if (symbolicUtil.getSymRef(expr)
								.isArrayElementReference()) {
							SymbolicExpression arrayPointer = symbolicUtil
									.parentPointer(null, expr);

							eval = evaluator.dereference(null, state, process,
									null, arrayPointer, false, true);
							/* Check if it's length == 0 */
							if (universe.length(eval.value).isZero())
								return;
						}
						eval = evaluator.dereference(null, state, process,
								null, expr, false, true);
						pointerValue = eval.value;
						state = eval.state;
						if (pointerValue.operator() == SymbolicOperator.CONCRETE
								&& pointerValue.type() != null
								&& pointerValue.type().equals(
										typeFactory.pointerSymbolicType()))
							if (this.symbolicUtil.isNullPointer(pointerValue))
								return;
						findPointersInExpression(pointerValue, set, state,
								process);
					}
				} catch (UnsatisfiablePathConditionException e) {
					// // TODO Auto-generated catch block
					// e.printStackTrace();
				}
			} else {
				int numArgs = expr.numArguments();

				for (int i = 0; i < numArgs; i++) {
					SymbolicObject arg = expr.argument(i);

					findPointersInObject(arg, set, state, process);
				}
			}
		}
	}

	/**
	 * Finds all the pointers that can be dereferenced inside a symbolic object.
	 * 
	 * @param object
	 *            a symbolic object
	 * @param set
	 *            a set to which the pointer values will be added
	 * @param heapType
	 *            the heap type, which will be ignored
	 */
	private void findPointersInObject(SymbolicObject object, MemoryUnitSet set,
			State state, String process) {
		switch (object.symbolicObjectKind()) {
		case EXPRESSION:
			findPointersInExpression((SymbolicExpression) object, set, state,
					process);
			break;
		case EXPRESSION_COLLECTION:
			for (SymbolicExpression expr : (SymbolicCollection<?>) object)
				findPointersInExpression(expr, set, state, process);
			break;
		default:
			// ignore types and primitives, they don't have any pointers
			// you can dereference.
		}
	}

}
