package edu.udel.cis.vsl.civl.dynamic.common;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelConfiguration;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.ArrayElementReference;
import edu.udel.cis.vsl.sarl.IF.expr.NTReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.ReferenceExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicConstant;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression.SymbolicOperator;
import edu.udel.cis.vsl.sarl.IF.expr.TupleComponentReference;
import edu.udel.cis.vsl.sarl.IF.expr.UnionMemberReference;
import edu.udel.cis.vsl.sarl.IF.object.IntObject;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * This class implements operations on a heap. A heap consists of a fixed number
 * (however, the number may vary from models to models) of heap fields, while a
 * heap field is composed of a dynamic number of heap objects of type array of
 * type T.
 * <ul>
 * <li>each dyscope has a heap by default, as the 0 variable of that dyscope;</li>
 * <li>the initial value of a heap is a SARL NULL expression (not JAVA's NULL);</li>
 * <li>a heap has the type &lt;array-of-array-of-T1, array-of-array-of-T2, ...>,
 * corresponding to malloc statements and handle objects used in the model;</li>
 * <li>a heap field has the type array-of-array-of-T;</li>
 * <li>a heap object has the type array of type T, which is
 * allocated/deallocated by malloc(handle create)/deallocate(handle destroy)
 * methods;</li>
 * <li>a heap atomic object has the type T, and is an element of a certain heap
 * object;</li>
 * <li>a heap memory unit is a pointer to a heap object, which has type
 * pointer-to-array-of-T, and has the form <code>&di$heap&lt;j,k></code>, where
 * <code>i</code> is the dyscope ID of the heap, <code>j</code> is the index of
 * the heap field that the heap object belongs to, and <code>k</code> is the
 * index of the heap object in the heap field.</li>
 * <li>a heap pointer is any pointer pointing to some part of the heap.</li>
 * </ul>
 * 
 * TODO: malloc pointer This class is part of the symbolic utility, the purpose
 * of which is to factor out the code related to heap.
 * 
 * @author Manchun Zheng
 * 
 */
public class HeapAnalyzer {

	/* *************************** Instance Fields ************************* */

	/**
	 * The symbolic utility to be used.
	 */
	private CommonSymbolicUtility symbolicUtil;

	/**
	 * The symbolic universe for operations on symbolic expressions.
	 */
	private SymbolicUniverse universe;

	/**
	 * Integer object 2.
	 */
	private IntObject twoObj;

	/* ***************************** Constructor *************************** */

	/**
	 * Creates a new instance of a heap analyzer.
	 * 
	 * @param util
	 *            The symbolic utility to be used.
	 */
	HeapAnalyzer(SymbolicUniverse universe, CommonSymbolicUtility util) {
		this.symbolicUtil = util;
		this.universe = universe;
		this.twoObj = universe.intObject(2);
	}

	/* *********************** Package-Private Methods ********************* */

	/**
	 * <p>
	 * Returns the memory unit of a heap object which is involved by the given
	 * pointer. For example,
	 * <code>p = (int*) $malloc($root, sizeof(int)*5)</code> allocates a heap
	 * object that has the type array of int with length 5, and the value of
	 * <code>p</code> is a pointer pointing to the first element of the heap
	 * object.
	 * </p>
	 * 
	 * @param pointer
	 *            A valid pointer that points to some part of a heap.
	 * @return A pointer to a heap object that is involved by the given pointer.
	 */
	SymbolicExpression heapMemUnit(SymbolicExpression pointer) {
		ReferenceExpression ref = symbolicUtil.getSymRef(pointer);
		List<ReferenceExpression> ancestors = symbolicUtil.ancestorsOfRef(ref);

		return symbolicUtil.setSymRef(pointer, ancestors.get(1));
	}

	/**
	 * Extracts the reference expression w.r.t a heap atomic object or a heap
	 * object.
	 * 
	 * @param ref
	 *            The original reference expression.
	 * @param heapAtomicObject
	 *            True iff the context is for a heap atomic object.
	 * @return The reference expression w.r.t. to either a heap atomic object or
	 *         a heap object.
	 */
	Pair<ReferenceExpression, Integer> heapReference(ReferenceExpression ref,
			boolean heapAtomicObject) {
		if (ref.isIdentityReference())
			return new Pair<>(ref, 0);
		else {
			ReferenceExpression parentRef = ((NTReferenceExpression) ref)
					.getParent();
			Pair<ReferenceExpression, Integer> parentResult;

			parentResult = heapReference(parentRef, heapAtomicObject);
			if (!heapAtomicObject) {
				// the case of heap memory unit
				if (parentResult.right < 2)
					return new Pair<>(ref, parentResult.right + 1);
				else {
					ReferenceExpression newRef;

					if (parentResult.right == 2)
						parentRef = universe.identityReference();
					else
						parentRef = parentResult.left;
					if (ref.isArrayElementReference()) {
						newRef = universe.arrayElementReference(parentRef,
								((ArrayElementReference) ref).getIndex());
					} else if (ref.isTupleComponentReference())
						newRef = universe.tupleComponentReference(parentRef,
								((TupleComponentReference) ref).getIndex());
					else
						newRef = universe.unionMemberReference(parentRef,
								((UnionMemberReference) ref).getIndex());
					return new Pair<>(newRef, 3);
				}
			} else {
				// the case of heap atomic object
				if (parentResult.right < 3)
					return new Pair<>(ref, parentResult.right + 1);
				else {
					ReferenceExpression newRef;

					if (parentResult.right == 3)
						parentRef = universe.identityReference();
					else
						parentRef = parentResult.left;
					if (ref.isArrayElementReference()) {
						newRef = universe.arrayElementReference(parentRef,
								((ArrayElementReference) ref).getIndex());
					} else if (ref.isTupleComponentReference())
						newRef = universe.tupleComponentReference(parentRef,
								((TupleComponentReference) ref).getIndex());
					else
						newRef = universe.unionMemberReference(parentRef,
								((UnionMemberReference) ref).getIndex());
					return new Pair<>(newRef, 4);
				}
			}
		}
	}

	/**
	 * Constructs an invalid heap object of a certain type. A heap object
	 * becomes invalid when it gets deallocated. An invalid heap object is a
	 * symbolic constant with the name "INVALID".
	 * 
	 * @param heapObjectType
	 *            The type of the heap object.
	 * @return The invalid heap object of the given type.
	 */
	SymbolicConstant invalidHeapObject(SymbolicType heapObjectType) {
		StringObject name = universe.stringObject(ModelConfiguration.INVALID);

		return universe.symbolicConstant(name, heapObjectType);
	}

	/**
	 * Is this heap empty?
	 * 
	 * @param heapValue
	 *            The heap to be tested.
	 * @return True iff the given heap is empty.
	 */
	boolean isEmptyHeap(SymbolicExpression heapValue) {
		if (heapValue.isNull())
			return true;
		else {
			int count = heapValue.numArguments();

			for (int i = 0; i < count; i++) {
				SymbolicExpression heapField = (SymbolicExpression) heapValue
						.argument(i);
				int numObjects = heapField.numArguments();

				for (int j = 0; j < numObjects; j++) {
					SymbolicExpression heapObj = (SymbolicExpression) heapField
							.argument(j);

					if (!this.isInvalidHeapObject(heapObj))
						return false;
				}
			}
		}
		return true;
	}

	/**
	 * TODO never called? Is the given pointer pointing to the first element of
	 * a heap object, i.e., a heap atomic object? A pointer to a heap atomic
	 * object shall have the form of: <code>&<dn,i,j>[0]</code>
	 * 
	 * @param source
	 *            The source code information for error report.
	 * @param pointer
	 *            The pointer to be checked.
	 * @return True iff the given pointer is pointing to the first element of a
	 *         heap object.
	 */
	boolean isHeapAtomicObjectPointer(CIVLSource source,
			SymbolicExpression pointer) {
		ReferenceExpression ref = symbolicUtil.getSymRef(pointer);
		ArrayElementReference arrayEleRef;

		if (!ref.isArrayElementReference())
			return false;
		arrayEleRef = (ArrayElementReference) ref;
		if (!arrayEleRef.getIndex().isZero())
			return false;
		ref = arrayEleRef.getParent();
		if (!ref.isArrayElementReference())
			return false;
		ref = ((ArrayElementReference) ref).getParent();
		if (!ref.isTupleComponentReference())
			return false;
		ref = ((TupleComponentReference) ref).getParent();
		if (ref.isIdentityReference())
			return true;
		return false;
	}

	/**
	 * Is this heap object invalid? An invalid heap object is a symbolic
	 * constant with the name "INVALID".
	 * 
	 * @param heapObject
	 *            The heap object.
	 * @return True iff the given heap object is invalid.
	 */
	boolean isInvalidHeapObject(SymbolicExpression heapObject) {
		if (heapObject instanceof SymbolicConstant) {
			SymbolicConstant constant = (SymbolicConstant) heapObject;
			StringObject name = constant.name();

			if (name.getString().equals(ModelConfiguration.INVALID))
				return true;
		}
		return false;
	}

	/**
	 * Is the given pointer pointing to a memory space that is part of a heap?
	 * For any dyscope, variable 0 is always the heap.
	 * 
	 * @param pointer
	 *            The pointer to be tested.
	 * 
	 * @return True iff the pointer points to a certain part of some heap.
	 */
	boolean isPointerToHeap(SymbolicExpression pointer) {
		if (pointer.operator() != SymbolicOperator.TUPLE)
			return false;

		int vid = symbolicUtil.getVariableId(null, pointer);

		return vid == 0;
	}

	/**
	 * Computes the reference expression of a given heap pointer w.r.t the
	 * corresponding heap memory unit.
	 * 
	 * @param heapPointer
	 *            The heap pointer.
	 * @return The reference expression of a given pointer w.r.t the
	 *         corresponding heap memory unit.
	 */
	ReferenceExpression referenceToHeapMemUnit(SymbolicExpression pointer) {
		ReferenceExpression ref = (ReferenceExpression) universe.tupleRead(
				pointer, twoObj);
		Pair<ReferenceExpression, Integer> refResult;

		assert this.isPointerToHeap(pointer);
		refResult = this.heapReference(ref, false);
		if (refResult.right == 2)
			return universe.identityReference();
		else
			return refResult.left;
	}

}
