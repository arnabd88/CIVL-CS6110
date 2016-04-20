package edu.udel.cis.vsl.civl.state.persistent;

import java.io.PrintStream;
import java.util.Map;

import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.state.IF.DynamicScope;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;

/**
 * An implementation of {@link DynamicScope} based on the Clojure persistent
 * data structures.
 * 
 * @author siegel
 * 
 */
public class PersistentDynamicScope extends PersistentObject implements
		DynamicScope {

	/************************* Static Fields *************************/

	private static int classCode = PersistentDynamicScope.class.hashCode();

	/************************ Instance Fields ************************/

	/**
	 * Non-null static scope to which this dynamic scope is associated.
	 */
	private Scope lexicalScope;

	/**
	 * The dynamic scope ID of the parent dynamic scope of this dynamic scope.
	 * If this is the root dynamic scope, it has no parent, and this will be -1.
	 */
	private int parent;

	/**
	 * Non-null array of variable values. The symbolic expression in position i
	 * is the value of the variable of index i. May contain null values.
	 */
	private ValueVector valueVector;

	/**
	 * Sets of PIDs of processes that can reach this dynamic scope. How to do a
	 * persistent set of Integers?
	 */
	private IntSet reachers;

	/************************** Constructors *************************/

	/**
	 * Creates new PersistentDynamicScope using the given fields. The data is
	 * not cloned, i.e., the given fields become the fields of this object.
	 * 
	 * @param lexicalScope
	 *            the lexical (static) scope of which this dynamic scope is an
	 *            instance
	 * @param parent
	 *            the dynamic scope ID of the parent dynamic scope, or -1 if
	 *            this is the root dynamic scope
	 * @param valueVector
	 *            the values to assign to each variable in the static scope;
	 *            must have size equal to the number of variables in the static
	 *            scope; must not contain any null values (but may contain the
	 *            symbolic expression NULL, which is not null)
	 * @param reachers
	 *            the set of PIDs of the processes which can "reach" this
	 *            dynamic scope starting from a dynamic scope references from a
	 *            frame in the proc's call stack and following the parent edges
	 *            in the dyscope tree
	 */
	PersistentDynamicScope(Scope lexicalScope, int parent,
			ValueVector valueVector, IntSet reachers) {
		assert valueVector != null
				&& valueVector.size() == lexicalScope.numVariables();
		this.lexicalScope = lexicalScope;
		this.parent = parent;
		this.valueVector = valueVector;
		this.reachers = reachers;
	}

	/******************** Package-private Methods ********************/

	/**
	 * Returns the dyscope ID of the parent of this dynamic scope, or -1 if this
	 * dyscope is the root scope (and therefore has no parent).
	 * 
	 * @return dyscope ID of parent dyscope or -1
	 */
	int getParent() {
		return parent;
	}

	/**
	 * Returns the set of PIDs of the processes which can "reach" this dynamic
	 * scope. A process can reach this dyscope in a state if there is a path (in
	 * the directed graph in which the nodes are the dyscopes and the edges are
	 * the parent edges) starting from a dyscope which is referenced from one of
	 * the frames in the proc's call stack to this dyscope.
	 * 
	 * Since it is an immutable structure no one has to know if it is a copy or
	 * the field itself.
	 * 
	 * @return set of PIDs of procs which can reach this dyscope
	 */
	IntSet getReachers() {
		return reachers;
	}

	/**
	 * Returns the vector variable values for this dyscope. Since it is an
	 * immutable structure no one has to know if it is a copy or the field
	 * itself.
	 * 
	 * @return the variable values
	 */
	ValueVector getValueVector() {
		return valueVector;
	}

	/**
	 * Returns a PersistentDynamicScope which is the same as this one except
	 * that the parent field has the given value. This is the ImmutablePattern
	 * at work.
	 * 
	 * @param newParent
	 *            new value for parent field
	 * @return dynamic scope like this one but with new parent value
	 */
	PersistentDynamicScope setParent(int newParent) {
		return newParent == parent ? this : new PersistentDynamicScope(
				lexicalScope, newParent, valueVector, reachers);
	}

	/**
	 * Returns a PersistentDynamicScope which is the same as this one except
	 * that the reachers field has the given value. This is the ImmutablePattern
	 * at work.
	 * 
	 * @param reachers
	 *            new value for reachers field
	 * @return dynamic scope like this one but with new reachers value
	 */
	PersistentDynamicScope setReachers(IntSet reachers) {
		return reachers == this.reachers ? this : new PersistentDynamicScope(
				lexicalScope, parent, valueVector, reachers);
	}

	/**
	 * Returns a PersistentDynamicScope which is the same as this one except
	 * that the variableValues field has the given value. This is the
	 * ImmutablePattern at work.
	 * 
	 * @param newVariableValues
	 *            new value for variableValues field
	 * @return dynamic scope like this one but with new variableValues field
	 */
	PersistentDynamicScope setValueVector(ValueVector valueVector) {
		return valueVector == this.valueVector ? this
				: new PersistentDynamicScope(lexicalScope, parent, valueVector,
						reachers);
	}

	/**
	 * Returns the number of variables in this dynamic scope, which is the same
	 * as the number in the static scope.
	 * 
	 * @return number of variables
	 */
	int numberOfVariables() {
		return valueVector.size();
	}

	/**
	 * How many processes can reach this dynamic scope? A process p can reach a
	 * dynamic scope d iff there is a path starting from a dynamic scope which
	 * is referenced in a frame on p's call stack to d, following the "parent"
	 * edges in the scope tree.
	 * 
	 * @return the number of processes which can reach this dynamic scope
	 */
	int numberOfReachers() {
		return reachers.size();
	}

	/**
	 * Is this dynamic scope reachable by the process with the given PID?
	 * 
	 * @param pid
	 *            PID of a process; a nonnegative integer
	 * @return true iff this dynamic scope is reachable from the process with
	 *         pid PID
	 */
	boolean reachableByProcess(int pid) {
		return reachers.contains(pid);
	}

	PersistentDynamicScope setReachable(int pid) {
		IntSet newReachers = reachers.add(pid);

		return reachers == newReachers ? this : new PersistentDynamicScope(
				lexicalScope, parent, valueVector, newReachers);
	}

	PersistentDynamicScope unsetReachable(int pid) {
		IntSet newReachers = reachers.remove(pid);

		return reachers == newReachers ? this : new PersistentDynamicScope(
				lexicalScope, parent, valueVector, newReachers);
	}

	/**
	 * Prints human readable representation of this dynamic scope.
	 * 
	 * @param out
	 *            print stream to which the output should be sent
	 * @param id
	 *            some string which should be used to identify this dynamic
	 *            scope
	 * @param prefix
	 *            a string which should be inserted at the beginning of each
	 *            line of output
	 */
	void print(PrintStream out, String id, String prefix) {
		out.println(prefix + "dyscope " + id + " (parent=" + parent + ", static="
				+ lexicalScope.id() + ")");
		out.println(prefix + "| reachers = " + reachers);
		out.println(prefix + "| variables");
		valueVector.print(out, prefix + "| ", lexicalScope);
		out.flush();
	}

	PersistentDynamicScope shiftProcReferences(int pid, int nprocs,
			Map<SymbolicExpression, SymbolicExpression> map,
			SymbolicUniverse universe) {
		ValueVector newValueVector = valueVector.substitute(map, universe,
				lexicalScope.variablesWithProcrefs());
		IntSet newReachers = reachers.shiftDown(pid);

		return newValueVector == valueVector && newReachers == reachers ? this
				: new PersistentDynamicScope(lexicalScope, parent,
						newValueVector, newReachers);
	}

	PersistentDynamicScope simplify(Reasoner reasoner) {
		ValueVector newValueVector = valueVector.simplify(reasoner);

		return newValueVector == valueVector ? this
				: new PersistentDynamicScope(lexicalScope, parent,
						newValueVector, reachers);
	}

	/****************** Methods from PersistentObject ****************/

	@Override
	protected void canonizeChildren(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap) {
		valueVector = valueVector.canonize(universe, canonicMap);
		reachers = reachers.canonize(universe, canonicMap);
	}

	@Override
	protected int computeHashCode() {
		return classCode ^ lexicalScope.hashCode() ^ (1017 * parent)
				^ valueVector.hashCode() ^ reachers.hashCode();
	}

	@Override
	protected boolean computeEquals(PersistentObject obj) {
		if (obj instanceof PersistentDynamicScope) {
			PersistentDynamicScope that = (PersistentDynamicScope) obj;

			return lexicalScope.equals(that.lexicalScope)
					&& parent == that.parent
					&& valueVector.equals(that.valueVector)
					&& reachers.equals(that.reachers);
		}
		return false;
	}

	@Override
	protected PersistentDynamicScope canonize(SymbolicUniverse universe,
			Map<PersistentObject, PersistentObject> canonicMap) {
		return (PersistentDynamicScope) super.canonize(universe, canonicMap);
	}

	/*********************** Methods from Object *********************/

	@Override
	public String toString() {
		return "DynamicScope[static=" + lexicalScope.id() + ", parent="
				+ parent + "]";
	}

	/******************** Methods from DynamicScope *******************/

	@Override
	public SymbolicExpression getValue(int vid) {
		return valueVector.get(vid);
	}

	@Override
	public Scope lexicalScope() {
		return lexicalScope;
	}

	@Override
	public PersistentDynamicScope setValue(int vid, SymbolicExpression value) {
		return setValueVector(valueVector.set(vid, value));
	}

	@Override
	public Iterable<SymbolicExpression> getValues() {
		return valueVector;
	}

	@Override
	public void print(PrintStream out, String prefix) {
		print(out, "", prefix);
	}
}
