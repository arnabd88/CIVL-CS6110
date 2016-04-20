/**
 * 
 */
package edu.udel.cis.vsl.civl.library.stdlib;

import java.util.HashSet;
import java.util.Set;
import java.util.Vector;

import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.statement.CallStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.civl.state.StateFactoryIF;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Executor for stdlib function calls.
 * 
 * @author zirkel
 * 
 */
public class StdlibExecutor implements LibraryExecutor {

	private StateFactoryIF factory;
	private SymbolicUniverse universe;
	private Vector<SymbolicType> elementTypes;
	private SymbolicType heapUnionType;
	private SymbolicExpression heap;

	/**
	 * Executor for stdlib function calls.
	 */
	public StdlibExecutor(Executor primaryExecutor) {
		this.factory = primaryExecutor.stateFactory();
		this.universe = primaryExecutor.universe();
		elementTypes = new Vector<SymbolicType>();
		// TODO: Get the set of malloc'd types from the model.
		elementTypes.add(universe.booleanType());
		elementTypes.add(universe.integerType());
		elementTypes.add(universe.realType());
		heapUnionType = universe.unionType(universe.stringObject("heap"),
				elementTypes);
		heap = universe.array(heapUnionType, new Vector<SymbolicExpression>());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor#name()
	 */
	@Override
	public String name() {
		return "stdlib";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor#execute(edu.udel.cis
	 * .vsl.civl.state.State, int,
	 * edu.udel.cis.vsl.civl.model.IF.statement.Statement)
	 */
	@Override
	public State execute(State state, int pid, Statement statement) {
		Identifier name;
		State result = null;

		if (!(statement instanceof CallStatement)) {
			throw new RuntimeException("Unsupported statement for stdlib: "
					+ statement);
		}
		name = ((CallStatement) statement).function().name();
		if (name.name().equals("malloc")) {
			Vector<SymbolicExpression> heapElements = new Vector<SymbolicExpression>();

		} else if (name.name().equals("free")) {

		} else {
			throw new RuntimeException("Unsupported statement for stdlib: "
					+ statement);
		}
		return result;
		// TODO Auto-generated method stub

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor#containsFunction(java
	 * .lang.String)
	 */
	@Override
	public boolean containsFunction(String name) {
		Set<String> functions = new HashSet<String>();

		functions.add("malloc");
		functions.add("free");
		return functions.contains(name);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor#initialize(edu.udel
	 * .cis.vsl.civl.state.State)
	 */
	@Override
	public State initialize(State state) {
		// TODO Auto-generated method stub
		return state;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor#wrapUp(edu.udel.cis
	 * .vsl.civl.state.State)
	 */
	@Override
	public State wrapUp(State state) {
		// TODO Auto-generated method stub
		return state;
	}

}
