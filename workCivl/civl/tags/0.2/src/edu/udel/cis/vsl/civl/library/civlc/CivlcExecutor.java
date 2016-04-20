/**
 * 
 */
package edu.udel.cis.vsl.civl.library.civlc;

import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.statement.CallStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.semantics.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.state.State;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.object.StringObject;

/**
 * @author zirkel
 * 
 */
public class CivlcExecutor implements LibraryExecutor {

	private Executor primaryExecutor;

	/**
	 * 
	 */
	public CivlcExecutor(Executor primaryExecutor) {
		this.primaryExecutor = primaryExecutor;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor#name()
	 */
	@Override
	public String name() {
		return "civl";
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
		SymbolicExpression[] arguments;

		if (!(statement instanceof CallStatement)) {
			throw new RuntimeException("Unsupported statement for stdlib: "
					+ statement);
		}
		name = ((CallStatement) statement).function().name();
		arguments = new SymbolicExpression[((CallStatement) statement)
				.arguments().size()];
		for (int i = 0; i < ((CallStatement) statement).arguments().size(); i++) {
			arguments[i] = primaryExecutor.evaluator().evaluate(state, pid,
					((CallStatement) statement).arguments().elementAt(i));
		}
		if (name.name().equals("malloc")) {
			assert arguments.length == 2;

		} else if (name.name().equals("free")) {
			assert arguments.length == 2;

		} else if (name.name().equals("printf")) {
			assert arguments[0] instanceof StringObject;

			System.out.println(arguments[0]);
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
		functions.add("write");
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
		return null;
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
		return null;
	}

}
