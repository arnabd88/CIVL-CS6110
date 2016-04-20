package edu.udel.cis.vsl.civl.semantics.IF;

import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.state.State;


/**
 * A Library Executor provides the semantics for system functions defined in a
 * library. It provides a method to "execute" each system library function.
 * 
 */
public interface LibraryExecutor {

	/** Returns the name associated to this executor, for example, "libstdio". */
	String name();
	
	State execute(State state, int pid, Statement statement);
	
	/**
	 * Does the library for which this is the executor contain a function with
	 * the given name?
	 */
	boolean containsFunction(String name);
	
	/**
	 * Initializes the part of the state dealing with the library.
	 */
	State initialize(State state);
	
	/**
	 * A method invoked at any terminal state. The library performs any final
	 * actions before system shutdown and may also check certain properties hold
	 * and throw an exception or log errors if they do not. For example, the MPI
	 * library may check there are no unreceived messages. The stdio library may
	 * check there are no open streams.
	 */
	State wrapUp(State state);
	
}
