package edu.udel.cis.vsl.civl.semantics.IF;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;

/**
 * The library executor loader provides the mechanism for loading the library
 * executor of a certain library.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public interface LibraryExecutorLoader {
	/**
	 * Obtains the library executor of the given name.
	 * 
	 * @param name
	 *            The name of the library whose executor is to be obtained.
	 * @param primaryExecutor
	 *            The CIVL executor of the system.
	 * @param modelFacotry
	 *            The model factory of the system.
	 * @param symbolicUtil
	 *            The symbolic utility for manipulations of symbolic
	 *            expressions.
	 * @param civlConfig
	 *            The CIVL configuration.
	 * @return The library executor of the given name.
	 * @throws LibraryLoaderException
	 *             If the library executor of the given name cannot be found.
	 */
	LibraryExecutor getLibraryExecutor(String name, Executor primaryExecutor,
			ModelFactory modelFacotry, SymbolicUtility symbolicUtil,
			CIVLConfiguration civlConfig) throws LibraryLoaderException;

}
