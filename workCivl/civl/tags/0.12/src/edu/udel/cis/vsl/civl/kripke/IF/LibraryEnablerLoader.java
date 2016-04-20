package edu.udel.cis.vsl.civl.kripke.IF;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;

/**
 * The library enabler loader provides the mechanism for loading the library
 * enabler of a certain library.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public interface LibraryEnablerLoader {
	/**
	 * Obtains the library executor of the given name.
	 * 
	 * @param name
	 *            The name of the library whose enabler is to be obtained.
	 * @param primaryEnabler
	 *            The CIVL enabler for normal CIVL statements.
	 * @param evaluator
	 *            The CIVL evaluator of the system.
	 * @param output
	 *            The print stream to be used in the library enabler.
	 * @param modelFacotry
	 *            The model factory to be used in the library enabler.
	 * @param symbolicUtil
	 *            The symbolic utility for manipulations of symbolic
	 *            expressions.
	 * @return The library enabler of the given name.
	 */
	LibraryEnabler getLibraryEnabler(String name, Enabler primaryEnabler,
			Evaluator evaluator, PrintStream output, ModelFactory modelFacotry,
			SymbolicUtility symbolicUtil) throws LibraryLoaderException;
}
