package edu.udel.cis.vsl.civl.semantics.common;

import java.lang.reflect.Constructor;
import java.util.LinkedHashMap;
import java.util.Map;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;

public class CommonLibraryExecutorLoader implements LibraryExecutorLoader {

	/* *************************** Instance Fields ************************* */

	/**
	 * The cache of known library executors.
	 */
	private Map<String, LibraryExecutor> libraryExecutorCache = new LinkedHashMap<>();

	/* ***************** Methods from LibraryExecutorLoader **************** */

	@Override
	public LibraryExecutor getLibraryExecutor(String name,
			Executor primaryExecutor, ModelFactory modelFacotry,
			SymbolicUtility symbolicUtil, SymbolicAnalyzer symbolicAnalyzer,
			CIVLConfiguration civlConfig) throws LibraryLoaderException {
		LibraryExecutor result;

		if (name.equals("assert"))
			name = "asserts";
		result = libraryExecutorCache.get(name);
		if (result == null) {
			String aClassName = className(name, "Executor");

			try {
				@SuppressWarnings("unchecked")
				Class<? extends LibraryExecutor> aClass = (Class<? extends LibraryExecutor>) Class
						.forName(aClassName);
				Constructor<? extends LibraryExecutor> constructor = aClass
						.getConstructor(String.class, Executor.class,
								ModelFactory.class, SymbolicUtility.class,
								SymbolicAnalyzer.class, CIVLConfiguration.class);

				result = constructor.newInstance(name, primaryExecutor,
						modelFacotry, symbolicUtil, symbolicAnalyzer,
						civlConfig);
			} catch (Exception e) {
				throw new LibraryLoaderException(e.getMessage());
			}
			libraryExecutorCache.put(name, result);
		}
		return result;
	}

	/* *************************** Private Methods ************************* */

	/**
	 * Computes the full name of the class of an enabler/executor of a library.
	 * 
	 * @param library
	 *            The name of the library.
	 * @param suffix
	 *            "Enabler" or "Executor", depending on whether the enabler or
	 *            executor is to be used.
	 * @return The full name of the class of the enabler or executor of the
	 *         given library.
	 */
	private String className(String library, String suffix) {
		String result = CIVLConstants.LIBRARY_PREFIX + library + ".Lib"
				+ library + suffix;

		return result;
	}

}
