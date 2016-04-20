package edu.udel.cis.vsl.civl.kripke.common;

import java.lang.reflect.Constructor;
import java.util.LinkedHashMap;
import java.util.Map;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.config.IF.CIVLConstants;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.kripke.IF.Enabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.kripke.IF.LibraryEnablerLoader;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryLoaderException;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;

public class CommonLibraryEnablerLoader implements LibraryEnablerLoader {

	/* *************************** Instance Fields ************************* */

	/**
	 * The cache of known library enablers.
	 */
	private Map<String, LibraryEnabler> libraryEnablerCache = new LinkedHashMap<>();

	private LibraryEvaluatorLoader libEvaluatorLoader;

	private CIVLConfiguration civlConfig;

	public CommonLibraryEnablerLoader(
			LibraryEvaluatorLoader libEvaluatorLoader,
			CIVLConfiguration civlConfig) {
		this.libEvaluatorLoader = libEvaluatorLoader;
		this.civlConfig = civlConfig;
	}

	/* ********************* Methods from LibraryLoader ******************** */

	@Override
	public LibraryEnabler getLibraryEnabler(String name,
			Enabler primaryEnabler, Evaluator evaluator,
			ModelFactory modelFacotry, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer) throws LibraryLoaderException {
		LibraryEnabler result;

		if (name.equals("assert"))
			name = "asserts";
		if (name.equals("civl-mpi"))
			name = "mpi";
		if (name.equals("civl-pthread"))
			name = "pthread";
		result = libraryEnablerCache.get(name);
		if (result == null) {
			String aClassName = this.className(name, "Enabler");

			try {
				@SuppressWarnings("unchecked")
				Class<? extends LibraryEnabler> aClass = (Class<? extends LibraryEnabler>) Class
						.forName(aClassName);
				Constructor<? extends LibraryEnabler> constructor = aClass
						.getConstructor(String.class, Enabler.class,
								Evaluator.class, ModelFactory.class,
								SymbolicUtility.class, SymbolicAnalyzer.class,
								CIVLConfiguration.class,
								LibraryEnablerLoader.class,
								LibraryEvaluatorLoader.class);

				result = constructor.newInstance(name, primaryEnabler,
						evaluator, modelFacotry, symbolicUtil,
						symbolicAnalyzer, this.civlConfig, this,
						this.libEvaluatorLoader);
			} catch (Exception e) {
				throw new LibraryLoaderException(e.getMessage());
			}
			libraryEnablerCache.put(name, result);
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
