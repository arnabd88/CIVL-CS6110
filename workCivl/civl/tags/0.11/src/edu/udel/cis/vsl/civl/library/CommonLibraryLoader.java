package edu.udel.cis.vsl.civl.library;

import java.io.PrintStream;
import java.lang.reflect.Constructor;
import java.util.LinkedHashMap;
import java.util.Map;

import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.kripke.Enabler;
import edu.udel.cis.vsl.civl.library.IF.LibraryEnabler;
import edu.udel.cis.vsl.civl.library.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.library.IF.LibraryLoader;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;

/**
 * The loader for library enabler or executor.
 * 
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonLibraryLoader implements LibraryLoader {

	/* **************************** Static Fields ************************** */

	/**
	 * The prefix of the full name of the class of a library enabler/executor.
	 */
	private final static String CLASS_PREFIX = "edu.udel.cis.vsl.civl.library.";

	/* *************************** Instance Fields ************************* */

	/**
	 * The cache of known library enablers.
	 */
	private Map<String, LibraryEnabler> libraryEnablerCache = new LinkedHashMap<>();

	/**
	 * The cache of known library executors.
	 */
	private Map<String, LibraryExecutor> libraryExecutorCache = new LinkedHashMap<>();

	/* ********************* Methods from LibraryLoader ******************** */

	@SuppressWarnings("unchecked")
	@Override
	public LibraryEnabler getLibraryEnabler(String name,
			Enabler primaryEnabler, PrintStream output,
			ModelFactory modelFacotry) {
		LibraryEnabler result = libraryEnablerCache.get(name);

		if (result == null) {
			String aClassName = this.className(name, "Enabler");

			try {
				Class<? extends LibraryEnabler> aClass = (Class<? extends LibraryEnabler>) Class
						.forName(aClassName);
				Constructor<? extends LibraryEnabler> constructor = aClass
						.getConstructor(Enabler.class, PrintStream.class,
								ModelFactory.class);

				result = constructor.newInstance(primaryEnabler, output,
						modelFacotry);
			} catch (Exception e) {
				throw new CIVLInternalException("Unable to load library: "
						+ name + "\n" + e.getMessage(), (CIVLSource) null);
			}
			libraryEnablerCache.put(name, result);
		}
		return result;
	}

	@SuppressWarnings("unchecked")
	@Override
	public LibraryExecutor getLibraryExecutor(String name,
			Executor primaryExecutor, PrintStream output, boolean enablePrintf,
			ModelFactory modelFacotry) {
		LibraryExecutor result = libraryExecutorCache.get(name);

		if (result == null) {
			String aClassName = className(name, "Executor");

			try {
				Class<? extends LibraryExecutor> aClass = (Class<? extends LibraryExecutor>) Class
						.forName(aClassName);
				Constructor<? extends LibraryExecutor> constructor = aClass
						.getConstructor(Executor.class, PrintStream.class,
								boolean.class, ModelFactory.class);

				result = constructor.newInstance(primaryExecutor, output,
						enablePrintf, modelFacotry);
			} catch (Exception e) {
				throw new CIVLInternalException("Unable to load library: "
						+ name + "\n" + e.getMessage(), (CIVLSource) null);
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
		String result = CLASS_PREFIX + library + ".Lib" + library + suffix;

		return result;
	}

}
