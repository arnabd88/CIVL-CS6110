package edu.udel.cis.vsl.civl.library;

import java.lang.reflect.Constructor;
import java.util.LinkedHashMap;
import java.util.Map;

import edu.udel.cis.vsl.civl.semantics.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutor;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryExecutorLoader;

public class CommonLibraryExecutorLoader implements LibraryExecutorLoader {

	private Map<String, LibraryExecutor> libraryExecutorCache = new LinkedHashMap<String, LibraryExecutor>();

	private static String classPrefix = "edu.udel.cis.vsl.civl.library.";

	public CommonLibraryExecutorLoader() {
		// TODO Auto-generated constructor stub
	}

	@SuppressWarnings("unchecked")
	@Override
	public LibraryExecutor getLibraryExecutor(String name,
			Executor primaryExecutor) {
		LibraryExecutor result = libraryExecutorCache.get(name);

		if (result == null) {
			String aClassName = classPrefix + name + "."
					+ capitalizeFirstLetter(name) + "Executor";

			try {
				Class<? extends LibraryExecutor> aClass = (Class<? extends LibraryExecutor>) Class
						.forName(aClassName);
				Constructor<? extends LibraryExecutor> constructor = aClass
						.getConstructor(Executor.class);

				result = constructor.newInstance(primaryExecutor);
			} catch (Exception e) {
				throw new RuntimeException("Unable to load library: " + name
						+ "\n" + e.getMessage());
			}
		}
		return result;
	}

	/**
	 * Returns string identical to given string except that first letter is
	 * capitalized.
	 * 
	 * @throws RuntimeException
	 *             if the string is empty
	 * */
	public static String capitalizeFirstLetter(String string) {
		if (string.length() < 1) {
			throw new RuntimeException("Empty name");
		} else {
			String first = string.substring(0, 1).toUpperCase();
			String rest = string.substring(1);
			String result = first.concat(rest);

			return result;
		}
	}

}
