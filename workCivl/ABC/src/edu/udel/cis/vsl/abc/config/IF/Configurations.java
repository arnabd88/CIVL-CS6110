package edu.udel.cis.vsl.abc.config.IF;

import edu.udel.cis.vsl.abc.config.common.CommonConfiguration;

public class Configurations {

	/**
	 * The language of the program being processed. C is the default, but if the
	 * file suffix ends in ".cvl" the command line processor will change it to
	 * CIVL_C. As this is a public static variable, it can also be set manually.
	 */
	public static enum Language {
		/** The programming language C, as specified in the C11 Standard */
		C,
		/**
		 * The programming language CIVL-C, an extension of C for concurrency
		 * and verification. See <a
		 * href="http://vsl.cis.udel.edu/civl">http://vsl.cis.udel.edu/civl</a>.
		 */
		CIVL_C,
		/**
		 * The programming language FORTRAN, as specified in the FORTRAn77
		 * Standard
		 */
		FORTRAN77,
	};

	public static Configuration newMinimalConfiguration() {
		return new CommonConfiguration();
	}

}
