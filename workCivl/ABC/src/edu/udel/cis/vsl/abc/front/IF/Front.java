package edu.udel.cis.vsl.abc.front.IF;

import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.front.c.astgen.CASTBuilder;
import edu.udel.cis.vsl.abc.front.c.parse.CParser;
import edu.udel.cis.vsl.abc.front.c.preproc.CPreprocessor;
import edu.udel.cis.vsl.abc.front.fortran.astgen.FortranASTBuilder;
import edu.udel.cis.vsl.abc.front.fortran.parse.FortranParser;
import edu.udel.cis.vsl.abc.front.fortran.preproc.FortranPreprocessor;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

/**
 * Entry point of the front module.
 * 
 * A factory class for producing new instances of {@link Preprocessor},
 * {@link Parser} and {@link ASTBuilder} for using those classes in some common
 * scenarios.
 * 
 * @author siegel
 * 
 */
public class Front {

	/**
	 * Returns a new Preprocessor using the default include paths. A runtime
	 * exception will be thrown if the language is not yet supported.
	 * 
	 * @param language
	 *            the language of the preprocessor
	 * @param config
	 *            the configuration of the translation task (e.g., is svcomp
	 *            enabled?)
	 * @return a new Preprocessor
	 */
	public static Preprocessor newPreprocessor(Language language,
			Configuration config, TokenFactory tokenFactory) {
		switch (language) {
		case C:
		case CIVL_C:
			return new CPreprocessor(config);
		case FORTRAN77:
			return new FortranPreprocessor(config, tokenFactory);
		default:
			throw new ABCRuntimeException(
					"ABC doesn't support preprocessing programs in " + language
							+ ".");
		}
	}

	/**
	 * Creates a new instance of a {@link Parser} for the given language. This
	 * method throws a runtime exception if the given language is not supported
	 * yet.
	 * 
	 * @return the new {@link Parser}
	 */
	public static Parser newParser(Language language) {
		switch (language) {
		case C:
		case CIVL_C:
			return new CParser();
		case FORTRAN77:
			return new FortranParser();
		default:
			throw new ABCRuntimeException(
					"ABC doesn't support parsing programs in " + language + ".");
		}
	}

	/**
	 * Creates an AST builder for the given language. A runtime exception is
	 * thrown if the language is not yet supported.
	 * 
	 * @param language
	 * @param configuration
	 * @param astFactory
	 * @return
	 */
	public static ASTBuilder newASTBuilder(Language language,
			Configuration configuration, ASTFactory astFactory) {
		switch (language) {
		case C:
		case CIVL_C:
			return new CASTBuilder(configuration, astFactory);
		case FORTRAN77:
			return new FortranASTBuilder(configuration, astFactory);
		default:
			throw new ABCRuntimeException(
					"ABC doesn't support generating AST for programs written in "
							+ language + ".");
		}
	}
}
