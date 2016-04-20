package edu.udel.cis.vsl.abc.analysis.IF;

import edu.udel.cis.vsl.abc.analysis.common.StandardAnalyzer;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.conversion.IF.ConversionFactory;
import edu.udel.cis.vsl.abc.ast.conversion.IF.Conversions;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entities;
import edu.udel.cis.vsl.abc.ast.entity.IF.EntityFactory;
import edu.udel.cis.vsl.abc.ast.type.IF.TypeFactory;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * Simple factory class providing static methods for creating new instances of
 * {@link Analyzer}. This is the prefered way to construct such instances.
 * 
 * @author siegel
 * 
 */
public class Analysis {

	/**
	 * Constructs a new "standard" analyzer. This analyzer determines the scope
	 * of every node, the type of any construct that has a type, the entity to
	 * which every identifier refers, and so on. This "fills in" the missing
	 * information in the AST so that after the analysis completes the AST
	 * methods for getting that information will return the correct answers
	 * instead of <code>null</code>.
	 * 
	 * @param configuration
	 *            the ABC application configuration
	 * @param astFactory
	 *            the factory used for producing AST components
	 * @param entityFactory
	 *            the factory used for producing entities
	 * @param conversionFactory
	 *            the factory used for producing conversions
	 * @return the new standard analyzer
	 */
	public static Analyzer newStandardAnalyzer(Language language,
			Configuration configuration, ASTFactory astFactory,
			EntityFactory entityFactory, ConversionFactory conversionFactory) {
		return new StandardAnalyzer(language, configuration, astFactory,
				entityFactory, conversionFactory);
	}

	/**
	 * A convenience method for performing the standard analyses on an AST. This
	 * creates a new standard analyzer and then applies it to the given AST.
	 * 
	 * @param configuration
	 *            the ABC application configuration
	 * @param ast
	 *            the AST
	 * @throws SyntaxException
	 *             if AST contains a syntax error
	 * @see #newStandardAnalyzer(Configuration, ASTFactory, EntityFactory,
	 *      ConversionFactory)
	 */
	public static void performStandardAnalysis(Language language,
			Configuration configuration, AST ast) throws SyntaxException {
		EntityFactory entityFactory = Entities.newEntityFactory();
		ASTFactory astFactory = ast.getASTFactory();
		TypeFactory typeFactory = astFactory.getTypeFactory();
		ConversionFactory conversionFactory = Conversions
				.newConversionFactory(typeFactory);
		Analyzer analyzer = newStandardAnalyzer(language, configuration,
				astFactory, entityFactory, conversionFactory);

		analyzer.clear(ast);
		analyzer.analyze(ast);
	}

}
