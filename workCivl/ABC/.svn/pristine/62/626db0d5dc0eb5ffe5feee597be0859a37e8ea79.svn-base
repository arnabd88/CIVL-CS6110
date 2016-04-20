package edu.udel.cis.vsl.abc.analysis.common;

import edu.udel.cis.vsl.abc.analysis.IF.Analyzer;
import edu.udel.cis.vsl.abc.analysis.entity.EntityAnalyzer;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.conversion.IF.ConversionFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.EntityFactory;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * Performs all standard analyses of a Translation Unit: determines and sets
 * Scopes, Types, and Entities.
 * 
 * @author siegel
 * 
 */
public class StandardAnalyzer implements Analyzer {

	private ScopeAnalyzer scopeAnalyzer;

	private EntityAnalyzer entityAnalyzer;

	private CallAnalyzer callAnalyzer;

	public StandardAnalyzer(Language language, Configuration configuration,
			ASTFactory astFactory, EntityFactory entityFactory,
			ConversionFactory conversionFactory) {
		scopeAnalyzer = new ScopeAnalyzer(entityFactory);
		entityAnalyzer = new EntityAnalyzer(language, configuration,
				astFactory, entityFactory, conversionFactory);
		callAnalyzer = new CallAnalyzer();
	}

	@Override
	public void analyze(AST unit) throws SyntaxException {
		scopeAnalyzer.analyze(unit);
		entityAnalyzer.analyze(unit);
		callAnalyzer.analyze(unit);
	}

	@Override
	public void clear(AST unit) {
		scopeAnalyzer.clear(unit);
		entityAnalyzer.clear(unit);
		callAnalyzer.clear(unit);
	}

}
