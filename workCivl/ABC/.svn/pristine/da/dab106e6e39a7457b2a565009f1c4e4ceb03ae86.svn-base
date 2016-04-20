package edu.udel.cis.vsl.abc.front.common.astgen;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.config.IF.Configuration;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.front.IF.Front;
import edu.udel.cis.vsl.abc.front.IF.ParseException;
import edu.udel.cis.vsl.abc.front.IF.ParseTree;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.front.c.preproc.CPreprocessor;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

public class LibraryASTFactory {

	public static String STDLIB = "stdlib.h";
	public static String STDIO = "stdio.h";

	/**
	 * 
	 * @param name
	 *            the file name of the header, including the suffix (.h/.cvh)
	 * @return
	 * @throws PreprocessorException
	 * @throws ParseException
	 * @throws SyntaxException
	 */
	public AST getASTofLibrary(String name, Configuration configuration,
			TokenFactory tokenFactory, ASTFactory astFactory)
			throws PreprocessorException, ParseException, SyntaxException {
		CPreprocessor cpreprocessor = (CPreprocessor) Front.newPreprocessor(
				Language.CIVL_C, configuration, tokenFactory);
		CivlcTokenSource tokenSource = cpreprocessor.tokenSourceOfLibrary(name);
		ParseTree parseTree = Front.newParser(Language.CIVL_C).parse(
				tokenSource);

		return Front.newASTBuilder(Language.CIVL_C, configuration, astFactory)
				.getTranslationUnit(parseTree);
	}
}
