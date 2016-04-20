package edu.udel.cis.vsl.abc.front.fortran.parse;

import org.antlr.runtime.RecognitionException;

import edu.udel.cis.vsl.abc.front.IF.ParseException;
import edu.udel.cis.vsl.abc.front.IF.ParseTree;
import edu.udel.cis.vsl.abc.front.IF.Parser;
import edu.udel.cis.vsl.abc.front.fortran.preproc.FortranLexer;
import edu.udel.cis.vsl.abc.front.fortran.preproc.FortranTokenSource;
import edu.udel.cis.vsl.abc.front.fortran.preproc.FortranTokenStream;
import edu.udel.cis.vsl.abc.token.IF.CivlcTokenSource;

public class FortranParser implements Parser {

	@Override
	public ParseTree parse(CivlcTokenSource tokenSource) throws ParseException {
		FortranTokenSource fortranTokenSource = (FortranTokenSource) tokenSource;
		FortranTokenStream fortranTokenStream = fortranTokenSource
				.getTokenStream();
		FortranParserExtras parser = new FortranParserExtras(fortranTokenStream);

		// FIXME can we get rid of the path in the parser?
		parser.initialize(new String[0],
				FortranParserActionFactory.ACTION_TREE,
				fortranTokenSource.getSourceName(), "");
		while (fortranTokenStream.LA(1) != FortranLexer.EOF) {
			// attempt to parse the current program unit
			boolean error;
			try {
				error = parseProgramUnit(fortranTokenStream, parser);
				// see if we successfully parse the program unit or not
				if (error) {
					throw new ParseException(
							"encounter error when parsing the fortran token stream");
				}
			} catch (RecognitionException e) {
				throw new ParseException(e.getMessage());
			}

		} // end while (not end of file)

		return parser.getAction().getFortranParseTree();

		// // Call the end_of_file action here so that it comes after the
		// // end_program_stmt occurs.
		// getParser().eofAction();
		//
		// // Call the cleanUp method for the give action class. This is more
		// // important in the case of a C action *class* since it could easily
		// // have created memory that's outside of the jvm.
		// getParser().getAction().cleanUp();

	}

	private static boolean parseMainProgram(FortranTokenStream tokens,
			IFortranParser parser, int start) throws RecognitionException {
		// try parsing the main program
		parser.main_program();

		return parser.hasErrorOccurred();
	} // end parseMainProgram()

	private static boolean parseModule(FortranTokenStream tokens,
			IFortranParser parser, int start) throws RecognitionException {
		parser.module();
		return parser.hasErrorOccurred();
	} // end parseModule()

	private static boolean parseSubmodule(FortranTokenStream tokens,
			IFortranParser parser, int start) throws RecognitionException {
		parser.submodule();
		return parser.hasErrorOccurred();
	} // end parseSubmodule()

	private static boolean parseBlockData(FortranTokenStream tokens,
			IFortranParser parser, int start) throws RecognitionException {
		parser.block_data();

		return parser.hasErrorOccurred();
	} // end parseBlockData()

	private static boolean parseSubroutine(FortranTokenStream tokens,
			IFortranParser parser, int start) throws RecognitionException {
		parser.subroutine_subprogram();

		return parser.hasErrorOccurred();
	} // end parserSubroutine()

	private static boolean parseFunction(FortranTokenStream tokens,
			IFortranParser parser, int start) throws RecognitionException {
		parser.ext_function_subprogram();
		return parser.hasErrorOccurred();
	} // end parseFunction()

	private static boolean parseProgramUnit(FortranTokenStream tokens,
			IFortranParser parser) throws RecognitionException {
		int firstToken;
		int lookAhead = 1;
		int start;
		boolean error = false;

		// check for opening with an include file
		parser.checkForInclude();

		// first token on the *line*. will check to see if it's
		// equal to module, block, etc. to determine what rule of
		// the grammar to start with.
		try {
			lookAhead = 1;
			do {
				firstToken = tokens.LA(lookAhead);
				lookAhead++;
			} while (firstToken == FortranLexer.LINE_COMMENT
					|| firstToken == FortranLexer.T_EOS);

			// mark the location of the first token we're looking at
			start = tokens.mark();

			// attempt to match the program unit
			// each of the parse routines called will first try and match
			// the unit they represent (function, block, etc.). if that
			// fails, they may or may not try and match it as a main
			// program; it depends on how it fails.
			//
			// due to Sale's algorithm, we know that if the token matches
			// then the parser should be able to successfully match.
			if (firstToken != FortranLexer.EOF) {
				if (firstToken == FortranLexer.T_MODULE
						&& tokens.LA(lookAhead) != FortranLexer.T_PROCEDURE) {
					// try matching a module
					error = parseModule(tokens, parser, start);
				} else if (firstToken == FortranLexer.T_SUBMODULE) {
					// try matching a submodule
					error = parseSubmodule(tokens, parser, start);
				} else if (firstToken == FortranLexer.T_BLOCKDATA
						|| (firstToken == FortranLexer.T_BLOCK && tokens
								.LA(lookAhead) == FortranLexer.T_DATA)) {
					// try matching block data
					error = parseBlockData(tokens, parser, start);
				} else if (tokens.lookForToken(FortranLexer.T_SUBROUTINE) == true) {
					// try matching a subroutine
					error = parseSubroutine(tokens, parser, start);
				} else if (tokens.lookForToken(FortranLexer.T_FUNCTION) == true) {
					// try matching a function
					error = parseFunction(tokens, parser, start);
				} else {
					// what's left should be a main program
					error = parseMainProgram(tokens, parser, start);
				}// end else(unhandled token)
			}// end if(file had nothing but comments empty)
		} catch (RecognitionException e) {
			e.printStackTrace();
			error = true;
		}// end try/catch(parsing program unit)

		return error;
	} // end parseProgramUnit()

}
