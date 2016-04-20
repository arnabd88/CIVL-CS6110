package edu.udel.cis.vsl.abc.front.c.parse;

import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.TokenStream;
import org.antlr.runtime.tree.CommonTree;

import edu.udel.cis.vsl.abc.front.common.parse.OmpPragmaParser;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

public class COmpParser implements OmpPragmaParser {
	public static final int AMPERSAND = OmpParser.AMPERSAND;
	public static final int ATOMIC = OmpParser.OMPATOMIC;
	public static final int BARRIER = OmpParser.BARRIER;
	public static final int BITOR = OmpParser.BITOR;
	public static final int BITXOR = OmpParser.BITXOR;
	public static final int CAPTURE = OmpParser.CAPTURE;
	public static final int COLLAPSE = OmpParser.COLLAPSE;
	public static final int COPYIN = OmpParser.COPYIN;
	public static final int COPYPRIVATE = OmpParser.COPYPRIVATE;
	public static final int CRITICAL = OmpParser.CRITICAL;
	public static final int DATA_CLAUSE = OmpParser.DATA_CLAUSE;
	public static final int DEFAULT = OmpParser.DEFAULT;
	public static final int DYNAMIC = OmpParser.DYNAMIC;
	public static final int FLUSH = OmpParser.FLUSH;
	public static final int FOR = OmpParser.FOR;
	public static final int FST_PRIVATE = OmpParser.FST_PRIVATE;
	public static final int GUIDED = OmpParser.GUIDED;
	public static final int IDENTIFIER = OmpParser.IDENTIFIER;
	public static final int IF = OmpParser.IF;
	public static final int LST_PRIVATE = OmpParser.LST_PRIVATE;
	public static final int MASTER = OmpParser.MASTER;
	public static final int NONE = OmpParser.NONE;
	public static final int NOWAIT = OmpParser.NOWAIT;
	public static final int NUM_THREADS = OmpParser.NUM_THREADS;
	public static final int ORDERED = OmpParser.ORDERED;
	public static final int PARALLEL = OmpParser.PARALLEL;
	public static final int PARALLEL_FOR = OmpParser.PARALLEL_FOR;
	public static final int PARALLEL_SECTIONS = OmpParser.PARALLEL_SECTIONS;
	public static final int PLUS = OmpParser.PLUS;
	public static final int PRIVATE = OmpParser.PRIVATE;
	public static final int READ = OmpParser.READ;
	public static final int REDUCTION = OmpParser.REDUCTION;
	public static final int RUNTIME = OmpParser.RUNTIME;
	public static final int SCHEDULE = OmpParser.SCHEDULE;
	public static final int SECTION = OmpParser.SECTION;
	public static final int SECTIONS = OmpParser.SECTIONS;
	public static final int SEQ_CST = OmpParser.SEQ_CST;
	public static final int SHARED = OmpParser.SHARED;
	public static final int SINGLE = OmpParser.SINGLE;
	public static final int STAR = OmpParser.STAR;
	public static final int STATIC = OmpParser.STATIC;
	public static final int SUB = OmpParser.SUB;
	public static final int THD_PRIVATE = OmpParser.THD_PRIVATE;
	public static final int UNIQUE_FOR = OmpParser.UNIQUE_FOR;
	public static final int UNIQUE_PARALLEL = OmpParser.UNIQUE_PARALLEL;
	public static final int UPDATE = OmpParser.UPDATE;
	public static final int WRITE = OmpParser.WRITE;

	@Override
	public CommonTree parse(Source source, TokenStream tokens) throws SyntaxException {
		OmpParser parser = new OmpParser(tokens);

		try {
			return (CommonTree) parser.openmp_construct().getTree();
		} catch (RecognitionException e) {
			throw new SyntaxException(e.getMessage(), null);
		}
	}
}
