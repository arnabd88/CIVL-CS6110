package edu.udel.cis.vsl.abc.front.c.parse;
import edu.udel.cis.vsl.abc.front.IF.RuntimeParseException;
import edu.udel.cis.vsl.abc.front.c.preproc.*;

// $ANTLR 3.5.2 OmpParser.g 2016-04-11 02:06:30

import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

import org.antlr.runtime.tree.*;


@SuppressWarnings("all")
public class OmpParser extends Parser {
	public static final String[] tokenNames = new String[] {
		"<invalid>", "<EOR>", "<DOWN>", "<UP>", "ABSTRACT", "ALIGNAS", "ALIGNOF", 
		"AMPERSAND", "AND", "ARROW", "ASSIGN", "ASSIGNS", "AT", "ATOMIC", "AUTO", 
		"BIG_O", "BITANDEQ", "BITOR", "BITOREQ", "BITXOR", "BITXOREQ", "BOOL", 
		"BREAK", "BinaryExponentPart", "CALLS", "CASE", "CChar", "CHAR", "CHARACTER_CONSTANT", 
		"CHOOSE", "CIVLATOM", "CIVLATOMIC", "CIVLFOR", "COLLECTIVE", "COLON", 
		"COMMA", "COMMENT", "COMPLEX", "CONST", "CONTIN", "CONTINUE", "DEFAULT", 
		"DEFINED", "DEPENDS", "DERIV", "DEVICE", "DIV", "DIVEQ", "DO", "DOMAIN", 
		"DOT", "DOTDOT", "DOUBLE", "DecimalConstant", "DecimalFloatingConstant", 
		"Digit", "ELLIPSIS", "ELSE", "ENSURES", "ENUM", "EQUALS", "EXISTS", "EXTERN", 
		"EscapeSequence", "ExponentPart", "FALSE", "FATOMIC", "FLOAT", "FLOATING_CONSTANT", 
		"FOR", "FORALL", "FloatingSuffix", "FractionalConstant", "GENERIC", "GLOBAL", 
		"GOTO", "GT", "GTE", "GUARD", "HASH", "HASHHASH", "HEADER_NAME", "HERE", 
		"HexEscape", "HexFractionalConstant", "HexPrefix", "HexQuad", "HexadecimalConstant", 
		"HexadecimalDigit", "HexadecimalFloatingConstant", "IDENTIFIER", "IF", 
		"IMAGINARY", "IMPLIES", "INLINE", "INPUT", "INT", "INTEGER_CONSTANT", 
		"INVARIANT", "IdentifierNonDigit", "IntegerSuffix", "LCURLY", "LEXCON", 
		"LONG", "LPAREN", "LSLIST", "LSQUARE", "LT", "LTE", "LongLongSuffix", 
		"LongSuffix", "MINUSMINUS", "MOD", "MODEQ", "NEQ", "NEWLINE", "NORETURN", 
		"NOT", "NewLine", "NonDigit", "NonZeroDigit", "NotLineStart", "OR", "OTHER", 
		"OUTPUT", "OctalConstant", "OctalDigit", "OctalEscape", "PARFOR", "PDEFINE", 
		"PELIF", "PELSE", "PENDIF", "PERROR", "PIF", "PIFDEF", "PIFNDEF", "PINCLUDE", 
		"PLINE", "PLUS", "PLUSEQ", "PLUSPLUS", "PP_NUMBER", "PRAGMA", "PROCNULL", 
		"PUNDEF", "PURE", "QMARK", "RANGE", "RCURLY", "READS", "REAL", "REGISTER", 
		"REQUIRES", "RESTRICT", "RESULT", "RETURN", "REXCON", "RPAREN", "RSLIST", 
		"RSQUARE", "SCOPEOF", "SChar", "SELF", "SEMI", "SHARED", "SHIFTLEFT", 
		"SHIFTLEFTEQ", "SHIFTRIGHT", "SHIFTRIGHTEQ", "SHORT", "SIGNED", "SIZEOF", 
		"SPAWN", "STAR", "STAREQ", "STATIC", "STATICASSERT", "STRING_LITERAL", 
		"STRUCT", "SUB", "SUBEQ", "SWITCH", "SYSTEM", "THREADLOCAL", "TILDE", 
		"TRUE", "TYPEDEF", "TYPEOF", "UNIFORM", "UNION", "UNSIGNED", "UniversalCharacterName", 
		"UnsignedSuffix", "VOID", "VOLATILE", "WHEN", "WHILE", "WS", "Zero", "BODY", 
		"EXPR", "FILE", "PARAMLIST", "ROOT", "SEQUENCE", "TEXT_BLOCK", "ABSENT", 
		"ABSTRACT_DECLARATOR", "ARGUMENT_LIST", "ARRAY_ELEMENT_DESIGNATOR", "ARRAY_SUFFIX", 
		"BLOCK_ITEM_LIST", "CALL", "CASE_LABELED_STATEMENT", "CAST", "COMPOUND_LITERAL", 
		"COMPOUND_STATEMENT", "CONTRACT", "DECLARATION", "DECLARATION_LIST", "DECLARATION_SPECIFIERS", 
		"DECLARATOR", "DEFAULT_LABELED_STATEMENT", "DERIVATIVE_EXPRESSION", "DESIGNATED_INITIALIZER", 
		"DESIGNATION", "DIRECT_ABSTRACT_DECLARATOR", "DIRECT_DECLARATOR", "ENUMERATION_CONSTANT", 
		"ENUMERATOR", "ENUMERATOR_LIST", "EXPRESSION_STATEMENT", "FIELD_DESIGNATOR", 
		"FUNCTION_DEFINITION", "FUNCTION_SUFFIX", "GENERIC_ASSOCIATION", "GENERIC_ASSOC_LIST", 
		"IDENTIFIER_LABELED_STATEMENT", "IDENTIFIER_LIST", "INDEX", "INITIALIZER_LIST", 
		"INIT_DECLARATOR", "INIT_DECLARATOR_LIST", "OPERATOR", "PARAMETER_DECLARATION", 
		"PARAMETER_LIST", "PARAMETER_TYPE_LIST", "PARENTHESIZED_EXPRESSION", "PARTIAL", 
		"PARTIAL_LIST", "POINTER", "POST_DECREMENT", "POST_INCREMENT", "PRE_DECREMENT", 
		"PRE_INCREMENT", "PROGRAM", "SCALAR_INITIALIZER", "SPECIFIER_QUALIFIER_LIST", 
		"STATEMENT", "STATEMENT_EXPRESSION", "STRUCT_DECLARATION", "STRUCT_DECLARATION_LIST", 
		"STRUCT_DECLARATOR", "STRUCT_DECLARATOR_LIST", "TOKEN_LIST", "TRANSLATION_UNIT", 
		"TYPE", "TYPEDEF_NAME", "TYPEOF_EXPRESSION", "TYPEOF_TYPE", "TYPE_NAME", 
		"TYPE_QUALIFIER_LIST", "BARRIER", "CAPTURE", "COLLAPSE", "COPYIN", "COPYPRIVATE", 
		"CRITICAL", "DYNAMIC", "FLUSH", "FST_PRIVATE", "GUIDED", "LST_PRIVATE", 
		"MASTER", "NONE", "NOWAIT", "NUM_THREADS", "OMPATOMIC", "ORDERED", "PARALLEL", 
		"PRIVATE", "READ", "REDUCTION", "RUNTIME", "SCHEDULE", "SECTION", "SECTIONS", 
		"SEQ_CST", "SINGLE", "THD_PRIVATE", "UPDATE", "WRITE", "DATA_CLAUSE", 
		"FOR_CLAUSE", "PARALLEL_FOR", "PARALLEL_SECTIONS", "UNIQUE_FOR", "UNIQUE_PARALLEL", 
		"516", "517", "518", "519", "520"
	};
	public static final int EOF=-1;
	public static final int ABSTRACT=4;
	public static final int ALIGNAS=5;
	public static final int ALIGNOF=6;
	public static final int AMPERSAND=7;
	public static final int AND=8;
	public static final int ARROW=9;
	public static final int ASSIGN=10;
	public static final int ASSIGNS=11;
	public static final int AT=12;
	public static final int ATOMIC=13;
	public static final int AUTO=14;
	public static final int BIG_O=15;
	public static final int BITANDEQ=16;
	public static final int BITOR=17;
	public static final int BITOREQ=18;
	public static final int BITXOR=19;
	public static final int BITXOREQ=20;
	public static final int BOOL=21;
	public static final int BREAK=22;
	public static final int BinaryExponentPart=23;
	public static final int CALLS=24;
	public static final int CASE=25;
	public static final int CChar=26;
	public static final int CHAR=27;
	public static final int CHARACTER_CONSTANT=28;
	public static final int CHOOSE=29;
	public static final int CIVLATOM=30;
	public static final int CIVLATOMIC=31;
	public static final int CIVLFOR=32;
	public static final int COLLECTIVE=33;
	public static final int COLON=34;
	public static final int COMMA=35;
	public static final int COMMENT=36;
	public static final int COMPLEX=37;
	public static final int CONST=38;
	public static final int CONTIN=39;
	public static final int CONTINUE=40;
	public static final int DEFAULT=41;
	public static final int DEFINED=42;
	public static final int DEPENDS=43;
	public static final int DERIV=44;
	public static final int DEVICE=45;
	public static final int DIV=46;
	public static final int DIVEQ=47;
	public static final int DO=48;
	public static final int DOMAIN=49;
	public static final int DOT=50;
	public static final int DOTDOT=51;
	public static final int DOUBLE=52;
	public static final int DecimalConstant=53;
	public static final int DecimalFloatingConstant=54;
	public static final int Digit=55;
	public static final int ELLIPSIS=56;
	public static final int ELSE=57;
	public static final int ENSURES=58;
	public static final int ENUM=59;
	public static final int EQUALS=60;
	public static final int EXISTS=61;
	public static final int EXTERN=62;
	public static final int EscapeSequence=63;
	public static final int ExponentPart=64;
	public static final int FALSE=65;
	public static final int FATOMIC=66;
	public static final int FLOAT=67;
	public static final int FLOATING_CONSTANT=68;
	public static final int FOR=69;
	public static final int FORALL=70;
	public static final int FloatingSuffix=71;
	public static final int FractionalConstant=72;
	public static final int GENERIC=73;
	public static final int GLOBAL=74;
	public static final int GOTO=75;
	public static final int GT=76;
	public static final int GTE=77;
	public static final int GUARD=78;
	public static final int HASH=79;
	public static final int HASHHASH=80;
	public static final int HEADER_NAME=81;
	public static final int HERE=82;
	public static final int HexEscape=83;
	public static final int HexFractionalConstant=84;
	public static final int HexPrefix=85;
	public static final int HexQuad=86;
	public static final int HexadecimalConstant=87;
	public static final int HexadecimalDigit=88;
	public static final int HexadecimalFloatingConstant=89;
	public static final int IDENTIFIER=90;
	public static final int IF=91;
	public static final int IMAGINARY=92;
	public static final int IMPLIES=93;
	public static final int INLINE=94;
	public static final int INPUT=95;
	public static final int INT=96;
	public static final int INTEGER_CONSTANT=97;
	public static final int INVARIANT=98;
	public static final int IdentifierNonDigit=99;
	public static final int IntegerSuffix=100;
	public static final int LCURLY=101;
	public static final int LEXCON=102;
	public static final int LONG=103;
	public static final int LPAREN=104;
	public static final int LSLIST=105;
	public static final int LSQUARE=106;
	public static final int LT=107;
	public static final int LTE=108;
	public static final int LongLongSuffix=109;
	public static final int LongSuffix=110;
	public static final int MINUSMINUS=111;
	public static final int MOD=112;
	public static final int MODEQ=113;
	public static final int NEQ=114;
	public static final int NEWLINE=115;
	public static final int NORETURN=116;
	public static final int NOT=117;
	public static final int NewLine=118;
	public static final int NonDigit=119;
	public static final int NonZeroDigit=120;
	public static final int NotLineStart=121;
	public static final int OR=122;
	public static final int OTHER=123;
	public static final int OUTPUT=124;
	public static final int OctalConstant=125;
	public static final int OctalDigit=126;
	public static final int OctalEscape=127;
	public static final int PARFOR=128;
	public static final int PDEFINE=129;
	public static final int PELIF=130;
	public static final int PELSE=131;
	public static final int PENDIF=132;
	public static final int PERROR=133;
	public static final int PIF=134;
	public static final int PIFDEF=135;
	public static final int PIFNDEF=136;
	public static final int PINCLUDE=137;
	public static final int PLINE=138;
	public static final int PLUS=139;
	public static final int PLUSEQ=140;
	public static final int PLUSPLUS=141;
	public static final int PP_NUMBER=142;
	public static final int PRAGMA=143;
	public static final int PROCNULL=144;
	public static final int PUNDEF=145;
	public static final int PURE=146;
	public static final int QMARK=147;
	public static final int RANGE=148;
	public static final int RCURLY=149;
	public static final int READS=150;
	public static final int REAL=151;
	public static final int REGISTER=152;
	public static final int REQUIRES=153;
	public static final int RESTRICT=154;
	public static final int RESULT=155;
	public static final int RETURN=156;
	public static final int REXCON=157;
	public static final int RPAREN=158;
	public static final int RSLIST=159;
	public static final int RSQUARE=160;
	public static final int SCOPEOF=161;
	public static final int SChar=162;
	public static final int SELF=163;
	public static final int SEMI=164;
	public static final int SHARED=165;
	public static final int SHIFTLEFT=166;
	public static final int SHIFTLEFTEQ=167;
	public static final int SHIFTRIGHT=168;
	public static final int SHIFTRIGHTEQ=169;
	public static final int SHORT=170;
	public static final int SIGNED=171;
	public static final int SIZEOF=172;
	public static final int SPAWN=173;
	public static final int STAR=174;
	public static final int STAREQ=175;
	public static final int STATIC=176;
	public static final int STATICASSERT=177;
	public static final int STRING_LITERAL=178;
	public static final int STRUCT=179;
	public static final int SUB=180;
	public static final int SUBEQ=181;
	public static final int SWITCH=182;
	public static final int SYSTEM=183;
	public static final int THREADLOCAL=184;
	public static final int TILDE=185;
	public static final int TRUE=186;
	public static final int TYPEDEF=187;
	public static final int TYPEOF=188;
	public static final int UNIFORM=189;
	public static final int UNION=190;
	public static final int UNSIGNED=191;
	public static final int UniversalCharacterName=192;
	public static final int UnsignedSuffix=193;
	public static final int VOID=194;
	public static final int VOLATILE=195;
	public static final int WHEN=196;
	public static final int WHILE=197;
	public static final int WS=198;
	public static final int Zero=199;
	public static final int BODY=200;
	public static final int EXPR=201;
	public static final int FILE=202;
	public static final int PARAMLIST=203;
	public static final int ROOT=204;
	public static final int SEQUENCE=205;
	public static final int TEXT_BLOCK=206;
	public static final int ABSENT=207;
	public static final int ABSTRACT_DECLARATOR=208;
	public static final int ARGUMENT_LIST=209;
	public static final int ARRAY_ELEMENT_DESIGNATOR=210;
	public static final int ARRAY_SUFFIX=211;
	public static final int BLOCK_ITEM_LIST=212;
	public static final int CALL=213;
	public static final int CASE_LABELED_STATEMENT=214;
	public static final int CAST=215;
	public static final int COMPOUND_LITERAL=216;
	public static final int COMPOUND_STATEMENT=217;
	public static final int CONTRACT=218;
	public static final int DECLARATION=219;
	public static final int DECLARATION_LIST=220;
	public static final int DECLARATION_SPECIFIERS=221;
	public static final int DECLARATOR=222;
	public static final int DEFAULT_LABELED_STATEMENT=223;
	public static final int DERIVATIVE_EXPRESSION=224;
	public static final int DESIGNATED_INITIALIZER=225;
	public static final int DESIGNATION=226;
	public static final int DIRECT_ABSTRACT_DECLARATOR=227;
	public static final int DIRECT_DECLARATOR=228;
	public static final int ENUMERATION_CONSTANT=229;
	public static final int ENUMERATOR=230;
	public static final int ENUMERATOR_LIST=231;
	public static final int EXPRESSION_STATEMENT=232;
	public static final int FIELD_DESIGNATOR=233;
	public static final int FUNCTION_DEFINITION=234;
	public static final int FUNCTION_SUFFIX=235;
	public static final int GENERIC_ASSOCIATION=236;
	public static final int GENERIC_ASSOC_LIST=237;
	public static final int IDENTIFIER_LABELED_STATEMENT=238;
	public static final int IDENTIFIER_LIST=239;
	public static final int INDEX=240;
	public static final int INITIALIZER_LIST=241;
	public static final int INIT_DECLARATOR=242;
	public static final int INIT_DECLARATOR_LIST=243;
	public static final int OPERATOR=244;
	public static final int PARAMETER_DECLARATION=245;
	public static final int PARAMETER_LIST=246;
	public static final int PARAMETER_TYPE_LIST=247;
	public static final int PARENTHESIZED_EXPRESSION=248;
	public static final int PARTIAL=249;
	public static final int PARTIAL_LIST=250;
	public static final int POINTER=251;
	public static final int POST_DECREMENT=252;
	public static final int POST_INCREMENT=253;
	public static final int PRE_DECREMENT=254;
	public static final int PRE_INCREMENT=255;
	public static final int PROGRAM=256;
	public static final int SCALAR_INITIALIZER=257;
	public static final int SPECIFIER_QUALIFIER_LIST=258;
	public static final int STATEMENT=259;
	public static final int STATEMENT_EXPRESSION=260;
	public static final int STRUCT_DECLARATION=261;
	public static final int STRUCT_DECLARATION_LIST=262;
	public static final int STRUCT_DECLARATOR=263;
	public static final int STRUCT_DECLARATOR_LIST=264;
	public static final int TOKEN_LIST=265;
	public static final int TRANSLATION_UNIT=266;
	public static final int TYPE=267;
	public static final int TYPEDEF_NAME=268;
	public static final int TYPEOF_EXPRESSION=269;
	public static final int TYPEOF_TYPE=270;
	public static final int TYPE_NAME=271;
	public static final int TYPE_QUALIFIER_LIST=272;
	public static final int BARRIER=273;
	public static final int CAPTURE=274;
	public static final int COLLAPSE=275;
	public static final int COPYIN=276;
	public static final int COPYPRIVATE=277;
	public static final int CRITICAL=278;
	public static final int DYNAMIC=279;
	public static final int FLUSH=280;
	public static final int FST_PRIVATE=281;
	public static final int GUIDED=282;
	public static final int LST_PRIVATE=283;
	public static final int MASTER=284;
	public static final int NONE=285;
	public static final int NOWAIT=286;
	public static final int NUM_THREADS=287;
	public static final int OMPATOMIC=288;
	public static final int ORDERED=289;
	public static final int PARALLEL=290;
	public static final int PRIVATE=291;
	public static final int READ=292;
	public static final int REDUCTION=293;
	public static final int RUNTIME=294;
	public static final int SCHEDULE=295;
	public static final int SECTION=296;
	public static final int SECTIONS=297;
	public static final int SEQ_CST=298;
	public static final int SINGLE=299;
	public static final int THD_PRIVATE=300;
	public static final int UPDATE=301;
	public static final int WRITE=302;
	public static final int DATA_CLAUSE=349;
	public static final int FOR_CLAUSE=390;
	public static final int PARALLEL_FOR=434;
	public static final int PARALLEL_SECTIONS=435;
	public static final int UNIQUE_FOR=514;
	public static final int UNIQUE_PARALLEL=515;

	// delegates
	public OmpParser_CivlCParser gCivlCParser;
	public Parser[] getDelegates() {
		return new Parser[] {gCivlCParser};
	}

	// delegators


	public OmpParser(TokenStream input) {
		this(input, new RecognizerSharedState());
	}
	public OmpParser(TokenStream input, RecognizerSharedState state) {
		super(input, state);
		gCivlCParser = new OmpParser_CivlCParser(input, state, this);
	}

	protected TreeAdaptor adaptor = new CommonTreeAdaptor();

	public void setTreeAdaptor(TreeAdaptor adaptor) {
		this.adaptor = adaptor;
		gCivlCParser.setTreeAdaptor(this.adaptor);
	}
	public TreeAdaptor getTreeAdaptor() {
		return adaptor;
	}
	@Override public String[] getTokenNames() { return OmpParser.tokenNames; }
	@Override public String getGrammarFileName() { return "OmpParser.g"; }


		@Override
		public void displayRecognitionError(String[] tokenNames, RecognitionException e) {
			String hdr = getErrorHeader(e);
			String msg = getErrorMessage(e, tokenNames);
			
			throw new RuntimeParseException(hdr+" "+msg, e.token);
		}

		@Override
		public void emitErrorMessage(String msg) { // don't try to recover!
		    throw new RuntimeParseException(msg);
		}


	public static class openmp_construct_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "openmp_construct"
	// OmpParser.g:49:1: openmp_construct : ( parallel_for_directive | parallel_sections_directive | parallel_directive | for_directive | sections_directive | single_directive | master_directive | critical_directive | ordered_directive | section_directive | ompatomic_directive | barrier_directive | flush_directive | threadprivate_directive );
	public final OmpParser.openmp_construct_return openmp_construct() throws RecognitionException {
		OmpParser.openmp_construct_return retval = new OmpParser.openmp_construct_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope parallel_for_directive1 =null;
		ParserRuleReturnScope parallel_sections_directive2 =null;
		ParserRuleReturnScope parallel_directive3 =null;
		ParserRuleReturnScope for_directive4 =null;
		ParserRuleReturnScope sections_directive5 =null;
		ParserRuleReturnScope single_directive6 =null;
		ParserRuleReturnScope master_directive7 =null;
		ParserRuleReturnScope critical_directive8 =null;
		ParserRuleReturnScope ordered_directive9 =null;
		ParserRuleReturnScope section_directive10 =null;
		ParserRuleReturnScope ompatomic_directive11 =null;
		ParserRuleReturnScope barrier_directive12 =null;
		ParserRuleReturnScope flush_directive13 =null;
		ParserRuleReturnScope threadprivate_directive14 =null;


		try {
			// OmpParser.g:50:3: ( parallel_for_directive | parallel_sections_directive | parallel_directive | for_directive | sections_directive | single_directive | master_directive | critical_directive | ordered_directive | section_directive | ompatomic_directive | barrier_directive | flush_directive | threadprivate_directive )
			int alt1=14;
			switch ( input.LA(1) ) {
			case PARALLEL:
				{
				switch ( input.LA(2) ) {
				case FOR:
					{
					alt1=1;
					}
					break;
				case SECTIONS:
					{
					alt1=2;
					}
					break;
				case EOF:
				case DEFAULT:
				case IF:
				case SHARED:
				case COPYIN:
				case COPYPRIVATE:
				case FST_PRIVATE:
				case LST_PRIVATE:
				case NUM_THREADS:
				case PRIVATE:
				case REDUCTION:
					{
					alt1=3;
					}
					break;
				default:
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 1, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}
				}
				break;
			case FOR:
				{
				alt1=4;
				}
				break;
			case SECTIONS:
				{
				alt1=5;
				}
				break;
			case SINGLE:
				{
				alt1=6;
				}
				break;
			case MASTER:
				{
				alt1=7;
				}
				break;
			case CRITICAL:
				{
				alt1=8;
				}
				break;
			case ORDERED:
				{
				alt1=9;
				}
				break;
			case SECTION:
				{
				alt1=10;
				}
				break;
			case OMPATOMIC:
				{
				alt1=11;
				}
				break;
			case BARRIER:
				{
				alt1=12;
				}
				break;
			case FLUSH:
				{
				alt1=13;
				}
				break;
			case THD_PRIVATE:
				{
				alt1=14;
				}
				break;
			default:
				NoViableAltException nvae =
					new NoViableAltException("", 1, 0, input);
				throw nvae;
			}
			switch (alt1) {
				case 1 :
					// OmpParser.g:51:5: parallel_for_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_parallel_for_directive_in_openmp_construct96);
					parallel_for_directive1=parallel_for_directive();
					state._fsp--;

					adaptor.addChild(root_0, parallel_for_directive1.getTree());

					}
					break;
				case 2 :
					// OmpParser.g:52:5: parallel_sections_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_parallel_sections_directive_in_openmp_construct102);
					parallel_sections_directive2=parallel_sections_directive();
					state._fsp--;

					adaptor.addChild(root_0, parallel_sections_directive2.getTree());

					}
					break;
				case 3 :
					// OmpParser.g:53:5: parallel_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_parallel_directive_in_openmp_construct108);
					parallel_directive3=parallel_directive();
					state._fsp--;

					adaptor.addChild(root_0, parallel_directive3.getTree());

					}
					break;
				case 4 :
					// OmpParser.g:54:5: for_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_for_directive_in_openmp_construct114);
					for_directive4=for_directive();
					state._fsp--;

					adaptor.addChild(root_0, for_directive4.getTree());

					}
					break;
				case 5 :
					// OmpParser.g:55:5: sections_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_sections_directive_in_openmp_construct120);
					sections_directive5=sections_directive();
					state._fsp--;

					adaptor.addChild(root_0, sections_directive5.getTree());

					}
					break;
				case 6 :
					// OmpParser.g:56:5: single_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_single_directive_in_openmp_construct126);
					single_directive6=single_directive();
					state._fsp--;

					adaptor.addChild(root_0, single_directive6.getTree());

					}
					break;
				case 7 :
					// OmpParser.g:57:5: master_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_master_directive_in_openmp_construct132);
					master_directive7=master_directive();
					state._fsp--;

					adaptor.addChild(root_0, master_directive7.getTree());

					}
					break;
				case 8 :
					// OmpParser.g:58:5: critical_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_critical_directive_in_openmp_construct138);
					critical_directive8=critical_directive();
					state._fsp--;

					adaptor.addChild(root_0, critical_directive8.getTree());

					}
					break;
				case 9 :
					// OmpParser.g:59:5: ordered_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_ordered_directive_in_openmp_construct144);
					ordered_directive9=ordered_directive();
					state._fsp--;

					adaptor.addChild(root_0, ordered_directive9.getTree());

					}
					break;
				case 10 :
					// OmpParser.g:60:5: section_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_section_directive_in_openmp_construct150);
					section_directive10=section_directive();
					state._fsp--;

					adaptor.addChild(root_0, section_directive10.getTree());

					}
					break;
				case 11 :
					// OmpParser.g:61:5: ompatomic_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_ompatomic_directive_in_openmp_construct156);
					ompatomic_directive11=ompatomic_directive();
					state._fsp--;

					adaptor.addChild(root_0, ompatomic_directive11.getTree());

					}
					break;
				case 12 :
					// OmpParser.g:62:5: barrier_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_barrier_directive_in_openmp_construct162);
					barrier_directive12=barrier_directive();
					state._fsp--;

					adaptor.addChild(root_0, barrier_directive12.getTree());

					}
					break;
				case 13 :
					// OmpParser.g:63:5: flush_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_flush_directive_in_openmp_construct168);
					flush_directive13=flush_directive();
					state._fsp--;

					adaptor.addChild(root_0, flush_directive13.getTree());

					}
					break;
				case 14 :
					// OmpParser.g:64:5: threadprivate_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_threadprivate_directive_in_openmp_construct174);
					threadprivate_directive14=threadprivate_directive();
					state._fsp--;

					adaptor.addChild(root_0, threadprivate_directive14.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "openmp_construct"


	public static class parallel_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "parallel_directive"
	// OmpParser.g:67:1: parallel_directive : PARALLEL (p+= parallel_clause )* -> ^( PARALLEL ( $p)* ) ;
	public final OmpParser.parallel_directive_return parallel_directive() throws RecognitionException {
		OmpParser.parallel_directive_return retval = new OmpParser.parallel_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PARALLEL15=null;
		List<Object> list_p=null;
		RuleReturnScope p = null;
		Object PARALLEL15_tree=null;
		RewriteRuleTokenStream stream_PARALLEL=new RewriteRuleTokenStream(adaptor,"token PARALLEL");
		RewriteRuleSubtreeStream stream_parallel_clause=new RewriteRuleSubtreeStream(adaptor,"rule parallel_clause");

		try {
			// OmpParser.g:68:3: ( PARALLEL (p+= parallel_clause )* -> ^( PARALLEL ( $p)* ) )
			// OmpParser.g:68:5: PARALLEL (p+= parallel_clause )*
			{
			PARALLEL15=(Token)match(input,PARALLEL,FOLLOW_PARALLEL_in_parallel_directive187);  
			stream_PARALLEL.add(PARALLEL15);

			// OmpParser.g:68:15: (p+= parallel_clause )*
			loop2:
			while (true) {
				int alt2=2;
				int LA2_0 = input.LA(1);
				if ( (LA2_0==DEFAULT||LA2_0==IF||LA2_0==SHARED||(LA2_0 >= COPYIN && LA2_0 <= COPYPRIVATE)||LA2_0==FST_PRIVATE||LA2_0==LST_PRIVATE||LA2_0==NUM_THREADS||LA2_0==PRIVATE||LA2_0==REDUCTION) ) {
					alt2=1;
				}

				switch (alt2) {
				case 1 :
					// OmpParser.g:68:16: p+= parallel_clause
					{
					pushFollow(FOLLOW_parallel_clause_in_parallel_directive193);
					p=parallel_clause();
					state._fsp--;

					stream_parallel_clause.add(p.getTree());
					if (list_p==null) list_p=new ArrayList<Object>();
					list_p.add(p.getTree());
					}
					break;

				default :
					break loop2;
				}
			}

			// AST REWRITE
			// elements: PARALLEL, p
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: p
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_p=new RewriteRuleSubtreeStream(adaptor,"token p",list_p);
			root_0 = (Object)adaptor.nil();
			// 69:3: -> ^( PARALLEL ( $p)* )
			{
				// OmpParser.g:69:6: ^( PARALLEL ( $p)* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_PARALLEL.nextNode(), root_1);
				// OmpParser.g:69:18: ( $p)*
				while ( stream_p.hasNext() ) {
					adaptor.addChild(root_1, stream_p.nextTree());
				}
				stream_p.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "parallel_directive"


	public static class parallel_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "parallel_clause"
	// OmpParser.g:72:1: parallel_clause : ( unique_parallel_clause | data_clause );
	public final OmpParser.parallel_clause_return parallel_clause() throws RecognitionException {
		OmpParser.parallel_clause_return retval = new OmpParser.parallel_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope unique_parallel_clause16 =null;
		ParserRuleReturnScope data_clause17 =null;


		try {
			// OmpParser.g:73:3: ( unique_parallel_clause | data_clause )
			int alt3=2;
			int LA3_0 = input.LA(1);
			if ( (LA3_0==IF||LA3_0==NUM_THREADS) ) {
				alt3=1;
			}
			else if ( (LA3_0==DEFAULT||LA3_0==SHARED||(LA3_0 >= COPYIN && LA3_0 <= COPYPRIVATE)||LA3_0==FST_PRIVATE||LA3_0==LST_PRIVATE||LA3_0==PRIVATE||LA3_0==REDUCTION) ) {
				alt3=2;
			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 3, 0, input);
				throw nvae;
			}

			switch (alt3) {
				case 1 :
					// OmpParser.g:73:5: unique_parallel_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_unique_parallel_clause_in_parallel_clause220);
					unique_parallel_clause16=unique_parallel_clause();
					state._fsp--;

					adaptor.addChild(root_0, unique_parallel_clause16.getTree());

					}
					break;
				case 2 :
					// OmpParser.g:74:5: data_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_data_clause_in_parallel_clause226);
					data_clause17=data_clause();
					state._fsp--;

					adaptor.addChild(root_0, data_clause17.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "parallel_clause"


	public static class master_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "master_directive"
	// OmpParser.g:77:1: master_directive : MASTER -> ^( MASTER ) ;
	public final OmpParser.master_directive_return master_directive() throws RecognitionException {
		OmpParser.master_directive_return retval = new OmpParser.master_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token MASTER18=null;

		Object MASTER18_tree=null;
		RewriteRuleTokenStream stream_MASTER=new RewriteRuleTokenStream(adaptor,"token MASTER");

		try {
			// OmpParser.g:78:3: ( MASTER -> ^( MASTER ) )
			// OmpParser.g:78:5: MASTER
			{
			MASTER18=(Token)match(input,MASTER,FOLLOW_MASTER_in_master_directive241);  
			stream_MASTER.add(MASTER18);

			// AST REWRITE
			// elements: MASTER
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 78:12: -> ^( MASTER )
			{
				// OmpParser.g:78:15: ^( MASTER )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_MASTER.nextNode(), root_1);
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "master_directive"


	public static class critical_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "critical_directive"
	// OmpParser.g:81:1: critical_directive : CRITICAL ( LPAREN id= IDENTIFIER RPAREN )? -> ^( CRITICAL ( $id)? ) ;
	public final OmpParser.critical_directive_return critical_directive() throws RecognitionException {
		OmpParser.critical_directive_return retval = new OmpParser.critical_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token id=null;
		Token CRITICAL19=null;
		Token LPAREN20=null;
		Token RPAREN21=null;

		Object id_tree=null;
		Object CRITICAL19_tree=null;
		Object LPAREN20_tree=null;
		Object RPAREN21_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_CRITICAL=new RewriteRuleTokenStream(adaptor,"token CRITICAL");
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");

		try {
			// OmpParser.g:82:3: ( CRITICAL ( LPAREN id= IDENTIFIER RPAREN )? -> ^( CRITICAL ( $id)? ) )
			// OmpParser.g:82:5: CRITICAL ( LPAREN id= IDENTIFIER RPAREN )?
			{
			CRITICAL19=(Token)match(input,CRITICAL,FOLLOW_CRITICAL_in_critical_directive260);  
			stream_CRITICAL.add(CRITICAL19);

			// OmpParser.g:82:15: ( LPAREN id= IDENTIFIER RPAREN )?
			int alt4=2;
			int LA4_0 = input.LA(1);
			if ( (LA4_0==LPAREN) ) {
				alt4=1;
			}
			switch (alt4) {
				case 1 :
					// OmpParser.g:82:16: LPAREN id= IDENTIFIER RPAREN
					{
					LPAREN20=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_critical_directive264);  
					stream_LPAREN.add(LPAREN20);

					id=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_critical_directive269);  
					stream_IDENTIFIER.add(id);

					RPAREN21=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_critical_directive272);  
					stream_RPAREN.add(RPAREN21);

					}
					break;

			}

			// AST REWRITE
			// elements: id, CRITICAL
			// token labels: id
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleTokenStream stream_id=new RewriteRuleTokenStream(adaptor,"token id",id);
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 83:3: -> ^( CRITICAL ( $id)? )
			{
				// OmpParser.g:83:6: ^( CRITICAL ( $id)? )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_CRITICAL.nextNode(), root_1);
				// OmpParser.g:83:18: ( $id)?
				if ( stream_id.hasNext() ) {
					adaptor.addChild(root_1, stream_id.nextNode());
				}
				stream_id.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "critical_directive"


	public static class sections_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "sections_directive"
	// OmpParser.g:86:1: sections_directive : SECTIONS (s+= sections_clause )* -> ^( SECTIONS ( $s)* ) ;
	public final OmpParser.sections_directive_return sections_directive() throws RecognitionException {
		OmpParser.sections_directive_return retval = new OmpParser.sections_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SECTIONS22=null;
		List<Object> list_s=null;
		RuleReturnScope s = null;
		Object SECTIONS22_tree=null;
		RewriteRuleTokenStream stream_SECTIONS=new RewriteRuleTokenStream(adaptor,"token SECTIONS");
		RewriteRuleSubtreeStream stream_sections_clause=new RewriteRuleSubtreeStream(adaptor,"rule sections_clause");

		try {
			// OmpParser.g:87:3: ( SECTIONS (s+= sections_clause )* -> ^( SECTIONS ( $s)* ) )
			// OmpParser.g:87:5: SECTIONS (s+= sections_clause )*
			{
			SECTIONS22=(Token)match(input,SECTIONS,FOLLOW_SECTIONS_in_sections_directive301);  
			stream_SECTIONS.add(SECTIONS22);

			// OmpParser.g:87:15: (s+= sections_clause )*
			loop5:
			while (true) {
				int alt5=2;
				int LA5_0 = input.LA(1);
				if ( (LA5_0==DEFAULT||LA5_0==SHARED||(LA5_0 >= COPYIN && LA5_0 <= COPYPRIVATE)||LA5_0==FST_PRIVATE||LA5_0==LST_PRIVATE||LA5_0==NOWAIT||LA5_0==PRIVATE||LA5_0==REDUCTION) ) {
					alt5=1;
				}

				switch (alt5) {
				case 1 :
					// OmpParser.g:87:16: s+= sections_clause
					{
					pushFollow(FOLLOW_sections_clause_in_sections_directive307);
					s=sections_clause();
					state._fsp--;

					stream_sections_clause.add(s.getTree());
					if (list_s==null) list_s=new ArrayList<Object>();
					list_s.add(s.getTree());
					}
					break;

				default :
					break loop5;
				}
			}

			// AST REWRITE
			// elements: SECTIONS, s
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: s
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"token s",list_s);
			root_0 = (Object)adaptor.nil();
			// 88:3: -> ^( SECTIONS ( $s)* )
			{
				// OmpParser.g:88:6: ^( SECTIONS ( $s)* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_SECTIONS.nextNode(), root_1);
				// OmpParser.g:88:18: ( $s)*
				while ( stream_s.hasNext() ) {
					adaptor.addChild(root_1, stream_s.nextTree());
				}
				stream_s.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "sections_directive"


	public static class sections_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "sections_clause"
	// OmpParser.g:91:1: sections_clause : ( data_clause | nowait_directive );
	public final OmpParser.sections_clause_return sections_clause() throws RecognitionException {
		OmpParser.sections_clause_return retval = new OmpParser.sections_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope data_clause23 =null;
		ParserRuleReturnScope nowait_directive24 =null;


		try {
			// OmpParser.g:92:3: ( data_clause | nowait_directive )
			int alt6=2;
			int LA6_0 = input.LA(1);
			if ( (LA6_0==DEFAULT||LA6_0==SHARED||(LA6_0 >= COPYIN && LA6_0 <= COPYPRIVATE)||LA6_0==FST_PRIVATE||LA6_0==LST_PRIVATE||LA6_0==PRIVATE||LA6_0==REDUCTION) ) {
				alt6=1;
			}
			else if ( (LA6_0==NOWAIT) ) {
				alt6=2;
			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 6, 0, input);
				throw nvae;
			}

			switch (alt6) {
				case 1 :
					// OmpParser.g:92:5: data_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_data_clause_in_sections_clause334);
					data_clause23=data_clause();
					state._fsp--;

					adaptor.addChild(root_0, data_clause23.getTree());

					}
					break;
				case 2 :
					// OmpParser.g:93:5: nowait_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_nowait_directive_in_sections_clause340);
					nowait_directive24=nowait_directive();
					state._fsp--;

					adaptor.addChild(root_0, nowait_directive24.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "sections_clause"


	public static class section_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "section_directive"
	// OmpParser.g:96:1: section_directive : SECTION -> ^( SECTION ) ;
	public final OmpParser.section_directive_return section_directive() throws RecognitionException {
		OmpParser.section_directive_return retval = new OmpParser.section_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SECTION25=null;

		Object SECTION25_tree=null;
		RewriteRuleTokenStream stream_SECTION=new RewriteRuleTokenStream(adaptor,"token SECTION");

		try {
			// OmpParser.g:97:3: ( SECTION -> ^( SECTION ) )
			// OmpParser.g:97:5: SECTION
			{
			SECTION25=(Token)match(input,SECTION,FOLLOW_SECTION_in_section_directive353);  
			stream_SECTION.add(SECTION25);

			// AST REWRITE
			// elements: SECTION
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 97:13: -> ^( SECTION )
			{
				// OmpParser.g:97:16: ^( SECTION )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_SECTION.nextNode(), root_1);
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "section_directive"


	public static class parallel_for_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "parallel_for_directive"
	// OmpParser.g:100:1: parallel_for_directive : PARALLEL FOR (p+= parallel_for_clause )* -> ^( PARALLEL_FOR ( $p)* ) ;
	public final OmpParser.parallel_for_directive_return parallel_for_directive() throws RecognitionException {
		OmpParser.parallel_for_directive_return retval = new OmpParser.parallel_for_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PARALLEL26=null;
		Token FOR27=null;
		List<Object> list_p=null;
		RuleReturnScope p = null;
		Object PARALLEL26_tree=null;
		Object FOR27_tree=null;
		RewriteRuleTokenStream stream_PARALLEL=new RewriteRuleTokenStream(adaptor,"token PARALLEL");
		RewriteRuleTokenStream stream_FOR=new RewriteRuleTokenStream(adaptor,"token FOR");
		RewriteRuleSubtreeStream stream_parallel_for_clause=new RewriteRuleSubtreeStream(adaptor,"rule parallel_for_clause");

		try {
			// OmpParser.g:101:3: ( PARALLEL FOR (p+= parallel_for_clause )* -> ^( PARALLEL_FOR ( $p)* ) )
			// OmpParser.g:101:5: PARALLEL FOR (p+= parallel_for_clause )*
			{
			PARALLEL26=(Token)match(input,PARALLEL,FOLLOW_PARALLEL_in_parallel_for_directive374);  
			stream_PARALLEL.add(PARALLEL26);

			FOR27=(Token)match(input,FOR,FOLLOW_FOR_in_parallel_for_directive376);  
			stream_FOR.add(FOR27);

			// OmpParser.g:101:19: (p+= parallel_for_clause )*
			loop7:
			while (true) {
				int alt7=2;
				int LA7_0 = input.LA(1);
				if ( (LA7_0==DEFAULT||LA7_0==IF||LA7_0==SHARED||(LA7_0 >= COLLAPSE && LA7_0 <= COPYPRIVATE)||LA7_0==FST_PRIVATE||LA7_0==LST_PRIVATE||LA7_0==NUM_THREADS||LA7_0==ORDERED||LA7_0==PRIVATE||LA7_0==REDUCTION||LA7_0==SCHEDULE) ) {
					alt7=1;
				}

				switch (alt7) {
				case 1 :
					// OmpParser.g:101:19: p+= parallel_for_clause
					{
					pushFollow(FOLLOW_parallel_for_clause_in_parallel_for_directive380);
					p=parallel_for_clause();
					state._fsp--;

					stream_parallel_for_clause.add(p.getTree());
					if (list_p==null) list_p=new ArrayList<Object>();
					list_p.add(p.getTree());
					}
					break;

				default :
					break loop7;
				}
			}

			// AST REWRITE
			// elements: p
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: p
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_p=new RewriteRuleSubtreeStream(adaptor,"token p",list_p);
			root_0 = (Object)adaptor.nil();
			// 102:5: -> ^( PARALLEL_FOR ( $p)* )
			{
				// OmpParser.g:102:8: ^( PARALLEL_FOR ( $p)* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(PARALLEL_FOR, "PARALLEL_FOR"), root_1);
				// OmpParser.g:102:24: ( $p)*
				while ( stream_p.hasNext() ) {
					adaptor.addChild(root_1, stream_p.nextTree());
				}
				stream_p.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "parallel_for_directive"


	public static class parallel_for_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "parallel_for_clause"
	// OmpParser.g:105:1: parallel_for_clause : ( unique_parallel_clause | unique_for_clause | data_clause );
	public final OmpParser.parallel_for_clause_return parallel_for_clause() throws RecognitionException {
		OmpParser.parallel_for_clause_return retval = new OmpParser.parallel_for_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope unique_parallel_clause28 =null;
		ParserRuleReturnScope unique_for_clause29 =null;
		ParserRuleReturnScope data_clause30 =null;


		try {
			// OmpParser.g:106:3: ( unique_parallel_clause | unique_for_clause | data_clause )
			int alt8=3;
			switch ( input.LA(1) ) {
			case IF:
			case NUM_THREADS:
				{
				alt8=1;
				}
				break;
			case COLLAPSE:
			case ORDERED:
			case SCHEDULE:
				{
				alt8=2;
				}
				break;
			case DEFAULT:
			case SHARED:
			case COPYIN:
			case COPYPRIVATE:
			case FST_PRIVATE:
			case LST_PRIVATE:
			case PRIVATE:
			case REDUCTION:
				{
				alt8=3;
				}
				break;
			default:
				NoViableAltException nvae =
					new NoViableAltException("", 8, 0, input);
				throw nvae;
			}
			switch (alt8) {
				case 1 :
					// OmpParser.g:106:5: unique_parallel_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_unique_parallel_clause_in_parallel_for_clause408);
					unique_parallel_clause28=unique_parallel_clause();
					state._fsp--;

					adaptor.addChild(root_0, unique_parallel_clause28.getTree());

					}
					break;
				case 2 :
					// OmpParser.g:107:5: unique_for_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_unique_for_clause_in_parallel_for_clause414);
					unique_for_clause29=unique_for_clause();
					state._fsp--;

					adaptor.addChild(root_0, unique_for_clause29.getTree());

					}
					break;
				case 3 :
					// OmpParser.g:108:5: data_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_data_clause_in_parallel_for_clause420);
					data_clause30=data_clause();
					state._fsp--;

					adaptor.addChild(root_0, data_clause30.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "parallel_for_clause"


	public static class parallel_sections_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "parallel_sections_directive"
	// OmpParser.g:111:1: parallel_sections_directive : PARALLEL SECTIONS (p+= parallel_sections_clause )* -> ^( PARALLEL_SECTIONS ( $p)* ) ;
	public final OmpParser.parallel_sections_directive_return parallel_sections_directive() throws RecognitionException {
		OmpParser.parallel_sections_directive_return retval = new OmpParser.parallel_sections_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PARALLEL31=null;
		Token SECTIONS32=null;
		List<Object> list_p=null;
		RuleReturnScope p = null;
		Object PARALLEL31_tree=null;
		Object SECTIONS32_tree=null;
		RewriteRuleTokenStream stream_PARALLEL=new RewriteRuleTokenStream(adaptor,"token PARALLEL");
		RewriteRuleTokenStream stream_SECTIONS=new RewriteRuleTokenStream(adaptor,"token SECTIONS");
		RewriteRuleSubtreeStream stream_parallel_sections_clause=new RewriteRuleSubtreeStream(adaptor,"rule parallel_sections_clause");

		try {
			// OmpParser.g:112:3: ( PARALLEL SECTIONS (p+= parallel_sections_clause )* -> ^( PARALLEL_SECTIONS ( $p)* ) )
			// OmpParser.g:112:5: PARALLEL SECTIONS (p+= parallel_sections_clause )*
			{
			PARALLEL31=(Token)match(input,PARALLEL,FOLLOW_PARALLEL_in_parallel_sections_directive433);  
			stream_PARALLEL.add(PARALLEL31);

			SECTIONS32=(Token)match(input,SECTIONS,FOLLOW_SECTIONS_in_parallel_sections_directive436);  
			stream_SECTIONS.add(SECTIONS32);

			// OmpParser.g:112:26: (p+= parallel_sections_clause )*
			loop9:
			while (true) {
				int alt9=2;
				int LA9_0 = input.LA(1);
				if ( (LA9_0==DEFAULT||LA9_0==IF||LA9_0==SHARED||(LA9_0 >= COPYIN && LA9_0 <= COPYPRIVATE)||LA9_0==FST_PRIVATE||LA9_0==LST_PRIVATE||LA9_0==NUM_THREADS||LA9_0==PRIVATE||LA9_0==REDUCTION) ) {
					alt9=1;
				}

				switch (alt9) {
				case 1 :
					// OmpParser.g:112:26: p+= parallel_sections_clause
					{
					pushFollow(FOLLOW_parallel_sections_clause_in_parallel_sections_directive441);
					p=parallel_sections_clause();
					state._fsp--;

					stream_parallel_sections_clause.add(p.getTree());
					if (list_p==null) list_p=new ArrayList<Object>();
					list_p.add(p.getTree());
					}
					break;

				default :
					break loop9;
				}
			}

			// AST REWRITE
			// elements: p
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: p
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_p=new RewriteRuleSubtreeStream(adaptor,"token p",list_p);
			root_0 = (Object)adaptor.nil();
			// 113:5: -> ^( PARALLEL_SECTIONS ( $p)* )
			{
				// OmpParser.g:113:8: ^( PARALLEL_SECTIONS ( $p)* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(PARALLEL_SECTIONS, "PARALLEL_SECTIONS"), root_1);
				// OmpParser.g:113:29: ( $p)*
				while ( stream_p.hasNext() ) {
					adaptor.addChild(root_1, stream_p.nextTree());
				}
				stream_p.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "parallel_sections_directive"


	public static class parallel_sections_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "parallel_sections_clause"
	// OmpParser.g:116:1: parallel_sections_clause : ( unique_parallel_clause | data_clause );
	public final OmpParser.parallel_sections_clause_return parallel_sections_clause() throws RecognitionException {
		OmpParser.parallel_sections_clause_return retval = new OmpParser.parallel_sections_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope unique_parallel_clause33 =null;
		ParserRuleReturnScope data_clause34 =null;


		try {
			// OmpParser.g:117:3: ( unique_parallel_clause | data_clause )
			int alt10=2;
			int LA10_0 = input.LA(1);
			if ( (LA10_0==IF||LA10_0==NUM_THREADS) ) {
				alt10=1;
			}
			else if ( (LA10_0==DEFAULT||LA10_0==SHARED||(LA10_0 >= COPYIN && LA10_0 <= COPYPRIVATE)||LA10_0==FST_PRIVATE||LA10_0==LST_PRIVATE||LA10_0==PRIVATE||LA10_0==REDUCTION) ) {
				alt10=2;
			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 10, 0, input);
				throw nvae;
			}

			switch (alt10) {
				case 1 :
					// OmpParser.g:117:5: unique_parallel_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_unique_parallel_clause_in_parallel_sections_clause469);
					unique_parallel_clause33=unique_parallel_clause();
					state._fsp--;

					adaptor.addChild(root_0, unique_parallel_clause33.getTree());

					}
					break;
				case 2 :
					// OmpParser.g:118:5: data_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_data_clause_in_parallel_sections_clause475);
					data_clause34=data_clause();
					state._fsp--;

					adaptor.addChild(root_0, data_clause34.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "parallel_sections_clause"


	public static class single_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "single_directive"
	// OmpParser.g:121:1: single_directive : SINGLE (s+= single_clause )* -> ^( SINGLE ( $s)* ) ;
	public final OmpParser.single_directive_return single_directive() throws RecognitionException {
		OmpParser.single_directive_return retval = new OmpParser.single_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SINGLE35=null;
		List<Object> list_s=null;
		RuleReturnScope s = null;
		Object SINGLE35_tree=null;
		RewriteRuleTokenStream stream_SINGLE=new RewriteRuleTokenStream(adaptor,"token SINGLE");
		RewriteRuleSubtreeStream stream_single_clause=new RewriteRuleSubtreeStream(adaptor,"rule single_clause");

		try {
			// OmpParser.g:122:3: ( SINGLE (s+= single_clause )* -> ^( SINGLE ( $s)* ) )
			// OmpParser.g:122:5: SINGLE (s+= single_clause )*
			{
			SINGLE35=(Token)match(input,SINGLE,FOLLOW_SINGLE_in_single_directive488);  
			stream_SINGLE.add(SINGLE35);

			// OmpParser.g:122:14: (s+= single_clause )*
			loop11:
			while (true) {
				int alt11=2;
				int LA11_0 = input.LA(1);
				if ( (LA11_0==DEFAULT||LA11_0==SHARED||(LA11_0 >= COPYIN && LA11_0 <= COPYPRIVATE)||LA11_0==FST_PRIVATE||LA11_0==LST_PRIVATE||LA11_0==NOWAIT||LA11_0==PRIVATE||LA11_0==REDUCTION) ) {
					alt11=1;
				}

				switch (alt11) {
				case 1 :
					// OmpParser.g:122:14: s+= single_clause
					{
					pushFollow(FOLLOW_single_clause_in_single_directive493);
					s=single_clause();
					state._fsp--;

					stream_single_clause.add(s.getTree());
					if (list_s==null) list_s=new ArrayList<Object>();
					list_s.add(s.getTree());
					}
					break;

				default :
					break loop11;
				}
			}

			// AST REWRITE
			// elements: s, SINGLE
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: s
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"token s",list_s);
			root_0 = (Object)adaptor.nil();
			// 123:5: -> ^( SINGLE ( $s)* )
			{
				// OmpParser.g:123:8: ^( SINGLE ( $s)* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_SINGLE.nextNode(), root_1);
				// OmpParser.g:123:18: ( $s)*
				while ( stream_s.hasNext() ) {
					adaptor.addChild(root_1, stream_s.nextTree());
				}
				stream_s.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "single_directive"


	public static class single_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "single_clause"
	// OmpParser.g:126:1: single_clause : ( data_clause | nowait_directive );
	public final OmpParser.single_clause_return single_clause() throws RecognitionException {
		OmpParser.single_clause_return retval = new OmpParser.single_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope data_clause36 =null;
		ParserRuleReturnScope nowait_directive37 =null;


		try {
			// OmpParser.g:127:3: ( data_clause | nowait_directive )
			int alt12=2;
			int LA12_0 = input.LA(1);
			if ( (LA12_0==DEFAULT||LA12_0==SHARED||(LA12_0 >= COPYIN && LA12_0 <= COPYPRIVATE)||LA12_0==FST_PRIVATE||LA12_0==LST_PRIVATE||LA12_0==PRIVATE||LA12_0==REDUCTION) ) {
				alt12=1;
			}
			else if ( (LA12_0==NOWAIT) ) {
				alt12=2;
			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 12, 0, input);
				throw nvae;
			}

			switch (alt12) {
				case 1 :
					// OmpParser.g:127:5: data_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_data_clause_in_single_clause521);
					data_clause36=data_clause();
					state._fsp--;

					adaptor.addChild(root_0, data_clause36.getTree());

					}
					break;
				case 2 :
					// OmpParser.g:128:5: nowait_directive
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_nowait_directive_in_single_clause527);
					nowait_directive37=nowait_directive();
					state._fsp--;

					adaptor.addChild(root_0, nowait_directive37.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "single_clause"


	public static class barrier_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "barrier_directive"
	// OmpParser.g:131:1: barrier_directive : BARRIER -> ^( BARRIER ) ;
	public final OmpParser.barrier_directive_return barrier_directive() throws RecognitionException {
		OmpParser.barrier_directive_return retval = new OmpParser.barrier_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token BARRIER38=null;

		Object BARRIER38_tree=null;
		RewriteRuleTokenStream stream_BARRIER=new RewriteRuleTokenStream(adaptor,"token BARRIER");

		try {
			// OmpParser.g:132:3: ( BARRIER -> ^( BARRIER ) )
			// OmpParser.g:132:5: BARRIER
			{
			BARRIER38=(Token)match(input,BARRIER,FOLLOW_BARRIER_in_barrier_directive540);  
			stream_BARRIER.add(BARRIER38);

			// AST REWRITE
			// elements: BARRIER
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 132:13: -> ^( BARRIER )
			{
				// OmpParser.g:132:16: ^( BARRIER )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_BARRIER.nextNode(), root_1);
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "barrier_directive"


	public static class ompatomic_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "ompatomic_directive"
	// OmpParser.g:135:1: ompatomic_directive : OMPATOMIC (c0= atomic_clasue )? (c1= seq_cst_clause )? -> ^( OMPATOMIC ( $c0)? ( $c1)? ) ;
	public final OmpParser.ompatomic_directive_return ompatomic_directive() throws RecognitionException {
		OmpParser.ompatomic_directive_return retval = new OmpParser.ompatomic_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token OMPATOMIC39=null;
		ParserRuleReturnScope c0 =null;
		ParserRuleReturnScope c1 =null;

		Object OMPATOMIC39_tree=null;
		RewriteRuleTokenStream stream_OMPATOMIC=new RewriteRuleTokenStream(adaptor,"token OMPATOMIC");
		RewriteRuleSubtreeStream stream_atomic_clasue=new RewriteRuleSubtreeStream(adaptor,"rule atomic_clasue");
		RewriteRuleSubtreeStream stream_seq_cst_clause=new RewriteRuleSubtreeStream(adaptor,"rule seq_cst_clause");

		try {
			// OmpParser.g:136:3: ( OMPATOMIC (c0= atomic_clasue )? (c1= seq_cst_clause )? -> ^( OMPATOMIC ( $c0)? ( $c1)? ) )
			// OmpParser.g:136:5: OMPATOMIC (c0= atomic_clasue )? (c1= seq_cst_clause )?
			{
			OMPATOMIC39=(Token)match(input,OMPATOMIC,FOLLOW_OMPATOMIC_in_ompatomic_directive561);  
			stream_OMPATOMIC.add(OMPATOMIC39);

			// OmpParser.g:136:17: (c0= atomic_clasue )?
			int alt13=2;
			int LA13_0 = input.LA(1);
			if ( (LA13_0==CAPTURE||LA13_0==READ||(LA13_0 >= UPDATE && LA13_0 <= WRITE)) ) {
				alt13=1;
			}
			switch (alt13) {
				case 1 :
					// OmpParser.g:136:17: c0= atomic_clasue
					{
					pushFollow(FOLLOW_atomic_clasue_in_ompatomic_directive565);
					c0=atomic_clasue();
					state._fsp--;

					stream_atomic_clasue.add(c0.getTree());
					}
					break;

			}

			// OmpParser.g:136:35: (c1= seq_cst_clause )?
			int alt14=2;
			int LA14_0 = input.LA(1);
			if ( (LA14_0==SEQ_CST) ) {
				alt14=1;
			}
			switch (alt14) {
				case 1 :
					// OmpParser.g:136:35: c1= seq_cst_clause
					{
					pushFollow(FOLLOW_seq_cst_clause_in_ompatomic_directive570);
					c1=seq_cst_clause();
					state._fsp--;

					stream_seq_cst_clause.add(c1.getTree());
					}
					break;

			}

			// AST REWRITE
			// elements: c0, c1, OMPATOMIC
			// token labels: 
			// rule labels: retval, c1, c0
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_c1=new RewriteRuleSubtreeStream(adaptor,"rule c1",c1!=null?c1.getTree():null);
			RewriteRuleSubtreeStream stream_c0=new RewriteRuleSubtreeStream(adaptor,"rule c0",c0!=null?c0.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 137:5: -> ^( OMPATOMIC ( $c0)? ( $c1)? )
			{
				// OmpParser.g:137:8: ^( OMPATOMIC ( $c0)? ( $c1)? )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_OMPATOMIC.nextNode(), root_1);
				// OmpParser.g:137:21: ( $c0)?
				if ( stream_c0.hasNext() ) {
					adaptor.addChild(root_1, stream_c0.nextTree());
				}
				stream_c0.reset();

				// OmpParser.g:137:26: ( $c1)?
				if ( stream_c1.hasNext() ) {
					adaptor.addChild(root_1, stream_c1.nextTree());
				}
				stream_c1.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "ompatomic_directive"


	public static class atomic_clasue_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "atomic_clasue"
	// OmpParser.g:140:1: atomic_clasue : ( READ | WRITE | UPDATE | CAPTURE );
	public final OmpParser.atomic_clasue_return atomic_clasue() throws RecognitionException {
		OmpParser.atomic_clasue_return retval = new OmpParser.atomic_clasue_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set40=null;

		Object set40_tree=null;

		try {
			// OmpParser.g:141:2: ( READ | WRITE | UPDATE | CAPTURE )
			// OmpParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set40=input.LT(1);
			if ( input.LA(1)==CAPTURE||input.LA(1)==READ||(input.LA(1) >= UPDATE && input.LA(1) <= WRITE) ) {
				input.consume();
				adaptor.addChild(root_0, (Object)adaptor.create(set40));
				state.errorRecovery=false;
			}
			else {
				MismatchedSetException mse = new MismatchedSetException(null,input);
				throw mse;
			}
			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "atomic_clasue"


	public static class seq_cst_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "seq_cst_clause"
	// OmpParser.g:144:1: seq_cst_clause : SEQ_CST ;
	public final OmpParser.seq_cst_clause_return seq_cst_clause() throws RecognitionException {
		OmpParser.seq_cst_clause_return retval = new OmpParser.seq_cst_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SEQ_CST41=null;

		Object SEQ_CST41_tree=null;

		try {
			// OmpParser.g:145:2: ( SEQ_CST )
			// OmpParser.g:145:4: SEQ_CST
			{
			root_0 = (Object)adaptor.nil();


			SEQ_CST41=(Token)match(input,SEQ_CST,FOLLOW_SEQ_CST_in_seq_cst_clause629); 
			SEQ_CST41_tree = (Object)adaptor.create(SEQ_CST41);
			adaptor.addChild(root_0, SEQ_CST41_tree);

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "seq_cst_clause"


	public static class flush_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "flush_directive"
	// OmpParser.g:148:1: flush_directive : FLUSH (f= flush_vars )? -> ^( FLUSH ( $f)? ) ;
	public final OmpParser.flush_directive_return flush_directive() throws RecognitionException {
		OmpParser.flush_directive_return retval = new OmpParser.flush_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token FLUSH42=null;
		ParserRuleReturnScope f =null;

		Object FLUSH42_tree=null;
		RewriteRuleTokenStream stream_FLUSH=new RewriteRuleTokenStream(adaptor,"token FLUSH");
		RewriteRuleSubtreeStream stream_flush_vars=new RewriteRuleSubtreeStream(adaptor,"rule flush_vars");

		try {
			// OmpParser.g:149:3: ( FLUSH (f= flush_vars )? -> ^( FLUSH ( $f)? ) )
			// OmpParser.g:149:5: FLUSH (f= flush_vars )?
			{
			FLUSH42=(Token)match(input,FLUSH,FOLLOW_FLUSH_in_flush_directive642);  
			stream_FLUSH.add(FLUSH42);

			// OmpParser.g:149:13: (f= flush_vars )?
			int alt15=2;
			int LA15_0 = input.LA(1);
			if ( (LA15_0==LPAREN) ) {
				alt15=1;
			}
			switch (alt15) {
				case 1 :
					// OmpParser.g:149:13: f= flush_vars
					{
					pushFollow(FOLLOW_flush_vars_in_flush_directive647);
					f=flush_vars();
					state._fsp--;

					stream_flush_vars.add(f.getTree());
					}
					break;

			}

			// AST REWRITE
			// elements: f, FLUSH
			// token labels: 
			// rule labels: f, retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_f=new RewriteRuleSubtreeStream(adaptor,"rule f",f!=null?f.getTree():null);
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 150:5: -> ^( FLUSH ( $f)? )
			{
				// OmpParser.g:150:8: ^( FLUSH ( $f)? )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_FLUSH.nextNode(), root_1);
				// OmpParser.g:150:17: ( $f)?
				if ( stream_f.hasNext() ) {
					adaptor.addChild(root_1, stream_f.nextTree());
				}
				stream_f.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "flush_directive"


	public static class flush_vars_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "flush_vars"
	// OmpParser.g:153:1: flush_vars : LPAREN i= identifier_list RPAREN -> ^( IDENTIFIER_LIST $i) ;
	public final OmpParser.flush_vars_return flush_vars() throws RecognitionException {
		OmpParser.flush_vars_return retval = new OmpParser.flush_vars_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LPAREN43=null;
		Token RPAREN44=null;
		ParserRuleReturnScope i =null;

		Object LPAREN43_tree=null;
		Object RPAREN44_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_identifier_list=new RewriteRuleSubtreeStream(adaptor,"rule identifier_list");

		try {
			// OmpParser.g:154:3: ( LPAREN i= identifier_list RPAREN -> ^( IDENTIFIER_LIST $i) )
			// OmpParser.g:154:5: LPAREN i= identifier_list RPAREN
			{
			LPAREN43=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_flush_vars675);  
			stream_LPAREN.add(LPAREN43);

			pushFollow(FOLLOW_identifier_list_in_flush_vars681);
			i=identifier_list();
			state._fsp--;

			stream_identifier_list.add(i.getTree());
			RPAREN44=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_flush_vars684);  
			stream_RPAREN.add(RPAREN44);

			// AST REWRITE
			// elements: i
			// token labels: 
			// rule labels: retval, i
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_i=new RewriteRuleSubtreeStream(adaptor,"rule i",i!=null?i.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 155:5: -> ^( IDENTIFIER_LIST $i)
			{
				// OmpParser.g:155:8: ^( IDENTIFIER_LIST $i)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(IDENTIFIER_LIST, "IDENTIFIER_LIST"), root_1);
				adaptor.addChild(root_1, stream_i.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "flush_vars"


	public static class ordered_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "ordered_directive"
	// OmpParser.g:158:1: ordered_directive : ORDERED -> ^( ORDERED ) ;
	public final OmpParser.ordered_directive_return ordered_directive() throws RecognitionException {
		OmpParser.ordered_directive_return retval = new OmpParser.ordered_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ORDERED45=null;

		Object ORDERED45_tree=null;
		RewriteRuleTokenStream stream_ORDERED=new RewriteRuleTokenStream(adaptor,"token ORDERED");

		try {
			// OmpParser.g:159:3: ( ORDERED -> ^( ORDERED ) )
			// OmpParser.g:159:5: ORDERED
			{
			ORDERED45=(Token)match(input,ORDERED,FOLLOW_ORDERED_in_ordered_directive710);  
			stream_ORDERED.add(ORDERED45);

			// AST REWRITE
			// elements: ORDERED
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 159:13: -> ^( ORDERED )
			{
				// OmpParser.g:159:16: ^( ORDERED )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_ORDERED.nextNode(), root_1);
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "ordered_directive"


	public static class nowait_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "nowait_directive"
	// OmpParser.g:162:1: nowait_directive : NOWAIT -> ^( NOWAIT ) ;
	public final OmpParser.nowait_directive_return nowait_directive() throws RecognitionException {
		OmpParser.nowait_directive_return retval = new OmpParser.nowait_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token NOWAIT46=null;

		Object NOWAIT46_tree=null;
		RewriteRuleTokenStream stream_NOWAIT=new RewriteRuleTokenStream(adaptor,"token NOWAIT");

		try {
			// OmpParser.g:163:3: ( NOWAIT -> ^( NOWAIT ) )
			// OmpParser.g:163:5: NOWAIT
			{
			NOWAIT46=(Token)match(input,NOWAIT,FOLLOW_NOWAIT_in_nowait_directive731);  
			stream_NOWAIT.add(NOWAIT46);

			// AST REWRITE
			// elements: NOWAIT
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 163:12: -> ^( NOWAIT )
			{
				// OmpParser.g:163:15: ^( NOWAIT )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_NOWAIT.nextNode(), root_1);
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "nowait_directive"


	public static class threadprivate_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "threadprivate_directive"
	// OmpParser.g:166:1: threadprivate_directive : THD_PRIVATE LPAREN i= identifier_list RPAREN -> ^( THD_PRIVATE $i) ;
	public final OmpParser.threadprivate_directive_return threadprivate_directive() throws RecognitionException {
		OmpParser.threadprivate_directive_return retval = new OmpParser.threadprivate_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token THD_PRIVATE47=null;
		Token LPAREN48=null;
		Token RPAREN49=null;
		ParserRuleReturnScope i =null;

		Object THD_PRIVATE47_tree=null;
		Object LPAREN48_tree=null;
		Object RPAREN49_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleTokenStream stream_THD_PRIVATE=new RewriteRuleTokenStream(adaptor,"token THD_PRIVATE");
		RewriteRuleSubtreeStream stream_identifier_list=new RewriteRuleSubtreeStream(adaptor,"rule identifier_list");

		try {
			// OmpParser.g:167:3: ( THD_PRIVATE LPAREN i= identifier_list RPAREN -> ^( THD_PRIVATE $i) )
			// OmpParser.g:167:5: THD_PRIVATE LPAREN i= identifier_list RPAREN
			{
			THD_PRIVATE47=(Token)match(input,THD_PRIVATE,FOLLOW_THD_PRIVATE_in_threadprivate_directive750);  
			stream_THD_PRIVATE.add(THD_PRIVATE47);

			LPAREN48=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_threadprivate_directive753);  
			stream_LPAREN.add(LPAREN48);

			pushFollow(FOLLOW_identifier_list_in_threadprivate_directive758);
			i=identifier_list();
			state._fsp--;

			stream_identifier_list.add(i.getTree());
			RPAREN49=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_threadprivate_directive761);  
			stream_RPAREN.add(RPAREN49);

			// AST REWRITE
			// elements: THD_PRIVATE, i
			// token labels: 
			// rule labels: retval, i
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_i=new RewriteRuleSubtreeStream(adaptor,"rule i",i!=null?i.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 168:5: -> ^( THD_PRIVATE $i)
			{
				// OmpParser.g:168:8: ^( THD_PRIVATE $i)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_THD_PRIVATE.nextNode(), root_1);
				adaptor.addChild(root_1, stream_i.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "threadprivate_directive"


	public static class for_directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "for_directive"
	// OmpParser.g:171:1: for_directive : FOR (f+= for_clause )* -> ^( FOR ( $f)* ) ;
	public final OmpParser.for_directive_return for_directive() throws RecognitionException {
		OmpParser.for_directive_return retval = new OmpParser.for_directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token FOR50=null;
		List<Object> list_f=null;
		RuleReturnScope f = null;
		Object FOR50_tree=null;
		RewriteRuleTokenStream stream_FOR=new RewriteRuleTokenStream(adaptor,"token FOR");
		RewriteRuleSubtreeStream stream_for_clause=new RewriteRuleSubtreeStream(adaptor,"rule for_clause");

		try {
			// OmpParser.g:172:3: ( FOR (f+= for_clause )* -> ^( FOR ( $f)* ) )
			// OmpParser.g:172:5: FOR (f+= for_clause )*
			{
			FOR50=(Token)match(input,FOR,FOLLOW_FOR_in_for_directive787);  
			stream_FOR.add(FOR50);

			// OmpParser.g:172:10: (f+= for_clause )*
			loop16:
			while (true) {
				int alt16=2;
				int LA16_0 = input.LA(1);
				if ( (LA16_0==DEFAULT||LA16_0==SHARED||(LA16_0 >= COLLAPSE && LA16_0 <= COPYPRIVATE)||LA16_0==FST_PRIVATE||LA16_0==LST_PRIVATE||LA16_0==NOWAIT||LA16_0==ORDERED||LA16_0==PRIVATE||LA16_0==REDUCTION||LA16_0==SCHEDULE) ) {
					alt16=1;
				}

				switch (alt16) {
				case 1 :
					// OmpParser.g:172:11: f+= for_clause
					{
					pushFollow(FOLLOW_for_clause_in_for_directive793);
					f=for_clause();
					state._fsp--;

					stream_for_clause.add(f.getTree());
					if (list_f==null) list_f=new ArrayList<Object>();
					list_f.add(f.getTree());
					}
					break;

				default :
					break loop16;
				}
			}

			// AST REWRITE
			// elements: FOR, f
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: f
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_f=new RewriteRuleSubtreeStream(adaptor,"token f",list_f);
			root_0 = (Object)adaptor.nil();
			// 173:5: -> ^( FOR ( $f)* )
			{
				// OmpParser.g:173:8: ^( FOR ( $f)* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_FOR.nextNode(), root_1);
				// OmpParser.g:173:15: ( $f)*
				while ( stream_f.hasNext() ) {
					adaptor.addChild(root_1, stream_f.nextTree());
				}
				stream_f.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "for_directive"


	public static class for_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "for_clause"
	// OmpParser.g:176:1: for_clause : (u= unique_for_clause -> ^( FOR_CLAUSE $u) |d= data_clause -> ^( FOR_CLAUSE $d) |n= nowait_directive -> ^( FOR_CLAUSE $n) );
	public final OmpParser.for_clause_return for_clause() throws RecognitionException {
		OmpParser.for_clause_return retval = new OmpParser.for_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope u =null;
		ParserRuleReturnScope d =null;
		ParserRuleReturnScope n =null;

		RewriteRuleSubtreeStream stream_data_clause=new RewriteRuleSubtreeStream(adaptor,"rule data_clause");
		RewriteRuleSubtreeStream stream_unique_for_clause=new RewriteRuleSubtreeStream(adaptor,"rule unique_for_clause");
		RewriteRuleSubtreeStream stream_nowait_directive=new RewriteRuleSubtreeStream(adaptor,"rule nowait_directive");

		try {
			// OmpParser.g:177:3: (u= unique_for_clause -> ^( FOR_CLAUSE $u) |d= data_clause -> ^( FOR_CLAUSE $d) |n= nowait_directive -> ^( FOR_CLAUSE $n) )
			int alt17=3;
			switch ( input.LA(1) ) {
			case COLLAPSE:
			case ORDERED:
			case SCHEDULE:
				{
				alt17=1;
				}
				break;
			case DEFAULT:
			case SHARED:
			case COPYIN:
			case COPYPRIVATE:
			case FST_PRIVATE:
			case LST_PRIVATE:
			case PRIVATE:
			case REDUCTION:
				{
				alt17=2;
				}
				break;
			case NOWAIT:
				{
				alt17=3;
				}
				break;
			default:
				NoViableAltException nvae =
					new NoViableAltException("", 17, 0, input);
				throw nvae;
			}
			switch (alt17) {
				case 1 :
					// OmpParser.g:177:5: u= unique_for_clause
					{
					pushFollow(FOLLOW_unique_for_clause_in_for_clause824);
					u=unique_for_clause();
					state._fsp--;

					stream_unique_for_clause.add(u.getTree());
					// AST REWRITE
					// elements: u
					// token labels: 
					// rule labels: retval, u
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_u=new RewriteRuleSubtreeStream(adaptor,"rule u",u!=null?u.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 177:25: -> ^( FOR_CLAUSE $u)
					{
						// OmpParser.g:177:28: ^( FOR_CLAUSE $u)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FOR_CLAUSE, "FOR_CLAUSE"), root_1);
						adaptor.addChild(root_1, stream_u.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 2 :
					// OmpParser.g:178:5: d= data_clause
					{
					pushFollow(FOLLOW_data_clause_in_for_clause841);
					d=data_clause();
					state._fsp--;

					stream_data_clause.add(d.getTree());
					// AST REWRITE
					// elements: d
					// token labels: 
					// rule labels: retval, d
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_d=new RewriteRuleSubtreeStream(adaptor,"rule d",d!=null?d.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 178:19: -> ^( FOR_CLAUSE $d)
					{
						// OmpParser.g:178:22: ^( FOR_CLAUSE $d)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FOR_CLAUSE, "FOR_CLAUSE"), root_1);
						adaptor.addChild(root_1, stream_d.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 3 :
					// OmpParser.g:179:5: n= nowait_directive
					{
					pushFollow(FOLLOW_nowait_directive_in_for_clause858);
					n=nowait_directive();
					state._fsp--;

					stream_nowait_directive.add(n.getTree());
					// AST REWRITE
					// elements: n
					// token labels: 
					// rule labels: retval, n
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_n=new RewriteRuleSubtreeStream(adaptor,"rule n",n!=null?n.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 179:24: -> ^( FOR_CLAUSE $n)
					{
						// OmpParser.g:179:27: ^( FOR_CLAUSE $n)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FOR_CLAUSE, "FOR_CLAUSE"), root_1);
						adaptor.addChild(root_1, stream_n.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "for_clause"


	public static class unique_for_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "unique_for_clause"
	// OmpParser.g:182:1: unique_for_clause : ( ORDERED -> ^( UNIQUE_FOR ORDERED ) |s1= schedule_clause -> ^( UNIQUE_FOR $s1) |c= collapse_clause -> ^( UNIQUE_FOR $c) );
	public final OmpParser.unique_for_clause_return unique_for_clause() throws RecognitionException {
		OmpParser.unique_for_clause_return retval = new OmpParser.unique_for_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ORDERED51=null;
		ParserRuleReturnScope s1 =null;
		ParserRuleReturnScope c =null;

		Object ORDERED51_tree=null;
		RewriteRuleTokenStream stream_ORDERED=new RewriteRuleTokenStream(adaptor,"token ORDERED");
		RewriteRuleSubtreeStream stream_collapse_clause=new RewriteRuleSubtreeStream(adaptor,"rule collapse_clause");
		RewriteRuleSubtreeStream stream_schedule_clause=new RewriteRuleSubtreeStream(adaptor,"rule schedule_clause");

		try {
			// OmpParser.g:183:3: ( ORDERED -> ^( UNIQUE_FOR ORDERED ) |s1= schedule_clause -> ^( UNIQUE_FOR $s1) |c= collapse_clause -> ^( UNIQUE_FOR $c) )
			int alt18=3;
			switch ( input.LA(1) ) {
			case ORDERED:
				{
				alt18=1;
				}
				break;
			case SCHEDULE:
				{
				alt18=2;
				}
				break;
			case COLLAPSE:
				{
				alt18=3;
				}
				break;
			default:
				NoViableAltException nvae =
					new NoViableAltException("", 18, 0, input);
				throw nvae;
			}
			switch (alt18) {
				case 1 :
					// OmpParser.g:183:5: ORDERED
					{
					ORDERED51=(Token)match(input,ORDERED,FOLLOW_ORDERED_in_unique_for_clause880);  
					stream_ORDERED.add(ORDERED51);

					// AST REWRITE
					// elements: ORDERED
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 183:13: -> ^( UNIQUE_FOR ORDERED )
					{
						// OmpParser.g:183:15: ^( UNIQUE_FOR ORDERED )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(UNIQUE_FOR, "UNIQUE_FOR"), root_1);
						adaptor.addChild(root_1, stream_ORDERED.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 2 :
					// OmpParser.g:184:5: s1= schedule_clause
					{
					pushFollow(FOLLOW_schedule_clause_in_unique_for_clause895);
					s1=schedule_clause();
					state._fsp--;

					stream_schedule_clause.add(s1.getTree());
					// AST REWRITE
					// elements: s1
					// token labels: 
					// rule labels: retval, s1
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_s1=new RewriteRuleSubtreeStream(adaptor,"rule s1",s1!=null?s1.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 184:24: -> ^( UNIQUE_FOR $s1)
					{
						// OmpParser.g:184:27: ^( UNIQUE_FOR $s1)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(UNIQUE_FOR, "UNIQUE_FOR"), root_1);
						adaptor.addChild(root_1, stream_s1.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 3 :
					// OmpParser.g:185:5: c= collapse_clause
					{
					pushFollow(FOLLOW_collapse_clause_in_unique_for_clause912);
					c=collapse_clause();
					state._fsp--;

					stream_collapse_clause.add(c.getTree());
					// AST REWRITE
					// elements: c
					// token labels: 
					// rule labels: retval, c
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_c=new RewriteRuleSubtreeStream(adaptor,"rule c",c!=null?c.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 185:23: -> ^( UNIQUE_FOR $c)
					{
						// OmpParser.g:185:26: ^( UNIQUE_FOR $c)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(UNIQUE_FOR, "UNIQUE_FOR"), root_1);
						adaptor.addChild(root_1, stream_c.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "unique_for_clause"


	public static class schedule_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "schedule_clause"
	// OmpParser.g:188:1: schedule_clause : ( SCHEDULE LPAREN s1= schedule_kind COMMA e= expression RPAREN -> ^( SCHEDULE $s1 $e) | SCHEDULE LPAREN s= schedule_kind RPAREN -> ^( SCHEDULE $s) );
	public final OmpParser.schedule_clause_return schedule_clause() throws RecognitionException {
		OmpParser.schedule_clause_return retval = new OmpParser.schedule_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SCHEDULE52=null;
		Token LPAREN53=null;
		Token COMMA54=null;
		Token RPAREN55=null;
		Token SCHEDULE56=null;
		Token LPAREN57=null;
		Token RPAREN58=null;
		ParserRuleReturnScope s1 =null;
		ParserRuleReturnScope e =null;
		ParserRuleReturnScope s =null;

		Object SCHEDULE52_tree=null;
		Object LPAREN53_tree=null;
		Object COMMA54_tree=null;
		Object RPAREN55_tree=null;
		Object SCHEDULE56_tree=null;
		Object LPAREN57_tree=null;
		Object RPAREN58_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_SCHEDULE=new RewriteRuleTokenStream(adaptor,"token SCHEDULE");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_schedule_kind=new RewriteRuleSubtreeStream(adaptor,"rule schedule_kind");

		try {
			// OmpParser.g:189:2: ( SCHEDULE LPAREN s1= schedule_kind COMMA e= expression RPAREN -> ^( SCHEDULE $s1 $e) | SCHEDULE LPAREN s= schedule_kind RPAREN -> ^( SCHEDULE $s) )
			int alt19=2;
			int LA19_0 = input.LA(1);
			if ( (LA19_0==SCHEDULE) ) {
				int LA19_1 = input.LA(2);
				if ( (LA19_1==LPAREN) ) {
					switch ( input.LA(3) ) {
					case STATIC:
						{
						int LA19_3 = input.LA(4);
						if ( (LA19_3==COMMA) ) {
							alt19=1;
						}
						else if ( (LA19_3==RPAREN) ) {
							alt19=2;
						}

						else {
							int nvaeMark = input.mark();
							try {
								for (int nvaeConsume = 0; nvaeConsume < 4 - 1; nvaeConsume++) {
									input.consume();
								}
								NoViableAltException nvae =
									new NoViableAltException("", 19, 3, input);
								throw nvae;
							} finally {
								input.rewind(nvaeMark);
							}
						}

						}
						break;
					case DYNAMIC:
						{
						int LA19_4 = input.LA(4);
						if ( (LA19_4==COMMA) ) {
							alt19=1;
						}
						else if ( (LA19_4==RPAREN) ) {
							alt19=2;
						}

						else {
							int nvaeMark = input.mark();
							try {
								for (int nvaeConsume = 0; nvaeConsume < 4 - 1; nvaeConsume++) {
									input.consume();
								}
								NoViableAltException nvae =
									new NoViableAltException("", 19, 4, input);
								throw nvae;
							} finally {
								input.rewind(nvaeMark);
							}
						}

						}
						break;
					case GUIDED:
						{
						int LA19_5 = input.LA(4);
						if ( (LA19_5==COMMA) ) {
							alt19=1;
						}
						else if ( (LA19_5==RPAREN) ) {
							alt19=2;
						}

						else {
							int nvaeMark = input.mark();
							try {
								for (int nvaeConsume = 0; nvaeConsume < 4 - 1; nvaeConsume++) {
									input.consume();
								}
								NoViableAltException nvae =
									new NoViableAltException("", 19, 5, input);
								throw nvae;
							} finally {
								input.rewind(nvaeMark);
							}
						}

						}
						break;
					case RUNTIME:
						{
						int LA19_6 = input.LA(4);
						if ( (LA19_6==COMMA) ) {
							alt19=1;
						}
						else if ( (LA19_6==RPAREN) ) {
							alt19=2;
						}

						else {
							int nvaeMark = input.mark();
							try {
								for (int nvaeConsume = 0; nvaeConsume < 4 - 1; nvaeConsume++) {
									input.consume();
								}
								NoViableAltException nvae =
									new NoViableAltException("", 19, 6, input);
								throw nvae;
							} finally {
								input.rewind(nvaeMark);
							}
						}

						}
						break;
					default:
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 19, 2, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}
				}

				else {
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 19, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 19, 0, input);
				throw nvae;
			}

			switch (alt19) {
				case 1 :
					// OmpParser.g:189:4: SCHEDULE LPAREN s1= schedule_kind COMMA e= expression RPAREN
					{
					SCHEDULE52=(Token)match(input,SCHEDULE,FOLLOW_SCHEDULE_in_schedule_clause935);  
					stream_SCHEDULE.add(SCHEDULE52);

					LPAREN53=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_schedule_clause938);  
					stream_LPAREN.add(LPAREN53);

					pushFollow(FOLLOW_schedule_kind_in_schedule_clause943);
					s1=schedule_kind();
					state._fsp--;

					stream_schedule_kind.add(s1.getTree());
					COMMA54=(Token)match(input,COMMA,FOLLOW_COMMA_in_schedule_clause946);  
					stream_COMMA.add(COMMA54);

					pushFollow(FOLLOW_expression_in_schedule_clause951);
					e=expression();
					state._fsp--;

					stream_expression.add(e.getTree());
					RPAREN55=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_schedule_clause954);  
					stream_RPAREN.add(RPAREN55);

					// AST REWRITE
					// elements: e, SCHEDULE, s1
					// token labels: 
					// rule labels: retval, s1, e
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_s1=new RewriteRuleSubtreeStream(adaptor,"rule s1",s1!=null?s1.getTree():null);
					RewriteRuleSubtreeStream stream_e=new RewriteRuleSubtreeStream(adaptor,"rule e",e!=null?e.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 190:7: -> ^( SCHEDULE $s1 $e)
					{
						// OmpParser.g:190:10: ^( SCHEDULE $s1 $e)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_SCHEDULE.nextNode(), root_1);
						adaptor.addChild(root_1, stream_s1.nextTree());
						adaptor.addChild(root_1, stream_e.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 2 :
					// OmpParser.g:191:8: SCHEDULE LPAREN s= schedule_kind RPAREN
					{
					SCHEDULE56=(Token)match(input,SCHEDULE,FOLLOW_SCHEDULE_in_schedule_clause981);  
					stream_SCHEDULE.add(SCHEDULE56);

					LPAREN57=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_schedule_clause984);  
					stream_LPAREN.add(LPAREN57);

					pushFollow(FOLLOW_schedule_kind_in_schedule_clause989);
					s=schedule_kind();
					state._fsp--;

					stream_schedule_kind.add(s.getTree());
					RPAREN58=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_schedule_clause992);  
					stream_RPAREN.add(RPAREN58);

					// AST REWRITE
					// elements: SCHEDULE, s
					// token labels: 
					// rule labels: retval, s
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"rule s",s!=null?s.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 192:4: -> ^( SCHEDULE $s)
					{
						// OmpParser.g:192:7: ^( SCHEDULE $s)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_SCHEDULE.nextNode(), root_1);
						adaptor.addChild(root_1, stream_s.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "schedule_clause"


	public static class collapse_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "collapse_clause"
	// OmpParser.g:195:1: collapse_clause : COLLAPSE LPAREN i= INTEGER_CONSTANT RPAREN -> ^( COLLAPSE $i) ;
	public final OmpParser.collapse_clause_return collapse_clause() throws RecognitionException {
		OmpParser.collapse_clause_return retval = new OmpParser.collapse_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token i=null;
		Token COLLAPSE59=null;
		Token LPAREN60=null;
		Token RPAREN61=null;

		Object i_tree=null;
		Object COLLAPSE59_tree=null;
		Object LPAREN60_tree=null;
		Object RPAREN61_tree=null;
		RewriteRuleTokenStream stream_COLLAPSE=new RewriteRuleTokenStream(adaptor,"token COLLAPSE");
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_INTEGER_CONSTANT=new RewriteRuleTokenStream(adaptor,"token INTEGER_CONSTANT");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");

		try {
			// OmpParser.g:196:2: ( COLLAPSE LPAREN i= INTEGER_CONSTANT RPAREN -> ^( COLLAPSE $i) )
			// OmpParser.g:197:2: COLLAPSE LPAREN i= INTEGER_CONSTANT RPAREN
			{
			COLLAPSE59=(Token)match(input,COLLAPSE,FOLLOW_COLLAPSE_in_collapse_clause1017);  
			stream_COLLAPSE.add(COLLAPSE59);

			LPAREN60=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_collapse_clause1020);  
			stream_LPAREN.add(LPAREN60);

			i=(Token)match(input,INTEGER_CONSTANT,FOLLOW_INTEGER_CONSTANT_in_collapse_clause1025);  
			stream_INTEGER_CONSTANT.add(i);

			RPAREN61=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_collapse_clause1028);  
			stream_RPAREN.add(RPAREN61);

			// AST REWRITE
			// elements: COLLAPSE, i
			// token labels: i
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleTokenStream stream_i=new RewriteRuleTokenStream(adaptor,"token i",i);
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 198:5: -> ^( COLLAPSE $i)
			{
				// OmpParser.g:198:8: ^( COLLAPSE $i)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_COLLAPSE.nextNode(), root_1);
				adaptor.addChild(root_1, stream_i.nextNode());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "collapse_clause"


	public static class schedule_kind_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "schedule_kind"
	// OmpParser.g:201:1: schedule_kind : ( STATIC -> ^( STATIC ) | DYNAMIC -> ^( DYNAMIC ) | GUIDED -> ^( GUIDED ) | RUNTIME -> ^( RUNTIME ) );
	public final OmpParser.schedule_kind_return schedule_kind() throws RecognitionException {
		OmpParser.schedule_kind_return retval = new OmpParser.schedule_kind_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token STATIC62=null;
		Token DYNAMIC63=null;
		Token GUIDED64=null;
		Token RUNTIME65=null;

		Object STATIC62_tree=null;
		Object DYNAMIC63_tree=null;
		Object GUIDED64_tree=null;
		Object RUNTIME65_tree=null;
		RewriteRuleTokenStream stream_STATIC=new RewriteRuleTokenStream(adaptor,"token STATIC");
		RewriteRuleTokenStream stream_GUIDED=new RewriteRuleTokenStream(adaptor,"token GUIDED");
		RewriteRuleTokenStream stream_DYNAMIC=new RewriteRuleTokenStream(adaptor,"token DYNAMIC");
		RewriteRuleTokenStream stream_RUNTIME=new RewriteRuleTokenStream(adaptor,"token RUNTIME");

		try {
			// OmpParser.g:202:3: ( STATIC -> ^( STATIC ) | DYNAMIC -> ^( DYNAMIC ) | GUIDED -> ^( GUIDED ) | RUNTIME -> ^( RUNTIME ) )
			int alt20=4;
			switch ( input.LA(1) ) {
			case STATIC:
				{
				alt20=1;
				}
				break;
			case DYNAMIC:
				{
				alt20=2;
				}
				break;
			case GUIDED:
				{
				alt20=3;
				}
				break;
			case RUNTIME:
				{
				alt20=4;
				}
				break;
			default:
				NoViableAltException nvae =
					new NoViableAltException("", 20, 0, input);
				throw nvae;
			}
			switch (alt20) {
				case 1 :
					// OmpParser.g:202:5: STATIC
					{
					STATIC62=(Token)match(input,STATIC,FOLLOW_STATIC_in_schedule_kind1053);  
					stream_STATIC.add(STATIC62);

					// AST REWRITE
					// elements: STATIC
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 202:12: -> ^( STATIC )
					{
						// OmpParser.g:202:15: ^( STATIC )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_STATIC.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 2 :
					// OmpParser.g:203:5: DYNAMIC
					{
					DYNAMIC63=(Token)match(input,DYNAMIC,FOLLOW_DYNAMIC_in_schedule_kind1065);  
					stream_DYNAMIC.add(DYNAMIC63);

					// AST REWRITE
					// elements: DYNAMIC
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 203:13: -> ^( DYNAMIC )
					{
						// OmpParser.g:203:16: ^( DYNAMIC )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_DYNAMIC.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 3 :
					// OmpParser.g:204:5: GUIDED
					{
					GUIDED64=(Token)match(input,GUIDED,FOLLOW_GUIDED_in_schedule_kind1077);  
					stream_GUIDED.add(GUIDED64);

					// AST REWRITE
					// elements: GUIDED
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 204:12: -> ^( GUIDED )
					{
						// OmpParser.g:204:15: ^( GUIDED )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_GUIDED.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 4 :
					// OmpParser.g:205:5: RUNTIME
					{
					RUNTIME65=(Token)match(input,RUNTIME,FOLLOW_RUNTIME_in_schedule_kind1089);  
					stream_RUNTIME.add(RUNTIME65);

					// AST REWRITE
					// elements: RUNTIME
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 205:13: -> ^( RUNTIME )
					{
						// OmpParser.g:205:16: ^( RUNTIME )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_RUNTIME.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "schedule_kind"


	public static class unique_parallel_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "unique_parallel_clause"
	// OmpParser.g:208:1: unique_parallel_clause : (i= if_clause -> ^( UNIQUE_PARALLEL $i) |n= num_threads_clause -> ^( UNIQUE_PARALLEL $n) );
	public final OmpParser.unique_parallel_clause_return unique_parallel_clause() throws RecognitionException {
		OmpParser.unique_parallel_clause_return retval = new OmpParser.unique_parallel_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope i =null;
		ParserRuleReturnScope n =null;

		RewriteRuleSubtreeStream stream_if_clause=new RewriteRuleSubtreeStream(adaptor,"rule if_clause");
		RewriteRuleSubtreeStream stream_num_threads_clause=new RewriteRuleSubtreeStream(adaptor,"rule num_threads_clause");

		try {
			// OmpParser.g:209:3: (i= if_clause -> ^( UNIQUE_PARALLEL $i) |n= num_threads_clause -> ^( UNIQUE_PARALLEL $n) )
			int alt21=2;
			int LA21_0 = input.LA(1);
			if ( (LA21_0==IF) ) {
				alt21=1;
			}
			else if ( (LA21_0==NUM_THREADS) ) {
				alt21=2;
			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 21, 0, input);
				throw nvae;
			}

			switch (alt21) {
				case 1 :
					// OmpParser.g:209:5: i= if_clause
					{
					pushFollow(FOLLOW_if_clause_in_unique_parallel_clause1110);
					i=if_clause();
					state._fsp--;

					stream_if_clause.add(i.getTree());
					// AST REWRITE
					// elements: i
					// token labels: 
					// rule labels: retval, i
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_i=new RewriteRuleSubtreeStream(adaptor,"rule i",i!=null?i.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 210:5: -> ^( UNIQUE_PARALLEL $i)
					{
						// OmpParser.g:210:8: ^( UNIQUE_PARALLEL $i)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(UNIQUE_PARALLEL, "UNIQUE_PARALLEL"), root_1);
						adaptor.addChild(root_1, stream_i.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 2 :
					// OmpParser.g:211:5: n= num_threads_clause
					{
					pushFollow(FOLLOW_num_threads_clause_in_unique_parallel_clause1132);
					n=num_threads_clause();
					state._fsp--;

					stream_num_threads_clause.add(n.getTree());
					// AST REWRITE
					// elements: n
					// token labels: 
					// rule labels: retval, n
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_n=new RewriteRuleSubtreeStream(adaptor,"rule n",n!=null?n.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 212:5: -> ^( UNIQUE_PARALLEL $n)
					{
						// OmpParser.g:212:8: ^( UNIQUE_PARALLEL $n)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(UNIQUE_PARALLEL, "UNIQUE_PARALLEL"), root_1);
						adaptor.addChild(root_1, stream_n.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "unique_parallel_clause"


	public static class if_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "if_clause"
	// OmpParser.g:215:1: if_clause : IF LPAREN e1= expression RPAREN -> ^( IF $e1) ;
	public final OmpParser.if_clause_return if_clause() throws RecognitionException {
		OmpParser.if_clause_return retval = new OmpParser.if_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token IF66=null;
		Token LPAREN67=null;
		Token RPAREN68=null;
		ParserRuleReturnScope e1 =null;

		Object IF66_tree=null;
		Object LPAREN67_tree=null;
		Object RPAREN68_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleTokenStream stream_IF=new RewriteRuleTokenStream(adaptor,"token IF");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");

		try {
			// OmpParser.g:216:3: ( IF LPAREN e1= expression RPAREN -> ^( IF $e1) )
			// OmpParser.g:216:5: IF LPAREN e1= expression RPAREN
			{
			IF66=(Token)match(input,IF,FOLLOW_IF_in_if_clause1161);  
			stream_IF.add(IF66);

			LPAREN67=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_if_clause1164);  
			stream_LPAREN.add(LPAREN67);

			pushFollow(FOLLOW_expression_in_if_clause1169);
			e1=expression();
			state._fsp--;

			stream_expression.add(e1.getTree());
			RPAREN68=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_if_clause1172);  
			stream_RPAREN.add(RPAREN68);

			// AST REWRITE
			// elements: e1, IF
			// token labels: 
			// rule labels: retval, e1
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_e1=new RewriteRuleSubtreeStream(adaptor,"rule e1",e1!=null?e1.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 217:5: -> ^( IF $e1)
			{
				// OmpParser.g:217:8: ^( IF $e1)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_IF.nextNode(), root_1);
				adaptor.addChild(root_1, stream_e1.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "if_clause"


	public static class num_threads_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "num_threads_clause"
	// OmpParser.g:220:1: num_threads_clause : NUM_THREADS LPAREN e2= expression RPAREN -> ^( NUM_THREADS $e2) ;
	public final OmpParser.num_threads_clause_return num_threads_clause() throws RecognitionException {
		OmpParser.num_threads_clause_return retval = new OmpParser.num_threads_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token NUM_THREADS69=null;
		Token LPAREN70=null;
		Token RPAREN71=null;
		ParserRuleReturnScope e2 =null;

		Object NUM_THREADS69_tree=null;
		Object LPAREN70_tree=null;
		Object RPAREN71_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_NUM_THREADS=new RewriteRuleTokenStream(adaptor,"token NUM_THREADS");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");

		try {
			// OmpParser.g:221:3: ( NUM_THREADS LPAREN e2= expression RPAREN -> ^( NUM_THREADS $e2) )
			// OmpParser.g:221:5: NUM_THREADS LPAREN e2= expression RPAREN
			{
			NUM_THREADS69=(Token)match(input,NUM_THREADS,FOLLOW_NUM_THREADS_in_num_threads_clause1200);  
			stream_NUM_THREADS.add(NUM_THREADS69);

			LPAREN70=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_num_threads_clause1203);  
			stream_LPAREN.add(LPAREN70);

			pushFollow(FOLLOW_expression_in_num_threads_clause1208);
			e2=expression();
			state._fsp--;

			stream_expression.add(e2.getTree());
			RPAREN71=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_num_threads_clause1211);  
			stream_RPAREN.add(RPAREN71);

			// AST REWRITE
			// elements: NUM_THREADS, e2
			// token labels: 
			// rule labels: retval, e2
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_e2=new RewriteRuleSubtreeStream(adaptor,"rule e2",e2!=null?e2.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 222:5: -> ^( NUM_THREADS $e2)
			{
				// OmpParser.g:222:8: ^( NUM_THREADS $e2)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_NUM_THREADS.nextNode(), root_1);
				adaptor.addChild(root_1, stream_e2.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "num_threads_clause"


	public static class data_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "data_clause"
	// OmpParser.g:225:1: data_clause : (d1= private_clause -> ^( DATA_CLAUSE $d1) |d2= firstprivate_clause -> ^( DATA_CLAUSE $d2) |d3= lastprivate_clause -> ^( DATA_CLAUSE $d3) |d4= shared_clause -> ^( DATA_CLAUSE $d4) |d5= default_clause -> ^( DATA_CLAUSE $d5) |d6= reduction_clause -> ^( DATA_CLAUSE $d6) |d7= copyin_clause -> ^( DATA_CLAUSE $d7) |d8= copyprivate_clause -> ^( DATA_CLAUSE $d8) );
	public final OmpParser.data_clause_return data_clause() throws RecognitionException {
		OmpParser.data_clause_return retval = new OmpParser.data_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope d1 =null;
		ParserRuleReturnScope d2 =null;
		ParserRuleReturnScope d3 =null;
		ParserRuleReturnScope d4 =null;
		ParserRuleReturnScope d5 =null;
		ParserRuleReturnScope d6 =null;
		ParserRuleReturnScope d7 =null;
		ParserRuleReturnScope d8 =null;

		RewriteRuleSubtreeStream stream_copyin_clause=new RewriteRuleSubtreeStream(adaptor,"rule copyin_clause");
		RewriteRuleSubtreeStream stream_firstprivate_clause=new RewriteRuleSubtreeStream(adaptor,"rule firstprivate_clause");
		RewriteRuleSubtreeStream stream_lastprivate_clause=new RewriteRuleSubtreeStream(adaptor,"rule lastprivate_clause");
		RewriteRuleSubtreeStream stream_default_clause=new RewriteRuleSubtreeStream(adaptor,"rule default_clause");
		RewriteRuleSubtreeStream stream_shared_clause=new RewriteRuleSubtreeStream(adaptor,"rule shared_clause");
		RewriteRuleSubtreeStream stream_copyprivate_clause=new RewriteRuleSubtreeStream(adaptor,"rule copyprivate_clause");
		RewriteRuleSubtreeStream stream_private_clause=new RewriteRuleSubtreeStream(adaptor,"rule private_clause");
		RewriteRuleSubtreeStream stream_reduction_clause=new RewriteRuleSubtreeStream(adaptor,"rule reduction_clause");

		try {
			// OmpParser.g:226:3: (d1= private_clause -> ^( DATA_CLAUSE $d1) |d2= firstprivate_clause -> ^( DATA_CLAUSE $d2) |d3= lastprivate_clause -> ^( DATA_CLAUSE $d3) |d4= shared_clause -> ^( DATA_CLAUSE $d4) |d5= default_clause -> ^( DATA_CLAUSE $d5) |d6= reduction_clause -> ^( DATA_CLAUSE $d6) |d7= copyin_clause -> ^( DATA_CLAUSE $d7) |d8= copyprivate_clause -> ^( DATA_CLAUSE $d8) )
			int alt22=8;
			switch ( input.LA(1) ) {
			case PRIVATE:
				{
				alt22=1;
				}
				break;
			case FST_PRIVATE:
				{
				alt22=2;
				}
				break;
			case LST_PRIVATE:
				{
				alt22=3;
				}
				break;
			case SHARED:
				{
				alt22=4;
				}
				break;
			case DEFAULT:
				{
				alt22=5;
				}
				break;
			case REDUCTION:
				{
				alt22=6;
				}
				break;
			case COPYIN:
				{
				alt22=7;
				}
				break;
			case COPYPRIVATE:
				{
				alt22=8;
				}
				break;
			default:
				NoViableAltException nvae =
					new NoViableAltException("", 22, 0, input);
				throw nvae;
			}
			switch (alt22) {
				case 1 :
					// OmpParser.g:226:5: d1= private_clause
					{
					pushFollow(FOLLOW_private_clause_in_data_clause1239);
					d1=private_clause();
					state._fsp--;

					stream_private_clause.add(d1.getTree());
					// AST REWRITE
					// elements: d1
					// token labels: 
					// rule labels: d1, retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_d1=new RewriteRuleSubtreeStream(adaptor,"rule d1",d1!=null?d1.getTree():null);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 227:5: -> ^( DATA_CLAUSE $d1)
					{
						// OmpParser.g:227:8: ^( DATA_CLAUSE $d1)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DATA_CLAUSE, "DATA_CLAUSE"), root_1);
						adaptor.addChild(root_1, stream_d1.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 2 :
					// OmpParser.g:228:5: d2= firstprivate_clause
					{
					pushFollow(FOLLOW_firstprivate_clause_in_data_clause1260);
					d2=firstprivate_clause();
					state._fsp--;

					stream_firstprivate_clause.add(d2.getTree());
					// AST REWRITE
					// elements: d2
					// token labels: 
					// rule labels: retval, d2
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_d2=new RewriteRuleSubtreeStream(adaptor,"rule d2",d2!=null?d2.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 229:5: -> ^( DATA_CLAUSE $d2)
					{
						// OmpParser.g:229:8: ^( DATA_CLAUSE $d2)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DATA_CLAUSE, "DATA_CLAUSE"), root_1);
						adaptor.addChild(root_1, stream_d2.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 3 :
					// OmpParser.g:230:5: d3= lastprivate_clause
					{
					pushFollow(FOLLOW_lastprivate_clause_in_data_clause1281);
					d3=lastprivate_clause();
					state._fsp--;

					stream_lastprivate_clause.add(d3.getTree());
					// AST REWRITE
					// elements: d3
					// token labels: 
					// rule labels: retval, d3
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_d3=new RewriteRuleSubtreeStream(adaptor,"rule d3",d3!=null?d3.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 231:5: -> ^( DATA_CLAUSE $d3)
					{
						// OmpParser.g:231:8: ^( DATA_CLAUSE $d3)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DATA_CLAUSE, "DATA_CLAUSE"), root_1);
						adaptor.addChild(root_1, stream_d3.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 4 :
					// OmpParser.g:232:5: d4= shared_clause
					{
					pushFollow(FOLLOW_shared_clause_in_data_clause1302);
					d4=shared_clause();
					state._fsp--;

					stream_shared_clause.add(d4.getTree());
					// AST REWRITE
					// elements: d4
					// token labels: 
					// rule labels: retval, d4
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_d4=new RewriteRuleSubtreeStream(adaptor,"rule d4",d4!=null?d4.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 233:5: -> ^( DATA_CLAUSE $d4)
					{
						// OmpParser.g:233:8: ^( DATA_CLAUSE $d4)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DATA_CLAUSE, "DATA_CLAUSE"), root_1);
						adaptor.addChild(root_1, stream_d4.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 5 :
					// OmpParser.g:234:5: d5= default_clause
					{
					pushFollow(FOLLOW_default_clause_in_data_clause1323);
					d5=default_clause();
					state._fsp--;

					stream_default_clause.add(d5.getTree());
					// AST REWRITE
					// elements: d5
					// token labels: 
					// rule labels: retval, d5
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_d5=new RewriteRuleSubtreeStream(adaptor,"rule d5",d5!=null?d5.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 235:5: -> ^( DATA_CLAUSE $d5)
					{
						// OmpParser.g:235:8: ^( DATA_CLAUSE $d5)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DATA_CLAUSE, "DATA_CLAUSE"), root_1);
						adaptor.addChild(root_1, stream_d5.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 6 :
					// OmpParser.g:236:5: d6= reduction_clause
					{
					pushFollow(FOLLOW_reduction_clause_in_data_clause1344);
					d6=reduction_clause();
					state._fsp--;

					stream_reduction_clause.add(d6.getTree());
					// AST REWRITE
					// elements: d6
					// token labels: 
					// rule labels: retval, d6
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_d6=new RewriteRuleSubtreeStream(adaptor,"rule d6",d6!=null?d6.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 237:5: -> ^( DATA_CLAUSE $d6)
					{
						// OmpParser.g:237:8: ^( DATA_CLAUSE $d6)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DATA_CLAUSE, "DATA_CLAUSE"), root_1);
						adaptor.addChild(root_1, stream_d6.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 7 :
					// OmpParser.g:238:5: d7= copyin_clause
					{
					pushFollow(FOLLOW_copyin_clause_in_data_clause1365);
					d7=copyin_clause();
					state._fsp--;

					stream_copyin_clause.add(d7.getTree());
					// AST REWRITE
					// elements: d7
					// token labels: 
					// rule labels: retval, d7
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_d7=new RewriteRuleSubtreeStream(adaptor,"rule d7",d7!=null?d7.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 239:5: -> ^( DATA_CLAUSE $d7)
					{
						// OmpParser.g:239:8: ^( DATA_CLAUSE $d7)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DATA_CLAUSE, "DATA_CLAUSE"), root_1);
						adaptor.addChild(root_1, stream_d7.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 8 :
					// OmpParser.g:240:5: d8= copyprivate_clause
					{
					pushFollow(FOLLOW_copyprivate_clause_in_data_clause1386);
					d8=copyprivate_clause();
					state._fsp--;

					stream_copyprivate_clause.add(d8.getTree());
					// AST REWRITE
					// elements: d8
					// token labels: 
					// rule labels: retval, d8
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_d8=new RewriteRuleSubtreeStream(adaptor,"rule d8",d8!=null?d8.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 241:5: -> ^( DATA_CLAUSE $d8)
					{
						// OmpParser.g:241:8: ^( DATA_CLAUSE $d8)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DATA_CLAUSE, "DATA_CLAUSE"), root_1);
						adaptor.addChild(root_1, stream_d8.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "data_clause"


	public static class private_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "private_clause"
	// OmpParser.g:244:1: private_clause : PRIVATE LPAREN i1= identifier_list RPAREN -> ^( PRIVATE $i1) ;
	public final OmpParser.private_clause_return private_clause() throws RecognitionException {
		OmpParser.private_clause_return retval = new OmpParser.private_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PRIVATE72=null;
		Token LPAREN73=null;
		Token RPAREN74=null;
		ParserRuleReturnScope i1 =null;

		Object PRIVATE72_tree=null;
		Object LPAREN73_tree=null;
		Object RPAREN74_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_PRIVATE=new RewriteRuleTokenStream(adaptor,"token PRIVATE");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_identifier_list=new RewriteRuleSubtreeStream(adaptor,"rule identifier_list");

		try {
			// OmpParser.g:245:3: ( PRIVATE LPAREN i1= identifier_list RPAREN -> ^( PRIVATE $i1) )
			// OmpParser.g:245:5: PRIVATE LPAREN i1= identifier_list RPAREN
			{
			PRIVATE72=(Token)match(input,PRIVATE,FOLLOW_PRIVATE_in_private_clause1414);  
			stream_PRIVATE.add(PRIVATE72);

			LPAREN73=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_private_clause1417);  
			stream_LPAREN.add(LPAREN73);

			pushFollow(FOLLOW_identifier_list_in_private_clause1422);
			i1=identifier_list();
			state._fsp--;

			stream_identifier_list.add(i1.getTree());
			RPAREN74=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_private_clause1425);  
			stream_RPAREN.add(RPAREN74);

			// AST REWRITE
			// elements: i1, PRIVATE
			// token labels: 
			// rule labels: retval, i1
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_i1=new RewriteRuleSubtreeStream(adaptor,"rule i1",i1!=null?i1.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 246:5: -> ^( PRIVATE $i1)
			{
				// OmpParser.g:246:8: ^( PRIVATE $i1)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_PRIVATE.nextNode(), root_1);
				adaptor.addChild(root_1, stream_i1.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "private_clause"


	public static class firstprivate_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "firstprivate_clause"
	// OmpParser.g:249:1: firstprivate_clause : FST_PRIVATE LPAREN i2= identifier_list RPAREN -> ^( FST_PRIVATE $i2) ;
	public final OmpParser.firstprivate_clause_return firstprivate_clause() throws RecognitionException {
		OmpParser.firstprivate_clause_return retval = new OmpParser.firstprivate_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token FST_PRIVATE75=null;
		Token LPAREN76=null;
		Token RPAREN77=null;
		ParserRuleReturnScope i2 =null;

		Object FST_PRIVATE75_tree=null;
		Object LPAREN76_tree=null;
		Object RPAREN77_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleTokenStream stream_FST_PRIVATE=new RewriteRuleTokenStream(adaptor,"token FST_PRIVATE");
		RewriteRuleSubtreeStream stream_identifier_list=new RewriteRuleSubtreeStream(adaptor,"rule identifier_list");

		try {
			// OmpParser.g:250:3: ( FST_PRIVATE LPAREN i2= identifier_list RPAREN -> ^( FST_PRIVATE $i2) )
			// OmpParser.g:250:5: FST_PRIVATE LPAREN i2= identifier_list RPAREN
			{
			FST_PRIVATE75=(Token)match(input,FST_PRIVATE,FOLLOW_FST_PRIVATE_in_firstprivate_clause1454);  
			stream_FST_PRIVATE.add(FST_PRIVATE75);

			LPAREN76=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_firstprivate_clause1457);  
			stream_LPAREN.add(LPAREN76);

			pushFollow(FOLLOW_identifier_list_in_firstprivate_clause1462);
			i2=identifier_list();
			state._fsp--;

			stream_identifier_list.add(i2.getTree());
			RPAREN77=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_firstprivate_clause1465);  
			stream_RPAREN.add(RPAREN77);

			// AST REWRITE
			// elements: FST_PRIVATE, i2
			// token labels: 
			// rule labels: retval, i2
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_i2=new RewriteRuleSubtreeStream(adaptor,"rule i2",i2!=null?i2.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 251:5: -> ^( FST_PRIVATE $i2)
			{
				// OmpParser.g:251:8: ^( FST_PRIVATE $i2)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_FST_PRIVATE.nextNode(), root_1);
				adaptor.addChild(root_1, stream_i2.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "firstprivate_clause"


	public static class lastprivate_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "lastprivate_clause"
	// OmpParser.g:254:1: lastprivate_clause : LST_PRIVATE LPAREN i3= identifier_list RPAREN -> ^( LST_PRIVATE $i3) ;
	public final OmpParser.lastprivate_clause_return lastprivate_clause() throws RecognitionException {
		OmpParser.lastprivate_clause_return retval = new OmpParser.lastprivate_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LST_PRIVATE78=null;
		Token LPAREN79=null;
		Token RPAREN80=null;
		ParserRuleReturnScope i3 =null;

		Object LST_PRIVATE78_tree=null;
		Object LPAREN79_tree=null;
		Object RPAREN80_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_LST_PRIVATE=new RewriteRuleTokenStream(adaptor,"token LST_PRIVATE");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_identifier_list=new RewriteRuleSubtreeStream(adaptor,"rule identifier_list");

		try {
			// OmpParser.g:255:3: ( LST_PRIVATE LPAREN i3= identifier_list RPAREN -> ^( LST_PRIVATE $i3) )
			// OmpParser.g:255:5: LST_PRIVATE LPAREN i3= identifier_list RPAREN
			{
			LST_PRIVATE78=(Token)match(input,LST_PRIVATE,FOLLOW_LST_PRIVATE_in_lastprivate_clause1493);  
			stream_LST_PRIVATE.add(LST_PRIVATE78);

			LPAREN79=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_lastprivate_clause1496);  
			stream_LPAREN.add(LPAREN79);

			pushFollow(FOLLOW_identifier_list_in_lastprivate_clause1501);
			i3=identifier_list();
			state._fsp--;

			stream_identifier_list.add(i3.getTree());
			RPAREN80=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_lastprivate_clause1504);  
			stream_RPAREN.add(RPAREN80);

			// AST REWRITE
			// elements: i3, LST_PRIVATE
			// token labels: 
			// rule labels: retval, i3
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_i3=new RewriteRuleSubtreeStream(adaptor,"rule i3",i3!=null?i3.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 256:5: -> ^( LST_PRIVATE $i3)
			{
				// OmpParser.g:256:8: ^( LST_PRIVATE $i3)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_LST_PRIVATE.nextNode(), root_1);
				adaptor.addChild(root_1, stream_i3.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "lastprivate_clause"


	public static class shared_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "shared_clause"
	// OmpParser.g:259:1: shared_clause : SHARED LPAREN i4= identifier_list RPAREN -> ^( SHARED $i4) ;
	public final OmpParser.shared_clause_return shared_clause() throws RecognitionException {
		OmpParser.shared_clause_return retval = new OmpParser.shared_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SHARED81=null;
		Token LPAREN82=null;
		Token RPAREN83=null;
		ParserRuleReturnScope i4 =null;

		Object SHARED81_tree=null;
		Object LPAREN82_tree=null;
		Object RPAREN83_tree=null;
		RewriteRuleTokenStream stream_SHARED=new RewriteRuleTokenStream(adaptor,"token SHARED");
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_identifier_list=new RewriteRuleSubtreeStream(adaptor,"rule identifier_list");

		try {
			// OmpParser.g:260:3: ( SHARED LPAREN i4= identifier_list RPAREN -> ^( SHARED $i4) )
			// OmpParser.g:260:5: SHARED LPAREN i4= identifier_list RPAREN
			{
			SHARED81=(Token)match(input,SHARED,FOLLOW_SHARED_in_shared_clause1532);  
			stream_SHARED.add(SHARED81);

			LPAREN82=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_shared_clause1535);  
			stream_LPAREN.add(LPAREN82);

			pushFollow(FOLLOW_identifier_list_in_shared_clause1540);
			i4=identifier_list();
			state._fsp--;

			stream_identifier_list.add(i4.getTree());
			RPAREN83=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_shared_clause1543);  
			stream_RPAREN.add(RPAREN83);

			// AST REWRITE
			// elements: i4, SHARED
			// token labels: 
			// rule labels: retval, i4
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_i4=new RewriteRuleSubtreeStream(adaptor,"rule i4",i4!=null?i4.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 261:5: -> ^( SHARED $i4)
			{
				// OmpParser.g:261:8: ^( SHARED $i4)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_SHARED.nextNode(), root_1);
				adaptor.addChild(root_1, stream_i4.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "shared_clause"


	public static class default_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "default_clause"
	// OmpParser.g:264:1: default_clause : ( DEFAULT LPAREN SHARED RPAREN -> ^( DEFAULT SHARED ) | DEFAULT LPAREN NONE RPAREN -> ^( DEFAULT NONE ) );
	public final OmpParser.default_clause_return default_clause() throws RecognitionException {
		OmpParser.default_clause_return retval = new OmpParser.default_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token DEFAULT84=null;
		Token LPAREN85=null;
		Token SHARED86=null;
		Token RPAREN87=null;
		Token DEFAULT88=null;
		Token LPAREN89=null;
		Token NONE90=null;
		Token RPAREN91=null;

		Object DEFAULT84_tree=null;
		Object LPAREN85_tree=null;
		Object SHARED86_tree=null;
		Object RPAREN87_tree=null;
		Object DEFAULT88_tree=null;
		Object LPAREN89_tree=null;
		Object NONE90_tree=null;
		Object RPAREN91_tree=null;
		RewriteRuleTokenStream stream_SHARED=new RewriteRuleTokenStream(adaptor,"token SHARED");
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_NONE=new RewriteRuleTokenStream(adaptor,"token NONE");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleTokenStream stream_DEFAULT=new RewriteRuleTokenStream(adaptor,"token DEFAULT");

		try {
			// OmpParser.g:265:3: ( DEFAULT LPAREN SHARED RPAREN -> ^( DEFAULT SHARED ) | DEFAULT LPAREN NONE RPAREN -> ^( DEFAULT NONE ) )
			int alt23=2;
			int LA23_0 = input.LA(1);
			if ( (LA23_0==DEFAULT) ) {
				int LA23_1 = input.LA(2);
				if ( (LA23_1==LPAREN) ) {
					int LA23_2 = input.LA(3);
					if ( (LA23_2==SHARED) ) {
						alt23=1;
					}
					else if ( (LA23_2==NONE) ) {
						alt23=2;
					}

					else {
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 23, 2, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

				}

				else {
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 23, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 23, 0, input);
				throw nvae;
			}

			switch (alt23) {
				case 1 :
					// OmpParser.g:265:5: DEFAULT LPAREN SHARED RPAREN
					{
					DEFAULT84=(Token)match(input,DEFAULT,FOLLOW_DEFAULT_in_default_clause1571);  
					stream_DEFAULT.add(DEFAULT84);

					LPAREN85=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_default_clause1574);  
					stream_LPAREN.add(LPAREN85);

					SHARED86=(Token)match(input,SHARED,FOLLOW_SHARED_in_default_clause1577);  
					stream_SHARED.add(SHARED86);

					RPAREN87=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_default_clause1580);  
					stream_RPAREN.add(RPAREN87);

					// AST REWRITE
					// elements: SHARED, DEFAULT
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 266:5: -> ^( DEFAULT SHARED )
					{
						// OmpParser.g:266:8: ^( DEFAULT SHARED )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_DEFAULT.nextNode(), root_1);
						adaptor.addChild(root_1, stream_SHARED.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 2 :
					// OmpParser.g:267:5: DEFAULT LPAREN NONE RPAREN
					{
					DEFAULT88=(Token)match(input,DEFAULT,FOLLOW_DEFAULT_in_default_clause1598);  
					stream_DEFAULT.add(DEFAULT88);

					LPAREN89=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_default_clause1601);  
					stream_LPAREN.add(LPAREN89);

					NONE90=(Token)match(input,NONE,FOLLOW_NONE_in_default_clause1604);  
					stream_NONE.add(NONE90);

					RPAREN91=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_default_clause1607);  
					stream_RPAREN.add(RPAREN91);

					// AST REWRITE
					// elements: NONE, DEFAULT
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 268:5: -> ^( DEFAULT NONE )
					{
						// OmpParser.g:268:8: ^( DEFAULT NONE )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_DEFAULT.nextNode(), root_1);
						adaptor.addChild(root_1, stream_NONE.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "default_clause"


	public static class reduction_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "reduction_clause"
	// OmpParser.g:271:1: reduction_clause : REDUCTION LPAREN r= reduction_operator COLON i5= identifier_list RPAREN -> ^( REDUCTION $r $i5) ;
	public final OmpParser.reduction_clause_return reduction_clause() throws RecognitionException {
		OmpParser.reduction_clause_return retval = new OmpParser.reduction_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token REDUCTION92=null;
		Token LPAREN93=null;
		Token COLON94=null;
		Token RPAREN95=null;
		ParserRuleReturnScope r =null;
		ParserRuleReturnScope i5 =null;

		Object REDUCTION92_tree=null;
		Object LPAREN93_tree=null;
		Object COLON94_tree=null;
		Object RPAREN95_tree=null;
		RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_REDUCTION=new RewriteRuleTokenStream(adaptor,"token REDUCTION");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_reduction_operator=new RewriteRuleSubtreeStream(adaptor,"rule reduction_operator");
		RewriteRuleSubtreeStream stream_identifier_list=new RewriteRuleSubtreeStream(adaptor,"rule identifier_list");

		try {
			// OmpParser.g:272:3: ( REDUCTION LPAREN r= reduction_operator COLON i5= identifier_list RPAREN -> ^( REDUCTION $r $i5) )
			// OmpParser.g:272:5: REDUCTION LPAREN r= reduction_operator COLON i5= identifier_list RPAREN
			{
			REDUCTION92=(Token)match(input,REDUCTION,FOLLOW_REDUCTION_in_reduction_clause1634);  
			stream_REDUCTION.add(REDUCTION92);

			LPAREN93=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_reduction_clause1636);  
			stream_LPAREN.add(LPAREN93);

			pushFollow(FOLLOW_reduction_operator_in_reduction_clause1640);
			r=reduction_operator();
			state._fsp--;

			stream_reduction_operator.add(r.getTree());
			COLON94=(Token)match(input,COLON,FOLLOW_COLON_in_reduction_clause1642);  
			stream_COLON.add(COLON94);

			pushFollow(FOLLOW_identifier_list_in_reduction_clause1646);
			i5=identifier_list();
			state._fsp--;

			stream_identifier_list.add(i5.getTree());
			RPAREN95=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_reduction_clause1648);  
			stream_RPAREN.add(RPAREN95);

			// AST REWRITE
			// elements: i5, r, REDUCTION
			// token labels: 
			// rule labels: retval, r, i5
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_r=new RewriteRuleSubtreeStream(adaptor,"rule r",r!=null?r.getTree():null);
			RewriteRuleSubtreeStream stream_i5=new RewriteRuleSubtreeStream(adaptor,"rule i5",i5!=null?i5.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 273:5: -> ^( REDUCTION $r $i5)
			{
				// OmpParser.g:273:8: ^( REDUCTION $r $i5)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_REDUCTION.nextNode(), root_1);
				adaptor.addChild(root_1, stream_r.nextTree());
				adaptor.addChild(root_1, stream_i5.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "reduction_clause"


	public static class copyin_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "copyin_clause"
	// OmpParser.g:276:1: copyin_clause : COPYIN LPAREN i6= identifier_list RPAREN -> ^( COPYIN $i6) ;
	public final OmpParser.copyin_clause_return copyin_clause() throws RecognitionException {
		OmpParser.copyin_clause_return retval = new OmpParser.copyin_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COPYIN96=null;
		Token LPAREN97=null;
		Token RPAREN98=null;
		ParserRuleReturnScope i6 =null;

		Object COPYIN96_tree=null;
		Object LPAREN97_tree=null;
		Object RPAREN98_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_COPYIN=new RewriteRuleTokenStream(adaptor,"token COPYIN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_identifier_list=new RewriteRuleSubtreeStream(adaptor,"rule identifier_list");

		try {
			// OmpParser.g:277:3: ( COPYIN LPAREN i6= identifier_list RPAREN -> ^( COPYIN $i6) )
			// OmpParser.g:277:5: COPYIN LPAREN i6= identifier_list RPAREN
			{
			COPYIN96=(Token)match(input,COPYIN,FOLLOW_COPYIN_in_copyin_clause1679);  
			stream_COPYIN.add(COPYIN96);

			LPAREN97=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_copyin_clause1682);  
			stream_LPAREN.add(LPAREN97);

			pushFollow(FOLLOW_identifier_list_in_copyin_clause1687);
			i6=identifier_list();
			state._fsp--;

			stream_identifier_list.add(i6.getTree());
			RPAREN98=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_copyin_clause1690);  
			stream_RPAREN.add(RPAREN98);

			// AST REWRITE
			// elements: i6, COPYIN
			// token labels: 
			// rule labels: retval, i6
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_i6=new RewriteRuleSubtreeStream(adaptor,"rule i6",i6!=null?i6.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 278:5: -> ^( COPYIN $i6)
			{
				// OmpParser.g:278:8: ^( COPYIN $i6)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_COPYIN.nextNode(), root_1);
				adaptor.addChild(root_1, stream_i6.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "copyin_clause"


	public static class copyprivate_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "copyprivate_clause"
	// OmpParser.g:281:1: copyprivate_clause : COPYPRIVATE LPAREN i7= identifier_list RPAREN -> ^( COPYPRIVATE $i7) ;
	public final OmpParser.copyprivate_clause_return copyprivate_clause() throws RecognitionException {
		OmpParser.copyprivate_clause_return retval = new OmpParser.copyprivate_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COPYPRIVATE99=null;
		Token LPAREN100=null;
		Token RPAREN101=null;
		ParserRuleReturnScope i7 =null;

		Object COPYPRIVATE99_tree=null;
		Object LPAREN100_tree=null;
		Object RPAREN101_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_COPYPRIVATE=new RewriteRuleTokenStream(adaptor,"token COPYPRIVATE");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_identifier_list=new RewriteRuleSubtreeStream(adaptor,"rule identifier_list");

		try {
			// OmpParser.g:282:3: ( COPYPRIVATE LPAREN i7= identifier_list RPAREN -> ^( COPYPRIVATE $i7) )
			// OmpParser.g:282:5: COPYPRIVATE LPAREN i7= identifier_list RPAREN
			{
			COPYPRIVATE99=(Token)match(input,COPYPRIVATE,FOLLOW_COPYPRIVATE_in_copyprivate_clause1718);  
			stream_COPYPRIVATE.add(COPYPRIVATE99);

			LPAREN100=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_copyprivate_clause1721);  
			stream_LPAREN.add(LPAREN100);

			pushFollow(FOLLOW_identifier_list_in_copyprivate_clause1726);
			i7=identifier_list();
			state._fsp--;

			stream_identifier_list.add(i7.getTree());
			RPAREN101=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_copyprivate_clause1729);  
			stream_RPAREN.add(RPAREN101);

			// AST REWRITE
			// elements: i7, COPYPRIVATE
			// token labels: 
			// rule labels: retval, i7
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_i7=new RewriteRuleSubtreeStream(adaptor,"rule i7",i7!=null?i7.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 283:5: -> ^( COPYPRIVATE $i7)
			{
				// OmpParser.g:283:8: ^( COPYPRIVATE $i7)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_COPYPRIVATE.nextNode(), root_1);
				adaptor.addChild(root_1, stream_i7.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "copyprivate_clause"


	public static class reduction_operator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "reduction_operator"
	// OmpParser.g:286:1: reduction_operator : ( PLUS -> ^( PLUS ) | STAR -> ^( STAR ) | SUB -> ^( SUB ) | AMPERSAND -> ^( AMPERSAND ) | BITXOR -> ^( BITXOR ) | BITOR -> ^( BITOR ) | AND -> ^( AND ) | OR -> ^( OR ) | IDENTIFIER -> ^( IDENTIFIER ) );
	public final OmpParser.reduction_operator_return reduction_operator() throws RecognitionException {
		OmpParser.reduction_operator_return retval = new OmpParser.reduction_operator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PLUS102=null;
		Token STAR103=null;
		Token SUB104=null;
		Token AMPERSAND105=null;
		Token BITXOR106=null;
		Token BITOR107=null;
		Token AND108=null;
		Token OR109=null;
		Token IDENTIFIER110=null;

		Object PLUS102_tree=null;
		Object STAR103_tree=null;
		Object SUB104_tree=null;
		Object AMPERSAND105_tree=null;
		Object BITXOR106_tree=null;
		Object BITOR107_tree=null;
		Object AND108_tree=null;
		Object OR109_tree=null;
		Object IDENTIFIER110_tree=null;
		RewriteRuleTokenStream stream_AMPERSAND=new RewriteRuleTokenStream(adaptor,"token AMPERSAND");
		RewriteRuleTokenStream stream_SUB=new RewriteRuleTokenStream(adaptor,"token SUB");
		RewriteRuleTokenStream stream_PLUS=new RewriteRuleTokenStream(adaptor,"token PLUS");
		RewriteRuleTokenStream stream_STAR=new RewriteRuleTokenStream(adaptor,"token STAR");
		RewriteRuleTokenStream stream_BITOR=new RewriteRuleTokenStream(adaptor,"token BITOR");
		RewriteRuleTokenStream stream_AND=new RewriteRuleTokenStream(adaptor,"token AND");
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
		RewriteRuleTokenStream stream_OR=new RewriteRuleTokenStream(adaptor,"token OR");
		RewriteRuleTokenStream stream_BITXOR=new RewriteRuleTokenStream(adaptor,"token BITXOR");

		try {
			// OmpParser.g:287:3: ( PLUS -> ^( PLUS ) | STAR -> ^( STAR ) | SUB -> ^( SUB ) | AMPERSAND -> ^( AMPERSAND ) | BITXOR -> ^( BITXOR ) | BITOR -> ^( BITOR ) | AND -> ^( AND ) | OR -> ^( OR ) | IDENTIFIER -> ^( IDENTIFIER ) )
			int alt24=9;
			switch ( input.LA(1) ) {
			case PLUS:
				{
				alt24=1;
				}
				break;
			case STAR:
				{
				alt24=2;
				}
				break;
			case SUB:
				{
				alt24=3;
				}
				break;
			case AMPERSAND:
				{
				alt24=4;
				}
				break;
			case BITXOR:
				{
				alt24=5;
				}
				break;
			case BITOR:
				{
				alt24=6;
				}
				break;
			case AND:
				{
				alt24=7;
				}
				break;
			case OR:
				{
				alt24=8;
				}
				break;
			case IDENTIFIER:
				{
				alt24=9;
				}
				break;
			default:
				NoViableAltException nvae =
					new NoViableAltException("", 24, 0, input);
				throw nvae;
			}
			switch (alt24) {
				case 1 :
					// OmpParser.g:287:5: PLUS
					{
					PLUS102=(Token)match(input,PLUS,FOLLOW_PLUS_in_reduction_operator1755);  
					stream_PLUS.add(PLUS102);

					// AST REWRITE
					// elements: PLUS
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 287:10: -> ^( PLUS )
					{
						// OmpParser.g:287:13: ^( PLUS )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_PLUS.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 2 :
					// OmpParser.g:288:5: STAR
					{
					STAR103=(Token)match(input,STAR,FOLLOW_STAR_in_reduction_operator1767);  
					stream_STAR.add(STAR103);

					// AST REWRITE
					// elements: STAR
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 288:10: -> ^( STAR )
					{
						// OmpParser.g:288:13: ^( STAR )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_STAR.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 3 :
					// OmpParser.g:289:5: SUB
					{
					SUB104=(Token)match(input,SUB,FOLLOW_SUB_in_reduction_operator1779);  
					stream_SUB.add(SUB104);

					// AST REWRITE
					// elements: SUB
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 289:9: -> ^( SUB )
					{
						// OmpParser.g:289:12: ^( SUB )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_SUB.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 4 :
					// OmpParser.g:290:5: AMPERSAND
					{
					AMPERSAND105=(Token)match(input,AMPERSAND,FOLLOW_AMPERSAND_in_reduction_operator1791);  
					stream_AMPERSAND.add(AMPERSAND105);

					// AST REWRITE
					// elements: AMPERSAND
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 290:15: -> ^( AMPERSAND )
					{
						// OmpParser.g:290:18: ^( AMPERSAND )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_AMPERSAND.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 5 :
					// OmpParser.g:291:5: BITXOR
					{
					BITXOR106=(Token)match(input,BITXOR,FOLLOW_BITXOR_in_reduction_operator1803);  
					stream_BITXOR.add(BITXOR106);

					// AST REWRITE
					// elements: BITXOR
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 291:12: -> ^( BITXOR )
					{
						// OmpParser.g:291:15: ^( BITXOR )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_BITXOR.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 6 :
					// OmpParser.g:292:5: BITOR
					{
					BITOR107=(Token)match(input,BITOR,FOLLOW_BITOR_in_reduction_operator1815);  
					stream_BITOR.add(BITOR107);

					// AST REWRITE
					// elements: BITOR
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 292:11: -> ^( BITOR )
					{
						// OmpParser.g:292:14: ^( BITOR )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_BITOR.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 7 :
					// OmpParser.g:293:5: AND
					{
					AND108=(Token)match(input,AND,FOLLOW_AND_in_reduction_operator1827);  
					stream_AND.add(AND108);

					// AST REWRITE
					// elements: AND
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 293:9: -> ^( AND )
					{
						// OmpParser.g:293:12: ^( AND )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_AND.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 8 :
					// OmpParser.g:294:5: OR
					{
					OR109=(Token)match(input,OR,FOLLOW_OR_in_reduction_operator1839);  
					stream_OR.add(OR109);

					// AST REWRITE
					// elements: OR
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 294:8: -> ^( OR )
					{
						// OmpParser.g:294:11: ^( OR )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_OR.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 9 :
					// OmpParser.g:295:5: IDENTIFIER
					{
					IDENTIFIER110=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_reduction_operator1851);  
					stream_IDENTIFIER.add(IDENTIFIER110);

					// AST REWRITE
					// elements: IDENTIFIER
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 295:16: -> ^( IDENTIFIER )
					{
						// OmpParser.g:295:19: ^( IDENTIFIER )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_IDENTIFIER.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "reduction_operator"


	public static class identifier_list_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "identifier_list"
	// OmpParser.g:298:1: identifier_list : i1= IDENTIFIER ( COMMA i2+= IDENTIFIER )* -> ^( IDENTIFIER_LIST $i1 ( $i2)* ) ;
	public final OmpParser.identifier_list_return identifier_list() throws RecognitionException {
		OmpParser.identifier_list_return retval = new OmpParser.identifier_list_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token i1=null;
		Token COMMA111=null;
		Token i2=null;
		List<Object> list_i2=null;

		Object i1_tree=null;
		Object COMMA111_tree=null;
		Object i2_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");

		try {
			// OmpParser.g:299:3: (i1= IDENTIFIER ( COMMA i2+= IDENTIFIER )* -> ^( IDENTIFIER_LIST $i1 ( $i2)* ) )
			// OmpParser.g:300:3: i1= IDENTIFIER ( COMMA i2+= IDENTIFIER )*
			{
			i1=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifier_list1874);  
			stream_IDENTIFIER.add(i1);

			// OmpParser.g:300:17: ( COMMA i2+= IDENTIFIER )*
			loop25:
			while (true) {
				int alt25=2;
				int LA25_0 = input.LA(1);
				if ( (LA25_0==COMMA) ) {
					alt25=1;
				}

				switch (alt25) {
				case 1 :
					// OmpParser.g:300:19: COMMA i2+= IDENTIFIER
					{
					COMMA111=(Token)match(input,COMMA,FOLLOW_COMMA_in_identifier_list1878);  
					stream_COMMA.add(COMMA111);

					i2=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifier_list1883);  
					stream_IDENTIFIER.add(i2);

					if (list_i2==null) list_i2=new ArrayList<Object>();
					list_i2.add(i2);
					}
					break;

				default :
					break loop25;
				}
			}

			// AST REWRITE
			// elements: i2, i1
			// token labels: i1
			// rule labels: retval
			// token list labels: i2
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleTokenStream stream_i1=new RewriteRuleTokenStream(adaptor,"token i1",i1);
			RewriteRuleTokenStream stream_i2=new RewriteRuleTokenStream(adaptor,"token i2", list_i2);
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 301:3: -> ^( IDENTIFIER_LIST $i1 ( $i2)* )
			{
				// OmpParser.g:301:6: ^( IDENTIFIER_LIST $i1 ( $i2)* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(IDENTIFIER_LIST, "IDENTIFIER_LIST"), root_1);
				adaptor.addChild(root_1, stream_i1.nextNode());
				// OmpParser.g:301:29: ( $i2)*
				while ( stream_i2.hasNext() ) {
					adaptor.addChild(root_1, stream_i2.nextNode());
				}
				stream_i2.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "identifier_list"

	// Delegated rules
	public OmpParser_CivlCParser.typeSpecifierOrQualifier_return typeSpecifierOrQualifier() throws RecognitionException { return gCivlCParser.typeSpecifierOrQualifier(); }

	public OmpParser_CivlCParser.initializer_return initializer() throws RecognitionException { return gCivlCParser.initializer(); }

	public OmpParser_CivlCParser.postfixExpression_return postfixExpression() throws RecognitionException { return gCivlCParser.postfixExpression(); }

	public OmpParser_CivlCParser.declaratorOrAbstractDeclarator_return declaratorOrAbstractDeclarator() throws RecognitionException { return gCivlCParser.declaratorOrAbstractDeclarator(); }

	public OmpParser_CivlCParser.translationUnit_return translationUnit() throws RecognitionException { return gCivlCParser.translationUnit(); }

	public OmpParser_CivlCParser.castExpression_return castExpression() throws RecognitionException { return gCivlCParser.castExpression(); }

	public OmpParser_CivlCParser.genericAssociation_return genericAssociation() throws RecognitionException { return gCivlCParser.genericAssociation(); }

	public OmpParser_CivlCParser.structDeclarationList_return structDeclarationList() throws RecognitionException { return gCivlCParser.structDeclarationList(); }

	public OmpParser_CivlCParser.conditionalExpression_return conditionalExpression() throws RecognitionException { return gCivlCParser.conditionalExpression(); }

	public OmpParser_CivlCParser.contract_return contract() throws RecognitionException { return gCivlCParser.contract(); }

	public OmpParser_CivlCParser.porItem_return porItem() throws RecognitionException { return gCivlCParser.porItem(); }

	public OmpParser_CivlCParser.initDeclarator_return initDeclarator() throws RecognitionException { return gCivlCParser.initDeclarator(); }

	public OmpParser_CivlCParser.quantifier_return quantifier() throws RecognitionException { return gCivlCParser.quantifier(); }

	public OmpParser_CivlCParser.designatedInitializer_return designatedInitializer() throws RecognitionException { return gCivlCParser.designatedInitializer(); }

	public OmpParser_CivlCParser.parameterTypeListWithScope_return parameterTypeListWithScope() throws RecognitionException { return gCivlCParser.parameterTypeListWithScope(); }

	public OmpParser_CivlCParser.postfixExpressionRoot_return postfixExpressionRoot() throws RecognitionException { return gCivlCParser.postfixExpressionRoot(); }

	public OmpParser_CivlCParser.callsExpression_return callsExpression() throws RecognitionException { return gCivlCParser.callsExpression(); }

	public OmpParser_CivlCParser.quantifierExpression_return quantifierExpression() throws RecognitionException { return gCivlCParser.quantifierExpression(); }

	public OmpParser_CivlCParser.unaryOperator_return unaryOperator() throws RecognitionException { return gCivlCParser.unaryOperator(); }

	public OmpParser_CivlCParser.rangeExpression_return rangeExpression() throws RecognitionException { return gCivlCParser.rangeExpression(); }

	public OmpParser_CivlCParser.blockItem_return blockItem() throws RecognitionException { return gCivlCParser.blockItem(); }

	public OmpParser_CivlCParser.argumentExpressionList_return argumentExpressionList() throws RecognitionException { return gCivlCParser.argumentExpressionList(); }

	public OmpParser_CivlCParser.directAbstractDeclarator_return directAbstractDeclarator() throws RecognitionException { return gCivlCParser.directAbstractDeclarator(); }

	public OmpParser_CivlCParser.structOrUnionSpecifier_return structOrUnionSpecifier() throws RecognitionException { return gCivlCParser.structOrUnionSpecifier(); }

	public OmpParser_CivlCParser.chooseStatement_return chooseStatement() throws RecognitionException { return gCivlCParser.chooseStatement(); }

	public OmpParser_CivlCParser.expressionStatement_return expressionStatement() throws RecognitionException { return gCivlCParser.expressionStatement(); }

	public OmpParser_CivlCParser.atomicTypeSpecifier_return atomicTypeSpecifier() throws RecognitionException { return gCivlCParser.atomicTypeSpecifier(); }

	public OmpParser_CivlCParser.parameterTypeList_return parameterTypeList() throws RecognitionException { return gCivlCParser.parameterTypeList(); }

	public OmpParser_CivlCParser.assignmentOperator_return assignmentOperator() throws RecognitionException { return gCivlCParser.assignmentOperator(); }

	public OmpParser_CivlCParser.shiftExpression_return shiftExpression() throws RecognitionException { return gCivlCParser.shiftExpression(); }

	public OmpParser_CivlCParser.equalityOperator_return equalityOperator() throws RecognitionException { return gCivlCParser.equalityOperator(); }

	public OmpParser_CivlCParser.enumeratorList_return enumeratorList() throws RecognitionException { return gCivlCParser.enumeratorList(); }

	public OmpParser_CivlCParser.declarationSpecifiers_return declarationSpecifiers() throws RecognitionException { return gCivlCParser.declarationSpecifiers(); }

	public OmpParser_CivlCParser.declarationSpecifierList_return declarationSpecifierList() throws RecognitionException { return gCivlCParser.declarationSpecifierList(); }

	public OmpParser_CivlCParser.storageClassSpecifier_return storageClassSpecifier() throws RecognitionException { return gCivlCParser.storageClassSpecifier(); }

	public OmpParser_CivlCParser.statementWithScope_return statementWithScope() throws RecognitionException { return gCivlCParser.statementWithScope(); }

	public OmpParser_CivlCParser.atomicStatement_return atomicStatement() throws RecognitionException { return gCivlCParser.atomicStatement(); }

	public OmpParser_CivlCParser.structDeclarator_return structDeclarator() throws RecognitionException { return gCivlCParser.structDeclarator(); }

	public OmpParser_CivlCParser.pointer_part_return pointer_part() throws RecognitionException { return gCivlCParser.pointer_part(); }

	public OmpParser_CivlCParser.inclusiveOrExpression_return inclusiveOrExpression() throws RecognitionException { return gCivlCParser.inclusiveOrExpression(); }

	public OmpParser_CivlCParser.invariant_opt_return invariant_opt() throws RecognitionException { return gCivlCParser.invariant_opt(); }

	public OmpParser_CivlCParser.partial_return partial() throws RecognitionException { return gCivlCParser.partial(); }

	public OmpParser_CivlCParser.designatorList_return designatorList() throws RecognitionException { return gCivlCParser.designatorList(); }

	public OmpParser_CivlCParser.genericSelection_return genericSelection() throws RecognitionException { return gCivlCParser.genericSelection(); }

	public OmpParser_CivlCParser.directDeclaratorArraySuffix_return directDeclaratorArraySuffix() throws RecognitionException { return gCivlCParser.directDeclaratorArraySuffix(); }

	public OmpParser_CivlCParser.directDeclaratorPrefix_return directDeclaratorPrefix() throws RecognitionException { return gCivlCParser.directDeclaratorPrefix(); }

	public OmpParser_CivlCParser.statement_return statement() throws RecognitionException { return gCivlCParser.statement(); }

	public OmpParser_CivlCParser.abstractDeclarator_return abstractDeclarator() throws RecognitionException { return gCivlCParser.abstractDeclarator(); }

	public OmpParser_CivlCParser.compoundStatement_return compoundStatement() throws RecognitionException { return gCivlCParser.compoundStatement(); }

	public OmpParser_CivlCParser.structDeclaration_return structDeclaration() throws RecognitionException { return gCivlCParser.structDeclaration(); }

	public OmpParser_CivlCParser.whenStatement_return whenStatement() throws RecognitionException { return gCivlCParser.whenStatement(); }

	public OmpParser_CivlCParser.selectionStatement_return selectionStatement() throws RecognitionException { return gCivlCParser.selectionStatement(); }

	public OmpParser_CivlCParser.derivativeExpression_return derivativeExpression() throws RecognitionException { return gCivlCParser.derivativeExpression(); }

	public OmpParser_CivlCParser.primaryExpression_return primaryExpression() throws RecognitionException { return gCivlCParser.primaryExpression(); }

	public OmpParser_CivlCParser.expression_return expression() throws RecognitionException { return gCivlCParser.expression(); }

	public OmpParser_CivlCParser.typeName_opt_return typeName_opt() throws RecognitionException { return gCivlCParser.typeName_opt(); }

	public OmpParser_CivlCParser.directDeclaratorFunctionSuffix_return directDeclaratorFunctionSuffix() throws RecognitionException { return gCivlCParser.directDeclaratorFunctionSuffix(); }

	public OmpParser_CivlCParser.typeQualifierList_opt_return typeQualifierList_opt() throws RecognitionException { return gCivlCParser.typeQualifierList_opt(); }

	public OmpParser_CivlCParser.assignmentExpression_return assignmentExpression() throws RecognitionException { return gCivlCParser.assignmentExpression(); }

	public OmpParser_CivlCParser.enumerator_return enumerator() throws RecognitionException { return gCivlCParser.enumerator(); }

	public OmpParser_CivlCParser.spawnExpression_return spawnExpression() throws RecognitionException { return gCivlCParser.spawnExpression(); }

	public OmpParser_CivlCParser.functionDefinition_return functionDefinition() throws RecognitionException { return gCivlCParser.functionDefinition(); }

	public OmpParser_CivlCParser.assignmentExpression_opt_return assignmentExpression_opt() throws RecognitionException { return gCivlCParser.assignmentExpression_opt(); }

	public OmpParser_CivlCParser.partialList_return partialList() throws RecognitionException { return gCivlCParser.partialList(); }

	public OmpParser_CivlCParser.relationalExpression_return relationalExpression() throws RecognitionException { return gCivlCParser.relationalExpression(); }

	public OmpParser_CivlCParser.enumSpecifier_return enumSpecifier() throws RecognitionException { return gCivlCParser.enumSpecifier(); }

	public OmpParser_CivlCParser.directDeclarator_return directDeclarator() throws RecognitionException { return gCivlCParser.directDeclarator(); }

	public OmpParser_CivlCParser.commaExpression_return commaExpression() throws RecognitionException { return gCivlCParser.commaExpression(); }

	public OmpParser_CivlCParser.additiveExpression_return additiveExpression() throws RecognitionException { return gCivlCParser.additiveExpression(); }

	public OmpParser_CivlCParser.relationalOperator_return relationalOperator() throws RecognitionException { return gCivlCParser.relationalOperator(); }

	public OmpParser_CivlCParser.iterationStatement_return iterationStatement() throws RecognitionException { return gCivlCParser.iterationStatement(); }

	public OmpParser_CivlCParser.parameterList_return parameterList() throws RecognitionException { return gCivlCParser.parameterList(); }

	public OmpParser_CivlCParser.datomicStatement_return datomicStatement() throws RecognitionException { return gCivlCParser.datomicStatement(); }

	public OmpParser_CivlCParser.designator_return designator() throws RecognitionException { return gCivlCParser.designator(); }

	public OmpParser_CivlCParser.designation_return designation() throws RecognitionException { return gCivlCParser.designation(); }

	public OmpParser_CivlCParser.pragmaBody_return pragmaBody() throws RecognitionException { return gCivlCParser.pragmaBody(); }

	public OmpParser_CivlCParser.specifierQualifierList_return specifierQualifierList() throws RecognitionException { return gCivlCParser.specifierQualifierList(); }

	public OmpParser_CivlCParser.typeofSpecifier_return typeofSpecifier() throws RecognitionException { return gCivlCParser.typeofSpecifier(); }

	public OmpParser_CivlCParser.remoteExpression_return remoteExpression() throws RecognitionException { return gCivlCParser.remoteExpression(); }

	public OmpParser_CivlCParser.staticAssertDeclaration_return staticAssertDeclaration() throws RecognitionException { return gCivlCParser.staticAssertDeclaration(); }

	public OmpParser_CivlCParser.jumpStatement_return jumpStatement() throws RecognitionException { return gCivlCParser.jumpStatement(); }

	public OmpParser_CivlCParser.typeQualifier_return typeQualifier() throws RecognitionException { return gCivlCParser.typeQualifier(); }

	public OmpParser_CivlCParser.labeledStatement_return labeledStatement() throws RecognitionException { return gCivlCParser.labeledStatement(); }

	public OmpParser_CivlCParser.typeName_return typeName() throws RecognitionException { return gCivlCParser.typeName(); }

	public OmpParser_CivlCParser.enumerationConstant_return enumerationConstant() throws RecognitionException { return gCivlCParser.enumerationConstant(); }

	public OmpParser_CivlCParser.blockItemWithScope_return blockItemWithScope() throws RecognitionException { return gCivlCParser.blockItemWithScope(); }

	public OmpParser_CivlCParser.pragma_return pragma() throws RecognitionException { return gCivlCParser.pragma(); }

	public OmpParser_CivlCParser.contractItem_return contractItem() throws RecognitionException { return gCivlCParser.contractItem(); }

	public OmpParser_CivlCParser.typeSpecifier_return typeSpecifier() throws RecognitionException { return gCivlCParser.typeSpecifier(); }

	public OmpParser_CivlCParser.constantExpression_return constantExpression() throws RecognitionException { return gCivlCParser.constantExpression(); }

	public OmpParser_CivlCParser.structDeclaratorList_return structDeclaratorList() throws RecognitionException { return gCivlCParser.structDeclaratorList(); }

	public OmpParser_CivlCParser.identifierList_return identifierList() throws RecognitionException { return gCivlCParser.identifierList(); }

	public OmpParser_CivlCParser.typedefName_return typedefName() throws RecognitionException { return gCivlCParser.typedefName(); }

	public OmpParser_CivlCParser.directDeclaratorSuffix_return directDeclaratorSuffix() throws RecognitionException { return gCivlCParser.directDeclaratorSuffix(); }

	public OmpParser_CivlCParser.functionSpecifier_return functionSpecifier() throws RecognitionException { return gCivlCParser.functionSpecifier(); }

	public OmpParser_CivlCParser.exclusiveOrExpression_return exclusiveOrExpression() throws RecognitionException { return gCivlCParser.exclusiveOrExpression(); }

	public OmpParser_CivlCParser.parameterDeclaration_return parameterDeclaration() throws RecognitionException { return gCivlCParser.parameterDeclaration(); }

	public OmpParser_CivlCParser.initDeclaratorList_return initDeclaratorList() throws RecognitionException { return gCivlCParser.initDeclaratorList(); }

	public OmpParser_CivlCParser.declarationList_opt_return declarationList_opt() throws RecognitionException { return gCivlCParser.declarationList_opt(); }

	public OmpParser_CivlCParser.structOrUnion_return structOrUnion() throws RecognitionException { return gCivlCParser.structOrUnion(); }

	public OmpParser_CivlCParser.multiplicativeExpression_return multiplicativeExpression() throws RecognitionException { return gCivlCParser.multiplicativeExpression(); }

	public OmpParser_CivlCParser.typeQualifierList_return typeQualifierList() throws RecognitionException { return gCivlCParser.typeQualifierList(); }

	public OmpParser_CivlCParser.logicalOrExpression_return logicalOrExpression() throws RecognitionException { return gCivlCParser.logicalOrExpression(); }

	public OmpParser_CivlCParser.logicalAndExpression_return logicalAndExpression() throws RecognitionException { return gCivlCParser.logicalAndExpression(); }

	public OmpParser_CivlCParser.alignmentSpecifier_return alignmentSpecifier() throws RecognitionException { return gCivlCParser.alignmentSpecifier(); }

	public OmpParser_CivlCParser.constant_return constant() throws RecognitionException { return gCivlCParser.constant(); }

	public OmpParser_CivlCParser.pointer_return pointer() throws RecognitionException { return gCivlCParser.pointer(); }

	public OmpParser_CivlCParser.equalityExpression_return equalityExpression() throws RecognitionException { return gCivlCParser.equalityExpression(); }

	public OmpParser_CivlCParser.declarator_return declarator() throws RecognitionException { return gCivlCParser.declarator(); }

	public OmpParser_CivlCParser.initializerList_return initializerList() throws RecognitionException { return gCivlCParser.initializerList(); }

	public OmpParser_CivlCParser.expression_opt_return expression_opt() throws RecognitionException { return gCivlCParser.expression_opt(); }

	public OmpParser_CivlCParser.andExpression_return andExpression() throws RecognitionException { return gCivlCParser.andExpression(); }

	public OmpParser_CivlCParser.logicalImpliesExpression_return logicalImpliesExpression() throws RecognitionException { return gCivlCParser.logicalImpliesExpression(); }

	public OmpParser_CivlCParser.blockItemList_return blockItemList() throws RecognitionException { return gCivlCParser.blockItemList(); }

	public OmpParser_CivlCParser.declarationSpecifier_return declarationSpecifier() throws RecognitionException { return gCivlCParser.declarationSpecifier(); }

	public OmpParser_CivlCParser.directAbstractDeclaratorSuffix_return directAbstractDeclaratorSuffix() throws RecognitionException { return gCivlCParser.directAbstractDeclaratorSuffix(); }

	public OmpParser_CivlCParser.genericAssocList_return genericAssocList() throws RecognitionException { return gCivlCParser.genericAssocList(); }

	public OmpParser_CivlCParser.separationLogicItem_return separationLogicItem() throws RecognitionException { return gCivlCParser.separationLogicItem(); }

	public OmpParser_CivlCParser.domainSpecifier_return domainSpecifier() throws RecognitionException { return gCivlCParser.domainSpecifier(); }

	public OmpParser_CivlCParser.parameterTypeListWithoutScope_return parameterTypeListWithoutScope() throws RecognitionException { return gCivlCParser.parameterTypeListWithoutScope(); }

	public OmpParser_CivlCParser.unaryExpression_return unaryExpression() throws RecognitionException { return gCivlCParser.unaryExpression(); }

	public OmpParser_CivlCParser.declaration_return declaration() throws RecognitionException { return gCivlCParser.declaration(); }



	public static final BitSet FOLLOW_parallel_for_directive_in_openmp_construct96 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_parallel_sections_directive_in_openmp_construct102 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_parallel_directive_in_openmp_construct108 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_for_directive_in_openmp_construct114 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_sections_directive_in_openmp_construct120 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_single_directive_in_openmp_construct126 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_master_directive_in_openmp_construct132 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_critical_directive_in_openmp_construct138 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ordered_directive_in_openmp_construct144 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_section_directive_in_openmp_construct150 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ompatomic_directive_in_openmp_construct156 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_barrier_directive_in_openmp_construct162 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_flush_directive_in_openmp_construct168 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_threadprivate_directive_in_openmp_construct174 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PARALLEL_in_parallel_directive187 = new BitSet(new long[]{0x0000020000000002L,0x0000000008000000L,0x0000002000000000L,0x0000000000000000L,0x000000288A300000L});
	public static final BitSet FOLLOW_parallel_clause_in_parallel_directive193 = new BitSet(new long[]{0x0000020000000002L,0x0000000008000000L,0x0000002000000000L,0x0000000000000000L,0x000000288A300000L});
	public static final BitSet FOLLOW_unique_parallel_clause_in_parallel_clause220 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_data_clause_in_parallel_clause226 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MASTER_in_master_directive241 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_CRITICAL_in_critical_directive260 = new BitSet(new long[]{0x0000000000000002L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_critical_directive264 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_critical_directive269 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_critical_directive272 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SECTIONS_in_sections_directive301 = new BitSet(new long[]{0x0000020000000002L,0x0000000000000000L,0x0000002000000000L,0x0000000000000000L,0x000000284A300000L});
	public static final BitSet FOLLOW_sections_clause_in_sections_directive307 = new BitSet(new long[]{0x0000020000000002L,0x0000000000000000L,0x0000002000000000L,0x0000000000000000L,0x000000284A300000L});
	public static final BitSet FOLLOW_data_clause_in_sections_clause334 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_nowait_directive_in_sections_clause340 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SECTION_in_section_directive353 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PARALLEL_in_parallel_for_directive374 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_FOR_in_parallel_for_directive376 = new BitSet(new long[]{0x0000020000000002L,0x0000000008000000L,0x0000002000000000L,0x0000000000000000L,0x000000AA8A380000L});
	public static final BitSet FOLLOW_parallel_for_clause_in_parallel_for_directive380 = new BitSet(new long[]{0x0000020000000002L,0x0000000008000000L,0x0000002000000000L,0x0000000000000000L,0x000000AA8A380000L});
	public static final BitSet FOLLOW_unique_parallel_clause_in_parallel_for_clause408 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unique_for_clause_in_parallel_for_clause414 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_data_clause_in_parallel_for_clause420 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PARALLEL_in_parallel_sections_directive433 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000020000000000L});
	public static final BitSet FOLLOW_SECTIONS_in_parallel_sections_directive436 = new BitSet(new long[]{0x0000020000000002L,0x0000000008000000L,0x0000002000000000L,0x0000000000000000L,0x000000288A300000L});
	public static final BitSet FOLLOW_parallel_sections_clause_in_parallel_sections_directive441 = new BitSet(new long[]{0x0000020000000002L,0x0000000008000000L,0x0000002000000000L,0x0000000000000000L,0x000000288A300000L});
	public static final BitSet FOLLOW_unique_parallel_clause_in_parallel_sections_clause469 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_data_clause_in_parallel_sections_clause475 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SINGLE_in_single_directive488 = new BitSet(new long[]{0x0000020000000002L,0x0000000000000000L,0x0000002000000000L,0x0000000000000000L,0x000000284A300000L});
	public static final BitSet FOLLOW_single_clause_in_single_directive493 = new BitSet(new long[]{0x0000020000000002L,0x0000000000000000L,0x0000002000000000L,0x0000000000000000L,0x000000284A300000L});
	public static final BitSet FOLLOW_data_clause_in_single_clause521 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_nowait_directive_in_single_clause527 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BARRIER_in_barrier_directive540 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_OMPATOMIC_in_ompatomic_directive561 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000641000040000L});
	public static final BitSet FOLLOW_atomic_clasue_in_ompatomic_directive565 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000040000000000L});
	public static final BitSet FOLLOW_seq_cst_clause_in_ompatomic_directive570 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SEQ_CST_in_seq_cst_clause629 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FLUSH_in_flush_directive642 = new BitSet(new long[]{0x0000000000000002L,0x0000010000000000L});
	public static final BitSet FOLLOW_flush_vars_in_flush_directive647 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_flush_vars675 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_identifier_list_in_flush_vars681 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_flush_vars684 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ORDERED_in_ordered_directive710 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NOWAIT_in_nowait_directive731 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_THD_PRIVATE_in_threadprivate_directive750 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_threadprivate_directive753 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_identifier_list_in_threadprivate_directive758 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_threadprivate_directive761 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FOR_in_for_directive787 = new BitSet(new long[]{0x0000020000000002L,0x0000000000000000L,0x0000002000000000L,0x0000000000000000L,0x000000AA4A380000L});
	public static final BitSet FOLLOW_for_clause_in_for_directive793 = new BitSet(new long[]{0x0000020000000002L,0x0000000000000000L,0x0000002000000000L,0x0000000000000000L,0x000000AA4A380000L});
	public static final BitSet FOLLOW_unique_for_clause_in_for_clause824 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_data_clause_in_for_clause841 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_nowait_directive_in_for_clause858 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ORDERED_in_unique_for_clause880 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_schedule_clause_in_unique_for_clause895 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_collapse_clause_in_unique_for_clause912 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SCHEDULE_in_schedule_clause935 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_schedule_clause938 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0001000000000000L,0x0000000000000000L,0x0000004004800000L});
	public static final BitSet FOLLOW_schedule_kind_in_schedule_clause943 = new BitSet(new long[]{0x0000000800000000L});
	public static final BitSet FOLLOW_COMMA_in_schedule_clause946 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_schedule_clause951 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_schedule_clause954 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SCHEDULE_in_schedule_clause981 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_schedule_clause984 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0001000000000000L,0x0000000000000000L,0x0000004004800000L});
	public static final BitSet FOLLOW_schedule_kind_in_schedule_clause989 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_schedule_clause992 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_COLLAPSE_in_collapse_clause1017 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_collapse_clause1020 = new BitSet(new long[]{0x0000000000000000L,0x0000000200000000L});
	public static final BitSet FOLLOW_INTEGER_CONSTANT_in_collapse_clause1025 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_collapse_clause1028 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STATIC_in_schedule_kind1053 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DYNAMIC_in_schedule_kind1065 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_GUIDED_in_schedule_kind1077 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RUNTIME_in_schedule_kind1089 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_if_clause_in_unique_parallel_clause1110 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_num_threads_clause_in_unique_parallel_clause1132 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IF_in_if_clause1161 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_if_clause1164 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_if_clause1169 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_if_clause1172 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NUM_THREADS_in_num_threads_clause1200 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_num_threads_clause1203 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_num_threads_clause1208 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_num_threads_clause1211 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_private_clause_in_data_clause1239 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_firstprivate_clause_in_data_clause1260 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_lastprivate_clause_in_data_clause1281 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_shared_clause_in_data_clause1302 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_default_clause_in_data_clause1323 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_reduction_clause_in_data_clause1344 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_copyin_clause_in_data_clause1365 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_copyprivate_clause_in_data_clause1386 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PRIVATE_in_private_clause1414 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_private_clause1417 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_identifier_list_in_private_clause1422 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_private_clause1425 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FST_PRIVATE_in_firstprivate_clause1454 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_firstprivate_clause1457 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_identifier_list_in_firstprivate_clause1462 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_firstprivate_clause1465 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LST_PRIVATE_in_lastprivate_clause1493 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_lastprivate_clause1496 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_identifier_list_in_lastprivate_clause1501 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_lastprivate_clause1504 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SHARED_in_shared_clause1532 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_shared_clause1535 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_identifier_list_in_shared_clause1540 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_shared_clause1543 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DEFAULT_in_default_clause1571 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_default_clause1574 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_SHARED_in_default_clause1577 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_default_clause1580 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DEFAULT_in_default_clause1598 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_default_clause1601 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000020000000L});
	public static final BitSet FOLLOW_NONE_in_default_clause1604 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_default_clause1607 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REDUCTION_in_reduction_clause1634 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_reduction_clause1636 = new BitSet(new long[]{0x00000000000A0180L,0x0400000004000000L,0x0010400000000800L});
	public static final BitSet FOLLOW_reduction_operator_in_reduction_clause1640 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_COLON_in_reduction_clause1642 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_identifier_list_in_reduction_clause1646 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_reduction_clause1648 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_COPYIN_in_copyin_clause1679 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_copyin_clause1682 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_identifier_list_in_copyin_clause1687 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_copyin_clause1690 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_COPYPRIVATE_in_copyprivate_clause1718 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_copyprivate_clause1721 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_identifier_list_in_copyprivate_clause1726 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_copyprivate_clause1729 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PLUS_in_reduction_operator1755 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STAR_in_reduction_operator1767 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SUB_in_reduction_operator1779 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_AMPERSAND_in_reduction_operator1791 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BITXOR_in_reduction_operator1803 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BITOR_in_reduction_operator1815 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_AND_in_reduction_operator1827 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_OR_in_reduction_operator1839 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENTIFIER_in_reduction_operator1851 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENTIFIER_in_identifier_list1874 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_COMMA_in_identifier_list1878 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_identifier_list1883 = new BitSet(new long[]{0x0000000800000002L});
}
