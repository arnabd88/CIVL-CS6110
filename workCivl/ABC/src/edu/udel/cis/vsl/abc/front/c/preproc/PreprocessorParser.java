// $ANTLR 3.5.2 PreprocessorParser.g 2016-04-11 02:06:17

package edu.udel.cis.vsl.abc.front.c.preproc;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

import org.antlr.runtime.tree.*;


@SuppressWarnings("all")
public class PreprocessorParser extends Parser {
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
		"EXPR", "FILE", "PARAMLIST", "ROOT", "SEQUENCE", "TEXT_BLOCK"
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

	// delegates
	public Parser[] getDelegates() {
		return new Parser[] {};
	}

	// delegators


	public PreprocessorParser(TokenStream input) {
		this(input, new RecognizerSharedState());
	}
	public PreprocessorParser(TokenStream input, RecognizerSharedState state) {
		super(input, state);
	}

	protected TreeAdaptor adaptor = new CommonTreeAdaptor();

	public void setTreeAdaptor(TreeAdaptor adaptor) {
		this.adaptor = adaptor;
	}
	public TreeAdaptor getTreeAdaptor() {
		return adaptor;
	}
	@Override public String[] getTokenNames() { return PreprocessorParser.tokenNames; }
	@Override public String getGrammarFileName() { return "PreprocessorParser.g"; }


	@Override
	public void emitErrorMessage(String msg) { // don't try to recover!
	    throw new RuntimeException(msg);
	}


	public static class file_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "file"
	// PreprocessorParser.g:47:1: file : block -> ^( FILE block ) ;
	public final PreprocessorParser.file_return file() throws RecognitionException {
		PreprocessorParser.file_return retval = new PreprocessorParser.file_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope block1 =null;

		RewriteRuleSubtreeStream stream_block=new RewriteRuleSubtreeStream(adaptor,"rule block");

		try {
			// PreprocessorParser.g:47:7: ( block -> ^( FILE block ) )
			// PreprocessorParser.g:47:9: block
			{
			pushFollow(FOLLOW_block_in_file120);
			block1=block();
			state._fsp--;

			stream_block.add(block1.getTree());
			// AST REWRITE
			// elements: block
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 47:15: -> ^( FILE block )
			{
				// PreprocessorParser.g:47:18: ^( FILE block )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FILE, "FILE"), root_1);
				adaptor.addChild(root_1, stream_block.nextTree());
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
	// $ANTLR end "file"


	public static class block_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "block"
	// PreprocessorParser.g:53:1: block : ( directive | textblock )* ;
	public final PreprocessorParser.block_return block() throws RecognitionException {
		PreprocessorParser.block_return retval = new PreprocessorParser.block_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope directive2 =null;
		ParserRuleReturnScope textblock3 =null;


		try {
			// PreprocessorParser.g:53:8: ( ( directive | textblock )* )
			// PreprocessorParser.g:53:10: ( directive | textblock )*
			{
			root_0 = (Object)adaptor.nil();


			// PreprocessorParser.g:53:10: ( directive | textblock )*
			loop1:
			while (true) {
				int alt1=3;
				int LA1_0 = input.LA(1);
				if ( (LA1_0==HASH||LA1_0==PDEFINE||(LA1_0 >= PERROR && LA1_0 <= PLINE)||LA1_0==PRAGMA||LA1_0==PUNDEF) ) {
					alt1=1;
				}
				else if ( ((LA1_0 >= ABSTRACT && LA1_0 <= BREAK)||(LA1_0 >= CALLS && LA1_0 <= CASE)||(LA1_0 >= CHAR && LA1_0 <= DEFAULT)||(LA1_0 >= DEPENDS && LA1_0 <= DOUBLE)||(LA1_0 >= ELLIPSIS && LA1_0 <= EXTERN)||(LA1_0 >= FALSE && LA1_0 <= FORALL)||(LA1_0 >= GENERIC && LA1_0 <= GUARD)||(LA1_0 >= HASHHASH && LA1_0 <= HERE)||(LA1_0 >= IDENTIFIER && LA1_0 <= INVARIANT)||(LA1_0 >= LCURLY && LA1_0 <= LTE)||(LA1_0 >= MINUSMINUS && LA1_0 <= NOT)||(LA1_0 >= OR && LA1_0 <= OUTPUT)||LA1_0==PARFOR||(LA1_0 >= PLUS && LA1_0 <= PP_NUMBER)||LA1_0==PROCNULL||(LA1_0 >= PURE && LA1_0 <= SCOPEOF)||(LA1_0 >= SELF && LA1_0 <= UNSIGNED)||(LA1_0 >= VOID && LA1_0 <= WS)||LA1_0==ROOT) ) {
					alt1=2;
				}

				switch (alt1) {
				case 1 :
					// PreprocessorParser.g:53:11: directive
					{
					pushFollow(FOLLOW_directive_in_block143);
					directive2=directive();
					state._fsp--;

					adaptor.addChild(root_0, directive2.getTree());

					}
					break;
				case 2 :
					// PreprocessorParser.g:53:23: textblock
					{
					pushFollow(FOLLOW_textblock_in_block147);
					textblock3=textblock();
					state._fsp--;

					adaptor.addChild(root_0, textblock3.getTree());

					}
					break;

				default :
					break loop1;
				}
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
	// $ANTLR end "block"


	public static class directive_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "directive"
	// PreprocessorParser.g:64:1: directive : ( macrodef | macroundef | includeline | pragmaline | ifblock | ifdefblock | ifndefblock | errorline | lineline | nondirectiveline );
	public final PreprocessorParser.directive_return directive() throws RecognitionException {
		PreprocessorParser.directive_return retval = new PreprocessorParser.directive_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope macrodef4 =null;
		ParserRuleReturnScope macroundef5 =null;
		ParserRuleReturnScope includeline6 =null;
		ParserRuleReturnScope pragmaline7 =null;
		ParserRuleReturnScope ifblock8 =null;
		ParserRuleReturnScope ifdefblock9 =null;
		ParserRuleReturnScope ifndefblock10 =null;
		ParserRuleReturnScope errorline11 =null;
		ParserRuleReturnScope lineline12 =null;
		ParserRuleReturnScope nondirectiveline13 =null;


		try {
			// PreprocessorParser.g:64:11: ( macrodef | macroundef | includeline | pragmaline | ifblock | ifdefblock | ifndefblock | errorline | lineline | nondirectiveline )
			int alt2=10;
			switch ( input.LA(1) ) {
			case PDEFINE:
				{
				alt2=1;
				}
				break;
			case PUNDEF:
				{
				alt2=2;
				}
				break;
			case PINCLUDE:
				{
				alt2=3;
				}
				break;
			case PRAGMA:
				{
				alt2=4;
				}
				break;
			case PIF:
				{
				alt2=5;
				}
				break;
			case PIFDEF:
				{
				alt2=6;
				}
				break;
			case PIFNDEF:
				{
				alt2=7;
				}
				break;
			case PERROR:
				{
				alt2=8;
				}
				break;
			case PLINE:
				{
				alt2=9;
				}
				break;
			case HASH:
				{
				alt2=10;
				}
				break;
			default:
				NoViableAltException nvae =
					new NoViableAltException("", 2, 0, input);
				throw nvae;
			}
			switch (alt2) {
				case 1 :
					// PreprocessorParser.g:64:13: macrodef
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_macrodef_in_directive160);
					macrodef4=macrodef();
					state._fsp--;

					adaptor.addChild(root_0, macrodef4.getTree());

					}
					break;
				case 2 :
					// PreprocessorParser.g:65:5: macroundef
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_macroundef_in_directive166);
					macroundef5=macroundef();
					state._fsp--;

					adaptor.addChild(root_0, macroundef5.getTree());

					}
					break;
				case 3 :
					// PreprocessorParser.g:66:5: includeline
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_includeline_in_directive172);
					includeline6=includeline();
					state._fsp--;

					adaptor.addChild(root_0, includeline6.getTree());

					}
					break;
				case 4 :
					// PreprocessorParser.g:67:5: pragmaline
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_pragmaline_in_directive178);
					pragmaline7=pragmaline();
					state._fsp--;

					adaptor.addChild(root_0, pragmaline7.getTree());

					}
					break;
				case 5 :
					// PreprocessorParser.g:68:5: ifblock
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_ifblock_in_directive184);
					ifblock8=ifblock();
					state._fsp--;

					adaptor.addChild(root_0, ifblock8.getTree());

					}
					break;
				case 6 :
					// PreprocessorParser.g:69:5: ifdefblock
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_ifdefblock_in_directive190);
					ifdefblock9=ifdefblock();
					state._fsp--;

					adaptor.addChild(root_0, ifdefblock9.getTree());

					}
					break;
				case 7 :
					// PreprocessorParser.g:70:5: ifndefblock
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_ifndefblock_in_directive196);
					ifndefblock10=ifndefblock();
					state._fsp--;

					adaptor.addChild(root_0, ifndefblock10.getTree());

					}
					break;
				case 8 :
					// PreprocessorParser.g:71:5: errorline
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_errorline_in_directive202);
					errorline11=errorline();
					state._fsp--;

					adaptor.addChild(root_0, errorline11.getTree());

					}
					break;
				case 9 :
					// PreprocessorParser.g:72:5: lineline
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_lineline_in_directive208);
					lineline12=lineline();
					state._fsp--;

					adaptor.addChild(root_0, lineline12.getTree());

					}
					break;
				case 10 :
					// PreprocessorParser.g:73:5: nondirectiveline
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_nondirectiveline_in_directive214);
					nondirectiveline13=nondirectiveline();
					state._fsp--;

					adaptor.addChild(root_0, nondirectiveline13.getTree());

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
	// $ANTLR end "directive"


	public static class textblock_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "textblock"
	// PreprocessorParser.g:82:1: textblock : ( options {greedy=true; } : textline )+ -> ^( TEXT_BLOCK ( textline )+ ) ;
	public final PreprocessorParser.textblock_return textblock() throws RecognitionException {
		PreprocessorParser.textblock_return retval = new PreprocessorParser.textblock_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope textline14 =null;

		RewriteRuleSubtreeStream stream_textline=new RewriteRuleSubtreeStream(adaptor,"rule textline");

		try {
			// PreprocessorParser.g:82:11: ( ( options {greedy=true; } : textline )+ -> ^( TEXT_BLOCK ( textline )+ ) )
			// PreprocessorParser.g:82:14: ( options {greedy=true; } : textline )+
			{
			// PreprocessorParser.g:82:14: ( options {greedy=true; } : textline )+
			int cnt3=0;
			loop3:
			while (true) {
				int alt3=2;
				switch ( input.LA(1) ) {
				case COMMENT:
				case WS:
					{
					alt3=1;
					}
					break;
				case HEADER_NAME:
					{
					alt3=1;
					}
					break;
				case IDENTIFIER:
					{
					alt3=1;
					}
					break;
				case ABSTRACT:
				case ALIGNAS:
				case ALIGNOF:
				case ASSIGNS:
				case ATOMIC:
				case AUTO:
				case BIG_O:
				case BOOL:
				case BREAK:
				case CALLS:
				case CASE:
				case CHAR:
				case CHOOSE:
				case CIVLATOM:
				case CIVLATOMIC:
				case CIVLFOR:
				case COLLECTIVE:
				case COMPLEX:
				case CONST:
				case CONTIN:
				case CONTINUE:
				case DEFAULT:
				case DEPENDS:
				case DERIV:
				case DEVICE:
				case DO:
				case DOMAIN:
				case DOUBLE:
				case ELSE:
				case ENSURES:
				case ENUM:
				case EXISTS:
				case EXTERN:
				case FALSE:
				case FATOMIC:
				case FLOAT:
				case FOR:
				case FORALL:
				case GENERIC:
				case GLOBAL:
				case GOTO:
				case GUARD:
				case HERE:
				case IF:
				case IMAGINARY:
				case INLINE:
				case INPUT:
				case INT:
				case INVARIANT:
				case LONG:
				case NORETURN:
				case OUTPUT:
				case PARFOR:
				case PROCNULL:
				case PURE:
				case RANGE:
				case READS:
				case REAL:
				case REGISTER:
				case REQUIRES:
				case RESTRICT:
				case RESULT:
				case RETURN:
				case SCOPEOF:
				case SELF:
				case SHARED:
				case SHORT:
				case SIGNED:
				case SIZEOF:
				case SPAWN:
				case STATIC:
				case STATICASSERT:
				case STRUCT:
				case SWITCH:
				case SYSTEM:
				case THREADLOCAL:
				case TRUE:
				case TYPEDEF:
				case UNIFORM:
				case UNION:
				case UNSIGNED:
				case VOID:
				case VOLATILE:
				case WHEN:
				case WHILE:
				case ROOT:
					{
					alt3=1;
					}
					break;
				case TYPEOF:
					{
					alt3=1;
					}
					break;
				case FLOATING_CONSTANT:
				case INTEGER_CONSTANT:
				case PP_NUMBER:
					{
					alt3=1;
					}
					break;
				case CHARACTER_CONSTANT:
					{
					alt3=1;
					}
					break;
				case STRING_LITERAL:
					{
					alt3=1;
					}
					break;
				case AMPERSAND:
				case AND:
				case ARROW:
				case ASSIGN:
				case AT:
				case BITANDEQ:
				case BITOR:
				case BITOREQ:
				case BITXOR:
				case BITXOREQ:
				case COLON:
				case COMMA:
				case DIV:
				case DIVEQ:
				case DOT:
				case DOTDOT:
				case ELLIPSIS:
				case EQUALS:
				case GT:
				case GTE:
				case HASHHASH:
				case IMPLIES:
				case LCURLY:
				case LEXCON:
				case LPAREN:
				case LSLIST:
				case LSQUARE:
				case LT:
				case LTE:
				case MINUSMINUS:
				case MOD:
				case MODEQ:
				case NEQ:
				case NOT:
				case OR:
				case PLUS:
				case PLUSEQ:
				case PLUSPLUS:
				case QMARK:
				case RCURLY:
				case REXCON:
				case RPAREN:
				case RSLIST:
				case RSQUARE:
				case SEMI:
				case SHIFTLEFT:
				case SHIFTLEFTEQ:
				case SHIFTRIGHT:
				case SHIFTRIGHTEQ:
				case STAR:
				case STAREQ:
				case SUB:
				case SUBEQ:
				case TILDE:
					{
					alt3=1;
					}
					break;
				case OTHER:
					{
					alt3=1;
					}
					break;
				case NEWLINE:
					{
					alt3=1;
					}
					break;
				}
				switch (alt3) {
				case 1 :
					// PreprocessorParser.g:82:40: textline
					{
					pushFollow(FOLLOW_textline_in_textblock238);
					textline14=textline();
					state._fsp--;

					stream_textline.add(textline14.getTree());
					}
					break;

				default :
					if ( cnt3 >= 1 ) break loop3;
					EarlyExitException eee = new EarlyExitException(3, input);
					throw eee;
				}
				cnt3++;
			}

			// AST REWRITE
			// elements: textline
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 83:5: -> ^( TEXT_BLOCK ( textline )+ )
			{
				// PreprocessorParser.g:83:8: ^( TEXT_BLOCK ( textline )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TEXT_BLOCK, "TEXT_BLOCK"), root_1);
				if ( !(stream_textline.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_textline.hasNext() ) {
					adaptor.addChild(root_1, stream_textline.nextTree());
				}
				stream_textline.reset();

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
	// $ANTLR end "textblock"


	public static class textline_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "textline"
	// PreprocessorParser.g:85:1: textline : ( white )* ( nonPoundPpToken ( wpptoken )* )? lineend ;
	public final PreprocessorParser.textline_return textline() throws RecognitionException {
		PreprocessorParser.textline_return retval = new PreprocessorParser.textline_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope white15 =null;
		ParserRuleReturnScope nonPoundPpToken16 =null;
		ParserRuleReturnScope wpptoken17 =null;
		ParserRuleReturnScope lineend18 =null;


		try {
			// PreprocessorParser.g:85:10: ( ( white )* ( nonPoundPpToken ( wpptoken )* )? lineend )
			// PreprocessorParser.g:85:12: ( white )* ( nonPoundPpToken ( wpptoken )* )? lineend
			{
			root_0 = (Object)adaptor.nil();


			// PreprocessorParser.g:85:12: ( white )*
			loop4:
			while (true) {
				int alt4=2;
				int LA4_0 = input.LA(1);
				if ( (LA4_0==COMMENT||LA4_0==WS) ) {
					alt4=1;
				}

				switch (alt4) {
				case 1 :
					// PreprocessorParser.g:85:12: white
					{
					pushFollow(FOLLOW_white_in_textline262);
					white15=white();
					state._fsp--;

					adaptor.addChild(root_0, white15.getTree());

					}
					break;

				default :
					break loop4;
				}
			}

			// PreprocessorParser.g:85:19: ( nonPoundPpToken ( wpptoken )* )?
			int alt6=2;
			int LA6_0 = input.LA(1);
			if ( ((LA6_0 >= ABSTRACT && LA6_0 <= BREAK)||(LA6_0 >= CALLS && LA6_0 <= CASE)||(LA6_0 >= CHAR && LA6_0 <= COMMA)||(LA6_0 >= COMPLEX && LA6_0 <= DEFAULT)||(LA6_0 >= DEPENDS && LA6_0 <= DOUBLE)||(LA6_0 >= ELLIPSIS && LA6_0 <= EXTERN)||(LA6_0 >= FALSE && LA6_0 <= FORALL)||(LA6_0 >= GENERIC && LA6_0 <= GUARD)||(LA6_0 >= HASHHASH && LA6_0 <= HERE)||(LA6_0 >= IDENTIFIER && LA6_0 <= INVARIANT)||(LA6_0 >= LCURLY && LA6_0 <= LTE)||(LA6_0 >= MINUSMINUS && LA6_0 <= NEQ)||(LA6_0 >= NORETURN && LA6_0 <= NOT)||(LA6_0 >= OR && LA6_0 <= OUTPUT)||LA6_0==PARFOR||(LA6_0 >= PLUS && LA6_0 <= PP_NUMBER)||LA6_0==PROCNULL||(LA6_0 >= PURE && LA6_0 <= SCOPEOF)||(LA6_0 >= SELF && LA6_0 <= UNSIGNED)||(LA6_0 >= VOID && LA6_0 <= WHILE)||LA6_0==ROOT) ) {
				alt6=1;
			}
			switch (alt6) {
				case 1 :
					// PreprocessorParser.g:85:20: nonPoundPpToken ( wpptoken )*
					{
					pushFollow(FOLLOW_nonPoundPpToken_in_textline266);
					nonPoundPpToken16=nonPoundPpToken();
					state._fsp--;

					adaptor.addChild(root_0, nonPoundPpToken16.getTree());

					// PreprocessorParser.g:85:36: ( wpptoken )*
					loop5:
					while (true) {
						int alt5=2;
						int LA5_0 = input.LA(1);
						if ( ((LA5_0 >= ABSTRACT && LA5_0 <= BREAK)||(LA5_0 >= CALLS && LA5_0 <= CASE)||(LA5_0 >= CHAR && LA5_0 <= DEFAULT)||(LA5_0 >= DEPENDS && LA5_0 <= DOUBLE)||(LA5_0 >= ELLIPSIS && LA5_0 <= EXTERN)||(LA5_0 >= FALSE && LA5_0 <= FORALL)||(LA5_0 >= GENERIC && LA5_0 <= HERE)||(LA5_0 >= IDENTIFIER && LA5_0 <= INVARIANT)||(LA5_0 >= LCURLY && LA5_0 <= LTE)||(LA5_0 >= MINUSMINUS && LA5_0 <= NEQ)||(LA5_0 >= NORETURN && LA5_0 <= NOT)||(LA5_0 >= OR && LA5_0 <= OUTPUT)||LA5_0==PARFOR||(LA5_0 >= PLUS && LA5_0 <= PP_NUMBER)||LA5_0==PROCNULL||(LA5_0 >= PURE && LA5_0 <= SCOPEOF)||(LA5_0 >= SELF && LA5_0 <= UNSIGNED)||(LA5_0 >= VOID && LA5_0 <= WS)||LA5_0==ROOT) ) {
							alt5=1;
						}

						switch (alt5) {
						case 1 :
							// PreprocessorParser.g:85:36: wpptoken
							{
							pushFollow(FOLLOW_wpptoken_in_textline268);
							wpptoken17=wpptoken();
							state._fsp--;

							adaptor.addChild(root_0, wpptoken17.getTree());

							}
							break;

						default :
							break loop5;
						}
					}

					}
					break;

			}

			pushFollow(FOLLOW_lineend_in_textline273);
			lineend18=lineend();
			state._fsp--;

			adaptor.addChild(root_0, lineend18.getTree());

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
	// $ANTLR end "textline"


	public static class white_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "white"
	// PreprocessorParser.g:87:1: white : ( WS | COMMENT );
	public final PreprocessorParser.white_return white() throws RecognitionException {
		PreprocessorParser.white_return retval = new PreprocessorParser.white_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set19=null;

		Object set19_tree=null;

		try {
			// PreprocessorParser.g:87:8: ( WS | COMMENT )
			// PreprocessorParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set19=input.LT(1);
			if ( input.LA(1)==COMMENT||input.LA(1)==WS ) {
				input.consume();
				adaptor.addChild(root_0, (Object)adaptor.create(set19));
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
	// $ANTLR end "white"


	public static class wpptoken_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "wpptoken"
	// PreprocessorParser.g:89:1: wpptoken : ( pptoken | white );
	public final PreprocessorParser.wpptoken_return wpptoken() throws RecognitionException {
		PreprocessorParser.wpptoken_return retval = new PreprocessorParser.wpptoken_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope pptoken20 =null;
		ParserRuleReturnScope white21 =null;


		try {
			// PreprocessorParser.g:89:10: ( pptoken | white )
			int alt7=2;
			int LA7_0 = input.LA(1);
			if ( ((LA7_0 >= ABSTRACT && LA7_0 <= BREAK)||(LA7_0 >= CALLS && LA7_0 <= CASE)||(LA7_0 >= CHAR && LA7_0 <= COMMA)||(LA7_0 >= COMPLEX && LA7_0 <= DEFAULT)||(LA7_0 >= DEPENDS && LA7_0 <= DOUBLE)||(LA7_0 >= ELLIPSIS && LA7_0 <= EXTERN)||(LA7_0 >= FALSE && LA7_0 <= FORALL)||(LA7_0 >= GENERIC && LA7_0 <= HERE)||(LA7_0 >= IDENTIFIER && LA7_0 <= INVARIANT)||(LA7_0 >= LCURLY && LA7_0 <= LTE)||(LA7_0 >= MINUSMINUS && LA7_0 <= NEQ)||(LA7_0 >= NORETURN && LA7_0 <= NOT)||(LA7_0 >= OR && LA7_0 <= OUTPUT)||LA7_0==PARFOR||(LA7_0 >= PLUS && LA7_0 <= PP_NUMBER)||LA7_0==PROCNULL||(LA7_0 >= PURE && LA7_0 <= SCOPEOF)||(LA7_0 >= SELF && LA7_0 <= UNSIGNED)||(LA7_0 >= VOID && LA7_0 <= WHILE)||LA7_0==ROOT) ) {
				alt7=1;
			}
			else if ( (LA7_0==COMMENT||LA7_0==WS) ) {
				alt7=2;
			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 7, 0, input);
				throw nvae;
			}

			switch (alt7) {
				case 1 :
					// PreprocessorParser.g:89:12: pptoken
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_pptoken_in_wpptoken296);
					pptoken20=pptoken();
					state._fsp--;

					adaptor.addChild(root_0, pptoken20.getTree());

					}
					break;
				case 2 :
					// PreprocessorParser.g:89:22: white
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_white_in_wpptoken300);
					white21=white();
					state._fsp--;

					adaptor.addChild(root_0, white21.getTree());

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
	// $ANTLR end "wpptoken"


	public static class lineend_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "lineend"
	// PreprocessorParser.g:91:1: lineend : NEWLINE ;
	public final PreprocessorParser.lineend_return lineend() throws RecognitionException {
		PreprocessorParser.lineend_return retval = new PreprocessorParser.lineend_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token NEWLINE22=null;

		Object NEWLINE22_tree=null;

		try {
			// PreprocessorParser.g:91:10: ( NEWLINE )
			// PreprocessorParser.g:91:12: NEWLINE
			{
			root_0 = (Object)adaptor.nil();


			NEWLINE22=(Token)match(input,NEWLINE,FOLLOW_NEWLINE_in_lineend310); 
			NEWLINE22_tree = (Object)adaptor.create(NEWLINE22);
			adaptor.addChild(root_0, NEWLINE22_tree);

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
	// $ANTLR end "lineend"


	public static class macrodef_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "macrodef"
	// PreprocessorParser.g:93:1: macrodef : PDEFINE ( white )+ i= identifier ( paramlist macrobody -> ^( PDEFINE $i paramlist macrobody ) | lineend -> ^( PDEFINE $i ^( BODY ) ) | white macrobody -> ^( PDEFINE $i macrobody ) ) ;
	public final PreprocessorParser.macrodef_return macrodef() throws RecognitionException {
		PreprocessorParser.macrodef_return retval = new PreprocessorParser.macrodef_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PDEFINE23=null;
		ParserRuleReturnScope i =null;
		ParserRuleReturnScope white24 =null;
		ParserRuleReturnScope paramlist25 =null;
		ParserRuleReturnScope macrobody26 =null;
		ParserRuleReturnScope lineend27 =null;
		ParserRuleReturnScope white28 =null;
		ParserRuleReturnScope macrobody29 =null;

		Object PDEFINE23_tree=null;
		RewriteRuleTokenStream stream_PDEFINE=new RewriteRuleTokenStream(adaptor,"token PDEFINE");
		RewriteRuleSubtreeStream stream_macrobody=new RewriteRuleSubtreeStream(adaptor,"rule macrobody");
		RewriteRuleSubtreeStream stream_lineend=new RewriteRuleSubtreeStream(adaptor,"rule lineend");
		RewriteRuleSubtreeStream stream_white=new RewriteRuleSubtreeStream(adaptor,"rule white");
		RewriteRuleSubtreeStream stream_paramlist=new RewriteRuleSubtreeStream(adaptor,"rule paramlist");
		RewriteRuleSubtreeStream stream_identifier=new RewriteRuleSubtreeStream(adaptor,"rule identifier");

		try {
			// PreprocessorParser.g:93:10: ( PDEFINE ( white )+ i= identifier ( paramlist macrobody -> ^( PDEFINE $i paramlist macrobody ) | lineend -> ^( PDEFINE $i ^( BODY ) ) | white macrobody -> ^( PDEFINE $i macrobody ) ) )
			// PreprocessorParser.g:93:12: PDEFINE ( white )+ i= identifier ( paramlist macrobody -> ^( PDEFINE $i paramlist macrobody ) | lineend -> ^( PDEFINE $i ^( BODY ) ) | white macrobody -> ^( PDEFINE $i macrobody ) )
			{
			PDEFINE23=(Token)match(input,PDEFINE,FOLLOW_PDEFINE_in_macrodef319);  
			stream_PDEFINE.add(PDEFINE23);

			// PreprocessorParser.g:93:20: ( white )+
			int cnt8=0;
			loop8:
			while (true) {
				int alt8=2;
				int LA8_0 = input.LA(1);
				if ( (LA8_0==COMMENT||LA8_0==WS) ) {
					alt8=1;
				}

				switch (alt8) {
				case 1 :
					// PreprocessorParser.g:93:20: white
					{
					pushFollow(FOLLOW_white_in_macrodef321);
					white24=white();
					state._fsp--;

					stream_white.add(white24.getTree());
					}
					break;

				default :
					if ( cnt8 >= 1 ) break loop8;
					EarlyExitException eee = new EarlyExitException(8, input);
					throw eee;
				}
				cnt8++;
			}

			pushFollow(FOLLOW_identifier_in_macrodef326);
			i=identifier();
			state._fsp--;

			stream_identifier.add(i.getTree());
			// PreprocessorParser.g:94:4: ( paramlist macrobody -> ^( PDEFINE $i paramlist macrobody ) | lineend -> ^( PDEFINE $i ^( BODY ) ) | white macrobody -> ^( PDEFINE $i macrobody ) )
			int alt9=3;
			switch ( input.LA(1) ) {
			case LPAREN:
				{
				alt9=1;
				}
				break;
			case NEWLINE:
				{
				alt9=2;
				}
				break;
			case COMMENT:
			case WS:
				{
				alt9=3;
				}
				break;
			default:
				NoViableAltException nvae =
					new NoViableAltException("", 9, 0, input);
				throw nvae;
			}
			switch (alt9) {
				case 1 :
					// PreprocessorParser.g:94:6: paramlist macrobody
					{
					pushFollow(FOLLOW_paramlist_in_macrodef333);
					paramlist25=paramlist();
					state._fsp--;

					stream_paramlist.add(paramlist25.getTree());
					pushFollow(FOLLOW_macrobody_in_macrodef335);
					macrobody26=macrobody();
					state._fsp--;

					stream_macrobody.add(macrobody26.getTree());
					// AST REWRITE
					// elements: PDEFINE, paramlist, i, macrobody
					// token labels: 
					// rule labels: retval, i
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_i=new RewriteRuleSubtreeStream(adaptor,"rule i",i!=null?i.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 94:26: -> ^( PDEFINE $i paramlist macrobody )
					{
						// PreprocessorParser.g:94:29: ^( PDEFINE $i paramlist macrobody )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_PDEFINE.nextNode(), root_1);
						adaptor.addChild(root_1, stream_i.nextTree());
						adaptor.addChild(root_1, stream_paramlist.nextTree());
						adaptor.addChild(root_1, stream_macrobody.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 2 :
					// PreprocessorParser.g:95:6: lineend
					{
					pushFollow(FOLLOW_lineend_in_macrodef355);
					lineend27=lineend();
					state._fsp--;

					stream_lineend.add(lineend27.getTree());
					// AST REWRITE
					// elements: PDEFINE, i
					// token labels: 
					// rule labels: retval, i
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_i=new RewriteRuleSubtreeStream(adaptor,"rule i",i!=null?i.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 95:14: -> ^( PDEFINE $i ^( BODY ) )
					{
						// PreprocessorParser.g:95:17: ^( PDEFINE $i ^( BODY ) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_PDEFINE.nextNode(), root_1);
						adaptor.addChild(root_1, stream_i.nextTree());
						// PreprocessorParser.g:95:30: ^( BODY )
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(BODY, "BODY"), root_2);
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 3 :
					// PreprocessorParser.g:96:6: white macrobody
					{
					pushFollow(FOLLOW_white_in_macrodef375);
					white28=white();
					state._fsp--;

					stream_white.add(white28.getTree());
					pushFollow(FOLLOW_macrobody_in_macrodef377);
					macrobody29=macrobody();
					state._fsp--;

					stream_macrobody.add(macrobody29.getTree());
					// AST REWRITE
					// elements: macrobody, i, PDEFINE
					// token labels: 
					// rule labels: retval, i
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_i=new RewriteRuleSubtreeStream(adaptor,"rule i",i!=null?i.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 96:22: -> ^( PDEFINE $i macrobody )
					{
						// PreprocessorParser.g:96:25: ^( PDEFINE $i macrobody )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_PDEFINE.nextNode(), root_1);
						adaptor.addChild(root_1, stream_i.nextTree());
						adaptor.addChild(root_1, stream_macrobody.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

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
	// $ANTLR end "macrodef"


	public static class macrobody_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "macrobody"
	// PreprocessorParser.g:100:1: macrobody : ( white )* (t+= pptoken ( (t+= wpptoken )* t+= pptoken )? ( white )* lineend -> ^( BODY ( $t)+ ) | lineend -> ^( BODY ) ) ;
	public final PreprocessorParser.macrobody_return macrobody() throws RecognitionException {
		PreprocessorParser.macrobody_return retval = new PreprocessorParser.macrobody_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		List<Object> list_t=null;
		ParserRuleReturnScope white30 =null;
		ParserRuleReturnScope white31 =null;
		ParserRuleReturnScope lineend32 =null;
		ParserRuleReturnScope lineend33 =null;
		RuleReturnScope t = null;
		RewriteRuleSubtreeStream stream_pptoken=new RewriteRuleSubtreeStream(adaptor,"rule pptoken");
		RewriteRuleSubtreeStream stream_lineend=new RewriteRuleSubtreeStream(adaptor,"rule lineend");
		RewriteRuleSubtreeStream stream_white=new RewriteRuleSubtreeStream(adaptor,"rule white");
		RewriteRuleSubtreeStream stream_wpptoken=new RewriteRuleSubtreeStream(adaptor,"rule wpptoken");

		try {
			// PreprocessorParser.g:100:11: ( ( white )* (t+= pptoken ( (t+= wpptoken )* t+= pptoken )? ( white )* lineend -> ^( BODY ( $t)+ ) | lineend -> ^( BODY ) ) )
			// PreprocessorParser.g:100:13: ( white )* (t+= pptoken ( (t+= wpptoken )* t+= pptoken )? ( white )* lineend -> ^( BODY ( $t)+ ) | lineend -> ^( BODY ) )
			{
			// PreprocessorParser.g:100:13: ( white )*
			loop10:
			while (true) {
				int alt10=2;
				int LA10_0 = input.LA(1);
				if ( (LA10_0==COMMENT||LA10_0==WS) ) {
					alt10=1;
				}

				switch (alt10) {
				case 1 :
					// PreprocessorParser.g:100:13: white
					{
					pushFollow(FOLLOW_white_in_macrobody404);
					white30=white();
					state._fsp--;

					stream_white.add(white30.getTree());
					}
					break;

				default :
					break loop10;
				}
			}

			// PreprocessorParser.g:101:4: (t+= pptoken ( (t+= wpptoken )* t+= pptoken )? ( white )* lineend -> ^( BODY ( $t)+ ) | lineend -> ^( BODY ) )
			int alt14=2;
			int LA14_0 = input.LA(1);
			if ( ((LA14_0 >= ABSTRACT && LA14_0 <= BREAK)||(LA14_0 >= CALLS && LA14_0 <= CASE)||(LA14_0 >= CHAR && LA14_0 <= COMMA)||(LA14_0 >= COMPLEX && LA14_0 <= DEFAULT)||(LA14_0 >= DEPENDS && LA14_0 <= DOUBLE)||(LA14_0 >= ELLIPSIS && LA14_0 <= EXTERN)||(LA14_0 >= FALSE && LA14_0 <= FORALL)||(LA14_0 >= GENERIC && LA14_0 <= HERE)||(LA14_0 >= IDENTIFIER && LA14_0 <= INVARIANT)||(LA14_0 >= LCURLY && LA14_0 <= LTE)||(LA14_0 >= MINUSMINUS && LA14_0 <= NEQ)||(LA14_0 >= NORETURN && LA14_0 <= NOT)||(LA14_0 >= OR && LA14_0 <= OUTPUT)||LA14_0==PARFOR||(LA14_0 >= PLUS && LA14_0 <= PP_NUMBER)||LA14_0==PROCNULL||(LA14_0 >= PURE && LA14_0 <= SCOPEOF)||(LA14_0 >= SELF && LA14_0 <= UNSIGNED)||(LA14_0 >= VOID && LA14_0 <= WHILE)||LA14_0==ROOT) ) {
				alt14=1;
			}
			else if ( (LA14_0==NEWLINE) ) {
				alt14=2;
			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 14, 0, input);
				throw nvae;
			}

			switch (alt14) {
				case 1 :
					// PreprocessorParser.g:101:6: t+= pptoken ( (t+= wpptoken )* t+= pptoken )? ( white )* lineend
					{
					pushFollow(FOLLOW_pptoken_in_macrobody415);
					t=pptoken();
					state._fsp--;

					stream_pptoken.add(t.getTree());
					if (list_t==null) list_t=new ArrayList<Object>();
					list_t.add(t.getTree());
					// PreprocessorParser.g:101:17: ( (t+= wpptoken )* t+= pptoken )?
					int alt12=2;
					alt12 = dfa12.predict(input);
					switch (alt12) {
						case 1 :
							// PreprocessorParser.g:101:18: (t+= wpptoken )* t+= pptoken
							{
							// PreprocessorParser.g:101:19: (t+= wpptoken )*
							loop11:
							while (true) {
								int alt11=2;
								alt11 = dfa11.predict(input);
								switch (alt11) {
								case 1 :
									// PreprocessorParser.g:101:19: t+= wpptoken
									{
									pushFollow(FOLLOW_wpptoken_in_macrobody420);
									t=wpptoken();
									state._fsp--;

									stream_wpptoken.add(t.getTree());
									if (list_t==null) list_t=new ArrayList<Object>();
									list_t.add(t.getTree());
									}
									break;

								default :
									break loop11;
								}
							}

							pushFollow(FOLLOW_pptoken_in_macrobody425);
							t=pptoken();
							state._fsp--;

							stream_pptoken.add(t.getTree());
							if (list_t==null) list_t=new ArrayList<Object>();
							list_t.add(t.getTree());
							}
							break;

					}

					// PreprocessorParser.g:101:44: ( white )*
					loop13:
					while (true) {
						int alt13=2;
						int LA13_0 = input.LA(1);
						if ( (LA13_0==COMMENT||LA13_0==WS) ) {
							alt13=1;
						}

						switch (alt13) {
						case 1 :
							// PreprocessorParser.g:101:44: white
							{
							pushFollow(FOLLOW_white_in_macrobody429);
							white31=white();
							state._fsp--;

							stream_white.add(white31.getTree());
							}
							break;

						default :
							break loop13;
						}
					}

					pushFollow(FOLLOW_lineend_in_macrobody432);
					lineend32=lineend();
					state._fsp--;

					stream_lineend.add(lineend32.getTree());
					// AST REWRITE
					// elements: t
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: t
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_t=new RewriteRuleSubtreeStream(adaptor,"token t",list_t);
					root_0 = (Object)adaptor.nil();
					// 102:6: -> ^( BODY ( $t)+ )
					{
						// PreprocessorParser.g:102:9: ^( BODY ( $t)+ )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(BODY, "BODY"), root_1);
						if ( !(stream_t.hasNext()) ) {
							throw new RewriteEarlyExitException();
						}
						while ( stream_t.hasNext() ) {
							adaptor.addChild(root_1, stream_t.nextTree());
						}
						stream_t.reset();

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 2 :
					// PreprocessorParser.g:103:6: lineend
					{
					pushFollow(FOLLOW_lineend_in_macrobody454);
					lineend33=lineend();
					state._fsp--;

					stream_lineend.add(lineend33.getTree());
					// AST REWRITE
					// elements: 
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 104:6: -> ^( BODY )
					{
						// PreprocessorParser.g:104:9: ^( BODY )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(BODY, "BODY"), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

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
	// $ANTLR end "macrobody"


	public static class paramlist_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "paramlist"
	// PreprocessorParser.g:108:1: paramlist : LPAREN ( white )* ( RPAREN -> ^( PARAMLIST ) | identifier ( ( white )* COMMA ( white )* identifier )* ( white )* RPAREN -> ^( PARAMLIST ( identifier )+ ) ) ;
	public final PreprocessorParser.paramlist_return paramlist() throws RecognitionException {
		PreprocessorParser.paramlist_return retval = new PreprocessorParser.paramlist_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LPAREN34=null;
		Token RPAREN36=null;
		Token COMMA39=null;
		Token RPAREN43=null;
		ParserRuleReturnScope white35 =null;
		ParserRuleReturnScope identifier37 =null;
		ParserRuleReturnScope white38 =null;
		ParserRuleReturnScope white40 =null;
		ParserRuleReturnScope identifier41 =null;
		ParserRuleReturnScope white42 =null;

		Object LPAREN34_tree=null;
		Object RPAREN36_tree=null;
		Object COMMA39_tree=null;
		Object RPAREN43_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_white=new RewriteRuleSubtreeStream(adaptor,"rule white");
		RewriteRuleSubtreeStream stream_identifier=new RewriteRuleSubtreeStream(adaptor,"rule identifier");

		try {
			// PreprocessorParser.g:108:11: ( LPAREN ( white )* ( RPAREN -> ^( PARAMLIST ) | identifier ( ( white )* COMMA ( white )* identifier )* ( white )* RPAREN -> ^( PARAMLIST ( identifier )+ ) ) )
			// PreprocessorParser.g:108:13: LPAREN ( white )* ( RPAREN -> ^( PARAMLIST ) | identifier ( ( white )* COMMA ( white )* identifier )* ( white )* RPAREN -> ^( PARAMLIST ( identifier )+ ) )
			{
			LPAREN34=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_paramlist481);  
			stream_LPAREN.add(LPAREN34);

			// PreprocessorParser.g:108:20: ( white )*
			loop15:
			while (true) {
				int alt15=2;
				int LA15_0 = input.LA(1);
				if ( (LA15_0==COMMENT||LA15_0==WS) ) {
					alt15=1;
				}

				switch (alt15) {
				case 1 :
					// PreprocessorParser.g:108:20: white
					{
					pushFollow(FOLLOW_white_in_paramlist483);
					white35=white();
					state._fsp--;

					stream_white.add(white35.getTree());
					}
					break;

				default :
					break loop15;
				}
			}

			// PreprocessorParser.g:109:4: ( RPAREN -> ^( PARAMLIST ) | identifier ( ( white )* COMMA ( white )* identifier )* ( white )* RPAREN -> ^( PARAMLIST ( identifier )+ ) )
			int alt20=2;
			int LA20_0 = input.LA(1);
			if ( (LA20_0==RPAREN) ) {
				alt20=1;
			}
			else if ( ((LA20_0 >= ABSTRACT && LA20_0 <= ALIGNOF)||LA20_0==ASSIGNS||(LA20_0 >= ATOMIC && LA20_0 <= BIG_O)||(LA20_0 >= BOOL && LA20_0 <= BREAK)||(LA20_0 >= CALLS && LA20_0 <= CASE)||LA20_0==CHAR||(LA20_0 >= CHOOSE && LA20_0 <= COLLECTIVE)||(LA20_0 >= COMPLEX && LA20_0 <= DEFAULT)||(LA20_0 >= DEPENDS && LA20_0 <= DEVICE)||(LA20_0 >= DO && LA20_0 <= DOMAIN)||LA20_0==DOUBLE||(LA20_0 >= ELSE && LA20_0 <= ENUM)||(LA20_0 >= EXISTS && LA20_0 <= EXTERN)||(LA20_0 >= FALSE && LA20_0 <= FLOAT)||(LA20_0 >= FOR && LA20_0 <= FORALL)||(LA20_0 >= GENERIC && LA20_0 <= GOTO)||LA20_0==GUARD||LA20_0==HERE||(LA20_0 >= IDENTIFIER && LA20_0 <= IMAGINARY)||(LA20_0 >= INLINE && LA20_0 <= INT)||LA20_0==INVARIANT||LA20_0==LONG||LA20_0==NORETURN||LA20_0==OUTPUT||LA20_0==PARFOR||LA20_0==PROCNULL||LA20_0==PURE||LA20_0==RANGE||(LA20_0 >= READS && LA20_0 <= RETURN)||LA20_0==SCOPEOF||LA20_0==SELF||LA20_0==SHARED||(LA20_0 >= SHORT && LA20_0 <= SPAWN)||(LA20_0 >= STATIC && LA20_0 <= STATICASSERT)||LA20_0==STRUCT||(LA20_0 >= SWITCH && LA20_0 <= THREADLOCAL)||(LA20_0 >= TRUE && LA20_0 <= UNSIGNED)||(LA20_0 >= VOID && LA20_0 <= WHILE)||LA20_0==ROOT) ) {
				alt20=2;
			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 20, 0, input);
				throw nvae;
			}

			switch (alt20) {
				case 1 :
					// PreprocessorParser.g:109:6: RPAREN
					{
					RPAREN36=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_paramlist492);  
					stream_RPAREN.add(RPAREN36);

					// AST REWRITE
					// elements: 
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 109:13: -> ^( PARAMLIST )
					{
						// PreprocessorParser.g:109:16: ^( PARAMLIST )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(PARAMLIST, "PARAMLIST"), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 2 :
					// PreprocessorParser.g:110:6: identifier ( ( white )* COMMA ( white )* identifier )* ( white )* RPAREN
					{
					pushFollow(FOLLOW_identifier_in_paramlist505);
					identifier37=identifier();
					state._fsp--;

					stream_identifier.add(identifier37.getTree());
					// PreprocessorParser.g:110:17: ( ( white )* COMMA ( white )* identifier )*
					loop18:
					while (true) {
						int alt18=2;
						alt18 = dfa18.predict(input);
						switch (alt18) {
						case 1 :
							// PreprocessorParser.g:110:18: ( white )* COMMA ( white )* identifier
							{
							// PreprocessorParser.g:110:18: ( white )*
							loop16:
							while (true) {
								int alt16=2;
								int LA16_0 = input.LA(1);
								if ( (LA16_0==COMMENT||LA16_0==WS) ) {
									alt16=1;
								}

								switch (alt16) {
								case 1 :
									// PreprocessorParser.g:110:18: white
									{
									pushFollow(FOLLOW_white_in_paramlist508);
									white38=white();
									state._fsp--;

									stream_white.add(white38.getTree());
									}
									break;

								default :
									break loop16;
								}
							}

							COMMA39=(Token)match(input,COMMA,FOLLOW_COMMA_in_paramlist511);  
							stream_COMMA.add(COMMA39);

							// PreprocessorParser.g:110:31: ( white )*
							loop17:
							while (true) {
								int alt17=2;
								int LA17_0 = input.LA(1);
								if ( (LA17_0==COMMENT||LA17_0==WS) ) {
									alt17=1;
								}

								switch (alt17) {
								case 1 :
									// PreprocessorParser.g:110:31: white
									{
									pushFollow(FOLLOW_white_in_paramlist513);
									white40=white();
									state._fsp--;

									stream_white.add(white40.getTree());
									}
									break;

								default :
									break loop17;
								}
							}

							pushFollow(FOLLOW_identifier_in_paramlist516);
							identifier41=identifier();
							state._fsp--;

							stream_identifier.add(identifier41.getTree());
							}
							break;

						default :
							break loop18;
						}
					}

					// PreprocessorParser.g:110:51: ( white )*
					loop19:
					while (true) {
						int alt19=2;
						int LA19_0 = input.LA(1);
						if ( (LA19_0==COMMENT||LA19_0==WS) ) {
							alt19=1;
						}

						switch (alt19) {
						case 1 :
							// PreprocessorParser.g:110:51: white
							{
							pushFollow(FOLLOW_white_in_paramlist520);
							white42=white();
							state._fsp--;

							stream_white.add(white42.getTree());
							}
							break;

						default :
							break loop19;
						}
					}

					RPAREN43=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_paramlist523);  
					stream_RPAREN.add(RPAREN43);

					// AST REWRITE
					// elements: identifier
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 111:6: -> ^( PARAMLIST ( identifier )+ )
					{
						// PreprocessorParser.g:111:9: ^( PARAMLIST ( identifier )+ )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(PARAMLIST, "PARAMLIST"), root_1);
						if ( !(stream_identifier.hasNext()) ) {
							throw new RewriteEarlyExitException();
						}
						while ( stream_identifier.hasNext() ) {
							adaptor.addChild(root_1, stream_identifier.nextTree());
						}
						stream_identifier.reset();

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

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
	// $ANTLR end "paramlist"


	public static class macroundef_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "macroundef"
	// PreprocessorParser.g:115:1: macroundef : PUNDEF ( white )+ identifier ( white )* lineend -> ^( PUNDEF identifier ) ;
	public final PreprocessorParser.macroundef_return macroundef() throws RecognitionException {
		PreprocessorParser.macroundef_return retval = new PreprocessorParser.macroundef_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PUNDEF44=null;
		ParserRuleReturnScope white45 =null;
		ParserRuleReturnScope identifier46 =null;
		ParserRuleReturnScope white47 =null;
		ParserRuleReturnScope lineend48 =null;

		Object PUNDEF44_tree=null;
		RewriteRuleTokenStream stream_PUNDEF=new RewriteRuleTokenStream(adaptor,"token PUNDEF");
		RewriteRuleSubtreeStream stream_lineend=new RewriteRuleSubtreeStream(adaptor,"rule lineend");
		RewriteRuleSubtreeStream stream_white=new RewriteRuleSubtreeStream(adaptor,"rule white");
		RewriteRuleSubtreeStream stream_identifier=new RewriteRuleSubtreeStream(adaptor,"rule identifier");

		try {
			// PreprocessorParser.g:115:12: ( PUNDEF ( white )+ identifier ( white )* lineend -> ^( PUNDEF identifier ) )
			// PreprocessorParser.g:115:14: PUNDEF ( white )+ identifier ( white )* lineend
			{
			PUNDEF44=(Token)match(input,PUNDEF,FOLLOW_PUNDEF_in_macroundef553);  
			stream_PUNDEF.add(PUNDEF44);

			// PreprocessorParser.g:115:21: ( white )+
			int cnt21=0;
			loop21:
			while (true) {
				int alt21=2;
				int LA21_0 = input.LA(1);
				if ( (LA21_0==COMMENT||LA21_0==WS) ) {
					alt21=1;
				}

				switch (alt21) {
				case 1 :
					// PreprocessorParser.g:115:21: white
					{
					pushFollow(FOLLOW_white_in_macroundef555);
					white45=white();
					state._fsp--;

					stream_white.add(white45.getTree());
					}
					break;

				default :
					if ( cnt21 >= 1 ) break loop21;
					EarlyExitException eee = new EarlyExitException(21, input);
					throw eee;
				}
				cnt21++;
			}

			pushFollow(FOLLOW_identifier_in_macroundef558);
			identifier46=identifier();
			state._fsp--;

			stream_identifier.add(identifier46.getTree());
			// PreprocessorParser.g:115:39: ( white )*
			loop22:
			while (true) {
				int alt22=2;
				int LA22_0 = input.LA(1);
				if ( (LA22_0==COMMENT||LA22_0==WS) ) {
					alt22=1;
				}

				switch (alt22) {
				case 1 :
					// PreprocessorParser.g:115:39: white
					{
					pushFollow(FOLLOW_white_in_macroundef560);
					white47=white();
					state._fsp--;

					stream_white.add(white47.getTree());
					}
					break;

				default :
					break loop22;
				}
			}

			pushFollow(FOLLOW_lineend_in_macroundef563);
			lineend48=lineend();
			state._fsp--;

			stream_lineend.add(lineend48.getTree());
			// AST REWRITE
			// elements: identifier, PUNDEF
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 116:4: -> ^( PUNDEF identifier )
			{
				// PreprocessorParser.g:116:7: ^( PUNDEF identifier )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_PUNDEF.nextNode(), root_1);
				adaptor.addChild(root_1, stream_identifier.nextTree());
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
	// $ANTLR end "macroundef"


	public static class includeline_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "includeline"
	// PreprocessorParser.g:119:1: includeline : PINCLUDE ( white )* HEADER_NAME ( white )* lineend -> ^( PINCLUDE HEADER_NAME ) ;
	public final PreprocessorParser.includeline_return includeline() throws RecognitionException {
		PreprocessorParser.includeline_return retval = new PreprocessorParser.includeline_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PINCLUDE49=null;
		Token HEADER_NAME51=null;
		ParserRuleReturnScope white50 =null;
		ParserRuleReturnScope white52 =null;
		ParserRuleReturnScope lineend53 =null;

		Object PINCLUDE49_tree=null;
		Object HEADER_NAME51_tree=null;
		RewriteRuleTokenStream stream_HEADER_NAME=new RewriteRuleTokenStream(adaptor,"token HEADER_NAME");
		RewriteRuleTokenStream stream_PINCLUDE=new RewriteRuleTokenStream(adaptor,"token PINCLUDE");
		RewriteRuleSubtreeStream stream_lineend=new RewriteRuleSubtreeStream(adaptor,"rule lineend");
		RewriteRuleSubtreeStream stream_white=new RewriteRuleSubtreeStream(adaptor,"rule white");

		try {
			// PreprocessorParser.g:119:13: ( PINCLUDE ( white )* HEADER_NAME ( white )* lineend -> ^( PINCLUDE HEADER_NAME ) )
			// PreprocessorParser.g:119:15: PINCLUDE ( white )* HEADER_NAME ( white )* lineend
			{
			PINCLUDE49=(Token)match(input,PINCLUDE,FOLLOW_PINCLUDE_in_includeline585);  
			stream_PINCLUDE.add(PINCLUDE49);

			// PreprocessorParser.g:119:24: ( white )*
			loop23:
			while (true) {
				int alt23=2;
				int LA23_0 = input.LA(1);
				if ( (LA23_0==COMMENT||LA23_0==WS) ) {
					alt23=1;
				}

				switch (alt23) {
				case 1 :
					// PreprocessorParser.g:119:24: white
					{
					pushFollow(FOLLOW_white_in_includeline587);
					white50=white();
					state._fsp--;

					stream_white.add(white50.getTree());
					}
					break;

				default :
					break loop23;
				}
			}

			HEADER_NAME51=(Token)match(input,HEADER_NAME,FOLLOW_HEADER_NAME_in_includeline590);  
			stream_HEADER_NAME.add(HEADER_NAME51);

			// PreprocessorParser.g:119:43: ( white )*
			loop24:
			while (true) {
				int alt24=2;
				int LA24_0 = input.LA(1);
				if ( (LA24_0==COMMENT||LA24_0==WS) ) {
					alt24=1;
				}

				switch (alt24) {
				case 1 :
					// PreprocessorParser.g:119:43: white
					{
					pushFollow(FOLLOW_white_in_includeline592);
					white52=white();
					state._fsp--;

					stream_white.add(white52.getTree());
					}
					break;

				default :
					break loop24;
				}
			}

			pushFollow(FOLLOW_lineend_in_includeline595);
			lineend53=lineend();
			state._fsp--;

			stream_lineend.add(lineend53.getTree());
			// AST REWRITE
			// elements: PINCLUDE, HEADER_NAME
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 120:4: -> ^( PINCLUDE HEADER_NAME )
			{
				// PreprocessorParser.g:120:7: ^( PINCLUDE HEADER_NAME )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_PINCLUDE.nextNode(), root_1);
				adaptor.addChild(root_1, stream_HEADER_NAME.nextNode());
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
	// $ANTLR end "includeline"


	public static class ifblock_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "ifblock"
	// PreprocessorParser.g:123:1: ifblock : PIF ( white )* expr lineend block ( elseblock )? endifline -> ^( PIF expr ^( SEQUENCE ( block )? ) ( elseblock )? ) ;
	public final PreprocessorParser.ifblock_return ifblock() throws RecognitionException {
		PreprocessorParser.ifblock_return retval = new PreprocessorParser.ifblock_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PIF54=null;
		ParserRuleReturnScope white55 =null;
		ParserRuleReturnScope expr56 =null;
		ParserRuleReturnScope lineend57 =null;
		ParserRuleReturnScope block58 =null;
		ParserRuleReturnScope elseblock59 =null;
		ParserRuleReturnScope endifline60 =null;

		Object PIF54_tree=null;
		RewriteRuleTokenStream stream_PIF=new RewriteRuleTokenStream(adaptor,"token PIF");
		RewriteRuleSubtreeStream stream_lineend=new RewriteRuleSubtreeStream(adaptor,"rule lineend");
		RewriteRuleSubtreeStream stream_endifline=new RewriteRuleSubtreeStream(adaptor,"rule endifline");
		RewriteRuleSubtreeStream stream_white=new RewriteRuleSubtreeStream(adaptor,"rule white");
		RewriteRuleSubtreeStream stream_block=new RewriteRuleSubtreeStream(adaptor,"rule block");
		RewriteRuleSubtreeStream stream_expr=new RewriteRuleSubtreeStream(adaptor,"rule expr");
		RewriteRuleSubtreeStream stream_elseblock=new RewriteRuleSubtreeStream(adaptor,"rule elseblock");

		try {
			// PreprocessorParser.g:123:10: ( PIF ( white )* expr lineend block ( elseblock )? endifline -> ^( PIF expr ^( SEQUENCE ( block )? ) ( elseblock )? ) )
			// PreprocessorParser.g:123:13: PIF ( white )* expr lineend block ( elseblock )? endifline
			{
			PIF54=(Token)match(input,PIF,FOLLOW_PIF_in_ifblock619);  
			stream_PIF.add(PIF54);

			// PreprocessorParser.g:123:17: ( white )*
			loop25:
			while (true) {
				int alt25=2;
				int LA25_0 = input.LA(1);
				if ( (LA25_0==COMMENT||LA25_0==WS) ) {
					alt25=1;
				}

				switch (alt25) {
				case 1 :
					// PreprocessorParser.g:123:17: white
					{
					pushFollow(FOLLOW_white_in_ifblock621);
					white55=white();
					state._fsp--;

					stream_white.add(white55.getTree());
					}
					break;

				default :
					break loop25;
				}
			}

			pushFollow(FOLLOW_expr_in_ifblock624);
			expr56=expr();
			state._fsp--;

			stream_expr.add(expr56.getTree());
			pushFollow(FOLLOW_lineend_in_ifblock626);
			lineend57=lineend();
			state._fsp--;

			stream_lineend.add(lineend57.getTree());
			pushFollow(FOLLOW_block_in_ifblock628);
			block58=block();
			state._fsp--;

			stream_block.add(block58.getTree());
			// PreprocessorParser.g:123:43: ( elseblock )?
			int alt26=2;
			int LA26_0 = input.LA(1);
			if ( ((LA26_0 >= PELIF && LA26_0 <= PELSE)) ) {
				alt26=1;
			}
			switch (alt26) {
				case 1 :
					// PreprocessorParser.g:123:43: elseblock
					{
					pushFollow(FOLLOW_elseblock_in_ifblock630);
					elseblock59=elseblock();
					state._fsp--;

					stream_elseblock.add(elseblock59.getTree());
					}
					break;

			}

			pushFollow(FOLLOW_endifline_in_ifblock633);
			endifline60=endifline();
			state._fsp--;

			stream_endifline.add(endifline60.getTree());
			// AST REWRITE
			// elements: PIF, elseblock, block, expr
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 124:4: -> ^( PIF expr ^( SEQUENCE ( block )? ) ( elseblock )? )
			{
				// PreprocessorParser.g:124:7: ^( PIF expr ^( SEQUENCE ( block )? ) ( elseblock )? )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_PIF.nextNode(), root_1);
				adaptor.addChild(root_1, stream_expr.nextTree());
				// PreprocessorParser.g:124:18: ^( SEQUENCE ( block )? )
				{
				Object root_2 = (Object)adaptor.nil();
				root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(SEQUENCE, "SEQUENCE"), root_2);
				// PreprocessorParser.g:124:29: ( block )?
				if ( stream_block.hasNext() ) {
					adaptor.addChild(root_2, stream_block.nextTree());
				}
				stream_block.reset();

				adaptor.addChild(root_1, root_2);
				}

				// PreprocessorParser.g:124:37: ( elseblock )?
				if ( stream_elseblock.hasNext() ) {
					adaptor.addChild(root_1, stream_elseblock.nextTree());
				}
				stream_elseblock.reset();

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
	// $ANTLR end "ifblock"


	public static class expr_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "expr"
	// PreprocessorParser.g:127:1: expr : ppdExpr ( ppdExpr | white )* -> ^( EXPR ( ppdExpr )+ ) ;
	public final PreprocessorParser.expr_return expr() throws RecognitionException {
		PreprocessorParser.expr_return retval = new PreprocessorParser.expr_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope ppdExpr61 =null;
		ParserRuleReturnScope ppdExpr62 =null;
		ParserRuleReturnScope white63 =null;

		RewriteRuleSubtreeStream stream_ppdExpr=new RewriteRuleSubtreeStream(adaptor,"rule ppdExpr");
		RewriteRuleSubtreeStream stream_white=new RewriteRuleSubtreeStream(adaptor,"rule white");

		try {
			// PreprocessorParser.g:127:7: ( ppdExpr ( ppdExpr | white )* -> ^( EXPR ( ppdExpr )+ ) )
			// PreprocessorParser.g:127:9: ppdExpr ( ppdExpr | white )*
			{
			pushFollow(FOLLOW_ppdExpr_in_expr668);
			ppdExpr61=ppdExpr();
			state._fsp--;

			stream_ppdExpr.add(ppdExpr61.getTree());
			// PreprocessorParser.g:127:17: ( ppdExpr | white )*
			loop27:
			while (true) {
				int alt27=3;
				int LA27_0 = input.LA(1);
				if ( ((LA27_0 >= ABSTRACT && LA27_0 <= BREAK)||(LA27_0 >= CALLS && LA27_0 <= CASE)||(LA27_0 >= CHAR && LA27_0 <= COMMA)||(LA27_0 >= COMPLEX && LA27_0 <= DOUBLE)||(LA27_0 >= ELLIPSIS && LA27_0 <= EXTERN)||(LA27_0 >= FALSE && LA27_0 <= FORALL)||(LA27_0 >= GENERIC && LA27_0 <= HERE)||(LA27_0 >= IDENTIFIER && LA27_0 <= INVARIANT)||(LA27_0 >= LCURLY && LA27_0 <= LTE)||(LA27_0 >= MINUSMINUS && LA27_0 <= NEQ)||(LA27_0 >= NORETURN && LA27_0 <= NOT)||(LA27_0 >= OR && LA27_0 <= OUTPUT)||LA27_0==PARFOR||(LA27_0 >= PLUS && LA27_0 <= PP_NUMBER)||LA27_0==PROCNULL||(LA27_0 >= PURE && LA27_0 <= SCOPEOF)||(LA27_0 >= SELF && LA27_0 <= UNSIGNED)||(LA27_0 >= VOID && LA27_0 <= WHILE)||LA27_0==ROOT) ) {
					alt27=1;
				}
				else if ( (LA27_0==COMMENT||LA27_0==WS) ) {
					alt27=2;
				}

				switch (alt27) {
				case 1 :
					// PreprocessorParser.g:127:18: ppdExpr
					{
					pushFollow(FOLLOW_ppdExpr_in_expr671);
					ppdExpr62=ppdExpr();
					state._fsp--;

					stream_ppdExpr.add(ppdExpr62.getTree());
					}
					break;
				case 2 :
					// PreprocessorParser.g:127:28: white
					{
					pushFollow(FOLLOW_white_in_expr675);
					white63=white();
					state._fsp--;

					stream_white.add(white63.getTree());
					}
					break;

				default :
					break loop27;
				}
			}

			// AST REWRITE
			// elements: ppdExpr
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 127:36: -> ^( EXPR ( ppdExpr )+ )
			{
				// PreprocessorParser.g:127:39: ^( EXPR ( ppdExpr )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(EXPR, "EXPR"), root_1);
				if ( !(stream_ppdExpr.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_ppdExpr.hasNext() ) {
					adaptor.addChild(root_1, stream_ppdExpr.nextTree());
				}
				stream_ppdExpr.reset();

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
	// $ANTLR end "expr"


	public static class definedExpr_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "definedExpr"
	// PreprocessorParser.g:129:1: definedExpr : DEFINED ( WS !)* ( identifier | LPAREN ! ( WS !)* identifier ( WS !)* RPAREN !) ;
	public final PreprocessorParser.definedExpr_return definedExpr() throws RecognitionException {
		PreprocessorParser.definedExpr_return retval = new PreprocessorParser.definedExpr_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token DEFINED64=null;
		Token WS65=null;
		Token LPAREN67=null;
		Token WS68=null;
		Token WS70=null;
		Token RPAREN71=null;
		ParserRuleReturnScope identifier66 =null;
		ParserRuleReturnScope identifier69 =null;

		Object DEFINED64_tree=null;
		Object WS65_tree=null;
		Object LPAREN67_tree=null;
		Object WS68_tree=null;
		Object WS70_tree=null;
		Object RPAREN71_tree=null;

		try {
			// PreprocessorParser.g:129:13: ( DEFINED ( WS !)* ( identifier | LPAREN ! ( WS !)* identifier ( WS !)* RPAREN !) )
			// PreprocessorParser.g:129:15: DEFINED ( WS !)* ( identifier | LPAREN ! ( WS !)* identifier ( WS !)* RPAREN !)
			{
			root_0 = (Object)adaptor.nil();


			DEFINED64=(Token)match(input,DEFINED,FOLLOW_DEFINED_in_definedExpr695); 
			DEFINED64_tree = (Object)adaptor.create(DEFINED64);
			adaptor.addChild(root_0, DEFINED64_tree);

			// PreprocessorParser.g:129:25: ( WS !)*
			loop28:
			while (true) {
				int alt28=2;
				int LA28_0 = input.LA(1);
				if ( (LA28_0==WS) ) {
					alt28=1;
				}

				switch (alt28) {
				case 1 :
					// PreprocessorParser.g:129:25: WS !
					{
					WS65=(Token)match(input,WS,FOLLOW_WS_in_definedExpr697); 
					}
					break;

				default :
					break loop28;
				}
			}

			// PreprocessorParser.g:130:4: ( identifier | LPAREN ! ( WS !)* identifier ( WS !)* RPAREN !)
			int alt31=2;
			int LA31_0 = input.LA(1);
			if ( ((LA31_0 >= ABSTRACT && LA31_0 <= ALIGNOF)||LA31_0==ASSIGNS||(LA31_0 >= ATOMIC && LA31_0 <= BIG_O)||(LA31_0 >= BOOL && LA31_0 <= BREAK)||(LA31_0 >= CALLS && LA31_0 <= CASE)||LA31_0==CHAR||(LA31_0 >= CHOOSE && LA31_0 <= COLLECTIVE)||(LA31_0 >= COMPLEX && LA31_0 <= DEFAULT)||(LA31_0 >= DEPENDS && LA31_0 <= DEVICE)||(LA31_0 >= DO && LA31_0 <= DOMAIN)||LA31_0==DOUBLE||(LA31_0 >= ELSE && LA31_0 <= ENUM)||(LA31_0 >= EXISTS && LA31_0 <= EXTERN)||(LA31_0 >= FALSE && LA31_0 <= FLOAT)||(LA31_0 >= FOR && LA31_0 <= FORALL)||(LA31_0 >= GENERIC && LA31_0 <= GOTO)||LA31_0==GUARD||LA31_0==HERE||(LA31_0 >= IDENTIFIER && LA31_0 <= IMAGINARY)||(LA31_0 >= INLINE && LA31_0 <= INT)||LA31_0==INVARIANT||LA31_0==LONG||LA31_0==NORETURN||LA31_0==OUTPUT||LA31_0==PARFOR||LA31_0==PROCNULL||LA31_0==PURE||LA31_0==RANGE||(LA31_0 >= READS && LA31_0 <= RETURN)||LA31_0==SCOPEOF||LA31_0==SELF||LA31_0==SHARED||(LA31_0 >= SHORT && LA31_0 <= SPAWN)||(LA31_0 >= STATIC && LA31_0 <= STATICASSERT)||LA31_0==STRUCT||(LA31_0 >= SWITCH && LA31_0 <= THREADLOCAL)||(LA31_0 >= TRUE && LA31_0 <= UNSIGNED)||(LA31_0 >= VOID && LA31_0 <= WHILE)||LA31_0==ROOT) ) {
				alt31=1;
			}
			else if ( (LA31_0==LPAREN) ) {
				alt31=2;
			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 31, 0, input);
				throw nvae;
			}

			switch (alt31) {
				case 1 :
					// PreprocessorParser.g:130:6: identifier
					{
					pushFollow(FOLLOW_identifier_in_definedExpr706);
					identifier66=identifier();
					state._fsp--;

					adaptor.addChild(root_0, identifier66.getTree());

					}
					break;
				case 2 :
					// PreprocessorParser.g:131:6: LPAREN ! ( WS !)* identifier ( WS !)* RPAREN !
					{
					LPAREN67=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_definedExpr713); 
					// PreprocessorParser.g:131:16: ( WS !)*
					loop29:
					while (true) {
						int alt29=2;
						int LA29_0 = input.LA(1);
						if ( (LA29_0==WS) ) {
							alt29=1;
						}

						switch (alt29) {
						case 1 :
							// PreprocessorParser.g:131:16: WS !
							{
							WS68=(Token)match(input,WS,FOLLOW_WS_in_definedExpr716); 
							}
							break;

						default :
							break loop29;
						}
					}

					pushFollow(FOLLOW_identifier_in_definedExpr720);
					identifier69=identifier();
					state._fsp--;

					adaptor.addChild(root_0, identifier69.getTree());

					// PreprocessorParser.g:131:32: ( WS !)*
					loop30:
					while (true) {
						int alt30=2;
						int LA30_0 = input.LA(1);
						if ( (LA30_0==WS) ) {
							alt30=1;
						}

						switch (alt30) {
						case 1 :
							// PreprocessorParser.g:131:32: WS !
							{
							WS70=(Token)match(input,WS,FOLLOW_WS_in_definedExpr722); 
							}
							break;

						default :
							break loop30;
						}
					}

					RPAREN71=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_definedExpr726); 
					}
					break;

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
	// $ANTLR end "definedExpr"


	public static class ppdExpr_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "ppdExpr"
	// PreprocessorParser.g:135:1: ppdExpr : ( pptoken | definedExpr );
	public final PreprocessorParser.ppdExpr_return ppdExpr() throws RecognitionException {
		PreprocessorParser.ppdExpr_return retval = new PreprocessorParser.ppdExpr_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope pptoken72 =null;
		ParserRuleReturnScope definedExpr73 =null;


		try {
			// PreprocessorParser.g:135:10: ( pptoken | definedExpr )
			int alt32=2;
			int LA32_0 = input.LA(1);
			if ( ((LA32_0 >= ABSTRACT && LA32_0 <= BREAK)||(LA32_0 >= CALLS && LA32_0 <= CASE)||(LA32_0 >= CHAR && LA32_0 <= COMMA)||(LA32_0 >= COMPLEX && LA32_0 <= DEFAULT)||(LA32_0 >= DEPENDS && LA32_0 <= DOUBLE)||(LA32_0 >= ELLIPSIS && LA32_0 <= EXTERN)||(LA32_0 >= FALSE && LA32_0 <= FORALL)||(LA32_0 >= GENERIC && LA32_0 <= HERE)||(LA32_0 >= IDENTIFIER && LA32_0 <= INVARIANT)||(LA32_0 >= LCURLY && LA32_0 <= LTE)||(LA32_0 >= MINUSMINUS && LA32_0 <= NEQ)||(LA32_0 >= NORETURN && LA32_0 <= NOT)||(LA32_0 >= OR && LA32_0 <= OUTPUT)||LA32_0==PARFOR||(LA32_0 >= PLUS && LA32_0 <= PP_NUMBER)||LA32_0==PROCNULL||(LA32_0 >= PURE && LA32_0 <= SCOPEOF)||(LA32_0 >= SELF && LA32_0 <= UNSIGNED)||(LA32_0 >= VOID && LA32_0 <= WHILE)||LA32_0==ROOT) ) {
				alt32=1;
			}
			else if ( (LA32_0==DEFINED) ) {
				alt32=2;
			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 32, 0, input);
				throw nvae;
			}

			switch (alt32) {
				case 1 :
					// PreprocessorParser.g:135:12: pptoken
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_pptoken_in_ppdExpr747);
					pptoken72=pptoken();
					state._fsp--;

					adaptor.addChild(root_0, pptoken72.getTree());

					}
					break;
				case 2 :
					// PreprocessorParser.g:135:22: definedExpr
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_definedExpr_in_ppdExpr751);
					definedExpr73=definedExpr();
					state._fsp--;

					adaptor.addChild(root_0, definedExpr73.getTree());

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
	// $ANTLR end "ppdExpr"


	public static class elseblock_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "elseblock"
	// PreprocessorParser.g:137:1: elseblock : ( simpleelseblock | elifblock );
	public final PreprocessorParser.elseblock_return elseblock() throws RecognitionException {
		PreprocessorParser.elseblock_return retval = new PreprocessorParser.elseblock_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope simpleelseblock74 =null;
		ParserRuleReturnScope elifblock75 =null;


		try {
			// PreprocessorParser.g:137:11: ( simpleelseblock | elifblock )
			int alt33=2;
			int LA33_0 = input.LA(1);
			if ( (LA33_0==PELSE) ) {
				alt33=1;
			}
			else if ( (LA33_0==PELIF) ) {
				alt33=2;
			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 33, 0, input);
				throw nvae;
			}

			switch (alt33) {
				case 1 :
					// PreprocessorParser.g:137:13: simpleelseblock
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_simpleelseblock_in_elseblock760);
					simpleelseblock74=simpleelseblock();
					state._fsp--;

					adaptor.addChild(root_0, simpleelseblock74.getTree());

					}
					break;
				case 2 :
					// PreprocessorParser.g:137:31: elifblock
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_elifblock_in_elseblock764);
					elifblock75=elifblock();
					state._fsp--;

					adaptor.addChild(root_0, elifblock75.getTree());

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
	// $ANTLR end "elseblock"


	public static class simpleelseblock_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "simpleelseblock"
	// PreprocessorParser.g:139:1: simpleelseblock : PELSE ( white )* lineend block -> ^( PELSE ( block )? ) ;
	public final PreprocessorParser.simpleelseblock_return simpleelseblock() throws RecognitionException {
		PreprocessorParser.simpleelseblock_return retval = new PreprocessorParser.simpleelseblock_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PELSE76=null;
		ParserRuleReturnScope white77 =null;
		ParserRuleReturnScope lineend78 =null;
		ParserRuleReturnScope block79 =null;

		Object PELSE76_tree=null;
		RewriteRuleTokenStream stream_PELSE=new RewriteRuleTokenStream(adaptor,"token PELSE");
		RewriteRuleSubtreeStream stream_lineend=new RewriteRuleSubtreeStream(adaptor,"rule lineend");
		RewriteRuleSubtreeStream stream_white=new RewriteRuleSubtreeStream(adaptor,"rule white");
		RewriteRuleSubtreeStream stream_block=new RewriteRuleSubtreeStream(adaptor,"rule block");

		try {
			// PreprocessorParser.g:139:17: ( PELSE ( white )* lineend block -> ^( PELSE ( block )? ) )
			// PreprocessorParser.g:139:19: PELSE ( white )* lineend block
			{
			PELSE76=(Token)match(input,PELSE,FOLLOW_PELSE_in_simpleelseblock773);  
			stream_PELSE.add(PELSE76);

			// PreprocessorParser.g:139:25: ( white )*
			loop34:
			while (true) {
				int alt34=2;
				int LA34_0 = input.LA(1);
				if ( (LA34_0==COMMENT||LA34_0==WS) ) {
					alt34=1;
				}

				switch (alt34) {
				case 1 :
					// PreprocessorParser.g:139:25: white
					{
					pushFollow(FOLLOW_white_in_simpleelseblock775);
					white77=white();
					state._fsp--;

					stream_white.add(white77.getTree());
					}
					break;

				default :
					break loop34;
				}
			}

			pushFollow(FOLLOW_lineend_in_simpleelseblock778);
			lineend78=lineend();
			state._fsp--;

			stream_lineend.add(lineend78.getTree());
			pushFollow(FOLLOW_block_in_simpleelseblock780);
			block79=block();
			state._fsp--;

			stream_block.add(block79.getTree());
			// AST REWRITE
			// elements: PELSE, block
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 139:46: -> ^( PELSE ( block )? )
			{
				// PreprocessorParser.g:139:49: ^( PELSE ( block )? )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_PELSE.nextNode(), root_1);
				// PreprocessorParser.g:139:57: ( block )?
				if ( stream_block.hasNext() ) {
					adaptor.addChild(root_1, stream_block.nextTree());
				}
				stream_block.reset();

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
	// $ANTLR end "simpleelseblock"


	public static class elifblock_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "elifblock"
	// PreprocessorParser.g:141:1: elifblock : c= PELIF ( white )* expr lineend block ( elseblock )? -> ^( $c ^( $c expr ^( SEQUENCE ( block )? ) ( elseblock )? ) ) ;
	public final PreprocessorParser.elifblock_return elifblock() throws RecognitionException {
		PreprocessorParser.elifblock_return retval = new PreprocessorParser.elifblock_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token c=null;
		ParserRuleReturnScope white80 =null;
		ParserRuleReturnScope expr81 =null;
		ParserRuleReturnScope lineend82 =null;
		ParserRuleReturnScope block83 =null;
		ParserRuleReturnScope elseblock84 =null;

		Object c_tree=null;
		RewriteRuleTokenStream stream_PELIF=new RewriteRuleTokenStream(adaptor,"token PELIF");
		RewriteRuleSubtreeStream stream_lineend=new RewriteRuleSubtreeStream(adaptor,"rule lineend");
		RewriteRuleSubtreeStream stream_white=new RewriteRuleSubtreeStream(adaptor,"rule white");
		RewriteRuleSubtreeStream stream_block=new RewriteRuleSubtreeStream(adaptor,"rule block");
		RewriteRuleSubtreeStream stream_expr=new RewriteRuleSubtreeStream(adaptor,"rule expr");
		RewriteRuleSubtreeStream stream_elseblock=new RewriteRuleSubtreeStream(adaptor,"rule elseblock");

		try {
			// PreprocessorParser.g:141:11: (c= PELIF ( white )* expr lineend block ( elseblock )? -> ^( $c ^( $c expr ^( SEQUENCE ( block )? ) ( elseblock )? ) ) )
			// PreprocessorParser.g:141:13: c= PELIF ( white )* expr lineend block ( elseblock )?
			{
			c=(Token)match(input,PELIF,FOLLOW_PELIF_in_elifblock800);  
			stream_PELIF.add(c);

			// PreprocessorParser.g:141:21: ( white )*
			loop35:
			while (true) {
				int alt35=2;
				int LA35_0 = input.LA(1);
				if ( (LA35_0==COMMENT||LA35_0==WS) ) {
					alt35=1;
				}

				switch (alt35) {
				case 1 :
					// PreprocessorParser.g:141:21: white
					{
					pushFollow(FOLLOW_white_in_elifblock802);
					white80=white();
					state._fsp--;

					stream_white.add(white80.getTree());
					}
					break;

				default :
					break loop35;
				}
			}

			pushFollow(FOLLOW_expr_in_elifblock805);
			expr81=expr();
			state._fsp--;

			stream_expr.add(expr81.getTree());
			pushFollow(FOLLOW_lineend_in_elifblock807);
			lineend82=lineend();
			state._fsp--;

			stream_lineend.add(lineend82.getTree());
			pushFollow(FOLLOW_block_in_elifblock809);
			block83=block();
			state._fsp--;

			stream_block.add(block83.getTree());
			// PreprocessorParser.g:141:47: ( elseblock )?
			int alt36=2;
			int LA36_0 = input.LA(1);
			if ( ((LA36_0 >= PELIF && LA36_0 <= PELSE)) ) {
				alt36=1;
			}
			switch (alt36) {
				case 1 :
					// PreprocessorParser.g:141:47: elseblock
					{
					pushFollow(FOLLOW_elseblock_in_elifblock811);
					elseblock84=elseblock();
					state._fsp--;

					stream_elseblock.add(elseblock84.getTree());
					}
					break;

			}

			// AST REWRITE
			// elements: elseblock, c, block, c, expr
			// token labels: c
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleTokenStream stream_c=new RewriteRuleTokenStream(adaptor,"token c",c);
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 142:4: -> ^( $c ^( $c expr ^( SEQUENCE ( block )? ) ( elseblock )? ) )
			{
				// PreprocessorParser.g:143:4: ^( $c ^( $c expr ^( SEQUENCE ( block )? ) ( elseblock )? ) )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_c.nextNode(), root_1);
				// PreprocessorParser.g:143:9: ^( $c expr ^( SEQUENCE ( block )? ) ( elseblock )? )
				{
				Object root_2 = (Object)adaptor.nil();
				root_2 = (Object)adaptor.becomeRoot(stream_c.nextNode(), root_2);
				adaptor.addChild(root_2, stream_expr.nextTree());
				// PreprocessorParser.g:143:19: ^( SEQUENCE ( block )? )
				{
				Object root_3 = (Object)adaptor.nil();
				root_3 = (Object)adaptor.becomeRoot((Object)adaptor.create(SEQUENCE, "SEQUENCE"), root_3);
				// PreprocessorParser.g:143:30: ( block )?
				if ( stream_block.hasNext() ) {
					adaptor.addChild(root_3, stream_block.nextTree());
				}
				stream_block.reset();

				adaptor.addChild(root_2, root_3);
				}

				// PreprocessorParser.g:143:38: ( elseblock )?
				if ( stream_elseblock.hasNext() ) {
					adaptor.addChild(root_2, stream_elseblock.nextTree());
				}
				stream_elseblock.reset();

				adaptor.addChild(root_1, root_2);
				}

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
	// $ANTLR end "elifblock"


	public static class ifdefblock_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "ifdefblock"
	// PreprocessorParser.g:146:1: ifdefblock : PIFDEF ( white )* identifier ( white )* lineend block ( elseblock )? endifline -> ^( PIFDEF identifier ^( SEQUENCE ( block )? ) ( elseblock )? ) ;
	public final PreprocessorParser.ifdefblock_return ifdefblock() throws RecognitionException {
		PreprocessorParser.ifdefblock_return retval = new PreprocessorParser.ifdefblock_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PIFDEF85=null;
		ParserRuleReturnScope white86 =null;
		ParserRuleReturnScope identifier87 =null;
		ParserRuleReturnScope white88 =null;
		ParserRuleReturnScope lineend89 =null;
		ParserRuleReturnScope block90 =null;
		ParserRuleReturnScope elseblock91 =null;
		ParserRuleReturnScope endifline92 =null;

		Object PIFDEF85_tree=null;
		RewriteRuleTokenStream stream_PIFDEF=new RewriteRuleTokenStream(adaptor,"token PIFDEF");
		RewriteRuleSubtreeStream stream_lineend=new RewriteRuleSubtreeStream(adaptor,"rule lineend");
		RewriteRuleSubtreeStream stream_endifline=new RewriteRuleSubtreeStream(adaptor,"rule endifline");
		RewriteRuleSubtreeStream stream_white=new RewriteRuleSubtreeStream(adaptor,"rule white");
		RewriteRuleSubtreeStream stream_block=new RewriteRuleSubtreeStream(adaptor,"rule block");
		RewriteRuleSubtreeStream stream_elseblock=new RewriteRuleSubtreeStream(adaptor,"rule elseblock");
		RewriteRuleSubtreeStream stream_identifier=new RewriteRuleSubtreeStream(adaptor,"rule identifier");

		try {
			// PreprocessorParser.g:146:12: ( PIFDEF ( white )* identifier ( white )* lineend block ( elseblock )? endifline -> ^( PIFDEF identifier ^( SEQUENCE ( block )? ) ( elseblock )? ) )
			// PreprocessorParser.g:146:14: PIFDEF ( white )* identifier ( white )* lineend block ( elseblock )? endifline
			{
			PIFDEF85=(Token)match(input,PIFDEF,FOLLOW_PIFDEF_in_ifdefblock854);  
			stream_PIFDEF.add(PIFDEF85);

			// PreprocessorParser.g:146:21: ( white )*
			loop37:
			while (true) {
				int alt37=2;
				int LA37_0 = input.LA(1);
				if ( (LA37_0==COMMENT||LA37_0==WS) ) {
					alt37=1;
				}

				switch (alt37) {
				case 1 :
					// PreprocessorParser.g:146:21: white
					{
					pushFollow(FOLLOW_white_in_ifdefblock856);
					white86=white();
					state._fsp--;

					stream_white.add(white86.getTree());
					}
					break;

				default :
					break loop37;
				}
			}

			pushFollow(FOLLOW_identifier_in_ifdefblock859);
			identifier87=identifier();
			state._fsp--;

			stream_identifier.add(identifier87.getTree());
			// PreprocessorParser.g:146:39: ( white )*
			loop38:
			while (true) {
				int alt38=2;
				int LA38_0 = input.LA(1);
				if ( (LA38_0==COMMENT||LA38_0==WS) ) {
					alt38=1;
				}

				switch (alt38) {
				case 1 :
					// PreprocessorParser.g:146:39: white
					{
					pushFollow(FOLLOW_white_in_ifdefblock861);
					white88=white();
					state._fsp--;

					stream_white.add(white88.getTree());
					}
					break;

				default :
					break loop38;
				}
			}

			pushFollow(FOLLOW_lineend_in_ifdefblock864);
			lineend89=lineend();
			state._fsp--;

			stream_lineend.add(lineend89.getTree());
			pushFollow(FOLLOW_block_in_ifdefblock869);
			block90=block();
			state._fsp--;

			stream_block.add(block90.getTree());
			// PreprocessorParser.g:147:10: ( elseblock )?
			int alt39=2;
			int LA39_0 = input.LA(1);
			if ( ((LA39_0 >= PELIF && LA39_0 <= PELSE)) ) {
				alt39=1;
			}
			switch (alt39) {
				case 1 :
					// PreprocessorParser.g:147:10: elseblock
					{
					pushFollow(FOLLOW_elseblock_in_ifdefblock871);
					elseblock91=elseblock();
					state._fsp--;

					stream_elseblock.add(elseblock91.getTree());
					}
					break;

			}

			pushFollow(FOLLOW_endifline_in_ifdefblock874);
			endifline92=endifline();
			state._fsp--;

			stream_endifline.add(endifline92.getTree());
			// AST REWRITE
			// elements: elseblock, PIFDEF, block, identifier
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 148:4: -> ^( PIFDEF identifier ^( SEQUENCE ( block )? ) ( elseblock )? )
			{
				// PreprocessorParser.g:148:7: ^( PIFDEF identifier ^( SEQUENCE ( block )? ) ( elseblock )? )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_PIFDEF.nextNode(), root_1);
				adaptor.addChild(root_1, stream_identifier.nextTree());
				// PreprocessorParser.g:148:27: ^( SEQUENCE ( block )? )
				{
				Object root_2 = (Object)adaptor.nil();
				root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(SEQUENCE, "SEQUENCE"), root_2);
				// PreprocessorParser.g:148:38: ( block )?
				if ( stream_block.hasNext() ) {
					adaptor.addChild(root_2, stream_block.nextTree());
				}
				stream_block.reset();

				adaptor.addChild(root_1, root_2);
				}

				// PreprocessorParser.g:148:46: ( elseblock )?
				if ( stream_elseblock.hasNext() ) {
					adaptor.addChild(root_1, stream_elseblock.nextTree());
				}
				stream_elseblock.reset();

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
	// $ANTLR end "ifdefblock"


	public static class ifndefblock_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "ifndefblock"
	// PreprocessorParser.g:151:1: ifndefblock : PIFNDEF ( white )* identifier ( white )* lineend block ( elseblock )? endifline -> ^( PIFNDEF identifier ^( SEQUENCE block ) ( elseblock )? ) ;
	public final PreprocessorParser.ifndefblock_return ifndefblock() throws RecognitionException {
		PreprocessorParser.ifndefblock_return retval = new PreprocessorParser.ifndefblock_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PIFNDEF93=null;
		ParserRuleReturnScope white94 =null;
		ParserRuleReturnScope identifier95 =null;
		ParserRuleReturnScope white96 =null;
		ParserRuleReturnScope lineend97 =null;
		ParserRuleReturnScope block98 =null;
		ParserRuleReturnScope elseblock99 =null;
		ParserRuleReturnScope endifline100 =null;

		Object PIFNDEF93_tree=null;
		RewriteRuleTokenStream stream_PIFNDEF=new RewriteRuleTokenStream(adaptor,"token PIFNDEF");
		RewriteRuleSubtreeStream stream_lineend=new RewriteRuleSubtreeStream(adaptor,"rule lineend");
		RewriteRuleSubtreeStream stream_endifline=new RewriteRuleSubtreeStream(adaptor,"rule endifline");
		RewriteRuleSubtreeStream stream_white=new RewriteRuleSubtreeStream(adaptor,"rule white");
		RewriteRuleSubtreeStream stream_block=new RewriteRuleSubtreeStream(adaptor,"rule block");
		RewriteRuleSubtreeStream stream_elseblock=new RewriteRuleSubtreeStream(adaptor,"rule elseblock");
		RewriteRuleSubtreeStream stream_identifier=new RewriteRuleSubtreeStream(adaptor,"rule identifier");

		try {
			// PreprocessorParser.g:151:13: ( PIFNDEF ( white )* identifier ( white )* lineend block ( elseblock )? endifline -> ^( PIFNDEF identifier ^( SEQUENCE block ) ( elseblock )? ) )
			// PreprocessorParser.g:151:15: PIFNDEF ( white )* identifier ( white )* lineend block ( elseblock )? endifline
			{
			PIFNDEF93=(Token)match(input,PIFNDEF,FOLLOW_PIFNDEF_in_ifndefblock906);  
			stream_PIFNDEF.add(PIFNDEF93);

			// PreprocessorParser.g:151:23: ( white )*
			loop40:
			while (true) {
				int alt40=2;
				int LA40_0 = input.LA(1);
				if ( (LA40_0==COMMENT||LA40_0==WS) ) {
					alt40=1;
				}

				switch (alt40) {
				case 1 :
					// PreprocessorParser.g:151:23: white
					{
					pushFollow(FOLLOW_white_in_ifndefblock908);
					white94=white();
					state._fsp--;

					stream_white.add(white94.getTree());
					}
					break;

				default :
					break loop40;
				}
			}

			pushFollow(FOLLOW_identifier_in_ifndefblock911);
			identifier95=identifier();
			state._fsp--;

			stream_identifier.add(identifier95.getTree());
			// PreprocessorParser.g:151:41: ( white )*
			loop41:
			while (true) {
				int alt41=2;
				int LA41_0 = input.LA(1);
				if ( (LA41_0==COMMENT||LA41_0==WS) ) {
					alt41=1;
				}

				switch (alt41) {
				case 1 :
					// PreprocessorParser.g:151:41: white
					{
					pushFollow(FOLLOW_white_in_ifndefblock913);
					white96=white();
					state._fsp--;

					stream_white.add(white96.getTree());
					}
					break;

				default :
					break loop41;
				}
			}

			pushFollow(FOLLOW_lineend_in_ifndefblock916);
			lineend97=lineend();
			state._fsp--;

			stream_lineend.add(lineend97.getTree());
			pushFollow(FOLLOW_block_in_ifndefblock921);
			block98=block();
			state._fsp--;

			stream_block.add(block98.getTree());
			// PreprocessorParser.g:152:10: ( elseblock )?
			int alt42=2;
			int LA42_0 = input.LA(1);
			if ( ((LA42_0 >= PELIF && LA42_0 <= PELSE)) ) {
				alt42=1;
			}
			switch (alt42) {
				case 1 :
					// PreprocessorParser.g:152:10: elseblock
					{
					pushFollow(FOLLOW_elseblock_in_ifndefblock923);
					elseblock99=elseblock();
					state._fsp--;

					stream_elseblock.add(elseblock99.getTree());
					}
					break;

			}

			pushFollow(FOLLOW_endifline_in_ifndefblock926);
			endifline100=endifline();
			state._fsp--;

			stream_endifline.add(endifline100.getTree());
			// AST REWRITE
			// elements: identifier, PIFNDEF, elseblock, block
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 153:4: -> ^( PIFNDEF identifier ^( SEQUENCE block ) ( elseblock )? )
			{
				// PreprocessorParser.g:153:7: ^( PIFNDEF identifier ^( SEQUENCE block ) ( elseblock )? )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_PIFNDEF.nextNode(), root_1);
				adaptor.addChild(root_1, stream_identifier.nextTree());
				// PreprocessorParser.g:153:28: ^( SEQUENCE block )
				{
				Object root_2 = (Object)adaptor.nil();
				root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(SEQUENCE, "SEQUENCE"), root_2);
				adaptor.addChild(root_2, stream_block.nextTree());
				adaptor.addChild(root_1, root_2);
				}

				// PreprocessorParser.g:153:46: ( elseblock )?
				if ( stream_elseblock.hasNext() ) {
					adaptor.addChild(root_1, stream_elseblock.nextTree());
				}
				stream_elseblock.reset();

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
	// $ANTLR end "ifndefblock"


	public static class endifline_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "endifline"
	// PreprocessorParser.g:156:1: endifline : PENDIF ( white )* lineend ;
	public final PreprocessorParser.endifline_return endifline() throws RecognitionException {
		PreprocessorParser.endifline_return retval = new PreprocessorParser.endifline_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PENDIF101=null;
		ParserRuleReturnScope white102 =null;
		ParserRuleReturnScope lineend103 =null;

		Object PENDIF101_tree=null;

		try {
			// PreprocessorParser.g:156:11: ( PENDIF ( white )* lineend )
			// PreprocessorParser.g:156:13: PENDIF ( white )* lineend
			{
			root_0 = (Object)adaptor.nil();


			PENDIF101=(Token)match(input,PENDIF,FOLLOW_PENDIF_in_endifline957); 
			PENDIF101_tree = (Object)adaptor.create(PENDIF101);
			adaptor.addChild(root_0, PENDIF101_tree);

			// PreprocessorParser.g:156:20: ( white )*
			loop43:
			while (true) {
				int alt43=2;
				int LA43_0 = input.LA(1);
				if ( (LA43_0==COMMENT||LA43_0==WS) ) {
					alt43=1;
				}

				switch (alt43) {
				case 1 :
					// PreprocessorParser.g:156:20: white
					{
					pushFollow(FOLLOW_white_in_endifline959);
					white102=white();
					state._fsp--;

					adaptor.addChild(root_0, white102.getTree());

					}
					break;

				default :
					break loop43;
				}
			}

			pushFollow(FOLLOW_lineend_in_endifline962);
			lineend103=lineend();
			state._fsp--;

			adaptor.addChild(root_0, lineend103.getTree());

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
	// $ANTLR end "endifline"


	public static class pragmaline_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "pragmaline"
	// PreprocessorParser.g:158:1: pragmaline : PRAGMA ( wpptoken )* lineend -> ^( PRAGMA ( wpptoken )* lineend ) ;
	public final PreprocessorParser.pragmaline_return pragmaline() throws RecognitionException {
		PreprocessorParser.pragmaline_return retval = new PreprocessorParser.pragmaline_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PRAGMA104=null;
		ParserRuleReturnScope wpptoken105 =null;
		ParserRuleReturnScope lineend106 =null;

		Object PRAGMA104_tree=null;
		RewriteRuleTokenStream stream_PRAGMA=new RewriteRuleTokenStream(adaptor,"token PRAGMA");
		RewriteRuleSubtreeStream stream_lineend=new RewriteRuleSubtreeStream(adaptor,"rule lineend");
		RewriteRuleSubtreeStream stream_wpptoken=new RewriteRuleSubtreeStream(adaptor,"rule wpptoken");

		try {
			// PreprocessorParser.g:158:12: ( PRAGMA ( wpptoken )* lineend -> ^( PRAGMA ( wpptoken )* lineend ) )
			// PreprocessorParser.g:158:14: PRAGMA ( wpptoken )* lineend
			{
			PRAGMA104=(Token)match(input,PRAGMA,FOLLOW_PRAGMA_in_pragmaline971);  
			stream_PRAGMA.add(PRAGMA104);

			// PreprocessorParser.g:158:21: ( wpptoken )*
			loop44:
			while (true) {
				int alt44=2;
				int LA44_0 = input.LA(1);
				if ( ((LA44_0 >= ABSTRACT && LA44_0 <= BREAK)||(LA44_0 >= CALLS && LA44_0 <= CASE)||(LA44_0 >= CHAR && LA44_0 <= DEFAULT)||(LA44_0 >= DEPENDS && LA44_0 <= DOUBLE)||(LA44_0 >= ELLIPSIS && LA44_0 <= EXTERN)||(LA44_0 >= FALSE && LA44_0 <= FORALL)||(LA44_0 >= GENERIC && LA44_0 <= HERE)||(LA44_0 >= IDENTIFIER && LA44_0 <= INVARIANT)||(LA44_0 >= LCURLY && LA44_0 <= LTE)||(LA44_0 >= MINUSMINUS && LA44_0 <= NEQ)||(LA44_0 >= NORETURN && LA44_0 <= NOT)||(LA44_0 >= OR && LA44_0 <= OUTPUT)||LA44_0==PARFOR||(LA44_0 >= PLUS && LA44_0 <= PP_NUMBER)||LA44_0==PROCNULL||(LA44_0 >= PURE && LA44_0 <= SCOPEOF)||(LA44_0 >= SELF && LA44_0 <= UNSIGNED)||(LA44_0 >= VOID && LA44_0 <= WS)||LA44_0==ROOT) ) {
					alt44=1;
				}

				switch (alt44) {
				case 1 :
					// PreprocessorParser.g:158:21: wpptoken
					{
					pushFollow(FOLLOW_wpptoken_in_pragmaline973);
					wpptoken105=wpptoken();
					state._fsp--;

					stream_wpptoken.add(wpptoken105.getTree());
					}
					break;

				default :
					break loop44;
				}
			}

			pushFollow(FOLLOW_lineend_in_pragmaline976);
			lineend106=lineend();
			state._fsp--;

			stream_lineend.add(lineend106.getTree());
			// AST REWRITE
			// elements: PRAGMA, wpptoken, lineend
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 158:39: -> ^( PRAGMA ( wpptoken )* lineend )
			{
				// PreprocessorParser.g:158:42: ^( PRAGMA ( wpptoken )* lineend )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_PRAGMA.nextNode(), root_1);
				// PreprocessorParser.g:158:51: ( wpptoken )*
				while ( stream_wpptoken.hasNext() ) {
					adaptor.addChild(root_1, stream_wpptoken.nextTree());
				}
				stream_wpptoken.reset();

				adaptor.addChild(root_1, stream_lineend.nextTree());
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
	// $ANTLR end "pragmaline"


	public static class errorline_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "errorline"
	// PreprocessorParser.g:160:1: errorline : PERROR ( wpptoken )* lineend -> ^( PERROR ( wpptoken )* ) ;
	public final PreprocessorParser.errorline_return errorline() throws RecognitionException {
		PreprocessorParser.errorline_return retval = new PreprocessorParser.errorline_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PERROR107=null;
		ParserRuleReturnScope wpptoken108 =null;
		ParserRuleReturnScope lineend109 =null;

		Object PERROR107_tree=null;
		RewriteRuleTokenStream stream_PERROR=new RewriteRuleTokenStream(adaptor,"token PERROR");
		RewriteRuleSubtreeStream stream_lineend=new RewriteRuleSubtreeStream(adaptor,"rule lineend");
		RewriteRuleSubtreeStream stream_wpptoken=new RewriteRuleSubtreeStream(adaptor,"rule wpptoken");

		try {
			// PreprocessorParser.g:160:11: ( PERROR ( wpptoken )* lineend -> ^( PERROR ( wpptoken )* ) )
			// PreprocessorParser.g:160:13: PERROR ( wpptoken )* lineend
			{
			PERROR107=(Token)match(input,PERROR,FOLLOW_PERROR_in_errorline996);  
			stream_PERROR.add(PERROR107);

			// PreprocessorParser.g:160:20: ( wpptoken )*
			loop45:
			while (true) {
				int alt45=2;
				int LA45_0 = input.LA(1);
				if ( ((LA45_0 >= ABSTRACT && LA45_0 <= BREAK)||(LA45_0 >= CALLS && LA45_0 <= CASE)||(LA45_0 >= CHAR && LA45_0 <= DEFAULT)||(LA45_0 >= DEPENDS && LA45_0 <= DOUBLE)||(LA45_0 >= ELLIPSIS && LA45_0 <= EXTERN)||(LA45_0 >= FALSE && LA45_0 <= FORALL)||(LA45_0 >= GENERIC && LA45_0 <= HERE)||(LA45_0 >= IDENTIFIER && LA45_0 <= INVARIANT)||(LA45_0 >= LCURLY && LA45_0 <= LTE)||(LA45_0 >= MINUSMINUS && LA45_0 <= NEQ)||(LA45_0 >= NORETURN && LA45_0 <= NOT)||(LA45_0 >= OR && LA45_0 <= OUTPUT)||LA45_0==PARFOR||(LA45_0 >= PLUS && LA45_0 <= PP_NUMBER)||LA45_0==PROCNULL||(LA45_0 >= PURE && LA45_0 <= SCOPEOF)||(LA45_0 >= SELF && LA45_0 <= UNSIGNED)||(LA45_0 >= VOID && LA45_0 <= WS)||LA45_0==ROOT) ) {
					alt45=1;
				}

				switch (alt45) {
				case 1 :
					// PreprocessorParser.g:160:20: wpptoken
					{
					pushFollow(FOLLOW_wpptoken_in_errorline998);
					wpptoken108=wpptoken();
					state._fsp--;

					stream_wpptoken.add(wpptoken108.getTree());
					}
					break;

				default :
					break loop45;
				}
			}

			pushFollow(FOLLOW_lineend_in_errorline1001);
			lineend109=lineend();
			state._fsp--;

			stream_lineend.add(lineend109.getTree());
			// AST REWRITE
			// elements: PERROR, wpptoken
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 160:38: -> ^( PERROR ( wpptoken )* )
			{
				// PreprocessorParser.g:160:41: ^( PERROR ( wpptoken )* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_PERROR.nextNode(), root_1);
				// PreprocessorParser.g:160:50: ( wpptoken )*
				while ( stream_wpptoken.hasNext() ) {
					adaptor.addChild(root_1, stream_wpptoken.nextTree());
				}
				stream_wpptoken.reset();

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
	// $ANTLR end "errorline"


	public static class lineline_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "lineline"
	// PreprocessorParser.g:162:1: lineline : PLINE ( wpptoken )* lineend -> ^( PLINE ( wpptoken )* ) ;
	public final PreprocessorParser.lineline_return lineline() throws RecognitionException {
		PreprocessorParser.lineline_return retval = new PreprocessorParser.lineline_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PLINE110=null;
		ParserRuleReturnScope wpptoken111 =null;
		ParserRuleReturnScope lineend112 =null;

		Object PLINE110_tree=null;
		RewriteRuleTokenStream stream_PLINE=new RewriteRuleTokenStream(adaptor,"token PLINE");
		RewriteRuleSubtreeStream stream_lineend=new RewriteRuleSubtreeStream(adaptor,"rule lineend");
		RewriteRuleSubtreeStream stream_wpptoken=new RewriteRuleSubtreeStream(adaptor,"rule wpptoken");

		try {
			// PreprocessorParser.g:162:10: ( PLINE ( wpptoken )* lineend -> ^( PLINE ( wpptoken )* ) )
			// PreprocessorParser.g:162:12: PLINE ( wpptoken )* lineend
			{
			PLINE110=(Token)match(input,PLINE,FOLLOW_PLINE_in_lineline1019);  
			stream_PLINE.add(PLINE110);

			// PreprocessorParser.g:162:18: ( wpptoken )*
			loop46:
			while (true) {
				int alt46=2;
				int LA46_0 = input.LA(1);
				if ( ((LA46_0 >= ABSTRACT && LA46_0 <= BREAK)||(LA46_0 >= CALLS && LA46_0 <= CASE)||(LA46_0 >= CHAR && LA46_0 <= DEFAULT)||(LA46_0 >= DEPENDS && LA46_0 <= DOUBLE)||(LA46_0 >= ELLIPSIS && LA46_0 <= EXTERN)||(LA46_0 >= FALSE && LA46_0 <= FORALL)||(LA46_0 >= GENERIC && LA46_0 <= HERE)||(LA46_0 >= IDENTIFIER && LA46_0 <= INVARIANT)||(LA46_0 >= LCURLY && LA46_0 <= LTE)||(LA46_0 >= MINUSMINUS && LA46_0 <= NEQ)||(LA46_0 >= NORETURN && LA46_0 <= NOT)||(LA46_0 >= OR && LA46_0 <= OUTPUT)||LA46_0==PARFOR||(LA46_0 >= PLUS && LA46_0 <= PP_NUMBER)||LA46_0==PROCNULL||(LA46_0 >= PURE && LA46_0 <= SCOPEOF)||(LA46_0 >= SELF && LA46_0 <= UNSIGNED)||(LA46_0 >= VOID && LA46_0 <= WS)||LA46_0==ROOT) ) {
					alt46=1;
				}

				switch (alt46) {
				case 1 :
					// PreprocessorParser.g:162:18: wpptoken
					{
					pushFollow(FOLLOW_wpptoken_in_lineline1021);
					wpptoken111=wpptoken();
					state._fsp--;

					stream_wpptoken.add(wpptoken111.getTree());
					}
					break;

				default :
					break loop46;
				}
			}

			pushFollow(FOLLOW_lineend_in_lineline1024);
			lineend112=lineend();
			state._fsp--;

			stream_lineend.add(lineend112.getTree());
			// AST REWRITE
			// elements: PLINE, wpptoken
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 162:36: -> ^( PLINE ( wpptoken )* )
			{
				// PreprocessorParser.g:162:39: ^( PLINE ( wpptoken )* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_PLINE.nextNode(), root_1);
				// PreprocessorParser.g:162:47: ( wpptoken )*
				while ( stream_wpptoken.hasNext() ) {
					adaptor.addChild(root_1, stream_wpptoken.nextTree());
				}
				stream_wpptoken.reset();

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
	// $ANTLR end "lineline"


	public static class nondirectiveline_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "nondirectiveline"
	// PreprocessorParser.g:164:1: nondirectiveline : HASH ( wpptoken )* lineend -> ^( HASH ( wpptoken )* ) ;
	public final PreprocessorParser.nondirectiveline_return nondirectiveline() throws RecognitionException {
		PreprocessorParser.nondirectiveline_return retval = new PreprocessorParser.nondirectiveline_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token HASH113=null;
		ParserRuleReturnScope wpptoken114 =null;
		ParserRuleReturnScope lineend115 =null;

		Object HASH113_tree=null;
		RewriteRuleTokenStream stream_HASH=new RewriteRuleTokenStream(adaptor,"token HASH");
		RewriteRuleSubtreeStream stream_lineend=new RewriteRuleSubtreeStream(adaptor,"rule lineend");
		RewriteRuleSubtreeStream stream_wpptoken=new RewriteRuleSubtreeStream(adaptor,"rule wpptoken");

		try {
			// PreprocessorParser.g:165:3: ( HASH ( wpptoken )* lineend -> ^( HASH ( wpptoken )* ) )
			// PreprocessorParser.g:165:5: HASH ( wpptoken )* lineend
			{
			HASH113=(Token)match(input,HASH,FOLLOW_HASH_in_nondirectiveline1044);  
			stream_HASH.add(HASH113);

			// PreprocessorParser.g:165:10: ( wpptoken )*
			loop47:
			while (true) {
				int alt47=2;
				int LA47_0 = input.LA(1);
				if ( ((LA47_0 >= ABSTRACT && LA47_0 <= BREAK)||(LA47_0 >= CALLS && LA47_0 <= CASE)||(LA47_0 >= CHAR && LA47_0 <= DEFAULT)||(LA47_0 >= DEPENDS && LA47_0 <= DOUBLE)||(LA47_0 >= ELLIPSIS && LA47_0 <= EXTERN)||(LA47_0 >= FALSE && LA47_0 <= FORALL)||(LA47_0 >= GENERIC && LA47_0 <= HERE)||(LA47_0 >= IDENTIFIER && LA47_0 <= INVARIANT)||(LA47_0 >= LCURLY && LA47_0 <= LTE)||(LA47_0 >= MINUSMINUS && LA47_0 <= NEQ)||(LA47_0 >= NORETURN && LA47_0 <= NOT)||(LA47_0 >= OR && LA47_0 <= OUTPUT)||LA47_0==PARFOR||(LA47_0 >= PLUS && LA47_0 <= PP_NUMBER)||LA47_0==PROCNULL||(LA47_0 >= PURE && LA47_0 <= SCOPEOF)||(LA47_0 >= SELF && LA47_0 <= UNSIGNED)||(LA47_0 >= VOID && LA47_0 <= WS)||LA47_0==ROOT) ) {
					alt47=1;
				}

				switch (alt47) {
				case 1 :
					// PreprocessorParser.g:165:10: wpptoken
					{
					pushFollow(FOLLOW_wpptoken_in_nondirectiveline1046);
					wpptoken114=wpptoken();
					state._fsp--;

					stream_wpptoken.add(wpptoken114.getTree());
					}
					break;

				default :
					break loop47;
				}
			}

			pushFollow(FOLLOW_lineend_in_nondirectiveline1049);
			lineend115=lineend();
			state._fsp--;

			stream_lineend.add(lineend115.getTree());
			// AST REWRITE
			// elements: HASH, wpptoken
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 165:28: -> ^( HASH ( wpptoken )* )
			{
				// PreprocessorParser.g:165:31: ^( HASH ( wpptoken )* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_HASH.nextNode(), root_1);
				// PreprocessorParser.g:165:38: ( wpptoken )*
				while ( stream_wpptoken.hasNext() ) {
					adaptor.addChild(root_1, stream_wpptoken.nextTree());
				}
				stream_wpptoken.reset();

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
	// $ANTLR end "nondirectiveline"


	public static class pptoken_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "pptoken"
	// PreprocessorParser.g:168:1: pptoken : ( HEADER_NAME | identifier | pp_number | CHARACTER_CONSTANT | STRING_LITERAL | punctuator | OTHER );
	public final PreprocessorParser.pptoken_return pptoken() throws RecognitionException {
		PreprocessorParser.pptoken_return retval = new PreprocessorParser.pptoken_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token HEADER_NAME116=null;
		Token CHARACTER_CONSTANT119=null;
		Token STRING_LITERAL120=null;
		Token OTHER122=null;
		ParserRuleReturnScope identifier117 =null;
		ParserRuleReturnScope pp_number118 =null;
		ParserRuleReturnScope punctuator121 =null;

		Object HEADER_NAME116_tree=null;
		Object CHARACTER_CONSTANT119_tree=null;
		Object STRING_LITERAL120_tree=null;
		Object OTHER122_tree=null;

		try {
			// PreprocessorParser.g:168:10: ( HEADER_NAME | identifier | pp_number | CHARACTER_CONSTANT | STRING_LITERAL | punctuator | OTHER )
			int alt48=7;
			switch ( input.LA(1) ) {
			case HEADER_NAME:
				{
				alt48=1;
				}
				break;
			case ABSTRACT:
			case ALIGNAS:
			case ALIGNOF:
			case ASSIGNS:
			case ATOMIC:
			case AUTO:
			case BIG_O:
			case BOOL:
			case BREAK:
			case CALLS:
			case CASE:
			case CHAR:
			case CHOOSE:
			case CIVLATOM:
			case CIVLATOMIC:
			case CIVLFOR:
			case COLLECTIVE:
			case COMPLEX:
			case CONST:
			case CONTIN:
			case CONTINUE:
			case DEFAULT:
			case DEPENDS:
			case DERIV:
			case DEVICE:
			case DO:
			case DOMAIN:
			case DOUBLE:
			case ELSE:
			case ENSURES:
			case ENUM:
			case EXISTS:
			case EXTERN:
			case FALSE:
			case FATOMIC:
			case FLOAT:
			case FOR:
			case FORALL:
			case GENERIC:
			case GLOBAL:
			case GOTO:
			case GUARD:
			case HERE:
			case IDENTIFIER:
			case IF:
			case IMAGINARY:
			case INLINE:
			case INPUT:
			case INT:
			case INVARIANT:
			case LONG:
			case NORETURN:
			case OUTPUT:
			case PARFOR:
			case PROCNULL:
			case PURE:
			case RANGE:
			case READS:
			case REAL:
			case REGISTER:
			case REQUIRES:
			case RESTRICT:
			case RESULT:
			case RETURN:
			case SCOPEOF:
			case SELF:
			case SHARED:
			case SHORT:
			case SIGNED:
			case SIZEOF:
			case SPAWN:
			case STATIC:
			case STATICASSERT:
			case STRUCT:
			case SWITCH:
			case SYSTEM:
			case THREADLOCAL:
			case TRUE:
			case TYPEDEF:
			case TYPEOF:
			case UNIFORM:
			case UNION:
			case UNSIGNED:
			case VOID:
			case VOLATILE:
			case WHEN:
			case WHILE:
			case ROOT:
				{
				alt48=2;
				}
				break;
			case FLOATING_CONSTANT:
			case INTEGER_CONSTANT:
			case PP_NUMBER:
				{
				alt48=3;
				}
				break;
			case CHARACTER_CONSTANT:
				{
				alt48=4;
				}
				break;
			case STRING_LITERAL:
				{
				alt48=5;
				}
				break;
			case AMPERSAND:
			case AND:
			case ARROW:
			case ASSIGN:
			case AT:
			case BITANDEQ:
			case BITOR:
			case BITOREQ:
			case BITXOR:
			case BITXOREQ:
			case COLON:
			case COMMA:
			case DIV:
			case DIVEQ:
			case DOT:
			case DOTDOT:
			case ELLIPSIS:
			case EQUALS:
			case GT:
			case GTE:
			case HASH:
			case HASHHASH:
			case IMPLIES:
			case LCURLY:
			case LEXCON:
			case LPAREN:
			case LSLIST:
			case LSQUARE:
			case LT:
			case LTE:
			case MINUSMINUS:
			case MOD:
			case MODEQ:
			case NEQ:
			case NOT:
			case OR:
			case PLUS:
			case PLUSEQ:
			case PLUSPLUS:
			case QMARK:
			case RCURLY:
			case REXCON:
			case RPAREN:
			case RSLIST:
			case RSQUARE:
			case SEMI:
			case SHIFTLEFT:
			case SHIFTLEFTEQ:
			case SHIFTRIGHT:
			case SHIFTRIGHTEQ:
			case STAR:
			case STAREQ:
			case SUB:
			case SUBEQ:
			case TILDE:
				{
				alt48=6;
				}
				break;
			case OTHER:
				{
				alt48=7;
				}
				break;
			default:
				NoViableAltException nvae =
					new NoViableAltException("", 48, 0, input);
				throw nvae;
			}
			switch (alt48) {
				case 1 :
					// PreprocessorParser.g:168:12: HEADER_NAME
					{
					root_0 = (Object)adaptor.nil();


					HEADER_NAME116=(Token)match(input,HEADER_NAME,FOLLOW_HEADER_NAME_in_pptoken1070); 
					HEADER_NAME116_tree = (Object)adaptor.create(HEADER_NAME116);
					adaptor.addChild(root_0, HEADER_NAME116_tree);

					}
					break;
				case 2 :
					// PreprocessorParser.g:169:5: identifier
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_identifier_in_pptoken1076);
					identifier117=identifier();
					state._fsp--;

					adaptor.addChild(root_0, identifier117.getTree());

					}
					break;
				case 3 :
					// PreprocessorParser.g:170:5: pp_number
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_pp_number_in_pptoken1082);
					pp_number118=pp_number();
					state._fsp--;

					adaptor.addChild(root_0, pp_number118.getTree());

					}
					break;
				case 4 :
					// PreprocessorParser.g:171:5: CHARACTER_CONSTANT
					{
					root_0 = (Object)adaptor.nil();


					CHARACTER_CONSTANT119=(Token)match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_pptoken1088); 
					CHARACTER_CONSTANT119_tree = (Object)adaptor.create(CHARACTER_CONSTANT119);
					adaptor.addChild(root_0, CHARACTER_CONSTANT119_tree);

					}
					break;
				case 5 :
					// PreprocessorParser.g:172:5: STRING_LITERAL
					{
					root_0 = (Object)adaptor.nil();


					STRING_LITERAL120=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_pptoken1094); 
					STRING_LITERAL120_tree = (Object)adaptor.create(STRING_LITERAL120);
					adaptor.addChild(root_0, STRING_LITERAL120_tree);

					}
					break;
				case 6 :
					// PreprocessorParser.g:173:5: punctuator
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_punctuator_in_pptoken1100);
					punctuator121=punctuator();
					state._fsp--;

					adaptor.addChild(root_0, punctuator121.getTree());

					}
					break;
				case 7 :
					// PreprocessorParser.g:174:5: OTHER
					{
					root_0 = (Object)adaptor.nil();


					OTHER122=(Token)match(input,OTHER,FOLLOW_OTHER_in_pptoken1106); 
					OTHER122_tree = (Object)adaptor.create(OTHER122);
					adaptor.addChild(root_0, OTHER122_tree);

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
	// $ANTLR end "pptoken"


	public static class nonPoundPpToken_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "nonPoundPpToken"
	// PreprocessorParser.g:178:1: nonPoundPpToken : ( HEADER_NAME | identifier | pp_number | CHARACTER_CONSTANT | STRING_LITERAL | nonPoundPunctuator | OTHER );
	public final PreprocessorParser.nonPoundPpToken_return nonPoundPpToken() throws RecognitionException {
		PreprocessorParser.nonPoundPpToken_return retval = new PreprocessorParser.nonPoundPpToken_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token HEADER_NAME123=null;
		Token CHARACTER_CONSTANT126=null;
		Token STRING_LITERAL127=null;
		Token OTHER129=null;
		ParserRuleReturnScope identifier124 =null;
		ParserRuleReturnScope pp_number125 =null;
		ParserRuleReturnScope nonPoundPunctuator128 =null;

		Object HEADER_NAME123_tree=null;
		Object CHARACTER_CONSTANT126_tree=null;
		Object STRING_LITERAL127_tree=null;
		Object OTHER129_tree=null;

		try {
			// PreprocessorParser.g:178:17: ( HEADER_NAME | identifier | pp_number | CHARACTER_CONSTANT | STRING_LITERAL | nonPoundPunctuator | OTHER )
			int alt49=7;
			switch ( input.LA(1) ) {
			case HEADER_NAME:
				{
				alt49=1;
				}
				break;
			case ABSTRACT:
			case ALIGNAS:
			case ALIGNOF:
			case ASSIGNS:
			case ATOMIC:
			case AUTO:
			case BIG_O:
			case BOOL:
			case BREAK:
			case CALLS:
			case CASE:
			case CHAR:
			case CHOOSE:
			case CIVLATOM:
			case CIVLATOMIC:
			case CIVLFOR:
			case COLLECTIVE:
			case COMPLEX:
			case CONST:
			case CONTIN:
			case CONTINUE:
			case DEFAULT:
			case DEPENDS:
			case DERIV:
			case DEVICE:
			case DO:
			case DOMAIN:
			case DOUBLE:
			case ELSE:
			case ENSURES:
			case ENUM:
			case EXISTS:
			case EXTERN:
			case FALSE:
			case FATOMIC:
			case FLOAT:
			case FOR:
			case FORALL:
			case GENERIC:
			case GLOBAL:
			case GOTO:
			case GUARD:
			case HERE:
			case IDENTIFIER:
			case IF:
			case IMAGINARY:
			case INLINE:
			case INPUT:
			case INT:
			case INVARIANT:
			case LONG:
			case NORETURN:
			case OUTPUT:
			case PARFOR:
			case PROCNULL:
			case PURE:
			case RANGE:
			case READS:
			case REAL:
			case REGISTER:
			case REQUIRES:
			case RESTRICT:
			case RESULT:
			case RETURN:
			case SCOPEOF:
			case SELF:
			case SHARED:
			case SHORT:
			case SIGNED:
			case SIZEOF:
			case SPAWN:
			case STATIC:
			case STATICASSERT:
			case STRUCT:
			case SWITCH:
			case SYSTEM:
			case THREADLOCAL:
			case TRUE:
			case TYPEDEF:
			case TYPEOF:
			case UNIFORM:
			case UNION:
			case UNSIGNED:
			case VOID:
			case VOLATILE:
			case WHEN:
			case WHILE:
			case ROOT:
				{
				alt49=2;
				}
				break;
			case FLOATING_CONSTANT:
			case INTEGER_CONSTANT:
			case PP_NUMBER:
				{
				alt49=3;
				}
				break;
			case CHARACTER_CONSTANT:
				{
				alt49=4;
				}
				break;
			case STRING_LITERAL:
				{
				alt49=5;
				}
				break;
			case AMPERSAND:
			case AND:
			case ARROW:
			case ASSIGN:
			case AT:
			case BITANDEQ:
			case BITOR:
			case BITOREQ:
			case BITXOR:
			case BITXOREQ:
			case COLON:
			case COMMA:
			case DIV:
			case DIVEQ:
			case DOT:
			case DOTDOT:
			case ELLIPSIS:
			case EQUALS:
			case GT:
			case GTE:
			case HASHHASH:
			case IMPLIES:
			case LCURLY:
			case LEXCON:
			case LPAREN:
			case LSLIST:
			case LSQUARE:
			case LT:
			case LTE:
			case MINUSMINUS:
			case MOD:
			case MODEQ:
			case NEQ:
			case NOT:
			case OR:
			case PLUS:
			case PLUSEQ:
			case PLUSPLUS:
			case QMARK:
			case RCURLY:
			case REXCON:
			case RPAREN:
			case RSLIST:
			case RSQUARE:
			case SEMI:
			case SHIFTLEFT:
			case SHIFTLEFTEQ:
			case SHIFTRIGHT:
			case SHIFTRIGHTEQ:
			case STAR:
			case STAREQ:
			case SUB:
			case SUBEQ:
			case TILDE:
				{
				alt49=6;
				}
				break;
			case OTHER:
				{
				alt49=7;
				}
				break;
			default:
				NoViableAltException nvae =
					new NoViableAltException("", 49, 0, input);
				throw nvae;
			}
			switch (alt49) {
				case 1 :
					// PreprocessorParser.g:178:19: HEADER_NAME
					{
					root_0 = (Object)adaptor.nil();


					HEADER_NAME123=(Token)match(input,HEADER_NAME,FOLLOW_HEADER_NAME_in_nonPoundPpToken1119); 
					HEADER_NAME123_tree = (Object)adaptor.create(HEADER_NAME123);
					adaptor.addChild(root_0, HEADER_NAME123_tree);

					}
					break;
				case 2 :
					// PreprocessorParser.g:179:5: identifier
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_identifier_in_nonPoundPpToken1125);
					identifier124=identifier();
					state._fsp--;

					adaptor.addChild(root_0, identifier124.getTree());

					}
					break;
				case 3 :
					// PreprocessorParser.g:180:5: pp_number
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_pp_number_in_nonPoundPpToken1131);
					pp_number125=pp_number();
					state._fsp--;

					adaptor.addChild(root_0, pp_number125.getTree());

					}
					break;
				case 4 :
					// PreprocessorParser.g:181:5: CHARACTER_CONSTANT
					{
					root_0 = (Object)adaptor.nil();


					CHARACTER_CONSTANT126=(Token)match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_nonPoundPpToken1137); 
					CHARACTER_CONSTANT126_tree = (Object)adaptor.create(CHARACTER_CONSTANT126);
					adaptor.addChild(root_0, CHARACTER_CONSTANT126_tree);

					}
					break;
				case 5 :
					// PreprocessorParser.g:182:5: STRING_LITERAL
					{
					root_0 = (Object)adaptor.nil();


					STRING_LITERAL127=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_nonPoundPpToken1143); 
					STRING_LITERAL127_tree = (Object)adaptor.create(STRING_LITERAL127);
					adaptor.addChild(root_0, STRING_LITERAL127_tree);

					}
					break;
				case 6 :
					// PreprocessorParser.g:183:5: nonPoundPunctuator
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_nonPoundPunctuator_in_nonPoundPpToken1149);
					nonPoundPunctuator128=nonPoundPunctuator();
					state._fsp--;

					adaptor.addChild(root_0, nonPoundPunctuator128.getTree());

					}
					break;
				case 7 :
					// PreprocessorParser.g:184:5: OTHER
					{
					root_0 = (Object)adaptor.nil();


					OTHER129=(Token)match(input,OTHER,FOLLOW_OTHER_in_nonPoundPpToken1155); 
					OTHER129_tree = (Object)adaptor.create(OTHER129);
					adaptor.addChild(root_0, OTHER129_tree);

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
	// $ANTLR end "nonPoundPpToken"


	public static class identifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "identifier"
	// PreprocessorParser.g:190:1: identifier : ( IDENTIFIER | c_keyword | gnuc_keyword );
	public final PreprocessorParser.identifier_return identifier() throws RecognitionException {
		PreprocessorParser.identifier_return retval = new PreprocessorParser.identifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token IDENTIFIER130=null;
		ParserRuleReturnScope c_keyword131 =null;
		ParserRuleReturnScope gnuc_keyword132 =null;

		Object IDENTIFIER130_tree=null;

		try {
			// PreprocessorParser.g:190:12: ( IDENTIFIER | c_keyword | gnuc_keyword )
			int alt50=3;
			switch ( input.LA(1) ) {
			case IDENTIFIER:
				{
				alt50=1;
				}
				break;
			case ABSTRACT:
			case ALIGNAS:
			case ALIGNOF:
			case ASSIGNS:
			case ATOMIC:
			case AUTO:
			case BIG_O:
			case BOOL:
			case BREAK:
			case CALLS:
			case CASE:
			case CHAR:
			case CHOOSE:
			case CIVLATOM:
			case CIVLATOMIC:
			case CIVLFOR:
			case COLLECTIVE:
			case COMPLEX:
			case CONST:
			case CONTIN:
			case CONTINUE:
			case DEFAULT:
			case DEPENDS:
			case DERIV:
			case DEVICE:
			case DO:
			case DOMAIN:
			case DOUBLE:
			case ELSE:
			case ENSURES:
			case ENUM:
			case EXISTS:
			case EXTERN:
			case FALSE:
			case FATOMIC:
			case FLOAT:
			case FOR:
			case FORALL:
			case GENERIC:
			case GLOBAL:
			case GOTO:
			case GUARD:
			case HERE:
			case IF:
			case IMAGINARY:
			case INLINE:
			case INPUT:
			case INT:
			case INVARIANT:
			case LONG:
			case NORETURN:
			case OUTPUT:
			case PARFOR:
			case PROCNULL:
			case PURE:
			case RANGE:
			case READS:
			case REAL:
			case REGISTER:
			case REQUIRES:
			case RESTRICT:
			case RESULT:
			case RETURN:
			case SCOPEOF:
			case SELF:
			case SHARED:
			case SHORT:
			case SIGNED:
			case SIZEOF:
			case SPAWN:
			case STATIC:
			case STATICASSERT:
			case STRUCT:
			case SWITCH:
			case SYSTEM:
			case THREADLOCAL:
			case TRUE:
			case TYPEDEF:
			case UNIFORM:
			case UNION:
			case UNSIGNED:
			case VOID:
			case VOLATILE:
			case WHEN:
			case WHILE:
			case ROOT:
				{
				alt50=2;
				}
				break;
			case TYPEOF:
				{
				alt50=3;
				}
				break;
			default:
				NoViableAltException nvae =
					new NoViableAltException("", 50, 0, input);
				throw nvae;
			}
			switch (alt50) {
				case 1 :
					// PreprocessorParser.g:190:14: IDENTIFIER
					{
					root_0 = (Object)adaptor.nil();


					IDENTIFIER130=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifier1173); 
					IDENTIFIER130_tree = (Object)adaptor.create(IDENTIFIER130);
					adaptor.addChild(root_0, IDENTIFIER130_tree);

					}
					break;
				case 2 :
					// PreprocessorParser.g:190:27: c_keyword
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_c_keyword_in_identifier1177);
					c_keyword131=c_keyword();
					state._fsp--;

					adaptor.addChild(root_0, c_keyword131.getTree());

					}
					break;
				case 3 :
					// PreprocessorParser.g:190:39: gnuc_keyword
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_gnuc_keyword_in_identifier1181);
					gnuc_keyword132=gnuc_keyword();
					state._fsp--;

					adaptor.addChild(root_0, gnuc_keyword132.getTree());

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
	// $ANTLR end "identifier"


	public static class c_keyword_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "c_keyword"
	// PreprocessorParser.g:192:1: c_keyword : ( AUTO | ASSIGNS | BREAK | CASE | CHAR | CONST | CONTINUE | DEFAULT | DEPENDS | DO | DOUBLE | ELSE | ENUM | EXTERN | FLOAT | FOR | GOTO | GUARD | IF | INLINE | INT | LONG | REGISTER | RESTRICT | RETURN | SHORT | SIGNED | SIZEOF | SCOPEOF | STATIC | STRUCT | SWITCH | TYPEDEF | UNION | UNSIGNED | VOID | VOLATILE | WHILE | ALIGNAS | ALIGNOF | ATOMIC | BOOL | COMPLEX | GENERIC | IMAGINARY | NORETURN | STATICASSERT | THREADLOCAL | CHOOSE | COLLECTIVE | ENSURES | FALSE | INPUT | INVARIANT | OUTPUT | READS | REQUIRES | RESULT | SELF | PROCNULL | HERE | ROOT | SPAWN | TRUE | WHEN | CIVLATOMIC | CIVLATOM | ABSTRACT | BIG_O | CONTIN | DERIV | FORALL | EXISTS | UNIFORM | PURE | REAL | CIVLFOR | PARFOR | DOMAIN | RANGE | SYSTEM | DEVICE | GLOBAL | SHARED | FATOMIC | CALLS );
	public final PreprocessorParser.c_keyword_return c_keyword() throws RecognitionException {
		PreprocessorParser.c_keyword_return retval = new PreprocessorParser.c_keyword_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set133=null;

		Object set133_tree=null;

		try {
			// PreprocessorParser.g:192:11: ( AUTO | ASSIGNS | BREAK | CASE | CHAR | CONST | CONTINUE | DEFAULT | DEPENDS | DO | DOUBLE | ELSE | ENUM | EXTERN | FLOAT | FOR | GOTO | GUARD | IF | INLINE | INT | LONG | REGISTER | RESTRICT | RETURN | SHORT | SIGNED | SIZEOF | SCOPEOF | STATIC | STRUCT | SWITCH | TYPEDEF | UNION | UNSIGNED | VOID | VOLATILE | WHILE | ALIGNAS | ALIGNOF | ATOMIC | BOOL | COMPLEX | GENERIC | IMAGINARY | NORETURN | STATICASSERT | THREADLOCAL | CHOOSE | COLLECTIVE | ENSURES | FALSE | INPUT | INVARIANT | OUTPUT | READS | REQUIRES | RESULT | SELF | PROCNULL | HERE | ROOT | SPAWN | TRUE | WHEN | CIVLATOMIC | CIVLATOM | ABSTRACT | BIG_O | CONTIN | DERIV | FORALL | EXISTS | UNIFORM | PURE | REAL | CIVLFOR | PARFOR | DOMAIN | RANGE | SYSTEM | DEVICE | GLOBAL | SHARED | FATOMIC | CALLS )
			// PreprocessorParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set133=input.LT(1);
			if ( (input.LA(1) >= ABSTRACT && input.LA(1) <= ALIGNOF)||input.LA(1)==ASSIGNS||(input.LA(1) >= ATOMIC && input.LA(1) <= BIG_O)||(input.LA(1) >= BOOL && input.LA(1) <= BREAK)||(input.LA(1) >= CALLS && input.LA(1) <= CASE)||input.LA(1)==CHAR||(input.LA(1) >= CHOOSE && input.LA(1) <= COLLECTIVE)||(input.LA(1) >= COMPLEX && input.LA(1) <= DEFAULT)||(input.LA(1) >= DEPENDS && input.LA(1) <= DEVICE)||(input.LA(1) >= DO && input.LA(1) <= DOMAIN)||input.LA(1)==DOUBLE||(input.LA(1) >= ELSE && input.LA(1) <= ENUM)||(input.LA(1) >= EXISTS && input.LA(1) <= EXTERN)||(input.LA(1) >= FALSE && input.LA(1) <= FLOAT)||(input.LA(1) >= FOR && input.LA(1) <= FORALL)||(input.LA(1) >= GENERIC && input.LA(1) <= GOTO)||input.LA(1)==GUARD||input.LA(1)==HERE||(input.LA(1) >= IF && input.LA(1) <= IMAGINARY)||(input.LA(1) >= INLINE && input.LA(1) <= INT)||input.LA(1)==INVARIANT||input.LA(1)==LONG||input.LA(1)==NORETURN||input.LA(1)==OUTPUT||input.LA(1)==PARFOR||input.LA(1)==PROCNULL||input.LA(1)==PURE||input.LA(1)==RANGE||(input.LA(1) >= READS && input.LA(1) <= RETURN)||input.LA(1)==SCOPEOF||input.LA(1)==SELF||input.LA(1)==SHARED||(input.LA(1) >= SHORT && input.LA(1) <= SPAWN)||(input.LA(1) >= STATIC && input.LA(1) <= STATICASSERT)||input.LA(1)==STRUCT||(input.LA(1) >= SWITCH && input.LA(1) <= THREADLOCAL)||(input.LA(1) >= TRUE && input.LA(1) <= TYPEDEF)||(input.LA(1) >= UNIFORM && input.LA(1) <= UNSIGNED)||(input.LA(1) >= VOID && input.LA(1) <= WHILE)||input.LA(1)==ROOT ) {
				input.consume();
				adaptor.addChild(root_0, (Object)adaptor.create(set133));
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
	// $ANTLR end "c_keyword"


	public static class gnuc_keyword_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "gnuc_keyword"
	// PreprocessorParser.g:209:1: gnuc_keyword : TYPEOF ;
	public final PreprocessorParser.gnuc_keyword_return gnuc_keyword() throws RecognitionException {
		PreprocessorParser.gnuc_keyword_return retval = new PreprocessorParser.gnuc_keyword_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token TYPEOF134=null;

		Object TYPEOF134_tree=null;

		try {
			// PreprocessorParser.g:209:14: ( TYPEOF )
			// PreprocessorParser.g:209:16: TYPEOF
			{
			root_0 = (Object)adaptor.nil();


			TYPEOF134=(Token)match(input,TYPEOF,FOLLOW_TYPEOF_in_gnuc_keyword1594); 
			TYPEOF134_tree = (Object)adaptor.create(TYPEOF134);
			adaptor.addChild(root_0, TYPEOF134_tree);

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
	// $ANTLR end "gnuc_keyword"


	public static class punctuator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "punctuator"
	// PreprocessorParser.g:211:1: punctuator : ( nonPoundPunctuator | HASH );
	public final PreprocessorParser.punctuator_return punctuator() throws RecognitionException {
		PreprocessorParser.punctuator_return retval = new PreprocessorParser.punctuator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token HASH136=null;
		ParserRuleReturnScope nonPoundPunctuator135 =null;

		Object HASH136_tree=null;

		try {
			// PreprocessorParser.g:211:12: ( nonPoundPunctuator | HASH )
			int alt51=2;
			int LA51_0 = input.LA(1);
			if ( ((LA51_0 >= AMPERSAND && LA51_0 <= ASSIGN)||LA51_0==AT||(LA51_0 >= BITANDEQ && LA51_0 <= BITXOREQ)||(LA51_0 >= COLON && LA51_0 <= COMMA)||(LA51_0 >= DIV && LA51_0 <= DIVEQ)||(LA51_0 >= DOT && LA51_0 <= DOTDOT)||LA51_0==ELLIPSIS||LA51_0==EQUALS||(LA51_0 >= GT && LA51_0 <= GTE)||LA51_0==HASHHASH||LA51_0==IMPLIES||(LA51_0 >= LCURLY && LA51_0 <= LEXCON)||(LA51_0 >= LPAREN && LA51_0 <= LTE)||(LA51_0 >= MINUSMINUS && LA51_0 <= NEQ)||LA51_0==NOT||LA51_0==OR||(LA51_0 >= PLUS && LA51_0 <= PLUSPLUS)||LA51_0==QMARK||LA51_0==RCURLY||(LA51_0 >= REXCON && LA51_0 <= RSQUARE)||LA51_0==SEMI||(LA51_0 >= SHIFTLEFT && LA51_0 <= SHIFTRIGHTEQ)||(LA51_0 >= STAR && LA51_0 <= STAREQ)||(LA51_0 >= SUB && LA51_0 <= SUBEQ)||LA51_0==TILDE) ) {
				alt51=1;
			}
			else if ( (LA51_0==HASH) ) {
				alt51=2;
			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 51, 0, input);
				throw nvae;
			}

			switch (alt51) {
				case 1 :
					// PreprocessorParser.g:211:14: nonPoundPunctuator
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_nonPoundPunctuator_in_punctuator1602);
					nonPoundPunctuator135=nonPoundPunctuator();
					state._fsp--;

					adaptor.addChild(root_0, nonPoundPunctuator135.getTree());

					}
					break;
				case 2 :
					// PreprocessorParser.g:211:35: HASH
					{
					root_0 = (Object)adaptor.nil();


					HASH136=(Token)match(input,HASH,FOLLOW_HASH_in_punctuator1606); 
					HASH136_tree = (Object)adaptor.create(HASH136);
					adaptor.addChild(root_0, HASH136_tree);

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
	// $ANTLR end "punctuator"


	public static class pp_number_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "pp_number"
	// PreprocessorParser.g:214:1: pp_number : ( INTEGER_CONSTANT | FLOATING_CONSTANT | PP_NUMBER );
	public final PreprocessorParser.pp_number_return pp_number() throws RecognitionException {
		PreprocessorParser.pp_number_return retval = new PreprocessorParser.pp_number_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set137=null;

		Object set137_tree=null;

		try {
			// PreprocessorParser.g:214:11: ( INTEGER_CONSTANT | FLOATING_CONSTANT | PP_NUMBER )
			// PreprocessorParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set137=input.LT(1);
			if ( input.LA(1)==FLOATING_CONSTANT||input.LA(1)==INTEGER_CONSTANT||input.LA(1)==PP_NUMBER ) {
				input.consume();
				adaptor.addChild(root_0, (Object)adaptor.create(set137));
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
	// $ANTLR end "pp_number"


	public static class nonPoundPunctuator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "nonPoundPunctuator"
	// PreprocessorParser.g:217:1: nonPoundPunctuator : ( AMPERSAND | AND | ARROW | ASSIGN | AT | BITANDEQ | BITOR | BITOREQ | BITXOR | BITXOREQ | COLON | COMMA | DIV | DIVEQ | DOT | DOTDOT | ELLIPSIS | EQUALS | GT | GTE | HASHHASH | IMPLIES | LCURLY | LEXCON | LPAREN | LSLIST | LSQUARE | LT | LTE | MINUSMINUS | MOD | MODEQ | NEQ | NOT | OR | PLUS | PLUSEQ | PLUSPLUS | QMARK | RCURLY | REXCON | RPAREN | RSLIST | RSQUARE | SEMI | SHIFTLEFT | SHIFTLEFTEQ | SHIFTRIGHT | SHIFTRIGHTEQ | STAR | STAREQ | SUB | SUBEQ | TILDE );
	public final PreprocessorParser.nonPoundPunctuator_return nonPoundPunctuator() throws RecognitionException {
		PreprocessorParser.nonPoundPunctuator_return retval = new PreprocessorParser.nonPoundPunctuator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set138=null;

		Object set138_tree=null;

		try {
			// PreprocessorParser.g:218:3: ( AMPERSAND | AND | ARROW | ASSIGN | AT | BITANDEQ | BITOR | BITOREQ | BITXOR | BITXOREQ | COLON | COMMA | DIV | DIVEQ | DOT | DOTDOT | ELLIPSIS | EQUALS | GT | GTE | HASHHASH | IMPLIES | LCURLY | LEXCON | LPAREN | LSLIST | LSQUARE | LT | LTE | MINUSMINUS | MOD | MODEQ | NEQ | NOT | OR | PLUS | PLUSEQ | PLUSPLUS | QMARK | RCURLY | REXCON | RPAREN | RSLIST | RSQUARE | SEMI | SHIFTLEFT | SHIFTLEFTEQ | SHIFTRIGHT | SHIFTRIGHTEQ | STAR | STAREQ | SUB | SUBEQ | TILDE )
			// PreprocessorParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set138=input.LT(1);
			if ( (input.LA(1) >= AMPERSAND && input.LA(1) <= ASSIGN)||input.LA(1)==AT||(input.LA(1) >= BITANDEQ && input.LA(1) <= BITXOREQ)||(input.LA(1) >= COLON && input.LA(1) <= COMMA)||(input.LA(1) >= DIV && input.LA(1) <= DIVEQ)||(input.LA(1) >= DOT && input.LA(1) <= DOTDOT)||input.LA(1)==ELLIPSIS||input.LA(1)==EQUALS||(input.LA(1) >= GT && input.LA(1) <= GTE)||input.LA(1)==HASHHASH||input.LA(1)==IMPLIES||(input.LA(1) >= LCURLY && input.LA(1) <= LEXCON)||(input.LA(1) >= LPAREN && input.LA(1) <= LTE)||(input.LA(1) >= MINUSMINUS && input.LA(1) <= NEQ)||input.LA(1)==NOT||input.LA(1)==OR||(input.LA(1) >= PLUS && input.LA(1) <= PLUSPLUS)||input.LA(1)==QMARK||input.LA(1)==RCURLY||(input.LA(1) >= REXCON && input.LA(1) <= RSQUARE)||input.LA(1)==SEMI||(input.LA(1) >= SHIFTLEFT && input.LA(1) <= SHIFTRIGHTEQ)||(input.LA(1) >= STAR && input.LA(1) <= STAREQ)||(input.LA(1) >= SUB && input.LA(1) <= SUBEQ)||input.LA(1)==TILDE ) {
				input.consume();
				adaptor.addChild(root_0, (Object)adaptor.create(set138));
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
	// $ANTLR end "nonPoundPunctuator"

	// Delegated rules


	protected DFA12 dfa12 = new DFA12(this);
	protected DFA11 dfa11 = new DFA11(this);
	protected DFA18 dfa18 = new DFA18(this);
	static final String DFA12_eotS =
		"\4\uffff";
	static final String DFA12_eofS =
		"\4\uffff";
	static final String DFA12_minS =
		"\1\4\1\uffff\1\4\1\uffff";
	static final String DFA12_maxS =
		"\1\u00cc\1\uffff\1\u00cc\1\uffff";
	static final String DFA12_acceptS =
		"\1\uffff\1\1\1\uffff\1\2";
	static final String DFA12_specialS =
		"\4\uffff}>";
	static final String[] DFA12_transitionS = {
			"\23\1\1\uffff\2\1\1\uffff\11\1\1\2\5\1\1\uffff\12\1\3\uffff\7\1\2\uffff"+
			"\6\1\2\uffff\12\1\7\uffff\11\1\2\uffff\10\1\2\uffff\4\1\1\3\2\1\4\uffff"+
			"\3\1\3\uffff\1\1\12\uffff\4\1\1\uffff\1\1\1\uffff\20\1\1\uffff\35\1\2"+
			"\uffff\4\1\1\2\5\uffff\1\1",
			"",
			"\23\1\1\uffff\2\1\1\uffff\11\1\1\2\5\1\1\uffff\12\1\3\uffff\7\1\2\uffff"+
			"\6\1\2\uffff\12\1\7\uffff\11\1\2\uffff\10\1\2\uffff\4\1\1\3\2\1\4\uffff"+
			"\3\1\3\uffff\1\1\12\uffff\4\1\1\uffff\1\1\1\uffff\20\1\1\uffff\35\1\2"+
			"\uffff\4\1\1\2\5\uffff\1\1",
			""
	};

	static final short[] DFA12_eot = DFA.unpackEncodedString(DFA12_eotS);
	static final short[] DFA12_eof = DFA.unpackEncodedString(DFA12_eofS);
	static final char[] DFA12_min = DFA.unpackEncodedStringToUnsignedChars(DFA12_minS);
	static final char[] DFA12_max = DFA.unpackEncodedStringToUnsignedChars(DFA12_maxS);
	static final short[] DFA12_accept = DFA.unpackEncodedString(DFA12_acceptS);
	static final short[] DFA12_special = DFA.unpackEncodedString(DFA12_specialS);
	static final short[][] DFA12_transition;

	static {
		int numStates = DFA12_transitionS.length;
		DFA12_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA12_transition[i] = DFA.unpackEncodedString(DFA12_transitionS[i]);
		}
	}

	protected class DFA12 extends DFA {

		public DFA12(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 12;
			this.eot = DFA12_eot;
			this.eof = DFA12_eof;
			this.min = DFA12_min;
			this.max = DFA12_max;
			this.accept = DFA12_accept;
			this.special = DFA12_special;
			this.transition = DFA12_transition;
		}
		@Override
		public String getDescription() {
			return "101:17: ( (t+= wpptoken )* t+= pptoken )?";
		}
	}

	static final String DFA11_eotS =
		"\16\uffff";
	static final String DFA11_eofS =
		"\16\uffff";
	static final String DFA11_minS =
		"\13\4\1\uffff\1\4\1\uffff";
	static final String DFA11_maxS =
		"\13\u00cc\1\uffff\1\u00cc\1\uffff";
	static final String DFA11_acceptS =
		"\13\uffff\1\1\1\uffff\1\2";
	static final String DFA11_specialS =
		"\16\uffff}>";
	static final String[] DFA11_transitionS = {
			"\3\3\4\10\1\3\1\10\3\3\5\10\2\3\1\uffff\2\3\1\uffff\1\3\1\6\5\3\2\10"+
			"\1\13\5\3\1\uffff\3\3\2\10\2\3\2\10\1\3\3\uffff\1\10\3\3\1\10\2\3\2\uffff"+
			"\3\3\1\5\2\3\2\uffff\3\3\2\10\1\3\1\11\1\10\1\1\1\3\7\uffff\1\2\2\3\1"+
			"\10\3\3\1\5\1\3\2\uffff\2\10\1\3\5\10\2\uffff\4\10\1\uffff\1\3\1\10\4"+
			"\uffff\1\10\1\12\1\3\3\uffff\1\3\12\uffff\3\10\1\5\1\uffff\1\3\1\uffff"+
			"\1\3\1\10\1\3\1\10\7\3\4\10\1\3\1\uffff\1\3\1\10\1\3\4\10\4\3\2\10\2"+
			"\3\1\7\1\3\2\10\3\3\1\10\2\3\1\4\3\3\2\uffff\4\3\1\13\5\uffff\1\3",
			"\23\13\1\uffff\2\13\1\uffff\11\13\1\14\5\13\1\uffff\12\13\3\uffff\7"+
			"\13\2\uffff\6\13\2\uffff\12\13\7\uffff\11\13\2\uffff\10\13\2\uffff\4"+
			"\13\1\15\2\13\4\uffff\3\13\3\uffff\1\13\12\uffff\4\13\1\uffff\1\13\1"+
			"\uffff\20\13\1\uffff\35\13\2\uffff\4\13\1\14\5\uffff\1\13",
			"\23\13\1\uffff\2\13\1\uffff\11\13\1\14\5\13\1\uffff\12\13\3\uffff\7"+
			"\13\2\uffff\6\13\2\uffff\12\13\7\uffff\11\13\2\uffff\10\13\2\uffff\4"+
			"\13\1\15\2\13\4\uffff\3\13\3\uffff\1\13\12\uffff\4\13\1\uffff\1\13\1"+
			"\uffff\20\13\1\uffff\35\13\2\uffff\4\13\1\14\5\uffff\1\13",
			"\23\13\1\uffff\2\13\1\uffff\11\13\1\14\5\13\1\uffff\12\13\3\uffff\7"+
			"\13\2\uffff\6\13\2\uffff\12\13\7\uffff\11\13\2\uffff\10\13\2\uffff\4"+
			"\13\1\15\2\13\4\uffff\3\13\3\uffff\1\13\12\uffff\4\13\1\uffff\1\13\1"+
			"\uffff\20\13\1\uffff\35\13\2\uffff\4\13\1\14\5\uffff\1\13",
			"\23\13\1\uffff\2\13\1\uffff\11\13\1\14\5\13\1\uffff\12\13\3\uffff\7"+
			"\13\2\uffff\6\13\2\uffff\12\13\7\uffff\11\13\2\uffff\10\13\2\uffff\4"+
			"\13\1\15\2\13\4\uffff\3\13\3\uffff\1\13\12\uffff\4\13\1\uffff\1\13\1"+
			"\uffff\20\13\1\uffff\35\13\2\uffff\4\13\1\14\5\uffff\1\13",
			"\23\13\1\uffff\2\13\1\uffff\11\13\1\14\5\13\1\uffff\12\13\3\uffff\7"+
			"\13\2\uffff\6\13\2\uffff\12\13\7\uffff\11\13\2\uffff\10\13\2\uffff\4"+
			"\13\1\15\2\13\4\uffff\3\13\3\uffff\1\13\12\uffff\4\13\1\uffff\1\13\1"+
			"\uffff\20\13\1\uffff\35\13\2\uffff\4\13\1\14\5\uffff\1\13",
			"\23\13\1\uffff\2\13\1\uffff\11\13\1\14\5\13\1\uffff\12\13\3\uffff\7"+
			"\13\2\uffff\6\13\2\uffff\12\13\7\uffff\11\13\2\uffff\10\13\2\uffff\4"+
			"\13\1\15\2\13\4\uffff\3\13\3\uffff\1\13\12\uffff\4\13\1\uffff\1\13\1"+
			"\uffff\20\13\1\uffff\35\13\2\uffff\4\13\1\14\5\uffff\1\13",
			"\23\13\1\uffff\2\13\1\uffff\11\13\1\14\5\13\1\uffff\12\13\3\uffff\7"+
			"\13\2\uffff\6\13\2\uffff\12\13\7\uffff\11\13\2\uffff\10\13\2\uffff\4"+
			"\13\1\15\2\13\4\uffff\3\13\3\uffff\1\13\12\uffff\4\13\1\uffff\1\13\1"+
			"\uffff\20\13\1\uffff\35\13\2\uffff\4\13\1\14\5\uffff\1\13",
			"\23\13\1\uffff\2\13\1\uffff\11\13\1\14\5\13\1\uffff\12\13\3\uffff\7"+
			"\13\2\uffff\6\13\2\uffff\12\13\7\uffff\11\13\2\uffff\10\13\2\uffff\4"+
			"\13\1\15\2\13\4\uffff\3\13\3\uffff\1\13\12\uffff\4\13\1\uffff\1\13\1"+
			"\uffff\20\13\1\uffff\35\13\2\uffff\4\13\1\14\5\uffff\1\13",
			"\23\13\1\uffff\2\13\1\uffff\11\13\1\14\5\13\1\uffff\12\13\3\uffff\7"+
			"\13\2\uffff\6\13\2\uffff\12\13\7\uffff\11\13\2\uffff\10\13\2\uffff\4"+
			"\13\1\15\2\13\4\uffff\3\13\3\uffff\1\13\12\uffff\4\13\1\uffff\1\13\1"+
			"\uffff\20\13\1\uffff\35\13\2\uffff\4\13\1\14\5\uffff\1\13",
			"\23\13\1\uffff\2\13\1\uffff\11\13\1\14\5\13\1\uffff\12\13\3\uffff\7"+
			"\13\2\uffff\6\13\2\uffff\12\13\7\uffff\11\13\2\uffff\10\13\2\uffff\4"+
			"\13\1\15\2\13\4\uffff\3\13\3\uffff\1\13\12\uffff\4\13\1\uffff\1\13\1"+
			"\uffff\20\13\1\uffff\35\13\2\uffff\4\13\1\14\5\uffff\1\13",
			"",
			"\23\13\1\uffff\2\13\1\uffff\11\13\1\14\5\13\1\uffff\12\13\3\uffff\7"+
			"\13\2\uffff\6\13\2\uffff\12\13\7\uffff\11\13\2\uffff\10\13\2\uffff\4"+
			"\13\1\15\2\13\4\uffff\3\13\3\uffff\1\13\12\uffff\4\13\1\uffff\1\13\1"+
			"\uffff\20\13\1\uffff\35\13\2\uffff\4\13\1\14\5\uffff\1\13",
			""
	};

	static final short[] DFA11_eot = DFA.unpackEncodedString(DFA11_eotS);
	static final short[] DFA11_eof = DFA.unpackEncodedString(DFA11_eofS);
	static final char[] DFA11_min = DFA.unpackEncodedStringToUnsignedChars(DFA11_minS);
	static final char[] DFA11_max = DFA.unpackEncodedStringToUnsignedChars(DFA11_maxS);
	static final short[] DFA11_accept = DFA.unpackEncodedString(DFA11_acceptS);
	static final short[] DFA11_special = DFA.unpackEncodedString(DFA11_specialS);
	static final short[][] DFA11_transition;

	static {
		int numStates = DFA11_transitionS.length;
		DFA11_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA11_transition[i] = DFA.unpackEncodedString(DFA11_transitionS[i]);
		}
	}

	protected class DFA11 extends DFA {

		public DFA11(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 11;
			this.eot = DFA11_eot;
			this.eof = DFA11_eof;
			this.min = DFA11_min;
			this.max = DFA11_max;
			this.accept = DFA11_accept;
			this.special = DFA11_special;
			this.transition = DFA11_transition;
		}
		@Override
		public String getDescription() {
			return "()* loopback of 101:19: (t+= wpptoken )*";
		}
	}

	static final String DFA18_eotS =
		"\4\uffff";
	static final String DFA18_eofS =
		"\4\uffff";
	static final String DFA18_minS =
		"\2\43\2\uffff";
	static final String DFA18_maxS =
		"\2\u00c6\2\uffff";
	static final String DFA18_acceptS =
		"\2\uffff\1\2\1\1";
	static final String DFA18_specialS =
		"\4\uffff}>";
	static final String[] DFA18_transitionS = {
			"\1\3\1\1\171\uffff\1\2\47\uffff\1\1",
			"\1\3\1\1\171\uffff\1\2\47\uffff\1\1",
			"",
			""
	};

	static final short[] DFA18_eot = DFA.unpackEncodedString(DFA18_eotS);
	static final short[] DFA18_eof = DFA.unpackEncodedString(DFA18_eofS);
	static final char[] DFA18_min = DFA.unpackEncodedStringToUnsignedChars(DFA18_minS);
	static final char[] DFA18_max = DFA.unpackEncodedStringToUnsignedChars(DFA18_maxS);
	static final short[] DFA18_accept = DFA.unpackEncodedString(DFA18_acceptS);
	static final short[] DFA18_special = DFA.unpackEncodedString(DFA18_specialS);
	static final short[][] DFA18_transition;

	static {
		int numStates = DFA18_transitionS.length;
		DFA18_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA18_transition[i] = DFA.unpackEncodedString(DFA18_transitionS[i]);
		}
	}

	protected class DFA18 extends DFA {

		public DFA18(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 18;
			this.eot = DFA18_eot;
			this.eof = DFA18_eof;
			this.min = DFA18_min;
			this.max = DFA18_max;
			this.accept = DFA18_accept;
			this.special = DFA18_special;
			this.transition = DFA18_transition;
		}
		@Override
		public String getDescription() {
			return "()* loopback of 110:17: ( ( white )* COMMA ( white )* identifier )*";
		}
	}

	public static final BitSet FOLLOW_block_in_file120 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_directive_in_block143 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF2L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFFFFE3L,0x000000000000107CL});
	public static final BitSet FOLLOW_textblock_in_block147 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF2L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFFFFE3L,0x000000000000107CL});
	public static final BitSet FOLLOW_macrodef_in_directive160 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_macroundef_in_directive166 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_includeline_in_directive172 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_pragmaline_in_directive178 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ifblock_in_directive184 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ifdefblock_in_directive190 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ifndefblock_in_directive196 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_errorline_in_directive202 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_lineline_in_directive208 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_nondirectiveline_in_directive214 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_textline_in_textblock238 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF2L,0x1C3F9FE7FC077E7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_white_in_textline262 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC077E7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_nonPoundPpToken_in_textline266 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_wpptoken_in_textline268 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_lineend_in_textline273 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_pptoken_in_wpptoken296 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_white_in_wpptoken300 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NEWLINE_in_lineend310 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PDEFINE_in_macrodef319 = new BitSet(new long[]{0x0000001000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_white_in_macrodef321 = new BitSet(new long[]{0x6E133BF3EB60E870L,0x10100085DC044E6EL,0xFDCB3C2A1FD50001L,0x000000000000107CL});
	public static final BitSet FOLLOW_identifier_in_macrodef326 = new BitSet(new long[]{0x0000001000000000L,0x0008010000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_paramlist_in_macrodef333 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_macrobody_in_macrodef335 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_lineend_in_macrodef355 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_white_in_macrodef375 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_macrobody_in_macrodef377 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_white_in_macrobody404 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_pptoken_in_macrobody415 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_wpptoken_in_macrobody420 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C379FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_pptoken_in_macrobody425 = new BitSet(new long[]{0x0000001000000000L,0x0008000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_white_in_macrobody429 = new BitSet(new long[]{0x0000001000000000L,0x0008000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_lineend_in_macrobody432 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_lineend_in_macrobody454 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_paramlist481 = new BitSet(new long[]{0x6E133BF3EB60E870L,0x10100085DC044E6EL,0xFDCB3C2A5FD50001L,0x000000000000107CL});
	public static final BitSet FOLLOW_white_in_paramlist483 = new BitSet(new long[]{0x6E133BF3EB60E870L,0x10100085DC044E6EL,0xFDCB3C2A5FD50001L,0x000000000000107CL});
	public static final BitSet FOLLOW_RPAREN_in_paramlist492 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_identifier_in_paramlist505 = new BitSet(new long[]{0x0000001800000000L,0x0000000000000000L,0x0000000040000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_white_in_paramlist508 = new BitSet(new long[]{0x0000001800000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_COMMA_in_paramlist511 = new BitSet(new long[]{0x6E133BF3EB60E870L,0x10100085DC044E6EL,0xFDCB3C2A1FD50001L,0x000000000000107CL});
	public static final BitSet FOLLOW_white_in_paramlist513 = new BitSet(new long[]{0x6E133BF3EB60E870L,0x10100085DC044E6EL,0xFDCB3C2A1FD50001L,0x000000000000107CL});
	public static final BitSet FOLLOW_identifier_in_paramlist516 = new BitSet(new long[]{0x0000001800000000L,0x0000000000000000L,0x0000000040000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_white_in_paramlist520 = new BitSet(new long[]{0x0000001000000000L,0x0000000000000000L,0x0000000040000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_RPAREN_in_paramlist523 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PUNDEF_in_macroundef553 = new BitSet(new long[]{0x0000001000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_white_in_macroundef555 = new BitSet(new long[]{0x6E133BF3EB60E870L,0x10100085DC044E6EL,0xFDCB3C2A1FD50001L,0x000000000000107CL});
	public static final BitSet FOLLOW_identifier_in_macroundef558 = new BitSet(new long[]{0x0000001000000000L,0x0008000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_white_in_macroundef560 = new BitSet(new long[]{0x0000001000000000L,0x0008000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_lineend_in_macroundef563 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PINCLUDE_in_includeline585 = new BitSet(new long[]{0x0000001000000000L,0x0000000000020000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_white_in_includeline587 = new BitSet(new long[]{0x0000001000000000L,0x0000000000020000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_HEADER_NAME_in_includeline590 = new BitSet(new long[]{0x0000001000000000L,0x0008000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_white_in_includeline592 = new BitSet(new long[]{0x0000001000000000L,0x0008000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_lineend_in_includeline595 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PIF_in_ifblock619 = new BitSet(new long[]{0x7F1FFFFFFB7FFFF0L,0x1C379FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_white_in_ifblock621 = new BitSet(new long[]{0x7F1FFFFFFB7FFFF0L,0x1C379FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_expr_in_ifblock624 = new BitSet(new long[]{0x0000000000000000L,0x0008000000000000L});
	public static final BitSet FOLLOW_lineend_in_ifblock626 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFFFFFFL,0x000000000000107CL});
	public static final BitSet FOLLOW_block_in_ifblock628 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x000000000000001CL});
	public static final BitSet FOLLOW_elseblock_in_ifblock630 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_endifline_in_ifblock633 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ppdExpr_in_expr668 = new BitSet(new long[]{0x7F1FFFFFFB7FFFF2L,0x1C379FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_ppdExpr_in_expr671 = new BitSet(new long[]{0x7F1FFFFFFB7FFFF2L,0x1C379FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_white_in_expr675 = new BitSet(new long[]{0x7F1FFFFFFB7FFFF2L,0x1C379FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_DEFINED_in_definedExpr695 = new BitSet(new long[]{0x6E133BE3EB60E870L,0x10100185DC044E6EL,0xFDCB3C2A1FD50001L,0x000000000000107CL});
	public static final BitSet FOLLOW_WS_in_definedExpr697 = new BitSet(new long[]{0x6E133BE3EB60E870L,0x10100185DC044E6EL,0xFDCB3C2A1FD50001L,0x000000000000107CL});
	public static final BitSet FOLLOW_identifier_in_definedExpr706 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_definedExpr713 = new BitSet(new long[]{0x6E133BE3EB60E870L,0x10100085DC044E6EL,0xFDCB3C2A1FD50001L,0x000000000000107CL});
	public static final BitSet FOLLOW_WS_in_definedExpr716 = new BitSet(new long[]{0x6E133BE3EB60E870L,0x10100085DC044E6EL,0xFDCB3C2A1FD50001L,0x000000000000107CL});
	public static final BitSet FOLLOW_identifier_in_definedExpr720 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_WS_in_definedExpr722 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_RPAREN_in_definedExpr726 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_pptoken_in_ppdExpr747 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_definedExpr_in_ppdExpr751 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_simpleelseblock_in_elseblock760 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_elifblock_in_elseblock764 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PELSE_in_simpleelseblock773 = new BitSet(new long[]{0x0000001000000000L,0x0008000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_white_in_simpleelseblock775 = new BitSet(new long[]{0x0000001000000000L,0x0008000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_lineend_in_simpleelseblock778 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFFFFE3L,0x000000000000107CL});
	public static final BitSet FOLLOW_block_in_simpleelseblock780 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PELIF_in_elifblock800 = new BitSet(new long[]{0x7F1FFFFFFB7FFFF0L,0x1C379FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_white_in_elifblock802 = new BitSet(new long[]{0x7F1FFFFFFB7FFFF0L,0x1C379FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_expr_in_elifblock805 = new BitSet(new long[]{0x0000000000000000L,0x0008000000000000L});
	public static final BitSet FOLLOW_lineend_in_elifblock807 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFFFFEFL,0x000000000000107CL});
	public static final BitSet FOLLOW_block_in_elifblock809 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x000000000000000CL});
	public static final BitSet FOLLOW_elseblock_in_elifblock811 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PIFDEF_in_ifdefblock854 = new BitSet(new long[]{0x6E133BF3EB60E870L,0x10100085DC044E6EL,0xFDCB3C2A1FD50001L,0x000000000000107CL});
	public static final BitSet FOLLOW_white_in_ifdefblock856 = new BitSet(new long[]{0x6E133BF3EB60E870L,0x10100085DC044E6EL,0xFDCB3C2A1FD50001L,0x000000000000107CL});
	public static final BitSet FOLLOW_identifier_in_ifdefblock859 = new BitSet(new long[]{0x0000001000000000L,0x0008000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_white_in_ifdefblock861 = new BitSet(new long[]{0x0000001000000000L,0x0008000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_lineend_in_ifdefblock864 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFFFFFFL,0x000000000000107CL});
	public static final BitSet FOLLOW_block_in_ifdefblock869 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x000000000000001CL});
	public static final BitSet FOLLOW_elseblock_in_ifdefblock871 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_endifline_in_ifdefblock874 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PIFNDEF_in_ifndefblock906 = new BitSet(new long[]{0x6E133BF3EB60E870L,0x10100085DC044E6EL,0xFDCB3C2A1FD50001L,0x000000000000107CL});
	public static final BitSet FOLLOW_white_in_ifndefblock908 = new BitSet(new long[]{0x6E133BF3EB60E870L,0x10100085DC044E6EL,0xFDCB3C2A1FD50001L,0x000000000000107CL});
	public static final BitSet FOLLOW_identifier_in_ifndefblock911 = new BitSet(new long[]{0x0000001000000000L,0x0008000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_white_in_ifndefblock913 = new BitSet(new long[]{0x0000001000000000L,0x0008000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_lineend_in_ifndefblock916 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFFFFFFL,0x000000000000107CL});
	public static final BitSet FOLLOW_block_in_ifndefblock921 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x000000000000001CL});
	public static final BitSet FOLLOW_elseblock_in_ifndefblock923 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_endifline_in_ifndefblock926 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PENDIF_in_endifline957 = new BitSet(new long[]{0x0000001000000000L,0x0008000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_white_in_endifline959 = new BitSet(new long[]{0x0000001000000000L,0x0008000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_lineend_in_endifline962 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PRAGMA_in_pragmaline971 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_wpptoken_in_pragmaline973 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_lineend_in_pragmaline976 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PERROR_in_errorline996 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_wpptoken_in_errorline998 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_lineend_in_errorline1001 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PLINE_in_lineline1019 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_wpptoken_in_lineline1021 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_lineend_in_lineline1024 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_HASH_in_nondirectiveline1044 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_wpptoken_in_nondirectiveline1046 = new BitSet(new long[]{0x7F1FFBFFFB7FFFF0L,0x1C3F9FE7FC07FE7EL,0xFFFFFFFBFFFD7801L,0x000000000000107CL});
	public static final BitSet FOLLOW_lineend_in_nondirectiveline1049 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_HEADER_NAME_in_pptoken1070 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_identifier_in_pptoken1076 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_pp_number_in_pptoken1082 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_pptoken1088 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_pptoken1094 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_punctuator_in_pptoken1100 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_OTHER_in_pptoken1106 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_HEADER_NAME_in_nonPoundPpToken1119 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_identifier_in_nonPoundPpToken1125 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_pp_number_in_nonPoundPpToken1131 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_nonPoundPpToken1137 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_nonPoundPpToken1143 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_nonPoundPunctuator_in_nonPoundPpToken1149 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_OTHER_in_nonPoundPpToken1155 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENTIFIER_in_identifier1173 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_c_keyword_in_identifier1177 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_gnuc_keyword_in_identifier1181 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_TYPEOF_in_gnuc_keyword1594 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_nonPoundPunctuator_in_punctuator1602 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_HASH_in_punctuator1606 = new BitSet(new long[]{0x0000000000000002L});
}
