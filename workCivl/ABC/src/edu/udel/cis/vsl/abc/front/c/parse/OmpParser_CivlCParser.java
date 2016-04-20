// $ANTLR 3.5.2 CivlCParser.g 2016-04-11 02:06:33

package edu.udel.cis.vsl.abc.front.c.parse;

import java.util.Set;
import java.util.HashSet;
import edu.udel.cis.vsl.abc.front.IF.RuntimeParseException;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;

import org.antlr.runtime.tree.*;


@SuppressWarnings("all")
public class OmpParser_CivlCParser extends Parser {
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
	public Parser[] getDelegates() {
		return new Parser[] {};
	}

	// delegators
	public OmpParser gOmpParser;
	public OmpParser gParent;

	protected static class Symbols_scope {
		Set<String> types;
		Set<String> enumerationConstants;
		boolean isFunctionDefinition;
	}
	protected Stack<Symbols_scope> Symbols_stack = new Stack<Symbols_scope>();

	protected static class DeclarationScope_scope {
		boolean isTypedef;
		boolean typedefNameUsed;
	}
	protected Stack<DeclarationScope_scope> DeclarationScope_stack = new Stack<DeclarationScope_scope>();


	public OmpParser_CivlCParser(TokenStream input, OmpParser gOmpParser) {
		this(input, new RecognizerSharedState(), gOmpParser);
	}
	public OmpParser_CivlCParser(TokenStream input, RecognizerSharedState state, OmpParser gOmpParser) {
		super(input, state);
		this.gOmpParser = gOmpParser;
		gParent = gOmpParser;
	}

	protected TreeAdaptor adaptor = new CommonTreeAdaptor();

	public void setTreeAdaptor(TreeAdaptor adaptor) {
		this.adaptor = adaptor;
	}
	public TreeAdaptor getTreeAdaptor() {
		return adaptor;
	}
	@Override public String[] getTokenNames() { return OmpParser.tokenNames; }
	@Override public String getGrammarFileName() { return "CivlCParser.g"; }


		public void setSymbols_stack(Stack<ScopeSymbols> symbols){
			this.Symbols_stack = new Stack();
			while(!symbols.isEmpty()){
				ScopeSymbols current = symbols.pop();
				Symbols_scope mySymbols = new Symbols_scope();

				mySymbols.types = current.types;
				mySymbols.enumerationConstants = current.enumerationConstants;
				Symbols_stack.add(mySymbols);
			}
		}

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

		boolean isTypeName(String name) {
			for (Object scope : Symbols_stack)
				if (((Symbols_scope)scope).types.contains(name)) return true;
			return false;
		}

		boolean isEnumerationConstant(String name) {
			boolean answer = false;
			
			// System.err.print("Is "+name+" an enumeration constant: ");
			for (Object scope : Symbols_stack) {
				if (((Symbols_scope)scope).enumerationConstants.contains(name)) {
					answer=true;
					break;
				}
			}
			// System.err.println(answer);
			// System.err.flush();
			return answer;
		}	


	public static class constant_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "constant"
	// CivlCParser.g:167:1: constant : ( enumerationConstant | INTEGER_CONSTANT | FLOATING_CONSTANT | CHARACTER_CONSTANT | SELF | PROCNULL | TRUE | FALSE | RESULT | HERE | ROOT | ELLIPSIS );
	public final OmpParser_CivlCParser.constant_return constant() throws RecognitionException {
		OmpParser_CivlCParser.constant_return retval = new OmpParser_CivlCParser.constant_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token INTEGER_CONSTANT2=null;
		Token FLOATING_CONSTANT3=null;
		Token CHARACTER_CONSTANT4=null;
		Token SELF5=null;
		Token PROCNULL6=null;
		Token TRUE7=null;
		Token FALSE8=null;
		Token RESULT9=null;
		Token HERE10=null;
		Token ROOT11=null;
		Token ELLIPSIS12=null;
		ParserRuleReturnScope enumerationConstant1 =null;

		Object INTEGER_CONSTANT2_tree=null;
		Object FLOATING_CONSTANT3_tree=null;
		Object CHARACTER_CONSTANT4_tree=null;
		Object SELF5_tree=null;
		Object PROCNULL6_tree=null;
		Object TRUE7_tree=null;
		Object FALSE8_tree=null;
		Object RESULT9_tree=null;
		Object HERE10_tree=null;
		Object ROOT11_tree=null;
		Object ELLIPSIS12_tree=null;

		try {
			// CivlCParser.g:168:2: ( enumerationConstant | INTEGER_CONSTANT | FLOATING_CONSTANT | CHARACTER_CONSTANT | SELF | PROCNULL | TRUE | FALSE | RESULT | HERE | ROOT | ELLIPSIS )
			int alt1=12;
			switch ( input.LA(1) ) {
			case IDENTIFIER:
				{
				alt1=1;
				}
				break;
			case INTEGER_CONSTANT:
				{
				alt1=2;
				}
				break;
			case FLOATING_CONSTANT:
				{
				alt1=3;
				}
				break;
			case CHARACTER_CONSTANT:
				{
				alt1=4;
				}
				break;
			case SELF:
				{
				alt1=5;
				}
				break;
			case PROCNULL:
				{
				alt1=6;
				}
				break;
			case TRUE:
				{
				alt1=7;
				}
				break;
			case FALSE:
				{
				alt1=8;
				}
				break;
			case RESULT:
				{
				alt1=9;
				}
				break;
			case HERE:
				{
				alt1=10;
				}
				break;
			case ROOT:
				{
				alt1=11;
				}
				break;
			case ELLIPSIS:
				{
				alt1=12;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 1, 0, input);
				throw nvae;
			}
			switch (alt1) {
				case 1 :
					// CivlCParser.g:168:4: enumerationConstant
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_enumerationConstant_in_constant997);
					enumerationConstant1=enumerationConstant();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, enumerationConstant1.getTree());

					}
					break;
				case 2 :
					// CivlCParser.g:169:4: INTEGER_CONSTANT
					{
					root_0 = (Object)adaptor.nil();


					INTEGER_CONSTANT2=(Token)match(input,INTEGER_CONSTANT,FOLLOW_INTEGER_CONSTANT_in_constant1002); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INTEGER_CONSTANT2_tree = (Object)adaptor.create(INTEGER_CONSTANT2);
					adaptor.addChild(root_0, INTEGER_CONSTANT2_tree);
					}

					}
					break;
				case 3 :
					// CivlCParser.g:170:4: FLOATING_CONSTANT
					{
					root_0 = (Object)adaptor.nil();


					FLOATING_CONSTANT3=(Token)match(input,FLOATING_CONSTANT,FOLLOW_FLOATING_CONSTANT_in_constant1007); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					FLOATING_CONSTANT3_tree = (Object)adaptor.create(FLOATING_CONSTANT3);
					adaptor.addChild(root_0, FLOATING_CONSTANT3_tree);
					}

					}
					break;
				case 4 :
					// CivlCParser.g:171:4: CHARACTER_CONSTANT
					{
					root_0 = (Object)adaptor.nil();


					CHARACTER_CONSTANT4=(Token)match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_constant1012); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					CHARACTER_CONSTANT4_tree = (Object)adaptor.create(CHARACTER_CONSTANT4);
					adaptor.addChild(root_0, CHARACTER_CONSTANT4_tree);
					}

					}
					break;
				case 5 :
					// CivlCParser.g:172:4: SELF
					{
					root_0 = (Object)adaptor.nil();


					SELF5=(Token)match(input,SELF,FOLLOW_SELF_in_constant1017); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					SELF5_tree = (Object)adaptor.create(SELF5);
					adaptor.addChild(root_0, SELF5_tree);
					}

					}
					break;
				case 6 :
					// CivlCParser.g:172:11: PROCNULL
					{
					root_0 = (Object)adaptor.nil();


					PROCNULL6=(Token)match(input,PROCNULL,FOLLOW_PROCNULL_in_constant1021); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					PROCNULL6_tree = (Object)adaptor.create(PROCNULL6);
					adaptor.addChild(root_0, PROCNULL6_tree);
					}

					}
					break;
				case 7 :
					// CivlCParser.g:172:22: TRUE
					{
					root_0 = (Object)adaptor.nil();


					TRUE7=(Token)match(input,TRUE,FOLLOW_TRUE_in_constant1025); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					TRUE7_tree = (Object)adaptor.create(TRUE7);
					adaptor.addChild(root_0, TRUE7_tree);
					}

					}
					break;
				case 8 :
					// CivlCParser.g:172:29: FALSE
					{
					root_0 = (Object)adaptor.nil();


					FALSE8=(Token)match(input,FALSE,FOLLOW_FALSE_in_constant1029); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					FALSE8_tree = (Object)adaptor.create(FALSE8);
					adaptor.addChild(root_0, FALSE8_tree);
					}

					}
					break;
				case 9 :
					// CivlCParser.g:172:37: RESULT
					{
					root_0 = (Object)adaptor.nil();


					RESULT9=(Token)match(input,RESULT,FOLLOW_RESULT_in_constant1033); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					RESULT9_tree = (Object)adaptor.create(RESULT9);
					adaptor.addChild(root_0, RESULT9_tree);
					}

					}
					break;
				case 10 :
					// CivlCParser.g:173:4: HERE
					{
					root_0 = (Object)adaptor.nil();


					HERE10=(Token)match(input,HERE,FOLLOW_HERE_in_constant1038); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					HERE10_tree = (Object)adaptor.create(HERE10);
					adaptor.addChild(root_0, HERE10_tree);
					}

					}
					break;
				case 11 :
					// CivlCParser.g:173:11: ROOT
					{
					root_0 = (Object)adaptor.nil();


					ROOT11=(Token)match(input,ROOT,FOLLOW_ROOT_in_constant1042); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ROOT11_tree = (Object)adaptor.create(ROOT11);
					adaptor.addChild(root_0, ROOT11_tree);
					}

					}
					break;
				case 12 :
					// CivlCParser.g:173:18: ELLIPSIS
					{
					root_0 = (Object)adaptor.nil();


					ELLIPSIS12=(Token)match(input,ELLIPSIS,FOLLOW_ELLIPSIS_in_constant1046); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ELLIPSIS12_tree = (Object)adaptor.create(ELLIPSIS12);
					adaptor.addChild(root_0, ELLIPSIS12_tree);
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "constant"


	public static class enumerationConstant_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "enumerationConstant"
	// CivlCParser.g:176:1: enumerationConstant :{...}? IDENTIFIER -> ^( ENUMERATION_CONSTANT IDENTIFIER ) ;
	public final OmpParser_CivlCParser.enumerationConstant_return enumerationConstant() throws RecognitionException {
		OmpParser_CivlCParser.enumerationConstant_return retval = new OmpParser_CivlCParser.enumerationConstant_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token IDENTIFIER13=null;

		Object IDENTIFIER13_tree=null;
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");

		try {
			// CivlCParser.g:177:2: ({...}? IDENTIFIER -> ^( ENUMERATION_CONSTANT IDENTIFIER ) )
			// CivlCParser.g:177:4: {...}? IDENTIFIER
			{
			if ( !((isEnumerationConstant(input.LT(1).getText()))) ) {
				if (state.backtracking>0) {state.failed=true; return retval;}
				throw new FailedPredicateException(input, "enumerationConstant", "isEnumerationConstant(input.LT(1).getText())");
			}
			IDENTIFIER13=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_enumerationConstant1059); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER13);

			// AST REWRITE
			// elements: IDENTIFIER
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 177:63: -> ^( ENUMERATION_CONSTANT IDENTIFIER )
			{
				// CivlCParser.g:178:4: ^( ENUMERATION_CONSTANT IDENTIFIER )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ENUMERATION_CONSTANT, "ENUMERATION_CONSTANT"), root_1);
				adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "enumerationConstant"


	public static class primaryExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "primaryExpression"
	// CivlCParser.g:182:1: primaryExpression : ( constant | IDENTIFIER | STRING_LITERAL | LPAREN compoundStatement RPAREN -> ^( STATEMENT_EXPRESSION LPAREN compoundStatement RPAREN ) | LPAREN expression RPAREN -> ^( PARENTHESIZED_EXPRESSION LPAREN expression RPAREN ) | genericSelection | derivativeExpression );
	public final OmpParser_CivlCParser.primaryExpression_return primaryExpression() throws RecognitionException {
		OmpParser_CivlCParser.primaryExpression_return retval = new OmpParser_CivlCParser.primaryExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token IDENTIFIER15=null;
		Token STRING_LITERAL16=null;
		Token LPAREN17=null;
		Token RPAREN19=null;
		Token LPAREN20=null;
		Token RPAREN22=null;
		ParserRuleReturnScope constant14 =null;
		ParserRuleReturnScope compoundStatement18 =null;
		ParserRuleReturnScope expression21 =null;
		ParserRuleReturnScope genericSelection23 =null;
		ParserRuleReturnScope derivativeExpression24 =null;

		Object IDENTIFIER15_tree=null;
		Object STRING_LITERAL16_tree=null;
		Object LPAREN17_tree=null;
		Object RPAREN19_tree=null;
		Object LPAREN20_tree=null;
		Object RPAREN22_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_compoundStatement=new RewriteRuleSubtreeStream(adaptor,"rule compoundStatement");

		try {
			// CivlCParser.g:183:2: ( constant | IDENTIFIER | STRING_LITERAL | LPAREN compoundStatement RPAREN -> ^( STATEMENT_EXPRESSION LPAREN compoundStatement RPAREN ) | LPAREN expression RPAREN -> ^( PARENTHESIZED_EXPRESSION LPAREN expression RPAREN ) | genericSelection | derivativeExpression )
			int alt2=7;
			switch ( input.LA(1) ) {
			case IDENTIFIER:
				{
				int LA2_1 = input.LA(2);
				if ( ((isEnumerationConstant(input.LT(1).getText()))) ) {
					alt2=1;
				}
				else if ( (true) ) {
					alt2=2;
				}

				}
				break;
			case CHARACTER_CONSTANT:
			case ELLIPSIS:
			case FALSE:
			case FLOATING_CONSTANT:
			case HERE:
			case INTEGER_CONSTANT:
			case PROCNULL:
			case RESULT:
			case SELF:
			case TRUE:
			case ROOT:
				{
				alt2=1;
				}
				break;
			case STRING_LITERAL:
				{
				alt2=3;
				}
				break;
			case LPAREN:
				{
				int LA2_4 = input.LA(2);
				if ( (LA2_4==LCURLY) ) {
					alt2=4;
				}
				else if ( ((LA2_4 >= ALIGNOF && LA2_4 <= AMPERSAND)||LA2_4==BIG_O||LA2_4==CALLS||LA2_4==CHARACTER_CONSTANT||LA2_4==COLLECTIVE||LA2_4==DERIV||LA2_4==ELLIPSIS||LA2_4==EXISTS||LA2_4==FALSE||LA2_4==FLOATING_CONSTANT||LA2_4==FORALL||LA2_4==GENERIC||LA2_4==HERE||LA2_4==IDENTIFIER||LA2_4==INTEGER_CONSTANT||LA2_4==LPAREN||LA2_4==MINUSMINUS||LA2_4==NOT||LA2_4==PLUS||LA2_4==PLUSPLUS||LA2_4==PROCNULL||LA2_4==RESULT||LA2_4==SCOPEOF||LA2_4==SELF||(LA2_4 >= SIZEOF && LA2_4 <= STAR)||LA2_4==STRING_LITERAL||LA2_4==SUB||(LA2_4 >= TILDE && LA2_4 <= TRUE)||LA2_4==UNIFORM||LA2_4==ROOT) ) {
					alt2=5;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 2, 4, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case GENERIC:
				{
				alt2=6;
				}
				break;
			case DERIV:
				{
				alt2=7;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 2, 0, input);
				throw nvae;
			}
			switch (alt2) {
				case 1 :
					// CivlCParser.g:183:4: constant
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_constant_in_primaryExpression1083);
					constant14=constant();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, constant14.getTree());

					}
					break;
				case 2 :
					// CivlCParser.g:184:4: IDENTIFIER
					{
					root_0 = (Object)adaptor.nil();


					IDENTIFIER15=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_primaryExpression1088); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					IDENTIFIER15_tree = (Object)adaptor.create(IDENTIFIER15);
					adaptor.addChild(root_0, IDENTIFIER15_tree);
					}

					}
					break;
				case 3 :
					// CivlCParser.g:185:4: STRING_LITERAL
					{
					root_0 = (Object)adaptor.nil();


					STRING_LITERAL16=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_primaryExpression1093); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					STRING_LITERAL16_tree = (Object)adaptor.create(STRING_LITERAL16);
					adaptor.addChild(root_0, STRING_LITERAL16_tree);
					}

					}
					break;
				case 4 :
					// CivlCParser.g:186:7: LPAREN compoundStatement RPAREN
					{
					LPAREN17=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_primaryExpression1101); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN17);

					pushFollow(FOLLOW_compoundStatement_in_primaryExpression1103);
					compoundStatement18=compoundStatement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_compoundStatement.add(compoundStatement18.getTree());
					RPAREN19=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_primaryExpression1105); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN19);

					// AST REWRITE
					// elements: LPAREN, RPAREN, compoundStatement
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 187:7: -> ^( STATEMENT_EXPRESSION LPAREN compoundStatement RPAREN )
					{
						// CivlCParser.g:187:10: ^( STATEMENT_EXPRESSION LPAREN compoundStatement RPAREN )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STATEMENT_EXPRESSION, "STATEMENT_EXPRESSION"), root_1);
						adaptor.addChild(root_1, stream_LPAREN.nextNode());
						adaptor.addChild(root_1, stream_compoundStatement.nextTree());
						adaptor.addChild(root_1, stream_RPAREN.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 5 :
					// CivlCParser.g:188:4: LPAREN expression RPAREN
					{
					LPAREN20=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_primaryExpression1128); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN20);

					pushFollow(FOLLOW_expression_in_primaryExpression1130);
					expression21=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression21.getTree());
					RPAREN22=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_primaryExpression1132); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN22);

					// AST REWRITE
					// elements: RPAREN, LPAREN, expression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 189:4: -> ^( PARENTHESIZED_EXPRESSION LPAREN expression RPAREN )
					{
						// CivlCParser.g:189:7: ^( PARENTHESIZED_EXPRESSION LPAREN expression RPAREN )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(PARENTHESIZED_EXPRESSION, "PARENTHESIZED_EXPRESSION"), root_1);
						adaptor.addChild(root_1, stream_LPAREN.nextNode());
						adaptor.addChild(root_1, stream_expression.nextTree());
						adaptor.addChild(root_1, stream_RPAREN.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 6 :
					// CivlCParser.g:190:4: genericSelection
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_genericSelection_in_primaryExpression1153);
					genericSelection23=genericSelection();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, genericSelection23.getTree());

					}
					break;
				case 7 :
					// CivlCParser.g:191:4: derivativeExpression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_derivativeExpression_in_primaryExpression1158);
					derivativeExpression24=derivativeExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, derivativeExpression24.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "primaryExpression"


	public static class genericSelection_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "genericSelection"
	// CivlCParser.g:195:1: genericSelection : GENERIC LPAREN assignmentExpression COMMA genericAssocList RPAREN -> ^( GENERIC assignmentExpression genericAssocList ) ;
	public final OmpParser_CivlCParser.genericSelection_return genericSelection() throws RecognitionException {
		OmpParser_CivlCParser.genericSelection_return retval = new OmpParser_CivlCParser.genericSelection_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token GENERIC25=null;
		Token LPAREN26=null;
		Token COMMA28=null;
		Token RPAREN30=null;
		ParserRuleReturnScope assignmentExpression27 =null;
		ParserRuleReturnScope genericAssocList29 =null;

		Object GENERIC25_tree=null;
		Object LPAREN26_tree=null;
		Object COMMA28_tree=null;
		Object RPAREN30_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_GENERIC=new RewriteRuleTokenStream(adaptor,"token GENERIC");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_genericAssocList=new RewriteRuleSubtreeStream(adaptor,"rule genericAssocList");
		RewriteRuleSubtreeStream stream_assignmentExpression=new RewriteRuleSubtreeStream(adaptor,"rule assignmentExpression");

		try {
			// CivlCParser.g:196:2: ( GENERIC LPAREN assignmentExpression COMMA genericAssocList RPAREN -> ^( GENERIC assignmentExpression genericAssocList ) )
			// CivlCParser.g:196:4: GENERIC LPAREN assignmentExpression COMMA genericAssocList RPAREN
			{
			GENERIC25=(Token)match(input,GENERIC,FOLLOW_GENERIC_in_genericSelection1171); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_GENERIC.add(GENERIC25);

			LPAREN26=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_genericSelection1173); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN26);

			pushFollow(FOLLOW_assignmentExpression_in_genericSelection1175);
			assignmentExpression27=assignmentExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression27.getTree());
			COMMA28=(Token)match(input,COMMA,FOLLOW_COMMA_in_genericSelection1177); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_COMMA.add(COMMA28);

			pushFollow(FOLLOW_genericAssocList_in_genericSelection1179);
			genericAssocList29=genericAssocList();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_genericAssocList.add(genericAssocList29.getTree());
			RPAREN30=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_genericSelection1184); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN30);

			// AST REWRITE
			// elements: genericAssocList, assignmentExpression, GENERIC
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 198:4: -> ^( GENERIC assignmentExpression genericAssocList )
			{
				// CivlCParser.g:198:7: ^( GENERIC assignmentExpression genericAssocList )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_GENERIC.nextNode(), root_1);
				adaptor.addChild(root_1, stream_assignmentExpression.nextTree());
				adaptor.addChild(root_1, stream_genericAssocList.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "genericSelection"


	public static class derivativeExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "derivativeExpression"
	// CivlCParser.g:204:1: derivativeExpression : DERIV LSQUARE IDENTIFIER COMMA partialList RSQUARE LPAREN argumentExpressionList RPAREN -> ^( DERIVATIVE_EXPRESSION IDENTIFIER partialList argumentExpressionList RPAREN ) ;
	public final OmpParser_CivlCParser.derivativeExpression_return derivativeExpression() throws RecognitionException {
		OmpParser_CivlCParser.derivativeExpression_return retval = new OmpParser_CivlCParser.derivativeExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token DERIV31=null;
		Token LSQUARE32=null;
		Token IDENTIFIER33=null;
		Token COMMA34=null;
		Token RSQUARE36=null;
		Token LPAREN37=null;
		Token RPAREN39=null;
		ParserRuleReturnScope partialList35 =null;
		ParserRuleReturnScope argumentExpressionList38 =null;

		Object DERIV31_tree=null;
		Object LSQUARE32_tree=null;
		Object IDENTIFIER33_tree=null;
		Object COMMA34_tree=null;
		Object RSQUARE36_tree=null;
		Object LPAREN37_tree=null;
		Object RPAREN39_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_DERIV=new RewriteRuleTokenStream(adaptor,"token DERIV");
		RewriteRuleTokenStream stream_LSQUARE=new RewriteRuleTokenStream(adaptor,"token LSQUARE");
		RewriteRuleTokenStream stream_RSQUARE=new RewriteRuleTokenStream(adaptor,"token RSQUARE");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_partialList=new RewriteRuleSubtreeStream(adaptor,"rule partialList");
		RewriteRuleSubtreeStream stream_argumentExpressionList=new RewriteRuleSubtreeStream(adaptor,"rule argumentExpressionList");

		try {
			// CivlCParser.g:205:2: ( DERIV LSQUARE IDENTIFIER COMMA partialList RSQUARE LPAREN argumentExpressionList RPAREN -> ^( DERIVATIVE_EXPRESSION IDENTIFIER partialList argumentExpressionList RPAREN ) )
			// CivlCParser.g:205:4: DERIV LSQUARE IDENTIFIER COMMA partialList RSQUARE LPAREN argumentExpressionList RPAREN
			{
			DERIV31=(Token)match(input,DERIV,FOLLOW_DERIV_in_derivativeExpression1210); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_DERIV.add(DERIV31);

			LSQUARE32=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_derivativeExpression1212); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LSQUARE.add(LSQUARE32);

			IDENTIFIER33=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_derivativeExpression1214); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER33);

			COMMA34=(Token)match(input,COMMA,FOLLOW_COMMA_in_derivativeExpression1216); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_COMMA.add(COMMA34);

			pushFollow(FOLLOW_partialList_in_derivativeExpression1218);
			partialList35=partialList();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_partialList.add(partialList35.getTree());
			RSQUARE36=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_derivativeExpression1220); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE36);

			LPAREN37=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_derivativeExpression1226); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN37);

			pushFollow(FOLLOW_argumentExpressionList_in_derivativeExpression1228);
			argumentExpressionList38=argumentExpressionList();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList38.getTree());
			RPAREN39=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_derivativeExpression1230); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN39);

			// AST REWRITE
			// elements: argumentExpressionList, IDENTIFIER, RPAREN, partialList
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 207:4: -> ^( DERIVATIVE_EXPRESSION IDENTIFIER partialList argumentExpressionList RPAREN )
			{
				// CivlCParser.g:207:7: ^( DERIVATIVE_EXPRESSION IDENTIFIER partialList argumentExpressionList RPAREN )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DERIVATIVE_EXPRESSION, "DERIVATIVE_EXPRESSION"), root_1);
				adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
				adaptor.addChild(root_1, stream_partialList.nextTree());
				adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
				adaptor.addChild(root_1, stream_RPAREN.nextNode());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "derivativeExpression"


	public static class partialList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "partialList"
	// CivlCParser.g:213:1: partialList : partial ( COMMA partial )* -> ^( PARTIAL_LIST ( partial )+ ) ;
	public final OmpParser_CivlCParser.partialList_return partialList() throws RecognitionException {
		OmpParser_CivlCParser.partialList_return retval = new OmpParser_CivlCParser.partialList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMMA41=null;
		ParserRuleReturnScope partial40 =null;
		ParserRuleReturnScope partial42 =null;

		Object COMMA41_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_partial=new RewriteRuleSubtreeStream(adaptor,"rule partial");

		try {
			// CivlCParser.g:214:2: ( partial ( COMMA partial )* -> ^( PARTIAL_LIST ( partial )+ ) )
			// CivlCParser.g:214:4: partial ( COMMA partial )*
			{
			pushFollow(FOLLOW_partial_in_partialList1268);
			partial40=partial();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_partial.add(partial40.getTree());
			// CivlCParser.g:214:12: ( COMMA partial )*
			loop3:
			while (true) {
				int alt3=2;
				int LA3_0 = input.LA(1);
				if ( (LA3_0==COMMA) ) {
					alt3=1;
				}

				switch (alt3) {
				case 1 :
					// CivlCParser.g:214:13: COMMA partial
					{
					COMMA41=(Token)match(input,COMMA,FOLLOW_COMMA_in_partialList1271); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA41);

					pushFollow(FOLLOW_partial_in_partialList1273);
					partial42=partial();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_partial.add(partial42.getTree());
					}
					break;

				default :
					break loop3;
				}
			}

			// AST REWRITE
			// elements: partial
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 214:29: -> ^( PARTIAL_LIST ( partial )+ )
			{
				// CivlCParser.g:214:32: ^( PARTIAL_LIST ( partial )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(PARTIAL_LIST, "PARTIAL_LIST"), root_1);
				if ( !(stream_partial.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_partial.hasNext() ) {
					adaptor.addChild(root_1, stream_partial.nextTree());
				}
				stream_partial.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "partialList"


	public static class partial_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "partial"
	// CivlCParser.g:218:1: partial : LCURLY IDENTIFIER COMMA INTEGER_CONSTANT RCURLY -> ^( PARTIAL IDENTIFIER INTEGER_CONSTANT ) ;
	public final OmpParser_CivlCParser.partial_return partial() throws RecognitionException {
		OmpParser_CivlCParser.partial_return retval = new OmpParser_CivlCParser.partial_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LCURLY43=null;
		Token IDENTIFIER44=null;
		Token COMMA45=null;
		Token INTEGER_CONSTANT46=null;
		Token RCURLY47=null;

		Object LCURLY43_tree=null;
		Object IDENTIFIER44_tree=null;
		Object COMMA45_tree=null;
		Object INTEGER_CONSTANT46_tree=null;
		Object RCURLY47_tree=null;
		RewriteRuleTokenStream stream_LCURLY=new RewriteRuleTokenStream(adaptor,"token LCURLY");
		RewriteRuleTokenStream stream_INTEGER_CONSTANT=new RewriteRuleTokenStream(adaptor,"token INTEGER_CONSTANT");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
		RewriteRuleTokenStream stream_RCURLY=new RewriteRuleTokenStream(adaptor,"token RCURLY");

		try {
			// CivlCParser.g:219:2: ( LCURLY IDENTIFIER COMMA INTEGER_CONSTANT RCURLY -> ^( PARTIAL IDENTIFIER INTEGER_CONSTANT ) )
			// CivlCParser.g:219:4: LCURLY IDENTIFIER COMMA INTEGER_CONSTANT RCURLY
			{
			LCURLY43=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_partial1297); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY43);

			IDENTIFIER44=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_partial1299); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER44);

			COMMA45=(Token)match(input,COMMA,FOLLOW_COMMA_in_partial1301); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_COMMA.add(COMMA45);

			INTEGER_CONSTANT46=(Token)match(input,INTEGER_CONSTANT,FOLLOW_INTEGER_CONSTANT_in_partial1303); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_INTEGER_CONSTANT.add(INTEGER_CONSTANT46);

			RCURLY47=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_partial1305); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY47);

			// AST REWRITE
			// elements: INTEGER_CONSTANT, IDENTIFIER
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 220:4: -> ^( PARTIAL IDENTIFIER INTEGER_CONSTANT )
			{
				// CivlCParser.g:220:7: ^( PARTIAL IDENTIFIER INTEGER_CONSTANT )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(PARTIAL, "PARTIAL"), root_1);
				adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
				adaptor.addChild(root_1, stream_INTEGER_CONSTANT.nextNode());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "partial"


	public static class genericAssocList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "genericAssocList"
	// CivlCParser.g:224:1: genericAssocList : genericAssociation ( COMMA genericAssociation )* -> ^( GENERIC_ASSOC_LIST ( genericAssociation )+ ) ;
	public final OmpParser_CivlCParser.genericAssocList_return genericAssocList() throws RecognitionException {
		OmpParser_CivlCParser.genericAssocList_return retval = new OmpParser_CivlCParser.genericAssocList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMMA49=null;
		ParserRuleReturnScope genericAssociation48 =null;
		ParserRuleReturnScope genericAssociation50 =null;

		Object COMMA49_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_genericAssociation=new RewriteRuleSubtreeStream(adaptor,"rule genericAssociation");

		try {
			// CivlCParser.g:225:2: ( genericAssociation ( COMMA genericAssociation )* -> ^( GENERIC_ASSOC_LIST ( genericAssociation )+ ) )
			// CivlCParser.g:225:4: genericAssociation ( COMMA genericAssociation )*
			{
			pushFollow(FOLLOW_genericAssociation_in_genericAssocList1332);
			genericAssociation48=genericAssociation();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_genericAssociation.add(genericAssociation48.getTree());
			// CivlCParser.g:225:23: ( COMMA genericAssociation )*
			loop4:
			while (true) {
				int alt4=2;
				int LA4_0 = input.LA(1);
				if ( (LA4_0==COMMA) ) {
					alt4=1;
				}

				switch (alt4) {
				case 1 :
					// CivlCParser.g:225:24: COMMA genericAssociation
					{
					COMMA49=(Token)match(input,COMMA,FOLLOW_COMMA_in_genericAssocList1335); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA49);

					pushFollow(FOLLOW_genericAssociation_in_genericAssocList1337);
					genericAssociation50=genericAssociation();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_genericAssociation.add(genericAssociation50.getTree());
					}
					break;

				default :
					break loop4;
				}
			}

			// AST REWRITE
			// elements: genericAssociation
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 226:4: -> ^( GENERIC_ASSOC_LIST ( genericAssociation )+ )
			{
				// CivlCParser.g:226:7: ^( GENERIC_ASSOC_LIST ( genericAssociation )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(GENERIC_ASSOC_LIST, "GENERIC_ASSOC_LIST"), root_1);
				if ( !(stream_genericAssociation.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_genericAssociation.hasNext() ) {
					adaptor.addChild(root_1, stream_genericAssociation.nextTree());
				}
				stream_genericAssociation.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "genericAssocList"


	public static class genericAssociation_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "genericAssociation"
	// CivlCParser.g:230:1: genericAssociation : ( typeName COLON assignmentExpression -> ^( GENERIC_ASSOCIATION typeName assignmentExpression ) | DEFAULT COLON assignmentExpression -> ^( GENERIC_ASSOCIATION DEFAULT assignmentExpression ) );
	public final OmpParser_CivlCParser.genericAssociation_return genericAssociation() throws RecognitionException {
		OmpParser_CivlCParser.genericAssociation_return retval = new OmpParser_CivlCParser.genericAssociation_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COLON52=null;
		Token DEFAULT54=null;
		Token COLON55=null;
		ParserRuleReturnScope typeName51 =null;
		ParserRuleReturnScope assignmentExpression53 =null;
		ParserRuleReturnScope assignmentExpression56 =null;

		Object COLON52_tree=null;
		Object DEFAULT54_tree=null;
		Object COLON55_tree=null;
		RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
		RewriteRuleTokenStream stream_DEFAULT=new RewriteRuleTokenStream(adaptor,"token DEFAULT");
		RewriteRuleSubtreeStream stream_typeName=new RewriteRuleSubtreeStream(adaptor,"rule typeName");
		RewriteRuleSubtreeStream stream_assignmentExpression=new RewriteRuleSubtreeStream(adaptor,"rule assignmentExpression");

		try {
			// CivlCParser.g:231:2: ( typeName COLON assignmentExpression -> ^( GENERIC_ASSOCIATION typeName assignmentExpression ) | DEFAULT COLON assignmentExpression -> ^( GENERIC_ASSOCIATION DEFAULT assignmentExpression ) )
			int alt5=2;
			int LA5_0 = input.LA(1);
			if ( (LA5_0==ATOMIC||LA5_0==BOOL||LA5_0==CHAR||(LA5_0 >= COMPLEX && LA5_0 <= CONST)||LA5_0==DOMAIN||LA5_0==DOUBLE||LA5_0==ENUM||LA5_0==FLOAT||LA5_0==IDENTIFIER||(LA5_0 >= INPUT && LA5_0 <= INT)||LA5_0==LONG||LA5_0==OUTPUT||LA5_0==RANGE||LA5_0==REAL||LA5_0==RESTRICT||(LA5_0 >= SHORT && LA5_0 <= SIGNED)||LA5_0==STRUCT||LA5_0==TYPEOF||(LA5_0 >= UNION && LA5_0 <= UNSIGNED)||(LA5_0 >= VOID && LA5_0 <= VOLATILE)) ) {
				alt5=1;
			}
			else if ( (LA5_0==DEFAULT) ) {
				alt5=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 5, 0, input);
				throw nvae;
			}

			switch (alt5) {
				case 1 :
					// CivlCParser.g:231:4: typeName COLON assignmentExpression
					{
					pushFollow(FOLLOW_typeName_in_genericAssociation1364);
					typeName51=typeName();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeName.add(typeName51.getTree());
					COLON52=(Token)match(input,COLON,FOLLOW_COLON_in_genericAssociation1366); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COLON.add(COLON52);

					pushFollow(FOLLOW_assignmentExpression_in_genericAssociation1368);
					assignmentExpression53=assignmentExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression53.getTree());
					// AST REWRITE
					// elements: assignmentExpression, typeName
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 232:4: -> ^( GENERIC_ASSOCIATION typeName assignmentExpression )
					{
						// CivlCParser.g:232:7: ^( GENERIC_ASSOCIATION typeName assignmentExpression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(GENERIC_ASSOCIATION, "GENERIC_ASSOCIATION"), root_1);
						adaptor.addChild(root_1, stream_typeName.nextTree());
						adaptor.addChild(root_1, stream_assignmentExpression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:233:4: DEFAULT COLON assignmentExpression
					{
					DEFAULT54=(Token)match(input,DEFAULT,FOLLOW_DEFAULT_in_genericAssociation1386); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DEFAULT.add(DEFAULT54);

					COLON55=(Token)match(input,COLON,FOLLOW_COLON_in_genericAssociation1388); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COLON.add(COLON55);

					pushFollow(FOLLOW_assignmentExpression_in_genericAssociation1390);
					assignmentExpression56=assignmentExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression56.getTree());
					// AST REWRITE
					// elements: DEFAULT, assignmentExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 234:4: -> ^( GENERIC_ASSOCIATION DEFAULT assignmentExpression )
					{
						// CivlCParser.g:234:7: ^( GENERIC_ASSOCIATION DEFAULT assignmentExpression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(GENERIC_ASSOCIATION, "GENERIC_ASSOCIATION"), root_1);
						adaptor.addChild(root_1, stream_DEFAULT.nextNode());
						adaptor.addChild(root_1, stream_assignmentExpression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "genericAssociation"


	public static class postfixExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "postfixExpression"
	// CivlCParser.g:238:1: postfixExpression : ( postfixExpressionRoot -> postfixExpressionRoot ) (l= LSQUARE expression RSQUARE -> ^( OPERATOR INDEX[$l] ^( ARGUMENT_LIST $postfixExpression expression ) RSQUARE ) | LPAREN argumentExpressionList RPAREN -> ^( CALL LPAREN $postfixExpression ABSENT argumentExpressionList RPAREN ABSENT ) | LEXCON args1= argumentExpressionList REXCON LPAREN args2= argumentExpressionList RPAREN -> ^( CALL LPAREN $postfixExpression $args1 $args2 RPAREN ABSENT ) | DOT IDENTIFIER -> ^( DOT $postfixExpression IDENTIFIER ) | ARROW IDENTIFIER -> ^( ARROW $postfixExpression IDENTIFIER ) |p= PLUSPLUS -> ^( OPERATOR POST_INCREMENT[$p] ^( ARGUMENT_LIST $postfixExpression) ) |m= MINUSMINUS -> ^( OPERATOR POST_DECREMENT[$m] ^( ARGUMENT_LIST $postfixExpression) ) )* ;
	public final OmpParser_CivlCParser.postfixExpression_return postfixExpression() throws RecognitionException {
		OmpParser_CivlCParser.postfixExpression_return retval = new OmpParser_CivlCParser.postfixExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token l=null;
		Token p=null;
		Token m=null;
		Token RSQUARE59=null;
		Token LPAREN60=null;
		Token RPAREN62=null;
		Token LEXCON63=null;
		Token REXCON64=null;
		Token LPAREN65=null;
		Token RPAREN66=null;
		Token DOT67=null;
		Token IDENTIFIER68=null;
		Token ARROW69=null;
		Token IDENTIFIER70=null;
		ParserRuleReturnScope args1 =null;
		ParserRuleReturnScope args2 =null;
		ParserRuleReturnScope postfixExpressionRoot57 =null;
		ParserRuleReturnScope expression58 =null;
		ParserRuleReturnScope argumentExpressionList61 =null;

		Object l_tree=null;
		Object p_tree=null;
		Object m_tree=null;
		Object RSQUARE59_tree=null;
		Object LPAREN60_tree=null;
		Object RPAREN62_tree=null;
		Object LEXCON63_tree=null;
		Object REXCON64_tree=null;
		Object LPAREN65_tree=null;
		Object RPAREN66_tree=null;
		Object DOT67_tree=null;
		Object IDENTIFIER68_tree=null;
		Object ARROW69_tree=null;
		Object IDENTIFIER70_tree=null;
		RewriteRuleTokenStream stream_LEXCON=new RewriteRuleTokenStream(adaptor,"token LEXCON");
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_ARROW=new RewriteRuleTokenStream(adaptor,"token ARROW");
		RewriteRuleTokenStream stream_MINUSMINUS=new RewriteRuleTokenStream(adaptor,"token MINUSMINUS");
		RewriteRuleTokenStream stream_LSQUARE=new RewriteRuleTokenStream(adaptor,"token LSQUARE");
		RewriteRuleTokenStream stream_RSQUARE=new RewriteRuleTokenStream(adaptor,"token RSQUARE");
		RewriteRuleTokenStream stream_DOT=new RewriteRuleTokenStream(adaptor,"token DOT");
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
		RewriteRuleTokenStream stream_PLUSPLUS=new RewriteRuleTokenStream(adaptor,"token PLUSPLUS");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleTokenStream stream_REXCON=new RewriteRuleTokenStream(adaptor,"token REXCON");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_postfixExpressionRoot=new RewriteRuleSubtreeStream(adaptor,"rule postfixExpressionRoot");
		RewriteRuleSubtreeStream stream_argumentExpressionList=new RewriteRuleSubtreeStream(adaptor,"rule argumentExpressionList");

		try {
			// CivlCParser.g:239:2: ( ( postfixExpressionRoot -> postfixExpressionRoot ) (l= LSQUARE expression RSQUARE -> ^( OPERATOR INDEX[$l] ^( ARGUMENT_LIST $postfixExpression expression ) RSQUARE ) | LPAREN argumentExpressionList RPAREN -> ^( CALL LPAREN $postfixExpression ABSENT argumentExpressionList RPAREN ABSENT ) | LEXCON args1= argumentExpressionList REXCON LPAREN args2= argumentExpressionList RPAREN -> ^( CALL LPAREN $postfixExpression $args1 $args2 RPAREN ABSENT ) | DOT IDENTIFIER -> ^( DOT $postfixExpression IDENTIFIER ) | ARROW IDENTIFIER -> ^( ARROW $postfixExpression IDENTIFIER ) |p= PLUSPLUS -> ^( OPERATOR POST_INCREMENT[$p] ^( ARGUMENT_LIST $postfixExpression) ) |m= MINUSMINUS -> ^( OPERATOR POST_DECREMENT[$m] ^( ARGUMENT_LIST $postfixExpression) ) )* )
			// CivlCParser.g:239:4: ( postfixExpressionRoot -> postfixExpressionRoot ) (l= LSQUARE expression RSQUARE -> ^( OPERATOR INDEX[$l] ^( ARGUMENT_LIST $postfixExpression expression ) RSQUARE ) | LPAREN argumentExpressionList RPAREN -> ^( CALL LPAREN $postfixExpression ABSENT argumentExpressionList RPAREN ABSENT ) | LEXCON args1= argumentExpressionList REXCON LPAREN args2= argumentExpressionList RPAREN -> ^( CALL LPAREN $postfixExpression $args1 $args2 RPAREN ABSENT ) | DOT IDENTIFIER -> ^( DOT $postfixExpression IDENTIFIER ) | ARROW IDENTIFIER -> ^( ARROW $postfixExpression IDENTIFIER ) |p= PLUSPLUS -> ^( OPERATOR POST_INCREMENT[$p] ^( ARGUMENT_LIST $postfixExpression) ) |m= MINUSMINUS -> ^( OPERATOR POST_DECREMENT[$m] ^( ARGUMENT_LIST $postfixExpression) ) )*
			{
			// CivlCParser.g:239:4: ( postfixExpressionRoot -> postfixExpressionRoot )
			// CivlCParser.g:239:5: postfixExpressionRoot
			{
			pushFollow(FOLLOW_postfixExpressionRoot_in_postfixExpression1417);
			postfixExpressionRoot57=postfixExpressionRoot();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_postfixExpressionRoot.add(postfixExpressionRoot57.getTree());
			// AST REWRITE
			// elements: postfixExpressionRoot
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 239:27: -> postfixExpressionRoot
			{
				adaptor.addChild(root_0, stream_postfixExpressionRoot.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:241:4: (l= LSQUARE expression RSQUARE -> ^( OPERATOR INDEX[$l] ^( ARGUMENT_LIST $postfixExpression expression ) RSQUARE ) | LPAREN argumentExpressionList RPAREN -> ^( CALL LPAREN $postfixExpression ABSENT argumentExpressionList RPAREN ABSENT ) | LEXCON args1= argumentExpressionList REXCON LPAREN args2= argumentExpressionList RPAREN -> ^( CALL LPAREN $postfixExpression $args1 $args2 RPAREN ABSENT ) | DOT IDENTIFIER -> ^( DOT $postfixExpression IDENTIFIER ) | ARROW IDENTIFIER -> ^( ARROW $postfixExpression IDENTIFIER ) |p= PLUSPLUS -> ^( OPERATOR POST_INCREMENT[$p] ^( ARGUMENT_LIST $postfixExpression) ) |m= MINUSMINUS -> ^( OPERATOR POST_DECREMENT[$m] ^( ARGUMENT_LIST $postfixExpression) ) )*
			loop6:
			while (true) {
				int alt6=8;
				switch ( input.LA(1) ) {
				case LSQUARE:
					{
					alt6=1;
					}
					break;
				case LPAREN:
					{
					alt6=2;
					}
					break;
				case LEXCON:
					{
					alt6=3;
					}
					break;
				case DOT:
					{
					alt6=4;
					}
					break;
				case ARROW:
					{
					alt6=5;
					}
					break;
				case PLUSPLUS:
					{
					alt6=6;
					}
					break;
				case MINUSMINUS:
					{
					alt6=7;
					}
					break;
				}
				switch (alt6) {
				case 1 :
					// CivlCParser.g:241:6: l= LSQUARE expression RSQUARE
					{
					l=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_postfixExpression1434); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LSQUARE.add(l);

					pushFollow(FOLLOW_expression_in_postfixExpression1436);
					expression58=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression58.getTree());
					RSQUARE59=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_postfixExpression1438); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE59);

					// AST REWRITE
					// elements: expression, postfixExpression, RSQUARE
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 242:6: -> ^( OPERATOR INDEX[$l] ^( ARGUMENT_LIST $postfixExpression expression ) RSQUARE )
					{
						// CivlCParser.g:242:9: ^( OPERATOR INDEX[$l] ^( ARGUMENT_LIST $postfixExpression expression ) RSQUARE )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(INDEX, l));
						// CivlCParser.g:244:13: ^( ARGUMENT_LIST $postfixExpression expression )
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_expression.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_1, stream_RSQUARE.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:247:6: LPAREN argumentExpressionList RPAREN
					{
					LPAREN60=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_postfixExpression1512); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN60);

					pushFollow(FOLLOW_argumentExpressionList_in_postfixExpression1514);
					argumentExpressionList61=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList61.getTree());
					RPAREN62=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_postfixExpression1516); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN62);

					// AST REWRITE
					// elements: postfixExpression, argumentExpressionList, RPAREN, LPAREN
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 248:6: -> ^( CALL LPAREN $postfixExpression ABSENT argumentExpressionList RPAREN ABSENT )
					{
						// CivlCParser.g:248:9: ^( CALL LPAREN $postfixExpression ABSENT argumentExpressionList RPAREN ABSENT )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CALL, "CALL"), root_1);
						adaptor.addChild(root_1, stream_LPAREN.nextNode());
						adaptor.addChild(root_1, stream_retval.nextTree());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
						adaptor.addChild(root_1, stream_RPAREN.nextNode());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// CivlCParser.g:251:6: LEXCON args1= argumentExpressionList REXCON LPAREN args2= argumentExpressionList RPAREN
					{
					LEXCON63=(Token)match(input,LEXCON,FOLLOW_LEXCON_in_postfixExpression1560); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LEXCON.add(LEXCON63);

					pushFollow(FOLLOW_argumentExpressionList_in_postfixExpression1564);
					args1=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(args1.getTree());
					REXCON64=(Token)match(input,REXCON,FOLLOW_REXCON_in_postfixExpression1566); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_REXCON.add(REXCON64);

					LPAREN65=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_postfixExpression1574); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN65);

					pushFollow(FOLLOW_argumentExpressionList_in_postfixExpression1578);
					args2=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(args2.getTree());
					RPAREN66=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_postfixExpression1580); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN66);

					// AST REWRITE
					// elements: args1, postfixExpression, LPAREN, args2, RPAREN
					// token labels: 
					// rule labels: retval, args1, args2
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_args1=new RewriteRuleSubtreeStream(adaptor,"rule args1",args1!=null?args1.getTree():null);
					RewriteRuleSubtreeStream stream_args2=new RewriteRuleSubtreeStream(adaptor,"rule args2",args2!=null?args2.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 253:6: -> ^( CALL LPAREN $postfixExpression $args1 $args2 RPAREN ABSENT )
					{
						// CivlCParser.g:253:9: ^( CALL LPAREN $postfixExpression $args1 $args2 RPAREN ABSENT )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CALL, "CALL"), root_1);
						adaptor.addChild(root_1, stream_LPAREN.nextNode());
						adaptor.addChild(root_1, stream_retval.nextTree());
						adaptor.addChild(root_1, stream_args1.nextTree());
						adaptor.addChild(root_1, stream_args2.nextTree());
						adaptor.addChild(root_1, stream_RPAREN.nextNode());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// CivlCParser.g:254:6: DOT IDENTIFIER
					{
					DOT67=(Token)match(input,DOT,FOLLOW_DOT_in_postfixExpression1613); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(DOT67);

					IDENTIFIER68=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_postfixExpression1615); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER68);

					// AST REWRITE
					// elements: IDENTIFIER, postfixExpression, DOT
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 255:6: -> ^( DOT $postfixExpression IDENTIFIER )
					{
						// CivlCParser.g:255:9: ^( DOT $postfixExpression IDENTIFIER )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_DOT.nextNode(), root_1);
						adaptor.addChild(root_1, stream_retval.nextTree());
						adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 5 :
					// CivlCParser.g:256:6: ARROW IDENTIFIER
					{
					ARROW69=(Token)match(input,ARROW,FOLLOW_ARROW_in_postfixExpression1638); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ARROW.add(ARROW69);

					IDENTIFIER70=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_postfixExpression1640); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER70);

					// AST REWRITE
					// elements: IDENTIFIER, ARROW, postfixExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 257:6: -> ^( ARROW $postfixExpression IDENTIFIER )
					{
						// CivlCParser.g:257:9: ^( ARROW $postfixExpression IDENTIFIER )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ARROW.nextNode(), root_1);
						adaptor.addChild(root_1, stream_retval.nextTree());
						adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 6 :
					// CivlCParser.g:258:6: p= PLUSPLUS
					{
					p=(Token)match(input,PLUSPLUS,FOLLOW_PLUSPLUS_in_postfixExpression1665); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_PLUSPLUS.add(p);

					// AST REWRITE
					// elements: postfixExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 259:6: -> ^( OPERATOR POST_INCREMENT[$p] ^( ARGUMENT_LIST $postfixExpression) )
					{
						// CivlCParser.g:259:9: ^( OPERATOR POST_INCREMENT[$p] ^( ARGUMENT_LIST $postfixExpression) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(POST_INCREMENT, p));
						// CivlCParser.g:260:11: ^( ARGUMENT_LIST $postfixExpression)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 7 :
					// CivlCParser.g:264:6: m= MINUSMINUS
					{
					m=(Token)match(input,MINUSMINUS,FOLLOW_MINUSMINUS_in_postfixExpression1721); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_MINUSMINUS.add(m);

					// AST REWRITE
					// elements: postfixExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 265:6: -> ^( OPERATOR POST_DECREMENT[$m] ^( ARGUMENT_LIST $postfixExpression) )
					{
						// CivlCParser.g:265:9: ^( OPERATOR POST_DECREMENT[$m] ^( ARGUMENT_LIST $postfixExpression) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(POST_DECREMENT, m));
						// CivlCParser.g:266:11: ^( ARGUMENT_LIST $postfixExpression)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop6;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "postfixExpression"


	public static class postfixExpressionRoot_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "postfixExpressionRoot"
	// CivlCParser.g:283:1: postfixExpressionRoot : ( ( LPAREN typeName RPAREN LCURLY )=> LPAREN typeName RPAREN LCURLY initializerList ( RCURLY | COMMA RCURLY ) -> ^( COMPOUND_LITERAL LPAREN typeName initializerList RCURLY ) | primaryExpression );
	public final OmpParser_CivlCParser.postfixExpressionRoot_return postfixExpressionRoot() throws RecognitionException {
		OmpParser_CivlCParser.postfixExpressionRoot_return retval = new OmpParser_CivlCParser.postfixExpressionRoot_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LPAREN71=null;
		Token RPAREN73=null;
		Token LCURLY74=null;
		Token RCURLY76=null;
		Token COMMA77=null;
		Token RCURLY78=null;
		ParserRuleReturnScope typeName72 =null;
		ParserRuleReturnScope initializerList75 =null;
		ParserRuleReturnScope primaryExpression79 =null;

		Object LPAREN71_tree=null;
		Object RPAREN73_tree=null;
		Object LCURLY74_tree=null;
		Object RCURLY76_tree=null;
		Object COMMA77_tree=null;
		Object RCURLY78_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_LCURLY=new RewriteRuleTokenStream(adaptor,"token LCURLY");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleTokenStream stream_RCURLY=new RewriteRuleTokenStream(adaptor,"token RCURLY");
		RewriteRuleSubtreeStream stream_typeName=new RewriteRuleSubtreeStream(adaptor,"rule typeName");
		RewriteRuleSubtreeStream stream_initializerList=new RewriteRuleSubtreeStream(adaptor,"rule initializerList");

		try {
			// CivlCParser.g:284:2: ( ( LPAREN typeName RPAREN LCURLY )=> LPAREN typeName RPAREN LCURLY initializerList ( RCURLY | COMMA RCURLY ) -> ^( COMPOUND_LITERAL LPAREN typeName initializerList RCURLY ) | primaryExpression )
			int alt8=2;
			int LA8_0 = input.LA(1);
			if ( (LA8_0==LPAREN) ) {
				int LA8_1 = input.LA(2);
				if ( (synpred1_CivlCParser()) ) {
					alt8=1;
				}
				else if ( (true) ) {
					alt8=2;
				}

			}
			else if ( (LA8_0==CHARACTER_CONSTANT||LA8_0==DERIV||LA8_0==ELLIPSIS||LA8_0==FALSE||LA8_0==FLOATING_CONSTANT||LA8_0==GENERIC||LA8_0==HERE||LA8_0==IDENTIFIER||LA8_0==INTEGER_CONSTANT||LA8_0==PROCNULL||LA8_0==RESULT||LA8_0==SELF||LA8_0==STRING_LITERAL||LA8_0==TRUE||LA8_0==ROOT) ) {
				alt8=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 8, 0, input);
				throw nvae;
			}

			switch (alt8) {
				case 1 :
					// CivlCParser.g:284:4: ( LPAREN typeName RPAREN LCURLY )=> LPAREN typeName RPAREN LCURLY initializerList ( RCURLY | COMMA RCURLY )
					{
					LPAREN71=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_postfixExpressionRoot1785); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN71);

					pushFollow(FOLLOW_typeName_in_postfixExpressionRoot1787);
					typeName72=typeName();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeName.add(typeName72.getTree());
					RPAREN73=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_postfixExpressionRoot1789); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN73);

					LCURLY74=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_postfixExpressionRoot1791); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY74);

					pushFollow(FOLLOW_initializerList_in_postfixExpressionRoot1793);
					initializerList75=initializerList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_initializerList.add(initializerList75.getTree());
					// CivlCParser.g:286:3: ( RCURLY | COMMA RCURLY )
					int alt7=2;
					int LA7_0 = input.LA(1);
					if ( (LA7_0==RCURLY) ) {
						alt7=1;
					}
					else if ( (LA7_0==COMMA) ) {
						alt7=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 7, 0, input);
						throw nvae;
					}

					switch (alt7) {
						case 1 :
							// CivlCParser.g:286:5: RCURLY
							{
							RCURLY76=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_postfixExpressionRoot1800); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY76);

							}
							break;
						case 2 :
							// CivlCParser.g:287:5: COMMA RCURLY
							{
							COMMA77=(Token)match(input,COMMA,FOLLOW_COMMA_in_postfixExpressionRoot1806); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_COMMA.add(COMMA77);

							RCURLY78=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_postfixExpressionRoot1808); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY78);

							}
							break;

					}

					// AST REWRITE
					// elements: initializerList, RCURLY, LPAREN, typeName
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 289:4: -> ^( COMPOUND_LITERAL LPAREN typeName initializerList RCURLY )
					{
						// CivlCParser.g:289:7: ^( COMPOUND_LITERAL LPAREN typeName initializerList RCURLY )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(COMPOUND_LITERAL, "COMPOUND_LITERAL"), root_1);
						adaptor.addChild(root_1, stream_LPAREN.nextNode());
						adaptor.addChild(root_1, stream_typeName.nextTree());
						adaptor.addChild(root_1, stream_initializerList.nextTree());
						adaptor.addChild(root_1, stream_RCURLY.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:290:4: primaryExpression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_primaryExpression_in_postfixExpressionRoot1834);
					primaryExpression79=primaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, primaryExpression79.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "postfixExpressionRoot"


	public static class argumentExpressionList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "argumentExpressionList"
	// CivlCParser.g:294:1: argumentExpressionList : ( -> ^( ARGUMENT_LIST ) | assignmentExpression ( COMMA assignmentExpression )* -> ^( ARGUMENT_LIST ( assignmentExpression )+ ) );
	public final OmpParser_CivlCParser.argumentExpressionList_return argumentExpressionList() throws RecognitionException {
		OmpParser_CivlCParser.argumentExpressionList_return retval = new OmpParser_CivlCParser.argumentExpressionList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMMA81=null;
		ParserRuleReturnScope assignmentExpression80 =null;
		ParserRuleReturnScope assignmentExpression82 =null;

		Object COMMA81_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_assignmentExpression=new RewriteRuleSubtreeStream(adaptor,"rule assignmentExpression");

		try {
			// CivlCParser.g:295:2: ( -> ^( ARGUMENT_LIST ) | assignmentExpression ( COMMA assignmentExpression )* -> ^( ARGUMENT_LIST ( assignmentExpression )+ ) )
			int alt10=2;
			int LA10_0 = input.LA(1);
			if ( (LA10_0==RCURLY||(LA10_0 >= REXCON && LA10_0 <= RPAREN)) ) {
				alt10=1;
			}
			else if ( ((LA10_0 >= ALIGNOF && LA10_0 <= AMPERSAND)||LA10_0==BIG_O||LA10_0==CALLS||LA10_0==CHARACTER_CONSTANT||LA10_0==DERIV||LA10_0==ELLIPSIS||LA10_0==EXISTS||LA10_0==FALSE||LA10_0==FLOATING_CONSTANT||LA10_0==FORALL||LA10_0==GENERIC||LA10_0==HERE||LA10_0==IDENTIFIER||LA10_0==INTEGER_CONSTANT||LA10_0==LPAREN||LA10_0==MINUSMINUS||LA10_0==NOT||LA10_0==PLUS||LA10_0==PLUSPLUS||LA10_0==PROCNULL||LA10_0==RESULT||LA10_0==SCOPEOF||LA10_0==SELF||(LA10_0 >= SIZEOF && LA10_0 <= STAR)||LA10_0==STRING_LITERAL||LA10_0==SUB||(LA10_0 >= TILDE && LA10_0 <= TRUE)||LA10_0==UNIFORM||LA10_0==ROOT) ) {
				alt10=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 10, 0, input);
				throw nvae;
			}

			switch (alt10) {
				case 1 :
					// CivlCParser.g:295:4: 
					{
					// AST REWRITE
					// elements: 
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 295:4: -> ^( ARGUMENT_LIST )
					{
						// CivlCParser.g:295:7: ^( ARGUMENT_LIST )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:296:4: assignmentExpression ( COMMA assignmentExpression )*
					{
					pushFollow(FOLLOW_assignmentExpression_in_argumentExpressionList1856);
					assignmentExpression80=assignmentExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression80.getTree());
					// CivlCParser.g:296:25: ( COMMA assignmentExpression )*
					loop9:
					while (true) {
						int alt9=2;
						int LA9_0 = input.LA(1);
						if ( (LA9_0==COMMA) ) {
							alt9=1;
						}

						switch (alt9) {
						case 1 :
							// CivlCParser.g:296:26: COMMA assignmentExpression
							{
							COMMA81=(Token)match(input,COMMA,FOLLOW_COMMA_in_argumentExpressionList1859); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_COMMA.add(COMMA81);

							pushFollow(FOLLOW_assignmentExpression_in_argumentExpressionList1861);
							assignmentExpression82=assignmentExpression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression82.getTree());
							}
							break;

						default :
							break loop9;
						}
					}

					// AST REWRITE
					// elements: assignmentExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 297:4: -> ^( ARGUMENT_LIST ( assignmentExpression )+ )
					{
						// CivlCParser.g:297:7: ^( ARGUMENT_LIST ( assignmentExpression )+ )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_1);
						if ( !(stream_assignmentExpression.hasNext()) ) {
							throw new RewriteEarlyExitException();
						}
						while ( stream_assignmentExpression.hasNext() ) {
							adaptor.addChild(root_1, stream_assignmentExpression.nextTree());
						}
						stream_assignmentExpression.reset();

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "argumentExpressionList"


	public static class unaryExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "unaryExpression"
	// CivlCParser.g:301:1: unaryExpression : ( postfixExpression |p= PLUSPLUS unaryExpression -> ^( OPERATOR PRE_INCREMENT[$p] ^( ARGUMENT_LIST unaryExpression ) ) |m= MINUSMINUS unaryExpression -> ^( OPERATOR PRE_DECREMENT[$m] ^( ARGUMENT_LIST unaryExpression ) ) | unaryOperator castExpression -> ^( OPERATOR unaryOperator ^( ARGUMENT_LIST castExpression ) ) | ( SIZEOF LPAREN typeName )=> SIZEOF LPAREN typeName RPAREN -> ^( SIZEOF TYPE typeName ) | SIZEOF unaryExpression -> ^( SIZEOF EXPR unaryExpression ) | SCOPEOF unaryExpression -> ^( SCOPEOF unaryExpression ) | ALIGNOF LPAREN typeName RPAREN -> ^( ALIGNOF typeName ) | spawnExpression | callsExpression );
	public final OmpParser_CivlCParser.unaryExpression_return unaryExpression() throws RecognitionException {
		DeclarationScope_stack.push(new DeclarationScope_scope());

		OmpParser_CivlCParser.unaryExpression_return retval = new OmpParser_CivlCParser.unaryExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token p=null;
		Token m=null;
		Token SIZEOF88=null;
		Token LPAREN89=null;
		Token RPAREN91=null;
		Token SIZEOF92=null;
		Token SCOPEOF94=null;
		Token ALIGNOF96=null;
		Token LPAREN97=null;
		Token RPAREN99=null;
		ParserRuleReturnScope postfixExpression83 =null;
		ParserRuleReturnScope unaryExpression84 =null;
		ParserRuleReturnScope unaryExpression85 =null;
		ParserRuleReturnScope unaryOperator86 =null;
		ParserRuleReturnScope castExpression87 =null;
		ParserRuleReturnScope typeName90 =null;
		ParserRuleReturnScope unaryExpression93 =null;
		ParserRuleReturnScope unaryExpression95 =null;
		ParserRuleReturnScope typeName98 =null;
		ParserRuleReturnScope spawnExpression100 =null;
		ParserRuleReturnScope callsExpression101 =null;

		Object p_tree=null;
		Object m_tree=null;
		Object SIZEOF88_tree=null;
		Object LPAREN89_tree=null;
		Object RPAREN91_tree=null;
		Object SIZEOF92_tree=null;
		Object SCOPEOF94_tree=null;
		Object ALIGNOF96_tree=null;
		Object LPAREN97_tree=null;
		Object RPAREN99_tree=null;
		RewriteRuleTokenStream stream_SIZEOF=new RewriteRuleTokenStream(adaptor,"token SIZEOF");
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_MINUSMINUS=new RewriteRuleTokenStream(adaptor,"token MINUSMINUS");
		RewriteRuleTokenStream stream_ALIGNOF=new RewriteRuleTokenStream(adaptor,"token ALIGNOF");
		RewriteRuleTokenStream stream_SCOPEOF=new RewriteRuleTokenStream(adaptor,"token SCOPEOF");
		RewriteRuleTokenStream stream_PLUSPLUS=new RewriteRuleTokenStream(adaptor,"token PLUSPLUS");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_typeName=new RewriteRuleSubtreeStream(adaptor,"rule typeName");
		RewriteRuleSubtreeStream stream_unaryOperator=new RewriteRuleSubtreeStream(adaptor,"rule unaryOperator");
		RewriteRuleSubtreeStream stream_castExpression=new RewriteRuleSubtreeStream(adaptor,"rule castExpression");
		RewriteRuleSubtreeStream stream_unaryExpression=new RewriteRuleSubtreeStream(adaptor,"rule unaryExpression");


		  DeclarationScope_stack.peek().isTypedef = false;
		  DeclarationScope_stack.peek().typedefNameUsed =false;

		try {
			// CivlCParser.g:307:2: ( postfixExpression |p= PLUSPLUS unaryExpression -> ^( OPERATOR PRE_INCREMENT[$p] ^( ARGUMENT_LIST unaryExpression ) ) |m= MINUSMINUS unaryExpression -> ^( OPERATOR PRE_DECREMENT[$m] ^( ARGUMENT_LIST unaryExpression ) ) | unaryOperator castExpression -> ^( OPERATOR unaryOperator ^( ARGUMENT_LIST castExpression ) ) | ( SIZEOF LPAREN typeName )=> SIZEOF LPAREN typeName RPAREN -> ^( SIZEOF TYPE typeName ) | SIZEOF unaryExpression -> ^( SIZEOF EXPR unaryExpression ) | SCOPEOF unaryExpression -> ^( SCOPEOF unaryExpression ) | ALIGNOF LPAREN typeName RPAREN -> ^( ALIGNOF typeName ) | spawnExpression | callsExpression )
			int alt11=10;
			switch ( input.LA(1) ) {
			case CHARACTER_CONSTANT:
			case DERIV:
			case ELLIPSIS:
			case FALSE:
			case FLOATING_CONSTANT:
			case GENERIC:
			case HERE:
			case IDENTIFIER:
			case INTEGER_CONSTANT:
			case LPAREN:
			case PROCNULL:
			case RESULT:
			case SELF:
			case STRING_LITERAL:
			case TRUE:
			case ROOT:
				{
				alt11=1;
				}
				break;
			case PLUSPLUS:
				{
				alt11=2;
				}
				break;
			case MINUSMINUS:
				{
				alt11=3;
				}
				break;
			case AMPERSAND:
			case BIG_O:
			case NOT:
			case PLUS:
			case STAR:
			case SUB:
			case TILDE:
				{
				alt11=4;
				}
				break;
			case SIZEOF:
				{
				int LA11_20 = input.LA(2);
				if ( (synpred2_CivlCParser()) ) {
					alt11=5;
				}
				else if ( (true) ) {
					alt11=6;
				}

				}
				break;
			case SCOPEOF:
				{
				alt11=7;
				}
				break;
			case ALIGNOF:
				{
				alt11=8;
				}
				break;
			case SPAWN:
				{
				alt11=9;
				}
				break;
			case CALLS:
				{
				alt11=10;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 11, 0, input);
				throw nvae;
			}
			switch (alt11) {
				case 1 :
					// CivlCParser.g:307:4: postfixExpression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_postfixExpression_in_unaryExpression1899);
					postfixExpression83=postfixExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, postfixExpression83.getTree());

					}
					break;
				case 2 :
					// CivlCParser.g:308:4: p= PLUSPLUS unaryExpression
					{
					p=(Token)match(input,PLUSPLUS,FOLLOW_PLUSPLUS_in_unaryExpression1906); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_PLUSPLUS.add(p);

					pushFollow(FOLLOW_unaryExpression_in_unaryExpression1908);
					unaryExpression84=unaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_unaryExpression.add(unaryExpression84.getTree());
					// AST REWRITE
					// elements: unaryExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 309:4: -> ^( OPERATOR PRE_INCREMENT[$p] ^( ARGUMENT_LIST unaryExpression ) )
					{
						// CivlCParser.g:309:7: ^( OPERATOR PRE_INCREMENT[$p] ^( ARGUMENT_LIST unaryExpression ) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(PRE_INCREMENT, p));
						// CivlCParser.g:310:9: ^( ARGUMENT_LIST unaryExpression )
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_unaryExpression.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// CivlCParser.g:311:4: m= MINUSMINUS unaryExpression
					{
					m=(Token)match(input,MINUSMINUS,FOLLOW_MINUSMINUS_in_unaryExpression1941); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_MINUSMINUS.add(m);

					pushFollow(FOLLOW_unaryExpression_in_unaryExpression1943);
					unaryExpression85=unaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_unaryExpression.add(unaryExpression85.getTree());
					// AST REWRITE
					// elements: unaryExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 312:4: -> ^( OPERATOR PRE_DECREMENT[$m] ^( ARGUMENT_LIST unaryExpression ) )
					{
						// CivlCParser.g:312:7: ^( OPERATOR PRE_DECREMENT[$m] ^( ARGUMENT_LIST unaryExpression ) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(PRE_DECREMENT, m));
						// CivlCParser.g:313:9: ^( ARGUMENT_LIST unaryExpression )
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_unaryExpression.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// CivlCParser.g:314:4: unaryOperator castExpression
					{
					pushFollow(FOLLOW_unaryOperator_in_unaryExpression1974);
					unaryOperator86=unaryOperator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_unaryOperator.add(unaryOperator86.getTree());
					pushFollow(FOLLOW_castExpression_in_unaryExpression1976);
					castExpression87=castExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_castExpression.add(castExpression87.getTree());
					// AST REWRITE
					// elements: unaryOperator, castExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 315:4: -> ^( OPERATOR unaryOperator ^( ARGUMENT_LIST castExpression ) )
					{
						// CivlCParser.g:315:7: ^( OPERATOR unaryOperator ^( ARGUMENT_LIST castExpression ) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_unaryOperator.nextTree());
						// CivlCParser.g:315:32: ^( ARGUMENT_LIST castExpression )
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_castExpression.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 5 :
					// CivlCParser.g:316:4: ( SIZEOF LPAREN typeName )=> SIZEOF LPAREN typeName RPAREN
					{
					SIZEOF88=(Token)match(input,SIZEOF,FOLLOW_SIZEOF_in_unaryExpression2007); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SIZEOF.add(SIZEOF88);

					LPAREN89=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_unaryExpression2009); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN89);

					pushFollow(FOLLOW_typeName_in_unaryExpression2011);
					typeName90=typeName();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeName.add(typeName90.getTree());
					RPAREN91=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_unaryExpression2013); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN91);

					// AST REWRITE
					// elements: typeName, SIZEOF
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 317:4: -> ^( SIZEOF TYPE typeName )
					{
						// CivlCParser.g:317:7: ^( SIZEOF TYPE typeName )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_SIZEOF.nextNode(), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(TYPE, "TYPE"));
						adaptor.addChild(root_1, stream_typeName.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 6 :
					// CivlCParser.g:318:4: SIZEOF unaryExpression
					{
					SIZEOF92=(Token)match(input,SIZEOF,FOLLOW_SIZEOF_in_unaryExpression2031); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SIZEOF.add(SIZEOF92);

					pushFollow(FOLLOW_unaryExpression_in_unaryExpression2033);
					unaryExpression93=unaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_unaryExpression.add(unaryExpression93.getTree());
					// AST REWRITE
					// elements: unaryExpression, SIZEOF
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 319:4: -> ^( SIZEOF EXPR unaryExpression )
					{
						// CivlCParser.g:319:7: ^( SIZEOF EXPR unaryExpression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_SIZEOF.nextNode(), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(EXPR, "EXPR"));
						adaptor.addChild(root_1, stream_unaryExpression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 7 :
					// CivlCParser.g:320:4: SCOPEOF unaryExpression
					{
					SCOPEOF94=(Token)match(input,SCOPEOF,FOLLOW_SCOPEOF_in_unaryExpression2051); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SCOPEOF.add(SCOPEOF94);

					pushFollow(FOLLOW_unaryExpression_in_unaryExpression2053);
					unaryExpression95=unaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_unaryExpression.add(unaryExpression95.getTree());
					// AST REWRITE
					// elements: unaryExpression, SCOPEOF
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 321:4: -> ^( SCOPEOF unaryExpression )
					{
						// CivlCParser.g:321:7: ^( SCOPEOF unaryExpression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_SCOPEOF.nextNode(), root_1);
						adaptor.addChild(root_1, stream_unaryExpression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 8 :
					// CivlCParser.g:322:4: ALIGNOF LPAREN typeName RPAREN
					{
					ALIGNOF96=(Token)match(input,ALIGNOF,FOLLOW_ALIGNOF_in_unaryExpression2069); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ALIGNOF.add(ALIGNOF96);

					LPAREN97=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_unaryExpression2071); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN97);

					pushFollow(FOLLOW_typeName_in_unaryExpression2073);
					typeName98=typeName();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeName.add(typeName98.getTree());
					RPAREN99=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_unaryExpression2075); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN99);

					// AST REWRITE
					// elements: ALIGNOF, typeName
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 323:4: -> ^( ALIGNOF typeName )
					{
						// CivlCParser.g:323:7: ^( ALIGNOF typeName )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ALIGNOF.nextNode(), root_1);
						adaptor.addChild(root_1, stream_typeName.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 9 :
					// CivlCParser.g:324:4: spawnExpression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_spawnExpression_in_unaryExpression2091);
					spawnExpression100=spawnExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, spawnExpression100.getTree());

					}
					break;
				case 10 :
					// CivlCParser.g:325:7: callsExpression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_callsExpression_in_unaryExpression2099);
					callsExpression101=callsExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, callsExpression101.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
			DeclarationScope_stack.pop();

		}
		return retval;
	}
	// $ANTLR end "unaryExpression"


	public static class spawnExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "spawnExpression"
	// CivlCParser.g:330:1: spawnExpression : SPAWN postfixExpressionRoot LPAREN argumentExpressionList RPAREN -> ^( SPAWN LPAREN postfixExpressionRoot ABSENT argumentExpressionList RPAREN ) ;
	public final OmpParser_CivlCParser.spawnExpression_return spawnExpression() throws RecognitionException {
		OmpParser_CivlCParser.spawnExpression_return retval = new OmpParser_CivlCParser.spawnExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SPAWN102=null;
		Token LPAREN104=null;
		Token RPAREN106=null;
		ParserRuleReturnScope postfixExpressionRoot103 =null;
		ParserRuleReturnScope argumentExpressionList105 =null;

		Object SPAWN102_tree=null;
		Object LPAREN104_tree=null;
		Object RPAREN106_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_SPAWN=new RewriteRuleTokenStream(adaptor,"token SPAWN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_postfixExpressionRoot=new RewriteRuleSubtreeStream(adaptor,"rule postfixExpressionRoot");
		RewriteRuleSubtreeStream stream_argumentExpressionList=new RewriteRuleSubtreeStream(adaptor,"rule argumentExpressionList");

		try {
			// CivlCParser.g:331:2: ( SPAWN postfixExpressionRoot LPAREN argumentExpressionList RPAREN -> ^( SPAWN LPAREN postfixExpressionRoot ABSENT argumentExpressionList RPAREN ) )
			// CivlCParser.g:331:4: SPAWN postfixExpressionRoot LPAREN argumentExpressionList RPAREN
			{
			SPAWN102=(Token)match(input,SPAWN,FOLLOW_SPAWN_in_spawnExpression2113); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_SPAWN.add(SPAWN102);

			pushFollow(FOLLOW_postfixExpressionRoot_in_spawnExpression2115);
			postfixExpressionRoot103=postfixExpressionRoot();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_postfixExpressionRoot.add(postfixExpressionRoot103.getTree());
			LPAREN104=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_spawnExpression2117); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN104);

			pushFollow(FOLLOW_argumentExpressionList_in_spawnExpression2123);
			argumentExpressionList105=argumentExpressionList();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList105.getTree());
			RPAREN106=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_spawnExpression2125); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN106);

			// AST REWRITE
			// elements: postfixExpressionRoot, SPAWN, RPAREN, argumentExpressionList, LPAREN
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 333:4: -> ^( SPAWN LPAREN postfixExpressionRoot ABSENT argumentExpressionList RPAREN )
			{
				// CivlCParser.g:333:7: ^( SPAWN LPAREN postfixExpressionRoot ABSENT argumentExpressionList RPAREN )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_SPAWN.nextNode(), root_1);
				adaptor.addChild(root_1, stream_LPAREN.nextNode());
				adaptor.addChild(root_1, stream_postfixExpressionRoot.nextTree());
				adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
				adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
				adaptor.addChild(root_1, stream_RPAREN.nextNode());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "spawnExpression"


	public static class callsExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "callsExpression"
	// CivlCParser.g:338:1: callsExpression : CALLS LPAREN postfixExpressionRoot LPAREN argumentExpressionList RPAREN RPAREN -> ^( CALLS LPAREN postfixExpressionRoot ABSENT argumentExpressionList RPAREN ) ;
	public final OmpParser_CivlCParser.callsExpression_return callsExpression() throws RecognitionException {
		OmpParser_CivlCParser.callsExpression_return retval = new OmpParser_CivlCParser.callsExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token CALLS107=null;
		Token LPAREN108=null;
		Token LPAREN110=null;
		Token RPAREN112=null;
		Token RPAREN113=null;
		ParserRuleReturnScope postfixExpressionRoot109 =null;
		ParserRuleReturnScope argumentExpressionList111 =null;

		Object CALLS107_tree=null;
		Object LPAREN108_tree=null;
		Object LPAREN110_tree=null;
		Object RPAREN112_tree=null;
		Object RPAREN113_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_CALLS=new RewriteRuleTokenStream(adaptor,"token CALLS");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_postfixExpressionRoot=new RewriteRuleSubtreeStream(adaptor,"rule postfixExpressionRoot");
		RewriteRuleSubtreeStream stream_argumentExpressionList=new RewriteRuleSubtreeStream(adaptor,"rule argumentExpressionList");

		try {
			// CivlCParser.g:339:2: ( CALLS LPAREN postfixExpressionRoot LPAREN argumentExpressionList RPAREN RPAREN -> ^( CALLS LPAREN postfixExpressionRoot ABSENT argumentExpressionList RPAREN ) )
			// CivlCParser.g:339:4: CALLS LPAREN postfixExpressionRoot LPAREN argumentExpressionList RPAREN RPAREN
			{
			CALLS107=(Token)match(input,CALLS,FOLLOW_CALLS_in_callsExpression2166); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_CALLS.add(CALLS107);

			LPAREN108=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_callsExpression2168); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN108);

			pushFollow(FOLLOW_postfixExpressionRoot_in_callsExpression2170);
			postfixExpressionRoot109=postfixExpressionRoot();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_postfixExpressionRoot.add(postfixExpressionRoot109.getTree());
			LPAREN110=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_callsExpression2172); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN110);

			pushFollow(FOLLOW_argumentExpressionList_in_callsExpression2178);
			argumentExpressionList111=argumentExpressionList();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList111.getTree());
			RPAREN112=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_callsExpression2180); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN112);

			RPAREN113=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_callsExpression2182); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN113);

			// AST REWRITE
			// elements: postfixExpressionRoot, CALLS, argumentExpressionList, RPAREN, LPAREN
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 341:4: -> ^( CALLS LPAREN postfixExpressionRoot ABSENT argumentExpressionList RPAREN )
			{
				// CivlCParser.g:341:7: ^( CALLS LPAREN postfixExpressionRoot ABSENT argumentExpressionList RPAREN )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_CALLS.nextNode(), root_1);
				adaptor.addChild(root_1, stream_LPAREN.nextNode());
				adaptor.addChild(root_1, stream_postfixExpressionRoot.nextTree());
				adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
				adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
				adaptor.addChild(root_1, stream_RPAREN.nextNode());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "callsExpression"


	public static class unaryOperator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "unaryOperator"
	// CivlCParser.g:347:1: unaryOperator : ( AMPERSAND | STAR | PLUS | SUB | TILDE | NOT | BIG_O );
	public final OmpParser_CivlCParser.unaryOperator_return unaryOperator() throws RecognitionException {
		OmpParser_CivlCParser.unaryOperator_return retval = new OmpParser_CivlCParser.unaryOperator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set114=null;

		Object set114_tree=null;

		try {
			// CivlCParser.g:348:2: ( AMPERSAND | STAR | PLUS | SUB | TILDE | NOT | BIG_O )
			// CivlCParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set114=input.LT(1);
			if ( input.LA(1)==AMPERSAND||input.LA(1)==BIG_O||input.LA(1)==NOT||input.LA(1)==PLUS||input.LA(1)==STAR||input.LA(1)==SUB||input.LA(1)==TILDE ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set114));
				state.errorRecovery=false;
				state.failed=false;
			}
			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				MismatchedSetException mse = new MismatchedSetException(null,input);
				throw mse;
			}
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "unaryOperator"


	public static class castExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "castExpression"
	// CivlCParser.g:354:1: castExpression : ( ( LPAREN typeName RPAREN ~ LCURLY )=>l= LPAREN typeName RPAREN castExpression -> ^( CAST typeName castExpression $l) | unaryExpression );
	public final OmpParser_CivlCParser.castExpression_return castExpression() throws RecognitionException {
		DeclarationScope_stack.push(new DeclarationScope_scope());

		OmpParser_CivlCParser.castExpression_return retval = new OmpParser_CivlCParser.castExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token l=null;
		Token RPAREN116=null;
		ParserRuleReturnScope typeName115 =null;
		ParserRuleReturnScope castExpression117 =null;
		ParserRuleReturnScope unaryExpression118 =null;

		Object l_tree=null;
		Object RPAREN116_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_typeName=new RewriteRuleSubtreeStream(adaptor,"rule typeName");
		RewriteRuleSubtreeStream stream_castExpression=new RewriteRuleSubtreeStream(adaptor,"rule castExpression");


			DeclarationScope_stack.peek().isTypedef = false;
			DeclarationScope_stack.peek().typedefNameUsed =false;

		try {
			// CivlCParser.g:360:2: ( ( LPAREN typeName RPAREN ~ LCURLY )=>l= LPAREN typeName RPAREN castExpression -> ^( CAST typeName castExpression $l) | unaryExpression )
			int alt12=2;
			int LA12_0 = input.LA(1);
			if ( (LA12_0==LPAREN) ) {
				int LA12_1 = input.LA(2);
				if ( (synpred3_CivlCParser()) ) {
					alt12=1;
				}
				else if ( (true) ) {
					alt12=2;
				}

			}
			else if ( ((LA12_0 >= ALIGNOF && LA12_0 <= AMPERSAND)||LA12_0==BIG_O||LA12_0==CALLS||LA12_0==CHARACTER_CONSTANT||LA12_0==DERIV||LA12_0==ELLIPSIS||LA12_0==FALSE||LA12_0==FLOATING_CONSTANT||LA12_0==GENERIC||LA12_0==HERE||LA12_0==IDENTIFIER||LA12_0==INTEGER_CONSTANT||LA12_0==MINUSMINUS||LA12_0==NOT||LA12_0==PLUS||LA12_0==PLUSPLUS||LA12_0==PROCNULL||LA12_0==RESULT||LA12_0==SCOPEOF||LA12_0==SELF||(LA12_0 >= SIZEOF && LA12_0 <= STAR)||LA12_0==STRING_LITERAL||LA12_0==SUB||(LA12_0 >= TILDE && LA12_0 <= TRUE)||LA12_0==ROOT) ) {
				alt12=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 12, 0, input);
				throw nvae;
			}

			switch (alt12) {
				case 1 :
					// CivlCParser.g:360:4: ( LPAREN typeName RPAREN ~ LCURLY )=>l= LPAREN typeName RPAREN castExpression
					{
					l=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_castExpression2285); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(l);

					pushFollow(FOLLOW_typeName_in_castExpression2287);
					typeName115=typeName();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeName.add(typeName115.getTree());
					RPAREN116=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_castExpression2289); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN116);

					pushFollow(FOLLOW_castExpression_in_castExpression2291);
					castExpression117=castExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_castExpression.add(castExpression117.getTree());
					// AST REWRITE
					// elements: l, castExpression, typeName
					// token labels: l
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleTokenStream stream_l=new RewriteRuleTokenStream(adaptor,"token l",l);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 361:4: -> ^( CAST typeName castExpression $l)
					{
						// CivlCParser.g:361:7: ^( CAST typeName castExpression $l)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CAST, "CAST"), root_1);
						adaptor.addChild(root_1, stream_typeName.nextTree());
						adaptor.addChild(root_1, stream_castExpression.nextTree());
						adaptor.addChild(root_1, stream_l.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:362:4: unaryExpression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_unaryExpression_in_castExpression2312);
					unaryExpression118=unaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, unaryExpression118.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
			DeclarationScope_stack.pop();

		}
		return retval;
	}
	// $ANTLR end "castExpression"


	public static class remoteExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "remoteExpression"
	// CivlCParser.g:366:1: remoteExpression : ( castExpression -> castExpression ) ( AT y= castExpression -> ^( OPERATOR AT ^( ARGUMENT_LIST $remoteExpression $y) ) )* ;
	public final OmpParser_CivlCParser.remoteExpression_return remoteExpression() throws RecognitionException {
		OmpParser_CivlCParser.remoteExpression_return retval = new OmpParser_CivlCParser.remoteExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token AT120=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope castExpression119 =null;

		Object AT120_tree=null;
		RewriteRuleTokenStream stream_AT=new RewriteRuleTokenStream(adaptor,"token AT");
		RewriteRuleSubtreeStream stream_castExpression=new RewriteRuleSubtreeStream(adaptor,"rule castExpression");

		try {
			// CivlCParser.g:367:2: ( ( castExpression -> castExpression ) ( AT y= castExpression -> ^( OPERATOR AT ^( ARGUMENT_LIST $remoteExpression $y) ) )* )
			// CivlCParser.g:367:3: ( castExpression -> castExpression ) ( AT y= castExpression -> ^( OPERATOR AT ^( ARGUMENT_LIST $remoteExpression $y) ) )*
			{
			// CivlCParser.g:367:3: ( castExpression -> castExpression )
			// CivlCParser.g:367:4: castExpression
			{
			pushFollow(FOLLOW_castExpression_in_remoteExpression2325);
			castExpression119=castExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_castExpression.add(castExpression119.getTree());
			// AST REWRITE
			// elements: castExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 367:19: -> castExpression
			{
				adaptor.addChild(root_0, stream_castExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:368:2: ( AT y= castExpression -> ^( OPERATOR AT ^( ARGUMENT_LIST $remoteExpression $y) ) )*
			loop13:
			while (true) {
				int alt13=2;
				int LA13_0 = input.LA(1);
				if ( (LA13_0==AT) ) {
					alt13=1;
				}

				switch (alt13) {
				case 1 :
					// CivlCParser.g:368:4: AT y= castExpression
					{
					AT120=(Token)match(input,AT,FOLLOW_AT_in_remoteExpression2335); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_AT.add(AT120);

					pushFollow(FOLLOW_castExpression_in_remoteExpression2339);
					y=castExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_castExpression.add(y.getTree());
					// AST REWRITE
					// elements: AT, remoteExpression, y
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 369:4: -> ^( OPERATOR AT ^( ARGUMENT_LIST $remoteExpression $y) )
					{
						// CivlCParser.g:369:7: ^( OPERATOR AT ^( ARGUMENT_LIST $remoteExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_AT.nextNode());
						// CivlCParser.g:369:21: ^( ARGUMENT_LIST $remoteExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop13;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "remoteExpression"


	public static class multiplicativeExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "multiplicativeExpression"
	// CivlCParser.g:374:1: multiplicativeExpression : ( remoteExpression -> remoteExpression ) ( STAR y= remoteExpression -> ^( OPERATOR STAR ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | DIV y= remoteExpression -> ^( OPERATOR DIV ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | MOD y= remoteExpression -> ^( OPERATOR MOD ^( ARGUMENT_LIST $multiplicativeExpression $y) ) )* ;
	public final OmpParser_CivlCParser.multiplicativeExpression_return multiplicativeExpression() throws RecognitionException {
		OmpParser_CivlCParser.multiplicativeExpression_return retval = new OmpParser_CivlCParser.multiplicativeExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token STAR122=null;
		Token DIV123=null;
		Token MOD124=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope remoteExpression121 =null;

		Object STAR122_tree=null;
		Object DIV123_tree=null;
		Object MOD124_tree=null;
		RewriteRuleTokenStream stream_STAR=new RewriteRuleTokenStream(adaptor,"token STAR");
		RewriteRuleTokenStream stream_DIV=new RewriteRuleTokenStream(adaptor,"token DIV");
		RewriteRuleTokenStream stream_MOD=new RewriteRuleTokenStream(adaptor,"token MOD");
		RewriteRuleSubtreeStream stream_remoteExpression=new RewriteRuleSubtreeStream(adaptor,"rule remoteExpression");

		try {
			// CivlCParser.g:375:2: ( ( remoteExpression -> remoteExpression ) ( STAR y= remoteExpression -> ^( OPERATOR STAR ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | DIV y= remoteExpression -> ^( OPERATOR DIV ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | MOD y= remoteExpression -> ^( OPERATOR MOD ^( ARGUMENT_LIST $multiplicativeExpression $y) ) )* )
			// CivlCParser.g:375:4: ( remoteExpression -> remoteExpression ) ( STAR y= remoteExpression -> ^( OPERATOR STAR ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | DIV y= remoteExpression -> ^( OPERATOR DIV ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | MOD y= remoteExpression -> ^( OPERATOR MOD ^( ARGUMENT_LIST $multiplicativeExpression $y) ) )*
			{
			// CivlCParser.g:375:4: ( remoteExpression -> remoteExpression )
			// CivlCParser.g:375:5: remoteExpression
			{
			pushFollow(FOLLOW_remoteExpression_in_multiplicativeExpression2381);
			remoteExpression121=remoteExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_remoteExpression.add(remoteExpression121.getTree());
			// AST REWRITE
			// elements: remoteExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 375:22: -> remoteExpression
			{
				adaptor.addChild(root_0, stream_remoteExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:376:2: ( STAR y= remoteExpression -> ^( OPERATOR STAR ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | DIV y= remoteExpression -> ^( OPERATOR DIV ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | MOD y= remoteExpression -> ^( OPERATOR MOD ^( ARGUMENT_LIST $multiplicativeExpression $y) ) )*
			loop14:
			while (true) {
				int alt14=4;
				switch ( input.LA(1) ) {
				case STAR:
					{
					alt14=1;
					}
					break;
				case DIV:
					{
					alt14=2;
					}
					break;
				case MOD:
					{
					alt14=3;
					}
					break;
				}
				switch (alt14) {
				case 1 :
					// CivlCParser.g:376:4: STAR y= remoteExpression
					{
					STAR122=(Token)match(input,STAR,FOLLOW_STAR_in_multiplicativeExpression2391); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_STAR.add(STAR122);

					pushFollow(FOLLOW_remoteExpression_in_multiplicativeExpression2395);
					y=remoteExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_remoteExpression.add(y.getTree());
					// AST REWRITE
					// elements: multiplicativeExpression, y, STAR
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 377:4: -> ^( OPERATOR STAR ^( ARGUMENT_LIST $multiplicativeExpression $y) )
					{
						// CivlCParser.g:377:7: ^( OPERATOR STAR ^( ARGUMENT_LIST $multiplicativeExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_STAR.nextNode());
						// CivlCParser.g:377:23: ^( ARGUMENT_LIST $multiplicativeExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:378:4: DIV y= remoteExpression
					{
					DIV123=(Token)match(input,DIV,FOLLOW_DIV_in_multiplicativeExpression2421); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DIV.add(DIV123);

					pushFollow(FOLLOW_remoteExpression_in_multiplicativeExpression2425);
					y=remoteExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_remoteExpression.add(y.getTree());
					// AST REWRITE
					// elements: DIV, y, multiplicativeExpression
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 379:4: -> ^( OPERATOR DIV ^( ARGUMENT_LIST $multiplicativeExpression $y) )
					{
						// CivlCParser.g:379:7: ^( OPERATOR DIV ^( ARGUMENT_LIST $multiplicativeExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_DIV.nextNode());
						// CivlCParser.g:379:22: ^( ARGUMENT_LIST $multiplicativeExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// CivlCParser.g:380:7: MOD y= remoteExpression
					{
					MOD124=(Token)match(input,MOD,FOLLOW_MOD_in_multiplicativeExpression2454); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_MOD.add(MOD124);

					pushFollow(FOLLOW_remoteExpression_in_multiplicativeExpression2458);
					y=remoteExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_remoteExpression.add(y.getTree());
					// AST REWRITE
					// elements: y, multiplicativeExpression, MOD
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 381:4: -> ^( OPERATOR MOD ^( ARGUMENT_LIST $multiplicativeExpression $y) )
					{
						// CivlCParser.g:381:7: ^( OPERATOR MOD ^( ARGUMENT_LIST $multiplicativeExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_MOD.nextNode());
						// CivlCParser.g:381:22: ^( ARGUMENT_LIST $multiplicativeExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop14;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "multiplicativeExpression"


	public static class additiveExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "additiveExpression"
	// CivlCParser.g:386:1: additiveExpression : ( multiplicativeExpression -> multiplicativeExpression ) ( PLUS y= multiplicativeExpression -> ^( OPERATOR PLUS ^( ARGUMENT_LIST $additiveExpression $y) ) | SUB y= multiplicativeExpression -> ^( OPERATOR SUB ^( ARGUMENT_LIST $additiveExpression $y) ) )* ;
	public final OmpParser_CivlCParser.additiveExpression_return additiveExpression() throws RecognitionException {
		OmpParser_CivlCParser.additiveExpression_return retval = new OmpParser_CivlCParser.additiveExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PLUS126=null;
		Token SUB127=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope multiplicativeExpression125 =null;

		Object PLUS126_tree=null;
		Object SUB127_tree=null;
		RewriteRuleTokenStream stream_PLUS=new RewriteRuleTokenStream(adaptor,"token PLUS");
		RewriteRuleTokenStream stream_SUB=new RewriteRuleTokenStream(adaptor,"token SUB");
		RewriteRuleSubtreeStream stream_multiplicativeExpression=new RewriteRuleSubtreeStream(adaptor,"rule multiplicativeExpression");

		try {
			// CivlCParser.g:387:2: ( ( multiplicativeExpression -> multiplicativeExpression ) ( PLUS y= multiplicativeExpression -> ^( OPERATOR PLUS ^( ARGUMENT_LIST $additiveExpression $y) ) | SUB y= multiplicativeExpression -> ^( OPERATOR SUB ^( ARGUMENT_LIST $additiveExpression $y) ) )* )
			// CivlCParser.g:387:4: ( multiplicativeExpression -> multiplicativeExpression ) ( PLUS y= multiplicativeExpression -> ^( OPERATOR PLUS ^( ARGUMENT_LIST $additiveExpression $y) ) | SUB y= multiplicativeExpression -> ^( OPERATOR SUB ^( ARGUMENT_LIST $additiveExpression $y) ) )*
			{
			// CivlCParser.g:387:4: ( multiplicativeExpression -> multiplicativeExpression )
			// CivlCParser.g:387:5: multiplicativeExpression
			{
			pushFollow(FOLLOW_multiplicativeExpression_in_additiveExpression2500);
			multiplicativeExpression125=multiplicativeExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_multiplicativeExpression.add(multiplicativeExpression125.getTree());
			// AST REWRITE
			// elements: multiplicativeExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 387:30: -> multiplicativeExpression
			{
				adaptor.addChild(root_0, stream_multiplicativeExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:388:9: ( PLUS y= multiplicativeExpression -> ^( OPERATOR PLUS ^( ARGUMENT_LIST $additiveExpression $y) ) | SUB y= multiplicativeExpression -> ^( OPERATOR SUB ^( ARGUMENT_LIST $additiveExpression $y) ) )*
			loop15:
			while (true) {
				int alt15=3;
				int LA15_0 = input.LA(1);
				if ( (LA15_0==PLUS) ) {
					alt15=1;
				}
				else if ( (LA15_0==SUB) ) {
					alt15=2;
				}

				switch (alt15) {
				case 1 :
					// CivlCParser.g:388:11: PLUS y= multiplicativeExpression
					{
					PLUS126=(Token)match(input,PLUS,FOLLOW_PLUS_in_additiveExpression2517); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_PLUS.add(PLUS126);

					pushFollow(FOLLOW_multiplicativeExpression_in_additiveExpression2521);
					y=multiplicativeExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_multiplicativeExpression.add(y.getTree());
					// AST REWRITE
					// elements: PLUS, additiveExpression, y
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 389:11: -> ^( OPERATOR PLUS ^( ARGUMENT_LIST $additiveExpression $y) )
					{
						// CivlCParser.g:389:14: ^( OPERATOR PLUS ^( ARGUMENT_LIST $additiveExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_PLUS.nextNode());
						// CivlCParser.g:389:30: ^( ARGUMENT_LIST $additiveExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:390:11: SUB y= multiplicativeExpression
					{
					SUB127=(Token)match(input,SUB,FOLLOW_SUB_in_additiveExpression2561); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SUB.add(SUB127);

					pushFollow(FOLLOW_multiplicativeExpression_in_additiveExpression2565);
					y=multiplicativeExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_multiplicativeExpression.add(y.getTree());
					// AST REWRITE
					// elements: y, additiveExpression, SUB
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 391:11: -> ^( OPERATOR SUB ^( ARGUMENT_LIST $additiveExpression $y) )
					{
						// CivlCParser.g:391:14: ^( OPERATOR SUB ^( ARGUMENT_LIST $additiveExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_SUB.nextNode());
						// CivlCParser.g:391:29: ^( ARGUMENT_LIST $additiveExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop15;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "additiveExpression"


	public static class rangeExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "rangeExpression"
	// CivlCParser.g:397:1: rangeExpression : ( additiveExpression -> additiveExpression ) ( DOTDOT y= additiveExpression ( -> ^( DOTDOT $rangeExpression $y) | HASH z= additiveExpression -> ^( DOTDOT $rangeExpression $y $z) ) )? ;
	public final OmpParser_CivlCParser.rangeExpression_return rangeExpression() throws RecognitionException {
		OmpParser_CivlCParser.rangeExpression_return retval = new OmpParser_CivlCParser.rangeExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token DOTDOT129=null;
		Token HASH130=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope z =null;
		ParserRuleReturnScope additiveExpression128 =null;

		Object DOTDOT129_tree=null;
		Object HASH130_tree=null;
		RewriteRuleTokenStream stream_HASH=new RewriteRuleTokenStream(adaptor,"token HASH");
		RewriteRuleTokenStream stream_DOTDOT=new RewriteRuleTokenStream(adaptor,"token DOTDOT");
		RewriteRuleSubtreeStream stream_additiveExpression=new RewriteRuleSubtreeStream(adaptor,"rule additiveExpression");

		try {
			// CivlCParser.g:398:2: ( ( additiveExpression -> additiveExpression ) ( DOTDOT y= additiveExpression ( -> ^( DOTDOT $rangeExpression $y) | HASH z= additiveExpression -> ^( DOTDOT $rangeExpression $y $z) ) )? )
			// CivlCParser.g:398:4: ( additiveExpression -> additiveExpression ) ( DOTDOT y= additiveExpression ( -> ^( DOTDOT $rangeExpression $y) | HASH z= additiveExpression -> ^( DOTDOT $rangeExpression $y $z) ) )?
			{
			// CivlCParser.g:398:4: ( additiveExpression -> additiveExpression )
			// CivlCParser.g:398:5: additiveExpression
			{
			pushFollow(FOLLOW_additiveExpression_in_rangeExpression2619);
			additiveExpression128=additiveExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_additiveExpression.add(additiveExpression128.getTree());
			// AST REWRITE
			// elements: additiveExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 398:24: -> additiveExpression
			{
				adaptor.addChild(root_0, stream_additiveExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:399:7: ( DOTDOT y= additiveExpression ( -> ^( DOTDOT $rangeExpression $y) | HASH z= additiveExpression -> ^( DOTDOT $rangeExpression $y $z) ) )?
			int alt17=2;
			int LA17_0 = input.LA(1);
			if ( (LA17_0==DOTDOT) ) {
				alt17=1;
			}
			switch (alt17) {
				case 1 :
					// CivlCParser.g:399:9: DOTDOT y= additiveExpression ( -> ^( DOTDOT $rangeExpression $y) | HASH z= additiveExpression -> ^( DOTDOT $rangeExpression $y $z) )
					{
					DOTDOT129=(Token)match(input,DOTDOT,FOLLOW_DOTDOT_in_rangeExpression2634); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOTDOT.add(DOTDOT129);

					pushFollow(FOLLOW_additiveExpression_in_rangeExpression2638);
					y=additiveExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_additiveExpression.add(y.getTree());
					// CivlCParser.g:400:9: ( -> ^( DOTDOT $rangeExpression $y) | HASH z= additiveExpression -> ^( DOTDOT $rangeExpression $y $z) )
					int alt16=2;
					int LA16_0 = input.LA(1);
					if ( ((LA16_0 >= ABSTRACT && LA16_0 <= ALIGNAS)||(LA16_0 >= AMPERSAND && LA16_0 <= AND)||LA16_0==ASSIGNS||(LA16_0 >= ATOMIC && LA16_0 <= AUTO)||LA16_0==BITOR||LA16_0==BITXOR||LA16_0==BOOL||LA16_0==CHAR||(LA16_0 >= COLON && LA16_0 <= COMMA)||(LA16_0 >= COMPLEX && LA16_0 <= CONST)||LA16_0==DEPENDS||LA16_0==DEVICE||LA16_0==DOMAIN||LA16_0==DOUBLE||(LA16_0 >= ENSURES && LA16_0 <= EQUALS)||LA16_0==EXTERN||(LA16_0 >= FATOMIC && LA16_0 <= FLOAT)||LA16_0==GLOBAL||(LA16_0 >= GT && LA16_0 <= GUARD)||LA16_0==IDENTIFIER||(LA16_0 >= IMPLIES && LA16_0 <= INT)||LA16_0==LCURLY||LA16_0==LONG||(LA16_0 >= LT && LA16_0 <= LTE)||LA16_0==NEQ||LA16_0==NORETURN||LA16_0==OR||LA16_0==OUTPUT||(LA16_0 >= PURE && LA16_0 <= RESTRICT)||(LA16_0 >= REXCON && LA16_0 <= RPAREN)||LA16_0==RSQUARE||(LA16_0 >= SEMI && LA16_0 <= SHIFTLEFT)||LA16_0==SHIFTRIGHT||(LA16_0 >= SHORT && LA16_0 <= SIGNED)||(LA16_0 >= STATIC && LA16_0 <= STATICASSERT)||LA16_0==STRUCT||(LA16_0 >= SYSTEM && LA16_0 <= THREADLOCAL)||(LA16_0 >= TYPEDEF && LA16_0 <= TYPEOF)||(LA16_0 >= UNION && LA16_0 <= UNSIGNED)||(LA16_0 >= VOID && LA16_0 <= VOLATILE)) ) {
						alt16=1;
					}
					else if ( (LA16_0==HASH) ) {
						alt16=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 16, 0, input);
						throw nvae;
					}

					switch (alt16) {
						case 1 :
							// CivlCParser.g:400:11: 
							{
							// AST REWRITE
							// elements: y, DOTDOT, rangeExpression
							// token labels: 
							// rule labels: retval, y
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
							RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 400:11: -> ^( DOTDOT $rangeExpression $y)
							{
								// CivlCParser.g:400:14: ^( DOTDOT $rangeExpression $y)
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot(stream_DOTDOT.nextNode(), root_1);
								adaptor.addChild(root_1, stream_retval.nextTree());
								adaptor.addChild(root_1, stream_y.nextTree());
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;
						case 2 :
							// CivlCParser.g:401:11: HASH z= additiveExpression
							{
							HASH130=(Token)match(input,HASH,FOLLOW_HASH_in_rangeExpression2672); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_HASH.add(HASH130);

							pushFollow(FOLLOW_additiveExpression_in_rangeExpression2676);
							z=additiveExpression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_additiveExpression.add(z.getTree());
							// AST REWRITE
							// elements: rangeExpression, y, DOTDOT, z
							// token labels: 
							// rule labels: retval, z, y
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
							RewriteRuleSubtreeStream stream_z=new RewriteRuleSubtreeStream(adaptor,"rule z",z!=null?z.getTree():null);
							RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 402:11: -> ^( DOTDOT $rangeExpression $y $z)
							{
								// CivlCParser.g:402:14: ^( DOTDOT $rangeExpression $y $z)
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot(stream_DOTDOT.nextNode(), root_1);
								adaptor.addChild(root_1, stream_retval.nextTree());
								adaptor.addChild(root_1, stream_y.nextTree());
								adaptor.addChild(root_1, stream_z.nextTree());
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;

					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "rangeExpression"


	public static class shiftExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "shiftExpression"
	// CivlCParser.g:408:1: shiftExpression : ( rangeExpression -> rangeExpression ) ( SHIFTLEFT y= rangeExpression -> ^( OPERATOR SHIFTLEFT ^( ARGUMENT_LIST $shiftExpression $y) ) | SHIFTRIGHT y= rangeExpression -> ^( OPERATOR SHIFTRIGHT ^( ARGUMENT_LIST $shiftExpression $y) ) )* ;
	public final OmpParser_CivlCParser.shiftExpression_return shiftExpression() throws RecognitionException {
		OmpParser_CivlCParser.shiftExpression_return retval = new OmpParser_CivlCParser.shiftExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SHIFTLEFT132=null;
		Token SHIFTRIGHT133=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope rangeExpression131 =null;

		Object SHIFTLEFT132_tree=null;
		Object SHIFTRIGHT133_tree=null;
		RewriteRuleTokenStream stream_SHIFTLEFT=new RewriteRuleTokenStream(adaptor,"token SHIFTLEFT");
		RewriteRuleTokenStream stream_SHIFTRIGHT=new RewriteRuleTokenStream(adaptor,"token SHIFTRIGHT");
		RewriteRuleSubtreeStream stream_rangeExpression=new RewriteRuleSubtreeStream(adaptor,"rule rangeExpression");

		try {
			// CivlCParser.g:409:2: ( ( rangeExpression -> rangeExpression ) ( SHIFTLEFT y= rangeExpression -> ^( OPERATOR SHIFTLEFT ^( ARGUMENT_LIST $shiftExpression $y) ) | SHIFTRIGHT y= rangeExpression -> ^( OPERATOR SHIFTRIGHT ^( ARGUMENT_LIST $shiftExpression $y) ) )* )
			// CivlCParser.g:409:4: ( rangeExpression -> rangeExpression ) ( SHIFTLEFT y= rangeExpression -> ^( OPERATOR SHIFTLEFT ^( ARGUMENT_LIST $shiftExpression $y) ) | SHIFTRIGHT y= rangeExpression -> ^( OPERATOR SHIFTRIGHT ^( ARGUMENT_LIST $shiftExpression $y) ) )*
			{
			// CivlCParser.g:409:4: ( rangeExpression -> rangeExpression )
			// CivlCParser.g:409:5: rangeExpression
			{
			pushFollow(FOLLOW_rangeExpression_in_shiftExpression2737);
			rangeExpression131=rangeExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_rangeExpression.add(rangeExpression131.getTree());
			// AST REWRITE
			// elements: rangeExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 409:21: -> rangeExpression
			{
				adaptor.addChild(root_0, stream_rangeExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:410:9: ( SHIFTLEFT y= rangeExpression -> ^( OPERATOR SHIFTLEFT ^( ARGUMENT_LIST $shiftExpression $y) ) | SHIFTRIGHT y= rangeExpression -> ^( OPERATOR SHIFTRIGHT ^( ARGUMENT_LIST $shiftExpression $y) ) )*
			loop18:
			while (true) {
				int alt18=3;
				int LA18_0 = input.LA(1);
				if ( (LA18_0==SHIFTLEFT) ) {
					alt18=1;
				}
				else if ( (LA18_0==SHIFTRIGHT) ) {
					alt18=2;
				}

				switch (alt18) {
				case 1 :
					// CivlCParser.g:410:11: SHIFTLEFT y= rangeExpression
					{
					SHIFTLEFT132=(Token)match(input,SHIFTLEFT,FOLLOW_SHIFTLEFT_in_shiftExpression2754); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SHIFTLEFT.add(SHIFTLEFT132);

					pushFollow(FOLLOW_rangeExpression_in_shiftExpression2758);
					y=rangeExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_rangeExpression.add(y.getTree());
					// AST REWRITE
					// elements: y, SHIFTLEFT, shiftExpression
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 411:11: -> ^( OPERATOR SHIFTLEFT ^( ARGUMENT_LIST $shiftExpression $y) )
					{
						// CivlCParser.g:411:14: ^( OPERATOR SHIFTLEFT ^( ARGUMENT_LIST $shiftExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_SHIFTLEFT.nextNode());
						// CivlCParser.g:411:35: ^( ARGUMENT_LIST $shiftExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:412:11: SHIFTRIGHT y= rangeExpression
					{
					SHIFTRIGHT133=(Token)match(input,SHIFTRIGHT,FOLLOW_SHIFTRIGHT_in_shiftExpression2798); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SHIFTRIGHT.add(SHIFTRIGHT133);

					pushFollow(FOLLOW_rangeExpression_in_shiftExpression2802);
					y=rangeExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_rangeExpression.add(y.getTree());
					// AST REWRITE
					// elements: shiftExpression, SHIFTRIGHT, y
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 413:11: -> ^( OPERATOR SHIFTRIGHT ^( ARGUMENT_LIST $shiftExpression $y) )
					{
						// CivlCParser.g:413:14: ^( OPERATOR SHIFTRIGHT ^( ARGUMENT_LIST $shiftExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_SHIFTRIGHT.nextNode());
						// CivlCParser.g:413:36: ^( ARGUMENT_LIST $shiftExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop18;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "shiftExpression"


	public static class relationalExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "relationalExpression"
	// CivlCParser.g:418:1: relationalExpression : ( shiftExpression -> shiftExpression ) ( relationalOperator y= shiftExpression -> ^( OPERATOR relationalOperator ^( ARGUMENT_LIST $relationalExpression $y) ) )* ;
	public final OmpParser_CivlCParser.relationalExpression_return relationalExpression() throws RecognitionException {
		OmpParser_CivlCParser.relationalExpression_return retval = new OmpParser_CivlCParser.relationalExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope y =null;
		ParserRuleReturnScope shiftExpression134 =null;
		ParserRuleReturnScope relationalOperator135 =null;

		RewriteRuleSubtreeStream stream_relationalOperator=new RewriteRuleSubtreeStream(adaptor,"rule relationalOperator");
		RewriteRuleSubtreeStream stream_shiftExpression=new RewriteRuleSubtreeStream(adaptor,"rule shiftExpression");

		try {
			// CivlCParser.g:419:2: ( ( shiftExpression -> shiftExpression ) ( relationalOperator y= shiftExpression -> ^( OPERATOR relationalOperator ^( ARGUMENT_LIST $relationalExpression $y) ) )* )
			// CivlCParser.g:419:4: ( shiftExpression -> shiftExpression ) ( relationalOperator y= shiftExpression -> ^( OPERATOR relationalOperator ^( ARGUMENT_LIST $relationalExpression $y) ) )*
			{
			// CivlCParser.g:419:4: ( shiftExpression -> shiftExpression )
			// CivlCParser.g:419:6: shiftExpression
			{
			pushFollow(FOLLOW_shiftExpression_in_relationalExpression2856);
			shiftExpression134=shiftExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_shiftExpression.add(shiftExpression134.getTree());
			// AST REWRITE
			// elements: shiftExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 419:22: -> shiftExpression
			{
				adaptor.addChild(root_0, stream_shiftExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:420:4: ( relationalOperator y= shiftExpression -> ^( OPERATOR relationalOperator ^( ARGUMENT_LIST $relationalExpression $y) ) )*
			loop19:
			while (true) {
				int alt19=2;
				int LA19_0 = input.LA(1);
				if ( ((LA19_0 >= GT && LA19_0 <= GTE)||(LA19_0 >= LT && LA19_0 <= LTE)) ) {
					alt19=1;
				}

				switch (alt19) {
				case 1 :
					// CivlCParser.g:420:6: relationalOperator y= shiftExpression
					{
					pushFollow(FOLLOW_relationalOperator_in_relationalExpression2869);
					relationalOperator135=relationalOperator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_relationalOperator.add(relationalOperator135.getTree());
					pushFollow(FOLLOW_shiftExpression_in_relationalExpression2873);
					y=shiftExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_shiftExpression.add(y.getTree());
					// AST REWRITE
					// elements: relationalOperator, relationalExpression, y
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 421:6: -> ^( OPERATOR relationalOperator ^( ARGUMENT_LIST $relationalExpression $y) )
					{
						// CivlCParser.g:421:9: ^( OPERATOR relationalOperator ^( ARGUMENT_LIST $relationalExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_relationalOperator.nextTree());
						// CivlCParser.g:421:39: ^( ARGUMENT_LIST $relationalExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop19;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "relationalExpression"


	public static class relationalOperator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "relationalOperator"
	// CivlCParser.g:425:1: relationalOperator : ( LT | GT | LTE | GTE );
	public final OmpParser_CivlCParser.relationalOperator_return relationalOperator() throws RecognitionException {
		OmpParser_CivlCParser.relationalOperator_return retval = new OmpParser_CivlCParser.relationalOperator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set136=null;

		Object set136_tree=null;

		try {
			// CivlCParser.g:426:2: ( LT | GT | LTE | GTE )
			// CivlCParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set136=input.LT(1);
			if ( (input.LA(1) >= GT && input.LA(1) <= GTE)||(input.LA(1) >= LT && input.LA(1) <= LTE) ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set136));
				state.errorRecovery=false;
				state.failed=false;
			}
			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				MismatchedSetException mse = new MismatchedSetException(null,input);
				throw mse;
			}
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "relationalOperator"


	public static class equalityExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "equalityExpression"
	// CivlCParser.g:430:1: equalityExpression : ( relationalExpression -> relationalExpression ) ( equalityOperator y= relationalExpression -> ^( OPERATOR equalityOperator ^( ARGUMENT_LIST $equalityExpression $y) ) )* ;
	public final OmpParser_CivlCParser.equalityExpression_return equalityExpression() throws RecognitionException {
		OmpParser_CivlCParser.equalityExpression_return retval = new OmpParser_CivlCParser.equalityExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope y =null;
		ParserRuleReturnScope relationalExpression137 =null;
		ParserRuleReturnScope equalityOperator138 =null;

		RewriteRuleSubtreeStream stream_relationalExpression=new RewriteRuleSubtreeStream(adaptor,"rule relationalExpression");
		RewriteRuleSubtreeStream stream_equalityOperator=new RewriteRuleSubtreeStream(adaptor,"rule equalityOperator");

		try {
			// CivlCParser.g:431:2: ( ( relationalExpression -> relationalExpression ) ( equalityOperator y= relationalExpression -> ^( OPERATOR equalityOperator ^( ARGUMENT_LIST $equalityExpression $y) ) )* )
			// CivlCParser.g:431:4: ( relationalExpression -> relationalExpression ) ( equalityOperator y= relationalExpression -> ^( OPERATOR equalityOperator ^( ARGUMENT_LIST $equalityExpression $y) ) )*
			{
			// CivlCParser.g:431:4: ( relationalExpression -> relationalExpression )
			// CivlCParser.g:431:6: relationalExpression
			{
			pushFollow(FOLLOW_relationalExpression_in_equalityExpression2940);
			relationalExpression137=relationalExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_relationalExpression.add(relationalExpression137.getTree());
			// AST REWRITE
			// elements: relationalExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 431:27: -> relationalExpression
			{
				adaptor.addChild(root_0, stream_relationalExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:432:4: ( equalityOperator y= relationalExpression -> ^( OPERATOR equalityOperator ^( ARGUMENT_LIST $equalityExpression $y) ) )*
			loop20:
			while (true) {
				int alt20=2;
				int LA20_0 = input.LA(1);
				if ( (LA20_0==EQUALS||LA20_0==NEQ) ) {
					alt20=1;
				}

				switch (alt20) {
				case 1 :
					// CivlCParser.g:432:6: equalityOperator y= relationalExpression
					{
					pushFollow(FOLLOW_equalityOperator_in_equalityExpression2953);
					equalityOperator138=equalityOperator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_equalityOperator.add(equalityOperator138.getTree());
					pushFollow(FOLLOW_relationalExpression_in_equalityExpression2957);
					y=relationalExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_relationalExpression.add(y.getTree());
					// AST REWRITE
					// elements: equalityOperator, equalityExpression, y
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 433:6: -> ^( OPERATOR equalityOperator ^( ARGUMENT_LIST $equalityExpression $y) )
					{
						// CivlCParser.g:433:9: ^( OPERATOR equalityOperator ^( ARGUMENT_LIST $equalityExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_equalityOperator.nextTree());
						// CivlCParser.g:433:37: ^( ARGUMENT_LIST $equalityExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop20;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "equalityExpression"


	public static class equalityOperator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "equalityOperator"
	// CivlCParser.g:437:1: equalityOperator : ( EQUALS | NEQ );
	public final OmpParser_CivlCParser.equalityOperator_return equalityOperator() throws RecognitionException {
		OmpParser_CivlCParser.equalityOperator_return retval = new OmpParser_CivlCParser.equalityOperator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set139=null;

		Object set139_tree=null;

		try {
			// CivlCParser.g:438:2: ( EQUALS | NEQ )
			// CivlCParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set139=input.LT(1);
			if ( input.LA(1)==EQUALS||input.LA(1)==NEQ ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set139));
				state.errorRecovery=false;
				state.failed=false;
			}
			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				MismatchedSetException mse = new MismatchedSetException(null,input);
				throw mse;
			}
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "equalityOperator"


	public static class andExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "andExpression"
	// CivlCParser.g:442:1: andExpression : ( equalityExpression -> equalityExpression ) ( AMPERSAND y= equalityExpression -> ^( OPERATOR AMPERSAND ^( ARGUMENT_LIST $andExpression $y) ) )* ;
	public final OmpParser_CivlCParser.andExpression_return andExpression() throws RecognitionException {
		OmpParser_CivlCParser.andExpression_return retval = new OmpParser_CivlCParser.andExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token AMPERSAND141=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope equalityExpression140 =null;

		Object AMPERSAND141_tree=null;
		RewriteRuleTokenStream stream_AMPERSAND=new RewriteRuleTokenStream(adaptor,"token AMPERSAND");
		RewriteRuleSubtreeStream stream_equalityExpression=new RewriteRuleSubtreeStream(adaptor,"rule equalityExpression");

		try {
			// CivlCParser.g:443:2: ( ( equalityExpression -> equalityExpression ) ( AMPERSAND y= equalityExpression -> ^( OPERATOR AMPERSAND ^( ARGUMENT_LIST $andExpression $y) ) )* )
			// CivlCParser.g:443:4: ( equalityExpression -> equalityExpression ) ( AMPERSAND y= equalityExpression -> ^( OPERATOR AMPERSAND ^( ARGUMENT_LIST $andExpression $y) ) )*
			{
			// CivlCParser.g:443:4: ( equalityExpression -> equalityExpression )
			// CivlCParser.g:443:6: equalityExpression
			{
			pushFollow(FOLLOW_equalityExpression_in_andExpression3016);
			equalityExpression140=equalityExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_equalityExpression.add(equalityExpression140.getTree());
			// AST REWRITE
			// elements: equalityExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 443:25: -> equalityExpression
			{
				adaptor.addChild(root_0, stream_equalityExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:444:4: ( AMPERSAND y= equalityExpression -> ^( OPERATOR AMPERSAND ^( ARGUMENT_LIST $andExpression $y) ) )*
			loop21:
			while (true) {
				int alt21=2;
				int LA21_0 = input.LA(1);
				if ( (LA21_0==AMPERSAND) ) {
					alt21=1;
				}

				switch (alt21) {
				case 1 :
					// CivlCParser.g:444:6: AMPERSAND y= equalityExpression
					{
					AMPERSAND141=(Token)match(input,AMPERSAND,FOLLOW_AMPERSAND_in_andExpression3029); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_AMPERSAND.add(AMPERSAND141);

					pushFollow(FOLLOW_equalityExpression_in_andExpression3033);
					y=equalityExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_equalityExpression.add(y.getTree());
					// AST REWRITE
					// elements: andExpression, AMPERSAND, y
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 445:6: -> ^( OPERATOR AMPERSAND ^( ARGUMENT_LIST $andExpression $y) )
					{
						// CivlCParser.g:445:9: ^( OPERATOR AMPERSAND ^( ARGUMENT_LIST $andExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_AMPERSAND.nextNode());
						// CivlCParser.g:445:30: ^( ARGUMENT_LIST $andExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop21;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "andExpression"


	public static class exclusiveOrExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "exclusiveOrExpression"
	// CivlCParser.g:450:1: exclusiveOrExpression : ( andExpression -> andExpression ) ( BITXOR y= andExpression -> ^( OPERATOR BITXOR ^( ARGUMENT_LIST $exclusiveOrExpression $y) ) )* ;
	public final OmpParser_CivlCParser.exclusiveOrExpression_return exclusiveOrExpression() throws RecognitionException {
		OmpParser_CivlCParser.exclusiveOrExpression_return retval = new OmpParser_CivlCParser.exclusiveOrExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token BITXOR143=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope andExpression142 =null;

		Object BITXOR143_tree=null;
		RewriteRuleTokenStream stream_BITXOR=new RewriteRuleTokenStream(adaptor,"token BITXOR");
		RewriteRuleSubtreeStream stream_andExpression=new RewriteRuleSubtreeStream(adaptor,"rule andExpression");

		try {
			// CivlCParser.g:451:2: ( ( andExpression -> andExpression ) ( BITXOR y= andExpression -> ^( OPERATOR BITXOR ^( ARGUMENT_LIST $exclusiveOrExpression $y) ) )* )
			// CivlCParser.g:451:4: ( andExpression -> andExpression ) ( BITXOR y= andExpression -> ^( OPERATOR BITXOR ^( ARGUMENT_LIST $exclusiveOrExpression $y) ) )*
			{
			// CivlCParser.g:451:4: ( andExpression -> andExpression )
			// CivlCParser.g:451:6: andExpression
			{
			pushFollow(FOLLOW_andExpression_in_exclusiveOrExpression3077);
			andExpression142=andExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_andExpression.add(andExpression142.getTree());
			// AST REWRITE
			// elements: andExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 451:20: -> andExpression
			{
				adaptor.addChild(root_0, stream_andExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:452:4: ( BITXOR y= andExpression -> ^( OPERATOR BITXOR ^( ARGUMENT_LIST $exclusiveOrExpression $y) ) )*
			loop22:
			while (true) {
				int alt22=2;
				int LA22_0 = input.LA(1);
				if ( (LA22_0==BITXOR) ) {
					alt22=1;
				}

				switch (alt22) {
				case 1 :
					// CivlCParser.g:452:6: BITXOR y= andExpression
					{
					BITXOR143=(Token)match(input,BITXOR,FOLLOW_BITXOR_in_exclusiveOrExpression3090); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BITXOR.add(BITXOR143);

					pushFollow(FOLLOW_andExpression_in_exclusiveOrExpression3094);
					y=andExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_andExpression.add(y.getTree());
					// AST REWRITE
					// elements: y, BITXOR, exclusiveOrExpression
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 453:6: -> ^( OPERATOR BITXOR ^( ARGUMENT_LIST $exclusiveOrExpression $y) )
					{
						// CivlCParser.g:453:9: ^( OPERATOR BITXOR ^( ARGUMENT_LIST $exclusiveOrExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_BITXOR.nextNode());
						// CivlCParser.g:453:27: ^( ARGUMENT_LIST $exclusiveOrExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop22;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "exclusiveOrExpression"


	public static class inclusiveOrExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "inclusiveOrExpression"
	// CivlCParser.g:458:1: inclusiveOrExpression : ( exclusiveOrExpression -> exclusiveOrExpression ) ( BITOR y= exclusiveOrExpression -> ^( OPERATOR BITOR ^( ARGUMENT_LIST $inclusiveOrExpression $y) ) )* ;
	public final OmpParser_CivlCParser.inclusiveOrExpression_return inclusiveOrExpression() throws RecognitionException {
		OmpParser_CivlCParser.inclusiveOrExpression_return retval = new OmpParser_CivlCParser.inclusiveOrExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token BITOR145=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope exclusiveOrExpression144 =null;

		Object BITOR145_tree=null;
		RewriteRuleTokenStream stream_BITOR=new RewriteRuleTokenStream(adaptor,"token BITOR");
		RewriteRuleSubtreeStream stream_exclusiveOrExpression=new RewriteRuleSubtreeStream(adaptor,"rule exclusiveOrExpression");

		try {
			// CivlCParser.g:459:2: ( ( exclusiveOrExpression -> exclusiveOrExpression ) ( BITOR y= exclusiveOrExpression -> ^( OPERATOR BITOR ^( ARGUMENT_LIST $inclusiveOrExpression $y) ) )* )
			// CivlCParser.g:459:4: ( exclusiveOrExpression -> exclusiveOrExpression ) ( BITOR y= exclusiveOrExpression -> ^( OPERATOR BITOR ^( ARGUMENT_LIST $inclusiveOrExpression $y) ) )*
			{
			// CivlCParser.g:459:4: ( exclusiveOrExpression -> exclusiveOrExpression )
			// CivlCParser.g:459:6: exclusiveOrExpression
			{
			pushFollow(FOLLOW_exclusiveOrExpression_in_inclusiveOrExpression3138);
			exclusiveOrExpression144=exclusiveOrExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_exclusiveOrExpression.add(exclusiveOrExpression144.getTree());
			// AST REWRITE
			// elements: exclusiveOrExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 459:28: -> exclusiveOrExpression
			{
				adaptor.addChild(root_0, stream_exclusiveOrExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:460:4: ( BITOR y= exclusiveOrExpression -> ^( OPERATOR BITOR ^( ARGUMENT_LIST $inclusiveOrExpression $y) ) )*
			loop23:
			while (true) {
				int alt23=2;
				int LA23_0 = input.LA(1);
				if ( (LA23_0==BITOR) ) {
					alt23=1;
				}

				switch (alt23) {
				case 1 :
					// CivlCParser.g:460:6: BITOR y= exclusiveOrExpression
					{
					BITOR145=(Token)match(input,BITOR,FOLLOW_BITOR_in_inclusiveOrExpression3151); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BITOR.add(BITOR145);

					pushFollow(FOLLOW_exclusiveOrExpression_in_inclusiveOrExpression3155);
					y=exclusiveOrExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_exclusiveOrExpression.add(y.getTree());
					// AST REWRITE
					// elements: y, BITOR, inclusiveOrExpression
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 461:6: -> ^( OPERATOR BITOR ^( ARGUMENT_LIST $inclusiveOrExpression $y) )
					{
						// CivlCParser.g:461:9: ^( OPERATOR BITOR ^( ARGUMENT_LIST $inclusiveOrExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_BITOR.nextNode());
						// CivlCParser.g:461:26: ^( ARGUMENT_LIST $inclusiveOrExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop23;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "inclusiveOrExpression"


	public static class logicalAndExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "logicalAndExpression"
	// CivlCParser.g:466:1: logicalAndExpression : ( inclusiveOrExpression -> inclusiveOrExpression ) ( AND y= inclusiveOrExpression -> ^( OPERATOR AND ^( ARGUMENT_LIST $logicalAndExpression $y) ) )* ;
	public final OmpParser_CivlCParser.logicalAndExpression_return logicalAndExpression() throws RecognitionException {
		OmpParser_CivlCParser.logicalAndExpression_return retval = new OmpParser_CivlCParser.logicalAndExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token AND147=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope inclusiveOrExpression146 =null;

		Object AND147_tree=null;
		RewriteRuleTokenStream stream_AND=new RewriteRuleTokenStream(adaptor,"token AND");
		RewriteRuleSubtreeStream stream_inclusiveOrExpression=new RewriteRuleSubtreeStream(adaptor,"rule inclusiveOrExpression");

		try {
			// CivlCParser.g:467:2: ( ( inclusiveOrExpression -> inclusiveOrExpression ) ( AND y= inclusiveOrExpression -> ^( OPERATOR AND ^( ARGUMENT_LIST $logicalAndExpression $y) ) )* )
			// CivlCParser.g:467:4: ( inclusiveOrExpression -> inclusiveOrExpression ) ( AND y= inclusiveOrExpression -> ^( OPERATOR AND ^( ARGUMENT_LIST $logicalAndExpression $y) ) )*
			{
			// CivlCParser.g:467:4: ( inclusiveOrExpression -> inclusiveOrExpression )
			// CivlCParser.g:467:6: inclusiveOrExpression
			{
			pushFollow(FOLLOW_inclusiveOrExpression_in_logicalAndExpression3199);
			inclusiveOrExpression146=inclusiveOrExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_inclusiveOrExpression.add(inclusiveOrExpression146.getTree());
			// AST REWRITE
			// elements: inclusiveOrExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 467:28: -> inclusiveOrExpression
			{
				adaptor.addChild(root_0, stream_inclusiveOrExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:468:4: ( AND y= inclusiveOrExpression -> ^( OPERATOR AND ^( ARGUMENT_LIST $logicalAndExpression $y) ) )*
			loop24:
			while (true) {
				int alt24=2;
				int LA24_0 = input.LA(1);
				if ( (LA24_0==AND) ) {
					alt24=1;
				}

				switch (alt24) {
				case 1 :
					// CivlCParser.g:468:6: AND y= inclusiveOrExpression
					{
					AND147=(Token)match(input,AND,FOLLOW_AND_in_logicalAndExpression3212); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_AND.add(AND147);

					pushFollow(FOLLOW_inclusiveOrExpression_in_logicalAndExpression3216);
					y=inclusiveOrExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_inclusiveOrExpression.add(y.getTree());
					// AST REWRITE
					// elements: y, AND, logicalAndExpression
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 469:6: -> ^( OPERATOR AND ^( ARGUMENT_LIST $logicalAndExpression $y) )
					{
						// CivlCParser.g:469:9: ^( OPERATOR AND ^( ARGUMENT_LIST $logicalAndExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_AND.nextNode());
						// CivlCParser.g:469:24: ^( ARGUMENT_LIST $logicalAndExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop24;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "logicalAndExpression"


	public static class logicalOrExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "logicalOrExpression"
	// CivlCParser.g:474:1: logicalOrExpression : ( logicalAndExpression -> logicalAndExpression ) ( OR y= logicalAndExpression -> ^( OPERATOR OR ^( ARGUMENT_LIST $logicalOrExpression $y) ) )* ;
	public final OmpParser_CivlCParser.logicalOrExpression_return logicalOrExpression() throws RecognitionException {
		OmpParser_CivlCParser.logicalOrExpression_return retval = new OmpParser_CivlCParser.logicalOrExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token OR149=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope logicalAndExpression148 =null;

		Object OR149_tree=null;
		RewriteRuleTokenStream stream_OR=new RewriteRuleTokenStream(adaptor,"token OR");
		RewriteRuleSubtreeStream stream_logicalAndExpression=new RewriteRuleSubtreeStream(adaptor,"rule logicalAndExpression");

		try {
			// CivlCParser.g:475:2: ( ( logicalAndExpression -> logicalAndExpression ) ( OR y= logicalAndExpression -> ^( OPERATOR OR ^( ARGUMENT_LIST $logicalOrExpression $y) ) )* )
			// CivlCParser.g:475:4: ( logicalAndExpression -> logicalAndExpression ) ( OR y= logicalAndExpression -> ^( OPERATOR OR ^( ARGUMENT_LIST $logicalOrExpression $y) ) )*
			{
			// CivlCParser.g:475:4: ( logicalAndExpression -> logicalAndExpression )
			// CivlCParser.g:475:6: logicalAndExpression
			{
			pushFollow(FOLLOW_logicalAndExpression_in_logicalOrExpression3260);
			logicalAndExpression148=logicalAndExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_logicalAndExpression.add(logicalAndExpression148.getTree());
			// AST REWRITE
			// elements: logicalAndExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 475:27: -> logicalAndExpression
			{
				adaptor.addChild(root_0, stream_logicalAndExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:476:4: ( OR y= logicalAndExpression -> ^( OPERATOR OR ^( ARGUMENT_LIST $logicalOrExpression $y) ) )*
			loop25:
			while (true) {
				int alt25=2;
				int LA25_0 = input.LA(1);
				if ( (LA25_0==OR) ) {
					alt25=1;
				}

				switch (alt25) {
				case 1 :
					// CivlCParser.g:476:6: OR y= logicalAndExpression
					{
					OR149=(Token)match(input,OR,FOLLOW_OR_in_logicalOrExpression3273); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_OR.add(OR149);

					pushFollow(FOLLOW_logicalAndExpression_in_logicalOrExpression3277);
					y=logicalAndExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_logicalAndExpression.add(y.getTree());
					// AST REWRITE
					// elements: y, logicalOrExpression, OR
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 477:6: -> ^( OPERATOR OR ^( ARGUMENT_LIST $logicalOrExpression $y) )
					{
						// CivlCParser.g:477:9: ^( OPERATOR OR ^( ARGUMENT_LIST $logicalOrExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_OR.nextNode());
						// CivlCParser.g:477:23: ^( ARGUMENT_LIST $logicalOrExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop25;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "logicalOrExpression"


	public static class logicalImpliesExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "logicalImpliesExpression"
	// CivlCParser.g:482:1: logicalImpliesExpression : ( logicalOrExpression -> logicalOrExpression ) ( IMPLIES y= logicalOrExpression -> ^( OPERATOR IMPLIES ^( ARGUMENT_LIST $logicalImpliesExpression $y) ) )* ;
	public final OmpParser_CivlCParser.logicalImpliesExpression_return logicalImpliesExpression() throws RecognitionException {
		OmpParser_CivlCParser.logicalImpliesExpression_return retval = new OmpParser_CivlCParser.logicalImpliesExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token IMPLIES151=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope logicalOrExpression150 =null;

		Object IMPLIES151_tree=null;
		RewriteRuleTokenStream stream_IMPLIES=new RewriteRuleTokenStream(adaptor,"token IMPLIES");
		RewriteRuleSubtreeStream stream_logicalOrExpression=new RewriteRuleSubtreeStream(adaptor,"rule logicalOrExpression");

		try {
			// CivlCParser.g:483:2: ( ( logicalOrExpression -> logicalOrExpression ) ( IMPLIES y= logicalOrExpression -> ^( OPERATOR IMPLIES ^( ARGUMENT_LIST $logicalImpliesExpression $y) ) )* )
			// CivlCParser.g:483:4: ( logicalOrExpression -> logicalOrExpression ) ( IMPLIES y= logicalOrExpression -> ^( OPERATOR IMPLIES ^( ARGUMENT_LIST $logicalImpliesExpression $y) ) )*
			{
			// CivlCParser.g:483:4: ( logicalOrExpression -> logicalOrExpression )
			// CivlCParser.g:483:6: logicalOrExpression
			{
			pushFollow(FOLLOW_logicalOrExpression_in_logicalImpliesExpression3322);
			logicalOrExpression150=logicalOrExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_logicalOrExpression.add(logicalOrExpression150.getTree());
			// AST REWRITE
			// elements: logicalOrExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 483:26: -> logicalOrExpression
			{
				adaptor.addChild(root_0, stream_logicalOrExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:484:4: ( IMPLIES y= logicalOrExpression -> ^( OPERATOR IMPLIES ^( ARGUMENT_LIST $logicalImpliesExpression $y) ) )*
			loop26:
			while (true) {
				int alt26=2;
				int LA26_0 = input.LA(1);
				if ( (LA26_0==IMPLIES) ) {
					alt26=1;
				}

				switch (alt26) {
				case 1 :
					// CivlCParser.g:484:6: IMPLIES y= logicalOrExpression
					{
					IMPLIES151=(Token)match(input,IMPLIES,FOLLOW_IMPLIES_in_logicalImpliesExpression3335); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IMPLIES.add(IMPLIES151);

					pushFollow(FOLLOW_logicalOrExpression_in_logicalImpliesExpression3339);
					y=logicalOrExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_logicalOrExpression.add(y.getTree());
					// AST REWRITE
					// elements: logicalImpliesExpression, IMPLIES, y
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 485:6: -> ^( OPERATOR IMPLIES ^( ARGUMENT_LIST $logicalImpliesExpression $y) )
					{
						// CivlCParser.g:485:9: ^( OPERATOR IMPLIES ^( ARGUMENT_LIST $logicalImpliesExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_IMPLIES.nextNode());
						// CivlCParser.g:485:28: ^( ARGUMENT_LIST $logicalImpliesExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop26;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "logicalImpliesExpression"


	public static class conditionalExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "conditionalExpression"
	// CivlCParser.g:490:1: conditionalExpression : logicalImpliesExpression ( -> logicalImpliesExpression | QMARK expression COLON conditionalExpression -> ^( OPERATOR QMARK ^( ARGUMENT_LIST logicalImpliesExpression expression conditionalExpression ) ) ) ;
	public final OmpParser_CivlCParser.conditionalExpression_return conditionalExpression() throws RecognitionException {
		OmpParser_CivlCParser.conditionalExpression_return retval = new OmpParser_CivlCParser.conditionalExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token QMARK153=null;
		Token COLON155=null;
		ParserRuleReturnScope logicalImpliesExpression152 =null;
		ParserRuleReturnScope expression154 =null;
		ParserRuleReturnScope conditionalExpression156 =null;

		Object QMARK153_tree=null;
		Object COLON155_tree=null;
		RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
		RewriteRuleTokenStream stream_QMARK=new RewriteRuleTokenStream(adaptor,"token QMARK");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_logicalImpliesExpression=new RewriteRuleSubtreeStream(adaptor,"rule logicalImpliesExpression");
		RewriteRuleSubtreeStream stream_conditionalExpression=new RewriteRuleSubtreeStream(adaptor,"rule conditionalExpression");

		try {
			// CivlCParser.g:491:2: ( logicalImpliesExpression ( -> logicalImpliesExpression | QMARK expression COLON conditionalExpression -> ^( OPERATOR QMARK ^( ARGUMENT_LIST logicalImpliesExpression expression conditionalExpression ) ) ) )
			// CivlCParser.g:491:4: logicalImpliesExpression ( -> logicalImpliesExpression | QMARK expression COLON conditionalExpression -> ^( OPERATOR QMARK ^( ARGUMENT_LIST logicalImpliesExpression expression conditionalExpression ) ) )
			{
			pushFollow(FOLLOW_logicalImpliesExpression_in_conditionalExpression3385);
			logicalImpliesExpression152=logicalImpliesExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_logicalImpliesExpression.add(logicalImpliesExpression152.getTree());
			// CivlCParser.g:492:2: ( -> logicalImpliesExpression | QMARK expression COLON conditionalExpression -> ^( OPERATOR QMARK ^( ARGUMENT_LIST logicalImpliesExpression expression conditionalExpression ) ) )
			int alt27=2;
			int LA27_0 = input.LA(1);
			if ( ((LA27_0 >= ABSTRACT && LA27_0 <= ALIGNAS)||LA27_0==ASSIGNS||(LA27_0 >= ATOMIC && LA27_0 <= AUTO)||LA27_0==BOOL||LA27_0==CHAR||(LA27_0 >= COLON && LA27_0 <= COMMA)||(LA27_0 >= COMPLEX && LA27_0 <= CONST)||LA27_0==DEPENDS||LA27_0==DEVICE||LA27_0==DOMAIN||LA27_0==DOUBLE||(LA27_0 >= ENSURES && LA27_0 <= ENUM)||LA27_0==EXTERN||(LA27_0 >= FATOMIC && LA27_0 <= FLOAT)||LA27_0==GLOBAL||LA27_0==GUARD||LA27_0==IDENTIFIER||(LA27_0 >= INLINE && LA27_0 <= INT)||LA27_0==LCURLY||LA27_0==LONG||LA27_0==NORETURN||LA27_0==OUTPUT||LA27_0==PURE||(LA27_0 >= RANGE && LA27_0 <= RESTRICT)||(LA27_0 >= REXCON && LA27_0 <= RPAREN)||LA27_0==RSQUARE||(LA27_0 >= SEMI && LA27_0 <= SHARED)||(LA27_0 >= SHORT && LA27_0 <= SIGNED)||(LA27_0 >= STATIC && LA27_0 <= STATICASSERT)||LA27_0==STRUCT||(LA27_0 >= SYSTEM && LA27_0 <= THREADLOCAL)||(LA27_0 >= TYPEDEF && LA27_0 <= TYPEOF)||(LA27_0 >= UNION && LA27_0 <= UNSIGNED)||(LA27_0 >= VOID && LA27_0 <= VOLATILE)) ) {
				alt27=1;
			}
			else if ( (LA27_0==QMARK) ) {
				alt27=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 27, 0, input);
				throw nvae;
			}

			switch (alt27) {
				case 1 :
					// CivlCParser.g:492:4: 
					{
					// AST REWRITE
					// elements: logicalImpliesExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 492:4: -> logicalImpliesExpression
					{
						adaptor.addChild(root_0, stream_logicalImpliesExpression.nextTree());
					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:493:8: QMARK expression COLON conditionalExpression
					{
					QMARK153=(Token)match(input,QMARK,FOLLOW_QMARK_in_conditionalExpression3401); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_QMARK.add(QMARK153);

					pushFollow(FOLLOW_expression_in_conditionalExpression3403);
					expression154=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression154.getTree());
					COLON155=(Token)match(input,COLON,FOLLOW_COLON_in_conditionalExpression3405); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COLON.add(COLON155);

					pushFollow(FOLLOW_conditionalExpression_in_conditionalExpression3407);
					conditionalExpression156=conditionalExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_conditionalExpression.add(conditionalExpression156.getTree());
					// AST REWRITE
					// elements: conditionalExpression, logicalImpliesExpression, QMARK, expression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 494:8: -> ^( OPERATOR QMARK ^( ARGUMENT_LIST logicalImpliesExpression expression conditionalExpression ) )
					{
						// CivlCParser.g:494:11: ^( OPERATOR QMARK ^( ARGUMENT_LIST logicalImpliesExpression expression conditionalExpression ) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_QMARK.nextNode());
						// CivlCParser.g:495:13: ^( ARGUMENT_LIST logicalImpliesExpression expression conditionalExpression )
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_logicalImpliesExpression.nextTree());
						adaptor.addChild(root_2, stream_expression.nextTree());
						adaptor.addChild(root_2, stream_conditionalExpression.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "conditionalExpression"


	public static class quantifierExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "quantifierExpression"
	// CivlCParser.g:504:1: quantifierExpression : ( quantifier LCURLY type= typeName id= IDENTIFIER BITOR restrict= conditionalExpression RCURLY cond= assignmentExpression -> ^( quantifier $type $id $restrict $cond) | quantifier LCURLY id= IDENTIFIER ASSIGN lower= additiveExpression DOTDOT upper= additiveExpression RCURLY cond= assignmentExpression -> ^( quantifier $id $lower $upper $cond) );
	public final OmpParser_CivlCParser.quantifierExpression_return quantifierExpression() throws RecognitionException {
		OmpParser_CivlCParser.quantifierExpression_return retval = new OmpParser_CivlCParser.quantifierExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token id=null;
		Token LCURLY158=null;
		Token BITOR159=null;
		Token RCURLY160=null;
		Token LCURLY162=null;
		Token ASSIGN163=null;
		Token DOTDOT164=null;
		Token RCURLY165=null;
		ParserRuleReturnScope type =null;
		ParserRuleReturnScope restrict =null;
		ParserRuleReturnScope cond =null;
		ParserRuleReturnScope lower =null;
		ParserRuleReturnScope upper =null;
		ParserRuleReturnScope quantifier157 =null;
		ParserRuleReturnScope quantifier161 =null;

		Object id_tree=null;
		Object LCURLY158_tree=null;
		Object BITOR159_tree=null;
		Object RCURLY160_tree=null;
		Object LCURLY162_tree=null;
		Object ASSIGN163_tree=null;
		Object DOTDOT164_tree=null;
		Object RCURLY165_tree=null;
		RewriteRuleTokenStream stream_LCURLY=new RewriteRuleTokenStream(adaptor,"token LCURLY");
		RewriteRuleTokenStream stream_DOTDOT=new RewriteRuleTokenStream(adaptor,"token DOTDOT");
		RewriteRuleTokenStream stream_BITOR=new RewriteRuleTokenStream(adaptor,"token BITOR");
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
		RewriteRuleTokenStream stream_RCURLY=new RewriteRuleTokenStream(adaptor,"token RCURLY");
		RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
		RewriteRuleSubtreeStream stream_quantifier=new RewriteRuleSubtreeStream(adaptor,"rule quantifier");
		RewriteRuleSubtreeStream stream_typeName=new RewriteRuleSubtreeStream(adaptor,"rule typeName");
		RewriteRuleSubtreeStream stream_assignmentExpression=new RewriteRuleSubtreeStream(adaptor,"rule assignmentExpression");
		RewriteRuleSubtreeStream stream_additiveExpression=new RewriteRuleSubtreeStream(adaptor,"rule additiveExpression");
		RewriteRuleSubtreeStream stream_conditionalExpression=new RewriteRuleSubtreeStream(adaptor,"rule conditionalExpression");

		try {
			// CivlCParser.g:505:2: ( quantifier LCURLY type= typeName id= IDENTIFIER BITOR restrict= conditionalExpression RCURLY cond= assignmentExpression -> ^( quantifier $type $id $restrict $cond) | quantifier LCURLY id= IDENTIFIER ASSIGN lower= additiveExpression DOTDOT upper= additiveExpression RCURLY cond= assignmentExpression -> ^( quantifier $id $lower $upper $cond) )
			int alt28=2;
			int LA28_0 = input.LA(1);
			if ( (LA28_0==EXISTS||LA28_0==FORALL||LA28_0==UNIFORM) ) {
				int LA28_1 = input.LA(2);
				if ( (LA28_1==LCURLY) ) {
					int LA28_2 = input.LA(3);
					if ( (LA28_2==IDENTIFIER) ) {
						int LA28_3 = input.LA(4);
						if ( (LA28_3==ASSIGN) ) {
							alt28=2;
						}
						else if ( (LA28_3==ATOMIC||LA28_3==BOOL||LA28_3==CHAR||(LA28_3 >= COMPLEX && LA28_3 <= CONST)||LA28_3==DOMAIN||LA28_3==DOUBLE||LA28_3==ENUM||LA28_3==FLOAT||LA28_3==IDENTIFIER||(LA28_3 >= INPUT && LA28_3 <= INT)||(LA28_3 >= LONG && LA28_3 <= LPAREN)||LA28_3==LSQUARE||LA28_3==OUTPUT||LA28_3==RANGE||LA28_3==REAL||LA28_3==RESTRICT||(LA28_3 >= SHORT && LA28_3 <= SIGNED)||LA28_3==STAR||LA28_3==STRUCT||LA28_3==TYPEOF||(LA28_3 >= UNION && LA28_3 <= UNSIGNED)||(LA28_3 >= VOID && LA28_3 <= VOLATILE)) ) {
							alt28=1;
						}

						else {
							if (state.backtracking>0) {state.failed=true; return retval;}
							int nvaeMark = input.mark();
							try {
								for (int nvaeConsume = 0; nvaeConsume < 4 - 1; nvaeConsume++) {
									input.consume();
								}
								NoViableAltException nvae =
									new NoViableAltException("", 28, 3, input);
								throw nvae;
							} finally {
								input.rewind(nvaeMark);
							}
						}

					}
					else if ( (LA28_2==ATOMIC||LA28_2==BOOL||LA28_2==CHAR||(LA28_2 >= COMPLEX && LA28_2 <= CONST)||LA28_2==DOMAIN||LA28_2==DOUBLE||LA28_2==ENUM||LA28_2==FLOAT||(LA28_2 >= INPUT && LA28_2 <= INT)||LA28_2==LONG||LA28_2==OUTPUT||LA28_2==RANGE||LA28_2==REAL||LA28_2==RESTRICT||(LA28_2 >= SHORT && LA28_2 <= SIGNED)||LA28_2==STRUCT||LA28_2==TYPEOF||(LA28_2 >= UNION && LA28_2 <= UNSIGNED)||(LA28_2 >= VOID && LA28_2 <= VOLATILE)) ) {
						alt28=1;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 28, 2, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 28, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 28, 0, input);
				throw nvae;
			}

			switch (alt28) {
				case 1 :
					// CivlCParser.g:505:4: quantifier LCURLY type= typeName id= IDENTIFIER BITOR restrict= conditionalExpression RCURLY cond= assignmentExpression
					{
					pushFollow(FOLLOW_quantifier_in_quantifierExpression3506);
					quantifier157=quantifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_quantifier.add(quantifier157.getTree());
					LCURLY158=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_quantifierExpression3508); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY158);

					pushFollow(FOLLOW_typeName_in_quantifierExpression3512);
					type=typeName();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeName.add(type.getTree());
					id=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_quantifierExpression3516); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IDENTIFIER.add(id);

					BITOR159=(Token)match(input,BITOR,FOLLOW_BITOR_in_quantifierExpression3521); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BITOR.add(BITOR159);

					pushFollow(FOLLOW_conditionalExpression_in_quantifierExpression3525);
					restrict=conditionalExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_conditionalExpression.add(restrict.getTree());
					RCURLY160=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_quantifierExpression3527); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY160);

					pushFollow(FOLLOW_assignmentExpression_in_quantifierExpression3535);
					cond=assignmentExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_assignmentExpression.add(cond.getTree());
					// AST REWRITE
					// elements: type, cond, restrict, id, quantifier
					// token labels: id
					// rule labels: retval, type, cond, restrict
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleTokenStream stream_id=new RewriteRuleTokenStream(adaptor,"token id",id);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_type=new RewriteRuleSubtreeStream(adaptor,"rule type",type!=null?type.getTree():null);
					RewriteRuleSubtreeStream stream_cond=new RewriteRuleSubtreeStream(adaptor,"rule cond",cond!=null?cond.getTree():null);
					RewriteRuleSubtreeStream stream_restrict=new RewriteRuleSubtreeStream(adaptor,"rule restrict",restrict!=null?restrict.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 508:4: -> ^( quantifier $type $id $restrict $cond)
					{
						// CivlCParser.g:508:7: ^( quantifier $type $id $restrict $cond)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_quantifier.nextNode(), root_1);
						adaptor.addChild(root_1, stream_type.nextTree());
						adaptor.addChild(root_1, stream_id.nextNode());
						adaptor.addChild(root_1, stream_restrict.nextTree());
						adaptor.addChild(root_1, stream_cond.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:509:4: quantifier LCURLY id= IDENTIFIER ASSIGN lower= additiveExpression DOTDOT upper= additiveExpression RCURLY cond= assignmentExpression
					{
					pushFollow(FOLLOW_quantifier_in_quantifierExpression3561);
					quantifier161=quantifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_quantifier.add(quantifier161.getTree());
					LCURLY162=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_quantifierExpression3563); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY162);

					id=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_quantifierExpression3567); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IDENTIFIER.add(id);

					ASSIGN163=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_quantifierExpression3569); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(ASSIGN163);

					pushFollow(FOLLOW_additiveExpression_in_quantifierExpression3576);
					lower=additiveExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_additiveExpression.add(lower.getTree());
					DOTDOT164=(Token)match(input,DOTDOT,FOLLOW_DOTDOT_in_quantifierExpression3578); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOTDOT.add(DOTDOT164);

					pushFollow(FOLLOW_additiveExpression_in_quantifierExpression3582);
					upper=additiveExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_additiveExpression.add(upper.getTree());
					RCURLY165=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_quantifierExpression3587); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY165);

					pushFollow(FOLLOW_assignmentExpression_in_quantifierExpression3591);
					cond=assignmentExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_assignmentExpression.add(cond.getTree());
					// AST REWRITE
					// elements: cond, id, upper, lower, quantifier
					// token labels: id
					// rule labels: upper, retval, lower, cond
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleTokenStream stream_id=new RewriteRuleTokenStream(adaptor,"token id",id);
					RewriteRuleSubtreeStream stream_upper=new RewriteRuleSubtreeStream(adaptor,"rule upper",upper!=null?upper.getTree():null);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_lower=new RewriteRuleSubtreeStream(adaptor,"rule lower",lower!=null?lower.getTree():null);
					RewriteRuleSubtreeStream stream_cond=new RewriteRuleSubtreeStream(adaptor,"rule cond",cond!=null?cond.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 512:4: -> ^( quantifier $id $lower $upper $cond)
					{
						// CivlCParser.g:512:7: ^( quantifier $id $lower $upper $cond)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_quantifier.nextNode(), root_1);
						adaptor.addChild(root_1, stream_id.nextNode());
						adaptor.addChild(root_1, stream_lower.nextTree());
						adaptor.addChild(root_1, stream_upper.nextTree());
						adaptor.addChild(root_1, stream_cond.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "quantifierExpression"


	public static class quantifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "quantifier"
	// CivlCParser.g:522:1: quantifier : ( FORALL | EXISTS | UNIFORM );
	public final OmpParser_CivlCParser.quantifier_return quantifier() throws RecognitionException {
		OmpParser_CivlCParser.quantifier_return retval = new OmpParser_CivlCParser.quantifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set166=null;

		Object set166_tree=null;

		try {
			// CivlCParser.g:523:2: ( FORALL | EXISTS | UNIFORM )
			// CivlCParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set166=input.LT(1);
			if ( input.LA(1)==EXISTS||input.LA(1)==FORALL||input.LA(1)==UNIFORM ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set166));
				state.errorRecovery=false;
				state.failed=false;
			}
			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				MismatchedSetException mse = new MismatchedSetException(null,input);
				throw mse;
			}
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "quantifier"


	public static class assignmentExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "assignmentExpression"
	// CivlCParser.g:534:1: assignmentExpression : ( ( unaryExpression assignmentOperator )=> unaryExpression assignmentOperator assignmentExpression -> ^( OPERATOR assignmentOperator ^( ARGUMENT_LIST unaryExpression assignmentExpression ) ) | conditionalExpression | quantifierExpression );
	public final OmpParser_CivlCParser.assignmentExpression_return assignmentExpression() throws RecognitionException {
		OmpParser_CivlCParser.assignmentExpression_return retval = new OmpParser_CivlCParser.assignmentExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope unaryExpression167 =null;
		ParserRuleReturnScope assignmentOperator168 =null;
		ParserRuleReturnScope assignmentExpression169 =null;
		ParserRuleReturnScope conditionalExpression170 =null;
		ParserRuleReturnScope quantifierExpression171 =null;

		RewriteRuleSubtreeStream stream_assignmentOperator=new RewriteRuleSubtreeStream(adaptor,"rule assignmentOperator");
		RewriteRuleSubtreeStream stream_assignmentExpression=new RewriteRuleSubtreeStream(adaptor,"rule assignmentExpression");
		RewriteRuleSubtreeStream stream_unaryExpression=new RewriteRuleSubtreeStream(adaptor,"rule unaryExpression");

		try {
			// CivlCParser.g:535:2: ( ( unaryExpression assignmentOperator )=> unaryExpression assignmentOperator assignmentExpression -> ^( OPERATOR assignmentOperator ^( ARGUMENT_LIST unaryExpression assignmentExpression ) ) | conditionalExpression | quantifierExpression )
			int alt29=3;
			switch ( input.LA(1) ) {
			case LPAREN:
				{
				int LA29_1 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case IDENTIFIER:
				{
				int LA29_2 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case INTEGER_CONSTANT:
				{
				int LA29_3 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case FLOATING_CONSTANT:
				{
				int LA29_4 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case CHARACTER_CONSTANT:
				{
				int LA29_5 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case SELF:
				{
				int LA29_6 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case PROCNULL:
				{
				int LA29_7 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case TRUE:
				{
				int LA29_8 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case FALSE:
				{
				int LA29_9 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case RESULT:
				{
				int LA29_10 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case HERE:
				{
				int LA29_11 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case ROOT:
				{
				int LA29_12 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case ELLIPSIS:
				{
				int LA29_13 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case STRING_LITERAL:
				{
				int LA29_14 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case GENERIC:
				{
				int LA29_15 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case DERIV:
				{
				int LA29_16 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case PLUSPLUS:
				{
				int LA29_17 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case MINUSMINUS:
				{
				int LA29_18 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case AMPERSAND:
			case BIG_O:
			case NOT:
			case PLUS:
			case STAR:
			case SUB:
			case TILDE:
				{
				int LA29_19 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case SIZEOF:
				{
				int LA29_20 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case SCOPEOF:
				{
				int LA29_21 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case ALIGNOF:
				{
				int LA29_22 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case SPAWN:
				{
				int LA29_23 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case CALLS:
				{
				int LA29_24 = input.LA(2);
				if ( (synpred4_CivlCParser()) ) {
					alt29=1;
				}
				else if ( (true) ) {
					alt29=2;
				}

				}
				break;
			case EXISTS:
			case FORALL:
			case UNIFORM:
				{
				alt29=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 29, 0, input);
				throw nvae;
			}
			switch (alt29) {
				case 1 :
					// CivlCParser.g:535:4: ( unaryExpression assignmentOperator )=> unaryExpression assignmentOperator assignmentExpression
					{
					pushFollow(FOLLOW_unaryExpression_in_assignmentExpression3661);
					unaryExpression167=unaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_unaryExpression.add(unaryExpression167.getTree());
					pushFollow(FOLLOW_assignmentOperator_in_assignmentExpression3663);
					assignmentOperator168=assignmentOperator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_assignmentOperator.add(assignmentOperator168.getTree());
					pushFollow(FOLLOW_assignmentExpression_in_assignmentExpression3665);
					assignmentExpression169=assignmentExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression169.getTree());
					// AST REWRITE
					// elements: assignmentExpression, assignmentOperator, unaryExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 537:4: -> ^( OPERATOR assignmentOperator ^( ARGUMENT_LIST unaryExpression assignmentExpression ) )
					{
						// CivlCParser.g:537:7: ^( OPERATOR assignmentOperator ^( ARGUMENT_LIST unaryExpression assignmentExpression ) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_assignmentOperator.nextTree());
						// CivlCParser.g:538:9: ^( ARGUMENT_LIST unaryExpression assignmentExpression )
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_unaryExpression.nextTree());
						adaptor.addChild(root_2, stream_assignmentExpression.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:539:4: conditionalExpression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_conditionalExpression_in_assignmentExpression3697);
					conditionalExpression170=conditionalExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, conditionalExpression170.getTree());

					}
					break;
				case 3 :
					// CivlCParser.g:540:4: quantifierExpression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_quantifierExpression_in_assignmentExpression3702);
					quantifierExpression171=quantifierExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, quantifierExpression171.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "assignmentExpression"


	public static class assignmentOperator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "assignmentOperator"
	// CivlCParser.g:544:1: assignmentOperator : ( ASSIGN | STAREQ | DIVEQ | MODEQ | PLUSEQ | SUBEQ | SHIFTLEFTEQ | SHIFTRIGHTEQ | BITANDEQ | BITXOREQ | BITOREQ );
	public final OmpParser_CivlCParser.assignmentOperator_return assignmentOperator() throws RecognitionException {
		OmpParser_CivlCParser.assignmentOperator_return retval = new OmpParser_CivlCParser.assignmentOperator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set172=null;

		Object set172_tree=null;

		try {
			// CivlCParser.g:545:2: ( ASSIGN | STAREQ | DIVEQ | MODEQ | PLUSEQ | SUBEQ | SHIFTLEFTEQ | SHIFTRIGHTEQ | BITANDEQ | BITXOREQ | BITOREQ )
			// CivlCParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set172=input.LT(1);
			if ( input.LA(1)==ASSIGN||input.LA(1)==BITANDEQ||input.LA(1)==BITOREQ||input.LA(1)==BITXOREQ||input.LA(1)==DIVEQ||input.LA(1)==MODEQ||input.LA(1)==PLUSEQ||input.LA(1)==SHIFTLEFTEQ||input.LA(1)==SHIFTRIGHTEQ||input.LA(1)==STAREQ||input.LA(1)==SUBEQ ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set172));
				state.errorRecovery=false;
				state.failed=false;
			}
			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				MismatchedSetException mse = new MismatchedSetException(null,input);
				throw mse;
			}
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "assignmentOperator"


	public static class commaExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "commaExpression"
	// CivlCParser.g:557:1: commaExpression : ( assignmentExpression -> assignmentExpression ) ( COMMA y= assignmentExpression -> ^( OPERATOR COMMA ^( ARGUMENT_LIST $commaExpression $y) ) )* ;
	public final OmpParser_CivlCParser.commaExpression_return commaExpression() throws RecognitionException {
		OmpParser_CivlCParser.commaExpression_return retval = new OmpParser_CivlCParser.commaExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMMA174=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope assignmentExpression173 =null;

		Object COMMA174_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_assignmentExpression=new RewriteRuleSubtreeStream(adaptor,"rule assignmentExpression");

		try {
			// CivlCParser.g:558:2: ( ( assignmentExpression -> assignmentExpression ) ( COMMA y= assignmentExpression -> ^( OPERATOR COMMA ^( ARGUMENT_LIST $commaExpression $y) ) )* )
			// CivlCParser.g:558:4: ( assignmentExpression -> assignmentExpression ) ( COMMA y= assignmentExpression -> ^( OPERATOR COMMA ^( ARGUMENT_LIST $commaExpression $y) ) )*
			{
			// CivlCParser.g:558:4: ( assignmentExpression -> assignmentExpression )
			// CivlCParser.g:558:6: assignmentExpression
			{
			pushFollow(FOLLOW_assignmentExpression_in_commaExpression3771);
			assignmentExpression173=assignmentExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression173.getTree());
			// AST REWRITE
			// elements: assignmentExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 558:27: -> assignmentExpression
			{
				adaptor.addChild(root_0, stream_assignmentExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// CivlCParser.g:559:4: ( COMMA y= assignmentExpression -> ^( OPERATOR COMMA ^( ARGUMENT_LIST $commaExpression $y) ) )*
			loop30:
			while (true) {
				int alt30=2;
				int LA30_0 = input.LA(1);
				if ( (LA30_0==COMMA) ) {
					alt30=1;
				}

				switch (alt30) {
				case 1 :
					// CivlCParser.g:559:6: COMMA y= assignmentExpression
					{
					COMMA174=(Token)match(input,COMMA,FOLLOW_COMMA_in_commaExpression3784); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA174);

					pushFollow(FOLLOW_assignmentExpression_in_commaExpression3788);
					y=assignmentExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_assignmentExpression.add(y.getTree());
					// AST REWRITE
					// elements: commaExpression, COMMA, y
					// token labels: 
					// rule labels: retval, y
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_y=new RewriteRuleSubtreeStream(adaptor,"rule y",y!=null?y.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 560:6: -> ^( OPERATOR COMMA ^( ARGUMENT_LIST $commaExpression $y) )
					{
						// CivlCParser.g:560:9: ^( OPERATOR COMMA ^( ARGUMENT_LIST $commaExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_COMMA.nextNode());
						// CivlCParser.g:560:26: ^( ARGUMENT_LIST $commaExpression $y)
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_y.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop30;
				}
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "commaExpression"


	public static class expression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "expression"
	// CivlCParser.g:568:1: expression : ( COLLECTIVE LPAREN proc= conditionalExpression RPAREN body= conditionalExpression -> ^( COLLECTIVE $proc $body) | commaExpression );
	public final OmpParser_CivlCParser.expression_return expression() throws RecognitionException {
		OmpParser_CivlCParser.expression_return retval = new OmpParser_CivlCParser.expression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COLLECTIVE175=null;
		Token LPAREN176=null;
		Token RPAREN177=null;
		ParserRuleReturnScope proc =null;
		ParserRuleReturnScope body =null;
		ParserRuleReturnScope commaExpression178 =null;

		Object COLLECTIVE175_tree=null;
		Object LPAREN176_tree=null;
		Object RPAREN177_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_COLLECTIVE=new RewriteRuleTokenStream(adaptor,"token COLLECTIVE");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_conditionalExpression=new RewriteRuleSubtreeStream(adaptor,"rule conditionalExpression");

		try {
			// CivlCParser.g:569:2: ( COLLECTIVE LPAREN proc= conditionalExpression RPAREN body= conditionalExpression -> ^( COLLECTIVE $proc $body) | commaExpression )
			int alt31=2;
			int LA31_0 = input.LA(1);
			if ( (LA31_0==COLLECTIVE) ) {
				alt31=1;
			}
			else if ( ((LA31_0 >= ALIGNOF && LA31_0 <= AMPERSAND)||LA31_0==BIG_O||LA31_0==CALLS||LA31_0==CHARACTER_CONSTANT||LA31_0==DERIV||LA31_0==ELLIPSIS||LA31_0==EXISTS||LA31_0==FALSE||LA31_0==FLOATING_CONSTANT||LA31_0==FORALL||LA31_0==GENERIC||LA31_0==HERE||LA31_0==IDENTIFIER||LA31_0==INTEGER_CONSTANT||LA31_0==LPAREN||LA31_0==MINUSMINUS||LA31_0==NOT||LA31_0==PLUS||LA31_0==PLUSPLUS||LA31_0==PROCNULL||LA31_0==RESULT||LA31_0==SCOPEOF||LA31_0==SELF||(LA31_0 >= SIZEOF && LA31_0 <= STAR)||LA31_0==STRING_LITERAL||LA31_0==SUB||(LA31_0 >= TILDE && LA31_0 <= TRUE)||LA31_0==UNIFORM||LA31_0==ROOT) ) {
				alt31=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 31, 0, input);
				throw nvae;
			}

			switch (alt31) {
				case 1 :
					// CivlCParser.g:569:4: COLLECTIVE LPAREN proc= conditionalExpression RPAREN body= conditionalExpression
					{
					COLLECTIVE175=(Token)match(input,COLLECTIVE,FOLLOW_COLLECTIVE_in_expression3830); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COLLECTIVE.add(COLLECTIVE175);

					LPAREN176=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_expression3832); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN176);

					pushFollow(FOLLOW_conditionalExpression_in_expression3836);
					proc=conditionalExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_conditionalExpression.add(proc.getTree());
					RPAREN177=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_expression3842); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN177);

					pushFollow(FOLLOW_conditionalExpression_in_expression3846);
					body=conditionalExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_conditionalExpression.add(body.getTree());
					// AST REWRITE
					// elements: body, proc, COLLECTIVE
					// token labels: 
					// rule labels: body, retval, proc
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_body=new RewriteRuleSubtreeStream(adaptor,"rule body",body!=null?body.getTree():null);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_proc=new RewriteRuleSubtreeStream(adaptor,"rule proc",proc!=null?proc.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 571:4: -> ^( COLLECTIVE $proc $body)
					{
						// CivlCParser.g:571:7: ^( COLLECTIVE $proc $body)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_COLLECTIVE.nextNode(), root_1);
						adaptor.addChild(root_1, stream_proc.nextTree());
						adaptor.addChild(root_1, stream_body.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:572:4: commaExpression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_commaExpression_in_expression3866);
					commaExpression178=commaExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, commaExpression178.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "expression"


	public static class constantExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "constantExpression"
	// CivlCParser.g:577:1: constantExpression : conditionalExpression ;
	public final OmpParser_CivlCParser.constantExpression_return constantExpression() throws RecognitionException {
		OmpParser_CivlCParser.constantExpression_return retval = new OmpParser_CivlCParser.constantExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope conditionalExpression179 =null;


		try {
			// CivlCParser.g:578:2: ( conditionalExpression )
			// CivlCParser.g:578:4: conditionalExpression
			{
			root_0 = (Object)adaptor.nil();


			pushFollow(FOLLOW_conditionalExpression_in_constantExpression3883);
			conditionalExpression179=conditionalExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, conditionalExpression179.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "constantExpression"


	public static class declaration_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "declaration"
	// CivlCParser.g:605:1: declaration : (d= declarationSpecifiers (i= initDeclaratorList contract SEMI -> ^( DECLARATION $d $i contract ) | SEMI -> ^( DECLARATION $d ABSENT ABSENT ) ) | staticAssertDeclaration );
	public final OmpParser_CivlCParser.declaration_return declaration() throws RecognitionException {
		DeclarationScope_stack.push(new DeclarationScope_scope());

		OmpParser_CivlCParser.declaration_return retval = new OmpParser_CivlCParser.declaration_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SEMI181=null;
		Token SEMI182=null;
		ParserRuleReturnScope d =null;
		ParserRuleReturnScope i =null;
		ParserRuleReturnScope contract180 =null;
		ParserRuleReturnScope staticAssertDeclaration183 =null;

		Object SEMI181_tree=null;
		Object SEMI182_tree=null;
		RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
		RewriteRuleSubtreeStream stream_contract=new RewriteRuleSubtreeStream(adaptor,"rule contract");
		RewriteRuleSubtreeStream stream_declarationSpecifiers=new RewriteRuleSubtreeStream(adaptor,"rule declarationSpecifiers");
		RewriteRuleSubtreeStream stream_initDeclaratorList=new RewriteRuleSubtreeStream(adaptor,"rule initDeclaratorList");


		  DeclarationScope_stack.peek().isTypedef = false;
		  DeclarationScope_stack.peek().typedefNameUsed =false;

		try {
			// CivlCParser.g:611:2: (d= declarationSpecifiers (i= initDeclaratorList contract SEMI -> ^( DECLARATION $d $i contract ) | SEMI -> ^( DECLARATION $d ABSENT ABSENT ) ) | staticAssertDeclaration )
			int alt33=2;
			int LA33_0 = input.LA(1);
			if ( ((LA33_0 >= ABSTRACT && LA33_0 <= ALIGNAS)||(LA33_0 >= ATOMIC && LA33_0 <= AUTO)||LA33_0==BOOL||LA33_0==CHAR||(LA33_0 >= COMPLEX && LA33_0 <= CONST)||LA33_0==DEVICE||LA33_0==DOMAIN||LA33_0==DOUBLE||LA33_0==ENUM||LA33_0==EXTERN||(LA33_0 >= FATOMIC && LA33_0 <= FLOAT)||LA33_0==GLOBAL||LA33_0==IDENTIFIER||(LA33_0 >= INLINE && LA33_0 <= INT)||LA33_0==LONG||LA33_0==NORETURN||LA33_0==OUTPUT||LA33_0==PURE||LA33_0==RANGE||(LA33_0 >= REAL && LA33_0 <= REGISTER)||LA33_0==RESTRICT||LA33_0==SHARED||(LA33_0 >= SHORT && LA33_0 <= SIGNED)||LA33_0==STATIC||LA33_0==STRUCT||(LA33_0 >= SYSTEM && LA33_0 <= THREADLOCAL)||(LA33_0 >= TYPEDEF && LA33_0 <= TYPEOF)||(LA33_0 >= UNION && LA33_0 <= UNSIGNED)||(LA33_0 >= VOID && LA33_0 <= VOLATILE)) ) {
				alt33=1;
			}
			else if ( (LA33_0==STATICASSERT) ) {
				alt33=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 33, 0, input);
				throw nvae;
			}

			switch (alt33) {
				case 1 :
					// CivlCParser.g:611:4: d= declarationSpecifiers (i= initDeclaratorList contract SEMI -> ^( DECLARATION $d $i contract ) | SEMI -> ^( DECLARATION $d ABSENT ABSENT ) )
					{
					pushFollow(FOLLOW_declarationSpecifiers_in_declaration3913);
					d=declarationSpecifiers();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_declarationSpecifiers.add(d.getTree());
					// CivlCParser.g:612:4: (i= initDeclaratorList contract SEMI -> ^( DECLARATION $d $i contract ) | SEMI -> ^( DECLARATION $d ABSENT ABSENT ) )
					int alt32=2;
					int LA32_0 = input.LA(1);
					if ( (LA32_0==IDENTIFIER||LA32_0==LPAREN||LA32_0==STAR) ) {
						alt32=1;
					}
					else if ( (LA32_0==SEMI) ) {
						alt32=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 32, 0, input);
						throw nvae;
					}

					switch (alt32) {
						case 1 :
							// CivlCParser.g:613:6: i= initDeclaratorList contract SEMI
							{
							pushFollow(FOLLOW_initDeclaratorList_in_declaration3928);
							i=initDeclaratorList();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_initDeclaratorList.add(i.getTree());
							pushFollow(FOLLOW_contract_in_declaration3930);
							contract180=contract();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_contract.add(contract180.getTree());
							SEMI181=(Token)match(input,SEMI,FOLLOW_SEMI_in_declaration3932); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_SEMI.add(SEMI181);

							// AST REWRITE
							// elements: d, contract, i
							// token labels: 
							// rule labels: retval, d, i
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
							RewriteRuleSubtreeStream stream_d=new RewriteRuleSubtreeStream(adaptor,"rule d",d!=null?d.getTree():null);
							RewriteRuleSubtreeStream stream_i=new RewriteRuleSubtreeStream(adaptor,"rule i",i!=null?i.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 614:6: -> ^( DECLARATION $d $i contract )
							{
								// CivlCParser.g:614:9: ^( DECLARATION $d $i contract )
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DECLARATION, "DECLARATION"), root_1);
								adaptor.addChild(root_1, stream_d.nextTree());
								adaptor.addChild(root_1, stream_i.nextTree());
								adaptor.addChild(root_1, stream_contract.nextTree());
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;
						case 2 :
							// CivlCParser.g:615:6: SEMI
							{
							SEMI182=(Token)match(input,SEMI,FOLLOW_SEMI_in_declaration3958); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_SEMI.add(SEMI182);

							// AST REWRITE
							// elements: d
							// token labels: 
							// rule labels: retval, d
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
							RewriteRuleSubtreeStream stream_d=new RewriteRuleSubtreeStream(adaptor,"rule d",d!=null?d.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 616:6: -> ^( DECLARATION $d ABSENT ABSENT )
							{
								// CivlCParser.g:616:9: ^( DECLARATION $d ABSENT ABSENT )
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DECLARATION, "DECLARATION"), root_1);
								adaptor.addChild(root_1, stream_d.nextTree());
								adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
								adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;

					}

					}
					break;
				case 2 :
					// CivlCParser.g:618:4: staticAssertDeclaration
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_staticAssertDeclaration_in_declaration3986);
					staticAssertDeclaration183=staticAssertDeclaration();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, staticAssertDeclaration183.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
			DeclarationScope_stack.pop();

		}
		return retval;
	}
	// $ANTLR end "declaration"


	public static class declarationSpecifiers_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "declarationSpecifiers"
	// CivlCParser.g:626:1: declarationSpecifiers : l= declarationSpecifierList -> ^( DECLARATION_SPECIFIERS declarationSpecifierList ) ;
	public final OmpParser_CivlCParser.declarationSpecifiers_return declarationSpecifiers() throws RecognitionException {
		OmpParser_CivlCParser.declarationSpecifiers_return retval = new OmpParser_CivlCParser.declarationSpecifiers_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope l =null;

		RewriteRuleSubtreeStream stream_declarationSpecifierList=new RewriteRuleSubtreeStream(adaptor,"rule declarationSpecifierList");

		try {
			// CivlCParser.g:627:2: (l= declarationSpecifierList -> ^( DECLARATION_SPECIFIERS declarationSpecifierList ) )
			// CivlCParser.g:627:4: l= declarationSpecifierList
			{
			pushFollow(FOLLOW_declarationSpecifierList_in_declarationSpecifiers4002);
			l=declarationSpecifierList();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_declarationSpecifierList.add(l.getTree());
			// AST REWRITE
			// elements: declarationSpecifierList
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 628:4: -> ^( DECLARATION_SPECIFIERS declarationSpecifierList )
			{
				// CivlCParser.g:628:7: ^( DECLARATION_SPECIFIERS declarationSpecifierList )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DECLARATION_SPECIFIERS, "DECLARATION_SPECIFIERS"), root_1);
				adaptor.addChild(root_1, stream_declarationSpecifierList.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "declarationSpecifiers"


	public static class declarationSpecifierList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "declarationSpecifierList"
	// CivlCParser.g:633:1: declarationSpecifierList : ({...}?s= declarationSpecifier )+ ;
	public final OmpParser_CivlCParser.declarationSpecifierList_return declarationSpecifierList() throws RecognitionException {
		OmpParser_CivlCParser.declarationSpecifierList_return retval = new OmpParser_CivlCParser.declarationSpecifierList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope s =null;


		try {
			// CivlCParser.g:634:2: ( ({...}?s= declarationSpecifier )+ )
			// CivlCParser.g:634:4: ({...}?s= declarationSpecifier )+
			{
			root_0 = (Object)adaptor.nil();


			// CivlCParser.g:634:4: ({...}?s= declarationSpecifier )+
			int cnt34=0;
			loop34:
			while (true) {
				int alt34=2;
				int LA34_0 = input.LA(1);
				if ( (LA34_0==IDENTIFIER) ) {
					int LA34_1 = input.LA(2);
					if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(!DeclarationScope_stack.peek().typedefNameUsed && isTypeName(input.LT(1).getText())))) ) {
						alt34=1;
					}

				}
				else if ( ((LA34_0 >= ABSTRACT && LA34_0 <= ALIGNAS)||(LA34_0 >= ATOMIC && LA34_0 <= AUTO)||LA34_0==BOOL||LA34_0==CHAR||(LA34_0 >= COMPLEX && LA34_0 <= CONST)||LA34_0==DEVICE||LA34_0==DOMAIN||LA34_0==DOUBLE||LA34_0==ENUM||LA34_0==EXTERN||(LA34_0 >= FATOMIC && LA34_0 <= FLOAT)||LA34_0==GLOBAL||(LA34_0 >= INLINE && LA34_0 <= INT)||LA34_0==LONG||LA34_0==NORETURN||LA34_0==OUTPUT||LA34_0==PURE||LA34_0==RANGE||(LA34_0 >= REAL && LA34_0 <= REGISTER)||LA34_0==RESTRICT||LA34_0==SHARED||(LA34_0 >= SHORT && LA34_0 <= SIGNED)||LA34_0==STATIC||LA34_0==STRUCT||(LA34_0 >= SYSTEM && LA34_0 <= THREADLOCAL)||(LA34_0 >= TYPEDEF && LA34_0 <= TYPEOF)||(LA34_0 >= UNION && LA34_0 <= UNSIGNED)||(LA34_0 >= VOID && LA34_0 <= VOLATILE)) ) {
					alt34=1;
				}

				switch (alt34) {
				case 1 :
					// CivlCParser.g:635:6: {...}?s= declarationSpecifier
					{
					if ( !((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
						if (state.backtracking>0) {state.failed=true; return retval;}
						throw new FailedPredicateException(input, "declarationSpecifierList", "!$DeclarationScope::isTypedef || input.LT(2).getType() != SEMI ");
					}
					pushFollow(FOLLOW_declarationSpecifier_in_declarationSpecifierList4042);
					s=declarationSpecifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, s.getTree());

					}
					break;

				default :
					if ( cnt34 >= 1 ) break loop34;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(34, input);
					throw eee;
				}
				cnt34++;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "declarationSpecifierList"


	public static class declarationSpecifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "declarationSpecifier"
	// CivlCParser.g:640:1: declarationSpecifier : (s= storageClassSpecifier | typeSpecifierOrQualifier | functionSpecifier | alignmentSpecifier );
	public final OmpParser_CivlCParser.declarationSpecifier_return declarationSpecifier() throws RecognitionException {
		OmpParser_CivlCParser.declarationSpecifier_return retval = new OmpParser_CivlCParser.declarationSpecifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope s =null;
		ParserRuleReturnScope typeSpecifierOrQualifier184 =null;
		ParserRuleReturnScope functionSpecifier185 =null;
		ParserRuleReturnScope alignmentSpecifier186 =null;


		try {
			// CivlCParser.g:641:2: (s= storageClassSpecifier | typeSpecifierOrQualifier | functionSpecifier | alignmentSpecifier )
			int alt35=4;
			switch ( input.LA(1) ) {
			case AUTO:
			case EXTERN:
			case REGISTER:
			case SHARED:
			case STATIC:
			case THREADLOCAL:
			case TYPEDEF:
				{
				alt35=1;
				}
				break;
			case ATOMIC:
			case BOOL:
			case CHAR:
			case COMPLEX:
			case CONST:
			case DOMAIN:
			case DOUBLE:
			case ENUM:
			case FLOAT:
			case IDENTIFIER:
			case INPUT:
			case INT:
			case LONG:
			case OUTPUT:
			case RANGE:
			case REAL:
			case RESTRICT:
			case SHORT:
			case SIGNED:
			case STRUCT:
			case TYPEOF:
			case UNION:
			case UNSIGNED:
			case VOID:
			case VOLATILE:
				{
				alt35=2;
				}
				break;
			case ABSTRACT:
			case DEVICE:
			case FATOMIC:
			case GLOBAL:
			case INLINE:
			case NORETURN:
			case PURE:
			case SYSTEM:
				{
				alt35=3;
				}
				break;
			case ALIGNAS:
				{
				alt35=4;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 35, 0, input);
				throw nvae;
			}
			switch (alt35) {
				case 1 :
					// CivlCParser.g:641:4: s= storageClassSpecifier
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_storageClassSpecifier_in_declarationSpecifier4061);
					s=storageClassSpecifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, s.getTree());

					}
					break;
				case 2 :
					// CivlCParser.g:642:4: typeSpecifierOrQualifier
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_typeSpecifierOrQualifier_in_declarationSpecifier4066);
					typeSpecifierOrQualifier184=typeSpecifierOrQualifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, typeSpecifierOrQualifier184.getTree());

					}
					break;
				case 3 :
					// CivlCParser.g:643:4: functionSpecifier
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_functionSpecifier_in_declarationSpecifier4071);
					functionSpecifier185=functionSpecifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, functionSpecifier185.getTree());

					}
					break;
				case 4 :
					// CivlCParser.g:644:4: alignmentSpecifier
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_alignmentSpecifier_in_declarationSpecifier4076);
					alignmentSpecifier186=alignmentSpecifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, alignmentSpecifier186.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "declarationSpecifier"


	public static class typeSpecifierOrQualifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "typeSpecifierOrQualifier"
	// CivlCParser.g:655:1: typeSpecifierOrQualifier : ( ( typeSpecifier )=> typeSpecifier | typeQualifier );
	public final OmpParser_CivlCParser.typeSpecifierOrQualifier_return typeSpecifierOrQualifier() throws RecognitionException {
		OmpParser_CivlCParser.typeSpecifierOrQualifier_return retval = new OmpParser_CivlCParser.typeSpecifierOrQualifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope typeSpecifier187 =null;
		ParserRuleReturnScope typeQualifier188 =null;


		try {
			// CivlCParser.g:656:2: ( ( typeSpecifier )=> typeSpecifier | typeQualifier )
			int alt36=2;
			int LA36_0 = input.LA(1);
			if ( (LA36_0==VOID) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==CHAR) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==SHORT) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==INT) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==LONG) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==FLOAT) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==DOUBLE) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==SIGNED) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==UNSIGNED) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==BOOL) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==COMPLEX) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==REAL) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==RANGE) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==ATOMIC) ) {
				int LA36_14 = input.LA(2);
				if ( (synpred5_CivlCParser()) ) {
					alt36=1;
				}
				else if ( (true) ) {
					alt36=2;
				}

			}
			else if ( (LA36_0==STRUCT||LA36_0==UNION) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==ENUM) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==IDENTIFIER) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==DOMAIN) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==TYPEOF) && (synpred5_CivlCParser())) {
				alt36=1;
			}
			else if ( (LA36_0==CONST||LA36_0==INPUT||LA36_0==OUTPUT||LA36_0==RESTRICT||LA36_0==VOLATILE) ) {
				alt36=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 36, 0, input);
				throw nvae;
			}

			switch (alt36) {
				case 1 :
					// CivlCParser.g:656:4: ( typeSpecifier )=> typeSpecifier
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_typeSpecifier_in_typeSpecifierOrQualifier4094);
					typeSpecifier187=typeSpecifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, typeSpecifier187.getTree());

					}
					break;
				case 2 :
					// CivlCParser.g:657:11: typeQualifier
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_typeQualifier_in_typeSpecifierOrQualifier4106);
					typeQualifier188=typeQualifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, typeQualifier188.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "typeSpecifierOrQualifier"


	public static class initDeclaratorList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "initDeclaratorList"
	// CivlCParser.g:664:1: initDeclaratorList :i+= initDeclarator ( COMMA i+= initDeclarator )* -> ^( INIT_DECLARATOR_LIST ( $i)+ ) ;
	public final OmpParser_CivlCParser.initDeclaratorList_return initDeclaratorList() throws RecognitionException {
		OmpParser_CivlCParser.initDeclaratorList_return retval = new OmpParser_CivlCParser.initDeclaratorList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMMA189=null;
		List<Object> list_i=null;
		RuleReturnScope i = null;
		Object COMMA189_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_initDeclarator=new RewriteRuleSubtreeStream(adaptor,"rule initDeclarator");

		try {
			// CivlCParser.g:665:2: (i+= initDeclarator ( COMMA i+= initDeclarator )* -> ^( INIT_DECLARATOR_LIST ( $i)+ ) )
			// CivlCParser.g:665:4: i+= initDeclarator ( COMMA i+= initDeclarator )*
			{
			pushFollow(FOLLOW_initDeclarator_in_initDeclaratorList4121);
			i=initDeclarator();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_initDeclarator.add(i.getTree());
			if (list_i==null) list_i=new ArrayList<Object>();
			list_i.add(i.getTree());
			// CivlCParser.g:665:22: ( COMMA i+= initDeclarator )*
			loop37:
			while (true) {
				int alt37=2;
				int LA37_0 = input.LA(1);
				if ( (LA37_0==COMMA) ) {
					alt37=1;
				}

				switch (alt37) {
				case 1 :
					// CivlCParser.g:665:23: COMMA i+= initDeclarator
					{
					COMMA189=(Token)match(input,COMMA,FOLLOW_COMMA_in_initDeclaratorList4124); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA189);

					pushFollow(FOLLOW_initDeclarator_in_initDeclaratorList4128);
					i=initDeclarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_initDeclarator.add(i.getTree());
					if (list_i==null) list_i=new ArrayList<Object>();
					list_i.add(i.getTree());
					}
					break;

				default :
					break loop37;
				}
			}

			// AST REWRITE
			// elements: i
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: i
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_i=new RewriteRuleSubtreeStream(adaptor,"token i",list_i);
			root_0 = (Object)adaptor.nil();
			// 666:4: -> ^( INIT_DECLARATOR_LIST ( $i)+ )
			{
				// CivlCParser.g:666:7: ^( INIT_DECLARATOR_LIST ( $i)+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(INIT_DECLARATOR_LIST, "INIT_DECLARATOR_LIST"), root_1);
				if ( !(stream_i.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_i.hasNext() ) {
					adaptor.addChild(root_1, stream_i.nextTree());
				}
				stream_i.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "initDeclaratorList"


	public static class initDeclarator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "initDeclarator"
	// CivlCParser.g:674:1: initDeclarator : d= declarator ( -> ^( INIT_DECLARATOR $d ABSENT ) | ( ASSIGN i= initializer ) -> ^( INIT_DECLARATOR $d $i) ) ;
	public final OmpParser_CivlCParser.initDeclarator_return initDeclarator() throws RecognitionException {
		OmpParser_CivlCParser.initDeclarator_return retval = new OmpParser_CivlCParser.initDeclarator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ASSIGN190=null;
		ParserRuleReturnScope d =null;
		ParserRuleReturnScope i =null;

		Object ASSIGN190_tree=null;
		RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
		RewriteRuleSubtreeStream stream_declarator=new RewriteRuleSubtreeStream(adaptor,"rule declarator");
		RewriteRuleSubtreeStream stream_initializer=new RewriteRuleSubtreeStream(adaptor,"rule initializer");

		try {
			// CivlCParser.g:675:2: (d= declarator ( -> ^( INIT_DECLARATOR $d ABSENT ) | ( ASSIGN i= initializer ) -> ^( INIT_DECLARATOR $d $i) ) )
			// CivlCParser.g:675:4: d= declarator ( -> ^( INIT_DECLARATOR $d ABSENT ) | ( ASSIGN i= initializer ) -> ^( INIT_DECLARATOR $d $i) )
			{
			pushFollow(FOLLOW_declarator_in_initDeclarator4158);
			d=declarator();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_declarator.add(d.getTree());
			// CivlCParser.g:676:4: ( -> ^( INIT_DECLARATOR $d ABSENT ) | ( ASSIGN i= initializer ) -> ^( INIT_DECLARATOR $d $i) )
			int alt38=2;
			int LA38_0 = input.LA(1);
			if ( ((LA38_0 >= ABSTRACT && LA38_0 <= ALIGNAS)||LA38_0==ASSIGNS||(LA38_0 >= ATOMIC && LA38_0 <= AUTO)||LA38_0==BOOL||LA38_0==CHAR||LA38_0==COMMA||(LA38_0 >= COMPLEX && LA38_0 <= CONST)||LA38_0==DEPENDS||LA38_0==DEVICE||LA38_0==DOMAIN||LA38_0==DOUBLE||(LA38_0 >= ENSURES && LA38_0 <= ENUM)||LA38_0==EXTERN||(LA38_0 >= FATOMIC && LA38_0 <= FLOAT)||LA38_0==GLOBAL||LA38_0==GUARD||LA38_0==IDENTIFIER||(LA38_0 >= INLINE && LA38_0 <= INT)||LA38_0==LCURLY||LA38_0==LONG||LA38_0==NORETURN||LA38_0==OUTPUT||LA38_0==PURE||LA38_0==RANGE||(LA38_0 >= READS && LA38_0 <= RESTRICT)||(LA38_0 >= SEMI && LA38_0 <= SHARED)||(LA38_0 >= SHORT && LA38_0 <= SIGNED)||(LA38_0 >= STATIC && LA38_0 <= STATICASSERT)||LA38_0==STRUCT||(LA38_0 >= SYSTEM && LA38_0 <= THREADLOCAL)||(LA38_0 >= TYPEDEF && LA38_0 <= TYPEOF)||(LA38_0 >= UNION && LA38_0 <= UNSIGNED)||(LA38_0 >= VOID && LA38_0 <= VOLATILE)) ) {
				alt38=1;
			}
			else if ( (LA38_0==ASSIGN) ) {
				alt38=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 38, 0, input);
				throw nvae;
			}

			switch (alt38) {
				case 1 :
					// CivlCParser.g:676:7: 
					{
					// AST REWRITE
					// elements: d
					// token labels: 
					// rule labels: retval, d
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_d=new RewriteRuleSubtreeStream(adaptor,"rule d",d!=null?d.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 676:7: -> ^( INIT_DECLARATOR $d ABSENT )
					{
						// CivlCParser.g:676:10: ^( INIT_DECLARATOR $d ABSENT )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(INIT_DECLARATOR, "INIT_DECLARATOR"), root_1);
						adaptor.addChild(root_1, stream_d.nextTree());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:677:6: ( ASSIGN i= initializer )
					{
					// CivlCParser.g:677:6: ( ASSIGN i= initializer )
					// CivlCParser.g:677:7: ASSIGN i= initializer
					{
					ASSIGN190=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_initDeclarator4183); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(ASSIGN190);

					pushFollow(FOLLOW_initializer_in_initDeclarator4187);
					i=initializer();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_initializer.add(i.getTree());
					}

					// AST REWRITE
					// elements: i, d
					// token labels: 
					// rule labels: retval, d, i
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_d=new RewriteRuleSubtreeStream(adaptor,"rule d",d!=null?d.getTree():null);
					RewriteRuleSubtreeStream stream_i=new RewriteRuleSubtreeStream(adaptor,"rule i",i!=null?i.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 677:29: -> ^( INIT_DECLARATOR $d $i)
					{
						// CivlCParser.g:677:32: ^( INIT_DECLARATOR $d $i)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(INIT_DECLARATOR, "INIT_DECLARATOR"), root_1);
						adaptor.addChild(root_1, stream_d.nextTree());
						adaptor.addChild(root_1, stream_i.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "initDeclarator"


	public static class storageClassSpecifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "storageClassSpecifier"
	// CivlCParser.g:682:1: storageClassSpecifier : ( TYPEDEF | ( EXTERN | STATIC | THREADLOCAL | AUTO | REGISTER | SHARED ) );
	public final OmpParser_CivlCParser.storageClassSpecifier_return storageClassSpecifier() throws RecognitionException {
		OmpParser_CivlCParser.storageClassSpecifier_return retval = new OmpParser_CivlCParser.storageClassSpecifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token TYPEDEF191=null;
		Token set192=null;

		Object TYPEDEF191_tree=null;
		Object set192_tree=null;

		try {
			// CivlCParser.g:683:2: ( TYPEDEF | ( EXTERN | STATIC | THREADLOCAL | AUTO | REGISTER | SHARED ) )
			int alt39=2;
			int LA39_0 = input.LA(1);
			if ( (LA39_0==TYPEDEF) ) {
				alt39=1;
			}
			else if ( (LA39_0==AUTO||LA39_0==EXTERN||LA39_0==REGISTER||LA39_0==SHARED||LA39_0==STATIC||LA39_0==THREADLOCAL) ) {
				alt39=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 39, 0, input);
				throw nvae;
			}

			switch (alt39) {
				case 1 :
					// CivlCParser.g:683:4: TYPEDEF
					{
					root_0 = (Object)adaptor.nil();


					TYPEDEF191=(Token)match(input,TYPEDEF,FOLLOW_TYPEDEF_in_storageClassSpecifier4218); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					TYPEDEF191_tree = (Object)adaptor.create(TYPEDEF191);
					adaptor.addChild(root_0, TYPEDEF191_tree);
					}

					if ( state.backtracking==0 ) {DeclarationScope_stack.peek().isTypedef = true;}
					}
					break;
				case 2 :
					// CivlCParser.g:684:4: ( EXTERN | STATIC | THREADLOCAL | AUTO | REGISTER | SHARED )
					{
					root_0 = (Object)adaptor.nil();


					set192=input.LT(1);
					if ( input.LA(1)==AUTO||input.LA(1)==EXTERN||input.LA(1)==REGISTER||input.LA(1)==SHARED||input.LA(1)==STATIC||input.LA(1)==THREADLOCAL ) {
						input.consume();
						if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set192));
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "storageClassSpecifier"


	public static class typeSpecifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "typeSpecifier"
	// CivlCParser.g:688:1: typeSpecifier : ( VOID | CHAR | SHORT | INT | LONG | FLOAT | DOUBLE | SIGNED | UNSIGNED | BOOL | COMPLEX | REAL | RANGE | atomicTypeSpecifier | structOrUnionSpecifier | enumSpecifier | typedefName | domainSpecifier | typeofSpecifier );
	public final OmpParser_CivlCParser.typeSpecifier_return typeSpecifier() throws RecognitionException {
		OmpParser_CivlCParser.typeSpecifier_return retval = new OmpParser_CivlCParser.typeSpecifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token VOID193=null;
		Token CHAR194=null;
		Token SHORT195=null;
		Token INT196=null;
		Token LONG197=null;
		Token FLOAT198=null;
		Token DOUBLE199=null;
		Token SIGNED200=null;
		Token UNSIGNED201=null;
		Token BOOL202=null;
		Token COMPLEX203=null;
		Token REAL204=null;
		Token RANGE205=null;
		ParserRuleReturnScope atomicTypeSpecifier206 =null;
		ParserRuleReturnScope structOrUnionSpecifier207 =null;
		ParserRuleReturnScope enumSpecifier208 =null;
		ParserRuleReturnScope typedefName209 =null;
		ParserRuleReturnScope domainSpecifier210 =null;
		ParserRuleReturnScope typeofSpecifier211 =null;

		Object VOID193_tree=null;
		Object CHAR194_tree=null;
		Object SHORT195_tree=null;
		Object INT196_tree=null;
		Object LONG197_tree=null;
		Object FLOAT198_tree=null;
		Object DOUBLE199_tree=null;
		Object SIGNED200_tree=null;
		Object UNSIGNED201_tree=null;
		Object BOOL202_tree=null;
		Object COMPLEX203_tree=null;
		Object REAL204_tree=null;
		Object RANGE205_tree=null;

		try {
			// CivlCParser.g:689:2: ( VOID | CHAR | SHORT | INT | LONG | FLOAT | DOUBLE | SIGNED | UNSIGNED | BOOL | COMPLEX | REAL | RANGE | atomicTypeSpecifier | structOrUnionSpecifier | enumSpecifier | typedefName | domainSpecifier | typeofSpecifier )
			int alt40=19;
			switch ( input.LA(1) ) {
			case VOID:
				{
				alt40=1;
				}
				break;
			case CHAR:
				{
				alt40=2;
				}
				break;
			case SHORT:
				{
				alt40=3;
				}
				break;
			case INT:
				{
				alt40=4;
				}
				break;
			case LONG:
				{
				alt40=5;
				}
				break;
			case FLOAT:
				{
				alt40=6;
				}
				break;
			case DOUBLE:
				{
				alt40=7;
				}
				break;
			case SIGNED:
				{
				alt40=8;
				}
				break;
			case UNSIGNED:
				{
				alt40=9;
				}
				break;
			case BOOL:
				{
				alt40=10;
				}
				break;
			case COMPLEX:
				{
				alt40=11;
				}
				break;
			case REAL:
				{
				alt40=12;
				}
				break;
			case RANGE:
				{
				alt40=13;
				}
				break;
			case ATOMIC:
				{
				alt40=14;
				}
				break;
			case STRUCT:
			case UNION:
				{
				alt40=15;
				}
				break;
			case ENUM:
				{
				alt40=16;
				}
				break;
			case IDENTIFIER:
				{
				alt40=17;
				}
				break;
			case DOMAIN:
				{
				alt40=18;
				}
				break;
			case TYPEOF:
				{
				alt40=19;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 40, 0, input);
				throw nvae;
			}
			switch (alt40) {
				case 1 :
					// CivlCParser.g:689:4: VOID
					{
					root_0 = (Object)adaptor.nil();


					VOID193=(Token)match(input,VOID,FOLLOW_VOID_in_typeSpecifier4260); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					VOID193_tree = (Object)adaptor.create(VOID193);
					adaptor.addChild(root_0, VOID193_tree);
					}

					}
					break;
				case 2 :
					// CivlCParser.g:689:11: CHAR
					{
					root_0 = (Object)adaptor.nil();


					CHAR194=(Token)match(input,CHAR,FOLLOW_CHAR_in_typeSpecifier4264); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					CHAR194_tree = (Object)adaptor.create(CHAR194);
					adaptor.addChild(root_0, CHAR194_tree);
					}

					}
					break;
				case 3 :
					// CivlCParser.g:689:18: SHORT
					{
					root_0 = (Object)adaptor.nil();


					SHORT195=(Token)match(input,SHORT,FOLLOW_SHORT_in_typeSpecifier4268); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					SHORT195_tree = (Object)adaptor.create(SHORT195);
					adaptor.addChild(root_0, SHORT195_tree);
					}

					}
					break;
				case 4 :
					// CivlCParser.g:689:26: INT
					{
					root_0 = (Object)adaptor.nil();


					INT196=(Token)match(input,INT,FOLLOW_INT_in_typeSpecifier4272); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INT196_tree = (Object)adaptor.create(INT196);
					adaptor.addChild(root_0, INT196_tree);
					}

					}
					break;
				case 5 :
					// CivlCParser.g:689:32: LONG
					{
					root_0 = (Object)adaptor.nil();


					LONG197=(Token)match(input,LONG,FOLLOW_LONG_in_typeSpecifier4276); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					LONG197_tree = (Object)adaptor.create(LONG197);
					adaptor.addChild(root_0, LONG197_tree);
					}

					}
					break;
				case 6 :
					// CivlCParser.g:689:39: FLOAT
					{
					root_0 = (Object)adaptor.nil();


					FLOAT198=(Token)match(input,FLOAT,FOLLOW_FLOAT_in_typeSpecifier4280); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					FLOAT198_tree = (Object)adaptor.create(FLOAT198);
					adaptor.addChild(root_0, FLOAT198_tree);
					}

					}
					break;
				case 7 :
					// CivlCParser.g:689:47: DOUBLE
					{
					root_0 = (Object)adaptor.nil();


					DOUBLE199=(Token)match(input,DOUBLE,FOLLOW_DOUBLE_in_typeSpecifier4284); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					DOUBLE199_tree = (Object)adaptor.create(DOUBLE199);
					adaptor.addChild(root_0, DOUBLE199_tree);
					}

					}
					break;
				case 8 :
					// CivlCParser.g:690:4: SIGNED
					{
					root_0 = (Object)adaptor.nil();


					SIGNED200=(Token)match(input,SIGNED,FOLLOW_SIGNED_in_typeSpecifier4289); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					SIGNED200_tree = (Object)adaptor.create(SIGNED200);
					adaptor.addChild(root_0, SIGNED200_tree);
					}

					}
					break;
				case 9 :
					// CivlCParser.g:690:13: UNSIGNED
					{
					root_0 = (Object)adaptor.nil();


					UNSIGNED201=(Token)match(input,UNSIGNED,FOLLOW_UNSIGNED_in_typeSpecifier4293); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					UNSIGNED201_tree = (Object)adaptor.create(UNSIGNED201);
					adaptor.addChild(root_0, UNSIGNED201_tree);
					}

					}
					break;
				case 10 :
					// CivlCParser.g:690:24: BOOL
					{
					root_0 = (Object)adaptor.nil();


					BOOL202=(Token)match(input,BOOL,FOLLOW_BOOL_in_typeSpecifier4297); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					BOOL202_tree = (Object)adaptor.create(BOOL202);
					adaptor.addChild(root_0, BOOL202_tree);
					}

					}
					break;
				case 11 :
					// CivlCParser.g:690:31: COMPLEX
					{
					root_0 = (Object)adaptor.nil();


					COMPLEX203=(Token)match(input,COMPLEX,FOLLOW_COMPLEX_in_typeSpecifier4301); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					COMPLEX203_tree = (Object)adaptor.create(COMPLEX203);
					adaptor.addChild(root_0, COMPLEX203_tree);
					}

					}
					break;
				case 12 :
					// CivlCParser.g:690:41: REAL
					{
					root_0 = (Object)adaptor.nil();


					REAL204=(Token)match(input,REAL,FOLLOW_REAL_in_typeSpecifier4305); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					REAL204_tree = (Object)adaptor.create(REAL204);
					adaptor.addChild(root_0, REAL204_tree);
					}

					}
					break;
				case 13 :
					// CivlCParser.g:690:48: RANGE
					{
					root_0 = (Object)adaptor.nil();


					RANGE205=(Token)match(input,RANGE,FOLLOW_RANGE_in_typeSpecifier4309); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					RANGE205_tree = (Object)adaptor.create(RANGE205);
					adaptor.addChild(root_0, RANGE205_tree);
					}

					}
					break;
				case 14 :
					// CivlCParser.g:691:4: atomicTypeSpecifier
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_atomicTypeSpecifier_in_typeSpecifier4314);
					atomicTypeSpecifier206=atomicTypeSpecifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, atomicTypeSpecifier206.getTree());

					}
					break;
				case 15 :
					// CivlCParser.g:692:4: structOrUnionSpecifier
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_structOrUnionSpecifier_in_typeSpecifier4319);
					structOrUnionSpecifier207=structOrUnionSpecifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, structOrUnionSpecifier207.getTree());

					}
					break;
				case 16 :
					// CivlCParser.g:693:4: enumSpecifier
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_enumSpecifier_in_typeSpecifier4324);
					enumSpecifier208=enumSpecifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, enumSpecifier208.getTree());

					}
					break;
				case 17 :
					// CivlCParser.g:694:4: typedefName
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_typedefName_in_typeSpecifier4329);
					typedefName209=typedefName();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, typedefName209.getTree());

					}
					break;
				case 18 :
					// CivlCParser.g:695:4: domainSpecifier
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_domainSpecifier_in_typeSpecifier4334);
					domainSpecifier210=domainSpecifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, domainSpecifier210.getTree());

					}
					break;
				case 19 :
					// CivlCParser.g:696:8: typeofSpecifier
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_typeofSpecifier_in_typeSpecifier4343);
					typeofSpecifier211=typeofSpecifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, typeofSpecifier211.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "typeSpecifier"


	public static class typeofSpecifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "typeofSpecifier"
	// CivlCParser.g:712:1: typeofSpecifier : TYPEOF LPAREN ( commaExpression RPAREN -> ^( TYPEOF_EXPRESSION LPAREN commaExpression RPAREN ) | typeName RPAREN -> ^( TYPEOF_TYPE LPAREN typeName RPAREN ) ) ;
	public final OmpParser_CivlCParser.typeofSpecifier_return typeofSpecifier() throws RecognitionException {
		OmpParser_CivlCParser.typeofSpecifier_return retval = new OmpParser_CivlCParser.typeofSpecifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token TYPEOF212=null;
		Token LPAREN213=null;
		Token RPAREN215=null;
		Token RPAREN217=null;
		ParserRuleReturnScope commaExpression214 =null;
		ParserRuleReturnScope typeName216 =null;

		Object TYPEOF212_tree=null;
		Object LPAREN213_tree=null;
		Object RPAREN215_tree=null;
		Object RPAREN217_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_TYPEOF=new RewriteRuleTokenStream(adaptor,"token TYPEOF");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_commaExpression=new RewriteRuleSubtreeStream(adaptor,"rule commaExpression");
		RewriteRuleSubtreeStream stream_typeName=new RewriteRuleSubtreeStream(adaptor,"rule typeName");

		try {
			// CivlCParser.g:713:5: ( TYPEOF LPAREN ( commaExpression RPAREN -> ^( TYPEOF_EXPRESSION LPAREN commaExpression RPAREN ) | typeName RPAREN -> ^( TYPEOF_TYPE LPAREN typeName RPAREN ) ) )
			// CivlCParser.g:713:7: TYPEOF LPAREN ( commaExpression RPAREN -> ^( TYPEOF_EXPRESSION LPAREN commaExpression RPAREN ) | typeName RPAREN -> ^( TYPEOF_TYPE LPAREN typeName RPAREN ) )
			{
			TYPEOF212=(Token)match(input,TYPEOF,FOLLOW_TYPEOF_in_typeofSpecifier4359); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_TYPEOF.add(TYPEOF212);

			LPAREN213=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_typeofSpecifier4361); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN213);

			// CivlCParser.g:714:9: ( commaExpression RPAREN -> ^( TYPEOF_EXPRESSION LPAREN commaExpression RPAREN ) | typeName RPAREN -> ^( TYPEOF_TYPE LPAREN typeName RPAREN ) )
			int alt41=2;
			switch ( input.LA(1) ) {
			case ALIGNOF:
			case AMPERSAND:
			case BIG_O:
			case CALLS:
			case CHARACTER_CONSTANT:
			case DERIV:
			case ELLIPSIS:
			case EXISTS:
			case FALSE:
			case FLOATING_CONSTANT:
			case FORALL:
			case GENERIC:
			case HERE:
			case INTEGER_CONSTANT:
			case LPAREN:
			case MINUSMINUS:
			case NOT:
			case PLUS:
			case PLUSPLUS:
			case PROCNULL:
			case RESULT:
			case SCOPEOF:
			case SELF:
			case SIZEOF:
			case SPAWN:
			case STAR:
			case STRING_LITERAL:
			case SUB:
			case TILDE:
			case TRUE:
			case UNIFORM:
			case ROOT:
				{
				alt41=1;
				}
				break;
			case IDENTIFIER:
				{
				int LA41_2 = input.LA(2);
				if ( (!(((!DeclarationScope_stack.peek().typedefNameUsed && isTypeName(input.LT(1).getText()))))) ) {
					alt41=1;
				}
				else if ( ((!DeclarationScope_stack.peek().typedefNameUsed && isTypeName(input.LT(1).getText()))) ) {
					alt41=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 41, 2, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case ATOMIC:
			case BOOL:
			case CHAR:
			case COMPLEX:
			case CONST:
			case DOMAIN:
			case DOUBLE:
			case ENUM:
			case FLOAT:
			case INPUT:
			case INT:
			case LONG:
			case OUTPUT:
			case RANGE:
			case REAL:
			case RESTRICT:
			case SHORT:
			case SIGNED:
			case STRUCT:
			case TYPEOF:
			case UNION:
			case UNSIGNED:
			case VOID:
			case VOLATILE:
				{
				alt41=2;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 41, 0, input);
				throw nvae;
			}
			switch (alt41) {
				case 1 :
					// CivlCParser.g:714:11: commaExpression RPAREN
					{
					pushFollow(FOLLOW_commaExpression_in_typeofSpecifier4373);
					commaExpression214=commaExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_commaExpression.add(commaExpression214.getTree());
					RPAREN215=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_typeofSpecifier4375); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN215);

					// AST REWRITE
					// elements: commaExpression, LPAREN, RPAREN
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 715:11: -> ^( TYPEOF_EXPRESSION LPAREN commaExpression RPAREN )
					{
						// CivlCParser.g:715:14: ^( TYPEOF_EXPRESSION LPAREN commaExpression RPAREN )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TYPEOF_EXPRESSION, "TYPEOF_EXPRESSION"), root_1);
						adaptor.addChild(root_1, stream_LPAREN.nextNode());
						adaptor.addChild(root_1, stream_commaExpression.nextTree());
						adaptor.addChild(root_1, stream_RPAREN.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:716:11: typeName RPAREN
					{
					pushFollow(FOLLOW_typeName_in_typeofSpecifier4409);
					typeName216=typeName();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeName.add(typeName216.getTree());
					RPAREN217=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_typeofSpecifier4411); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN217);

					// AST REWRITE
					// elements: RPAREN, typeName, LPAREN
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 717:11: -> ^( TYPEOF_TYPE LPAREN typeName RPAREN )
					{
						// CivlCParser.g:717:14: ^( TYPEOF_TYPE LPAREN typeName RPAREN )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TYPEOF_TYPE, "TYPEOF_TYPE"), root_1);
						adaptor.addChild(root_1, stream_LPAREN.nextNode());
						adaptor.addChild(root_1, stream_typeName.nextTree());
						adaptor.addChild(root_1, stream_RPAREN.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "typeofSpecifier"


	public static class structOrUnionSpecifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "structOrUnionSpecifier"
	// CivlCParser.g:726:1: structOrUnionSpecifier : structOrUnion ( IDENTIFIER LCURLY structDeclarationList RCURLY -> ^( structOrUnion IDENTIFIER structDeclarationList RCURLY ) | LCURLY structDeclarationList RCURLY -> ^( structOrUnion ABSENT structDeclarationList RCURLY ) | IDENTIFIER -> ^( structOrUnion IDENTIFIER ABSENT ) ) ;
	public final OmpParser_CivlCParser.structOrUnionSpecifier_return structOrUnionSpecifier() throws RecognitionException {
		OmpParser_CivlCParser.structOrUnionSpecifier_return retval = new OmpParser_CivlCParser.structOrUnionSpecifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token IDENTIFIER219=null;
		Token LCURLY220=null;
		Token RCURLY222=null;
		Token LCURLY223=null;
		Token RCURLY225=null;
		Token IDENTIFIER226=null;
		ParserRuleReturnScope structOrUnion218 =null;
		ParserRuleReturnScope structDeclarationList221 =null;
		ParserRuleReturnScope structDeclarationList224 =null;

		Object IDENTIFIER219_tree=null;
		Object LCURLY220_tree=null;
		Object RCURLY222_tree=null;
		Object LCURLY223_tree=null;
		Object RCURLY225_tree=null;
		Object IDENTIFIER226_tree=null;
		RewriteRuleTokenStream stream_LCURLY=new RewriteRuleTokenStream(adaptor,"token LCURLY");
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
		RewriteRuleTokenStream stream_RCURLY=new RewriteRuleTokenStream(adaptor,"token RCURLY");
		RewriteRuleSubtreeStream stream_structDeclarationList=new RewriteRuleSubtreeStream(adaptor,"rule structDeclarationList");
		RewriteRuleSubtreeStream stream_structOrUnion=new RewriteRuleSubtreeStream(adaptor,"rule structOrUnion");

		try {
			// CivlCParser.g:727:2: ( structOrUnion ( IDENTIFIER LCURLY structDeclarationList RCURLY -> ^( structOrUnion IDENTIFIER structDeclarationList RCURLY ) | LCURLY structDeclarationList RCURLY -> ^( structOrUnion ABSENT structDeclarationList RCURLY ) | IDENTIFIER -> ^( structOrUnion IDENTIFIER ABSENT ) ) )
			// CivlCParser.g:727:4: structOrUnion ( IDENTIFIER LCURLY structDeclarationList RCURLY -> ^( structOrUnion IDENTIFIER structDeclarationList RCURLY ) | LCURLY structDeclarationList RCURLY -> ^( structOrUnion ABSENT structDeclarationList RCURLY ) | IDENTIFIER -> ^( structOrUnion IDENTIFIER ABSENT ) )
			{
			pushFollow(FOLLOW_structOrUnion_in_structOrUnionSpecifier4459);
			structOrUnion218=structOrUnion();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_structOrUnion.add(structOrUnion218.getTree());
			// CivlCParser.g:728:6: ( IDENTIFIER LCURLY structDeclarationList RCURLY -> ^( structOrUnion IDENTIFIER structDeclarationList RCURLY ) | LCURLY structDeclarationList RCURLY -> ^( structOrUnion ABSENT structDeclarationList RCURLY ) | IDENTIFIER -> ^( structOrUnion IDENTIFIER ABSENT ) )
			int alt42=3;
			int LA42_0 = input.LA(1);
			if ( (LA42_0==IDENTIFIER) ) {
				int LA42_1 = input.LA(2);
				if ( (LA42_1==LCURLY) ) {
					alt42=1;
				}
				else if ( (LA42_1==EOF||(LA42_1 >= ABSTRACT && LA42_1 <= ALIGNAS)||(LA42_1 >= ATOMIC && LA42_1 <= AUTO)||LA42_1==BOOL||LA42_1==CHAR||(LA42_1 >= COLON && LA42_1 <= COMMA)||(LA42_1 >= COMPLEX && LA42_1 <= CONST)||LA42_1==DEVICE||LA42_1==DOMAIN||LA42_1==DOUBLE||LA42_1==ENUM||LA42_1==EXTERN||(LA42_1 >= FATOMIC && LA42_1 <= FLOAT)||LA42_1==GLOBAL||LA42_1==IDENTIFIER||(LA42_1 >= INLINE && LA42_1 <= INT)||(LA42_1 >= LONG && LA42_1 <= LPAREN)||LA42_1==LSQUARE||LA42_1==NORETURN||LA42_1==OUTPUT||LA42_1==PURE||LA42_1==RANGE||(LA42_1 >= REAL && LA42_1 <= REGISTER)||LA42_1==RESTRICT||LA42_1==RPAREN||(LA42_1 >= SEMI && LA42_1 <= SHARED)||(LA42_1 >= SHORT && LA42_1 <= SIGNED)||LA42_1==STAR||LA42_1==STATIC||LA42_1==STRUCT||(LA42_1 >= SYSTEM && LA42_1 <= THREADLOCAL)||(LA42_1 >= TYPEDEF && LA42_1 <= TYPEOF)||(LA42_1 >= UNION && LA42_1 <= UNSIGNED)||(LA42_1 >= VOID && LA42_1 <= VOLATILE)) ) {
					alt42=3;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 42, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}
			else if ( (LA42_0==LCURLY) ) {
				alt42=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 42, 0, input);
				throw nvae;
			}

			switch (alt42) {
				case 1 :
					// CivlCParser.g:728:8: IDENTIFIER LCURLY structDeclarationList RCURLY
					{
					IDENTIFIER219=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_structOrUnionSpecifier4468); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER219);

					LCURLY220=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_structOrUnionSpecifier4470); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY220);

					pushFollow(FOLLOW_structDeclarationList_in_structOrUnionSpecifier4472);
					structDeclarationList221=structDeclarationList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_structDeclarationList.add(structDeclarationList221.getTree());
					RCURLY222=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_structOrUnionSpecifier4474); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY222);

					// AST REWRITE
					// elements: structDeclarationList, IDENTIFIER, structOrUnion, RCURLY
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 729:8: -> ^( structOrUnion IDENTIFIER structDeclarationList RCURLY )
					{
						// CivlCParser.g:729:11: ^( structOrUnion IDENTIFIER structDeclarationList RCURLY )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_structOrUnion.nextNode(), root_1);
						adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
						adaptor.addChild(root_1, stream_structDeclarationList.nextTree());
						adaptor.addChild(root_1, stream_RCURLY.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:730:8: LCURLY structDeclarationList RCURLY
					{
					LCURLY223=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_structOrUnionSpecifier4502); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY223);

					pushFollow(FOLLOW_structDeclarationList_in_structOrUnionSpecifier4504);
					structDeclarationList224=structDeclarationList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_structDeclarationList.add(structDeclarationList224.getTree());
					RCURLY225=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_structOrUnionSpecifier4506); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY225);

					// AST REWRITE
					// elements: structDeclarationList, RCURLY, structOrUnion
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 731:8: -> ^( structOrUnion ABSENT structDeclarationList RCURLY )
					{
						// CivlCParser.g:731:11: ^( structOrUnion ABSENT structDeclarationList RCURLY )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_structOrUnion.nextNode(), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_1, stream_structDeclarationList.nextTree());
						adaptor.addChild(root_1, stream_RCURLY.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// CivlCParser.g:732:8: IDENTIFIER
					{
					IDENTIFIER226=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_structOrUnionSpecifier4534); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER226);

					// AST REWRITE
					// elements: structOrUnion, IDENTIFIER
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 733:8: -> ^( structOrUnion IDENTIFIER ABSENT )
					{
						// CivlCParser.g:733:11: ^( structOrUnion IDENTIFIER ABSENT )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_structOrUnion.nextNode(), root_1);
						adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "structOrUnionSpecifier"


	public static class structOrUnion_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "structOrUnion"
	// CivlCParser.g:738:1: structOrUnion : ( STRUCT | UNION );
	public final OmpParser_CivlCParser.structOrUnion_return structOrUnion() throws RecognitionException {
		OmpParser_CivlCParser.structOrUnion_return retval = new OmpParser_CivlCParser.structOrUnion_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set227=null;

		Object set227_tree=null;

		try {
			// CivlCParser.g:739:2: ( STRUCT | UNION )
			// CivlCParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set227=input.LT(1);
			if ( input.LA(1)==STRUCT||input.LA(1)==UNION ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set227));
				state.errorRecovery=false;
				state.failed=false;
			}
			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				MismatchedSetException mse = new MismatchedSetException(null,input);
				throw mse;
			}
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "structOrUnion"


	public static class structDeclarationList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "structDeclarationList"
	// CivlCParser.g:746:1: structDeclarationList : ( structDeclaration )* -> ^( STRUCT_DECLARATION_LIST ( structDeclaration )* ) ;
	public final OmpParser_CivlCParser.structDeclarationList_return structDeclarationList() throws RecognitionException {
		OmpParser_CivlCParser.structDeclarationList_return retval = new OmpParser_CivlCParser.structDeclarationList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope structDeclaration228 =null;

		RewriteRuleSubtreeStream stream_structDeclaration=new RewriteRuleSubtreeStream(adaptor,"rule structDeclaration");

		try {
			// CivlCParser.g:747:2: ( ( structDeclaration )* -> ^( STRUCT_DECLARATION_LIST ( structDeclaration )* ) )
			// CivlCParser.g:747:4: ( structDeclaration )*
			{
			// CivlCParser.g:747:4: ( structDeclaration )*
			loop43:
			while (true) {
				int alt43=2;
				int LA43_0 = input.LA(1);
				if ( (LA43_0==ATOMIC||LA43_0==BOOL||LA43_0==CHAR||(LA43_0 >= COMPLEX && LA43_0 <= CONST)||LA43_0==DOMAIN||LA43_0==DOUBLE||LA43_0==ENUM||LA43_0==FLOAT||LA43_0==IDENTIFIER||(LA43_0 >= INPUT && LA43_0 <= INT)||LA43_0==LONG||LA43_0==OUTPUT||LA43_0==RANGE||LA43_0==REAL||LA43_0==RESTRICT||(LA43_0 >= SHORT && LA43_0 <= SIGNED)||LA43_0==STATICASSERT||LA43_0==STRUCT||LA43_0==TYPEOF||(LA43_0 >= UNION && LA43_0 <= UNSIGNED)||(LA43_0 >= VOID && LA43_0 <= VOLATILE)) ) {
					alt43=1;
				}

				switch (alt43) {
				case 1 :
					// CivlCParser.g:747:4: structDeclaration
					{
					pushFollow(FOLLOW_structDeclaration_in_structDeclarationList4588);
					structDeclaration228=structDeclaration();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_structDeclaration.add(structDeclaration228.getTree());
					}
					break;

				default :
					break loop43;
				}
			}

			// AST REWRITE
			// elements: structDeclaration
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 748:4: -> ^( STRUCT_DECLARATION_LIST ( structDeclaration )* )
			{
				// CivlCParser.g:748:7: ^( STRUCT_DECLARATION_LIST ( structDeclaration )* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STRUCT_DECLARATION_LIST, "STRUCT_DECLARATION_LIST"), root_1);
				// CivlCParser.g:748:33: ( structDeclaration )*
				while ( stream_structDeclaration.hasNext() ) {
					adaptor.addChild(root_1, stream_structDeclaration.nextTree());
				}
				stream_structDeclaration.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "structDeclarationList"


	public static class structDeclaration_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "structDeclaration"
	// CivlCParser.g:762:1: structDeclaration : (s= specifierQualifierList ( -> ^( STRUCT_DECLARATION $s ABSENT ) | structDeclaratorList -> ^( STRUCT_DECLARATION $s structDeclaratorList ) ) SEMI | staticAssertDeclaration );
	public final OmpParser_CivlCParser.structDeclaration_return structDeclaration() throws RecognitionException {
		DeclarationScope_stack.push(new DeclarationScope_scope());

		OmpParser_CivlCParser.structDeclaration_return retval = new OmpParser_CivlCParser.structDeclaration_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SEMI230=null;
		ParserRuleReturnScope s =null;
		ParserRuleReturnScope structDeclaratorList229 =null;
		ParserRuleReturnScope staticAssertDeclaration231 =null;

		Object SEMI230_tree=null;
		RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
		RewriteRuleSubtreeStream stream_structDeclaratorList=new RewriteRuleSubtreeStream(adaptor,"rule structDeclaratorList");
		RewriteRuleSubtreeStream stream_specifierQualifierList=new RewriteRuleSubtreeStream(adaptor,"rule specifierQualifierList");


		  DeclarationScope_stack.peek().isTypedef = false;
		  DeclarationScope_stack.peek().typedefNameUsed = false;

		try {
			// CivlCParser.g:768:5: (s= specifierQualifierList ( -> ^( STRUCT_DECLARATION $s ABSENT ) | structDeclaratorList -> ^( STRUCT_DECLARATION $s structDeclaratorList ) ) SEMI | staticAssertDeclaration )
			int alt45=2;
			int LA45_0 = input.LA(1);
			if ( (LA45_0==ATOMIC||LA45_0==BOOL||LA45_0==CHAR||(LA45_0 >= COMPLEX && LA45_0 <= CONST)||LA45_0==DOMAIN||LA45_0==DOUBLE||LA45_0==ENUM||LA45_0==FLOAT||LA45_0==IDENTIFIER||(LA45_0 >= INPUT && LA45_0 <= INT)||LA45_0==LONG||LA45_0==OUTPUT||LA45_0==RANGE||LA45_0==REAL||LA45_0==RESTRICT||(LA45_0 >= SHORT && LA45_0 <= SIGNED)||LA45_0==STRUCT||LA45_0==TYPEOF||(LA45_0 >= UNION && LA45_0 <= UNSIGNED)||(LA45_0 >= VOID && LA45_0 <= VOLATILE)) ) {
				alt45=1;
			}
			else if ( (LA45_0==STATICASSERT) ) {
				alt45=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 45, 0, input);
				throw nvae;
			}

			switch (alt45) {
				case 1 :
					// CivlCParser.g:768:7: s= specifierQualifierList ( -> ^( STRUCT_DECLARATION $s ABSENT ) | structDeclaratorList -> ^( STRUCT_DECLARATION $s structDeclaratorList ) ) SEMI
					{
					pushFollow(FOLLOW_specifierQualifierList_in_structDeclaration4629);
					s=specifierQualifierList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_specifierQualifierList.add(s.getTree());
					// CivlCParser.g:769:7: ( -> ^( STRUCT_DECLARATION $s ABSENT ) | structDeclaratorList -> ^( STRUCT_DECLARATION $s structDeclaratorList ) )
					int alt44=2;
					int LA44_0 = input.LA(1);
					if ( (LA44_0==SEMI) ) {
						alt44=1;
					}
					else if ( (LA44_0==COLON||LA44_0==IDENTIFIER||LA44_0==LPAREN||LA44_0==STAR) ) {
						alt44=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 44, 0, input);
						throw nvae;
					}

					switch (alt44) {
						case 1 :
							// CivlCParser.g:769:9: 
							{
							// AST REWRITE
							// elements: s
							// token labels: 
							// rule labels: retval, s
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
							RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"rule s",s!=null?s.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 769:9: -> ^( STRUCT_DECLARATION $s ABSENT )
							{
								// CivlCParser.g:769:12: ^( STRUCT_DECLARATION $s ABSENT )
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STRUCT_DECLARATION, "STRUCT_DECLARATION"), root_1);
								adaptor.addChild(root_1, stream_s.nextTree());
								adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;
						case 2 :
							// CivlCParser.g:770:9: structDeclaratorList
							{
							pushFollow(FOLLOW_structDeclaratorList_in_structDeclaration4658);
							structDeclaratorList229=structDeclaratorList();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_structDeclaratorList.add(structDeclaratorList229.getTree());
							// AST REWRITE
							// elements: structDeclaratorList, s
							// token labels: 
							// rule labels: retval, s
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
							RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"rule s",s!=null?s.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 771:9: -> ^( STRUCT_DECLARATION $s structDeclaratorList )
							{
								// CivlCParser.g:771:12: ^( STRUCT_DECLARATION $s structDeclaratorList )
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STRUCT_DECLARATION, "STRUCT_DECLARATION"), root_1);
								adaptor.addChild(root_1, stream_s.nextTree());
								adaptor.addChild(root_1, stream_structDeclaratorList.nextTree());
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;

					}

					SEMI230=(Token)match(input,SEMI,FOLLOW_SEMI_in_structDeclaration4693); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMI.add(SEMI230);

					}
					break;
				case 2 :
					// CivlCParser.g:774:7: staticAssertDeclaration
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_staticAssertDeclaration_in_structDeclaration4701);
					staticAssertDeclaration231=staticAssertDeclaration();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, staticAssertDeclaration231.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
			DeclarationScope_stack.pop();

		}
		return retval;
	}
	// $ANTLR end "structDeclaration"


	public static class specifierQualifierList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "specifierQualifierList"
	// CivlCParser.g:781:1: specifierQualifierList : ( typeSpecifierOrQualifier )+ -> ^( SPECIFIER_QUALIFIER_LIST ( typeSpecifierOrQualifier )+ ) ;
	public final OmpParser_CivlCParser.specifierQualifierList_return specifierQualifierList() throws RecognitionException {
		OmpParser_CivlCParser.specifierQualifierList_return retval = new OmpParser_CivlCParser.specifierQualifierList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope typeSpecifierOrQualifier232 =null;

		RewriteRuleSubtreeStream stream_typeSpecifierOrQualifier=new RewriteRuleSubtreeStream(adaptor,"rule typeSpecifierOrQualifier");

		try {
			// CivlCParser.g:782:5: ( ( typeSpecifierOrQualifier )+ -> ^( SPECIFIER_QUALIFIER_LIST ( typeSpecifierOrQualifier )+ ) )
			// CivlCParser.g:782:7: ( typeSpecifierOrQualifier )+
			{
			// CivlCParser.g:782:7: ( typeSpecifierOrQualifier )+
			int cnt46=0;
			loop46:
			while (true) {
				int alt46=2;
				int LA46_0 = input.LA(1);
				if ( (LA46_0==IDENTIFIER) ) {
					int LA46_2 = input.LA(2);
					if ( ((!DeclarationScope_stack.peek().typedefNameUsed && isTypeName(input.LT(1).getText()))) ) {
						alt46=1;
					}

				}
				else if ( (LA46_0==ATOMIC||LA46_0==BOOL||LA46_0==CHAR||(LA46_0 >= COMPLEX && LA46_0 <= CONST)||LA46_0==DOMAIN||LA46_0==DOUBLE||LA46_0==ENUM||LA46_0==FLOAT||(LA46_0 >= INPUT && LA46_0 <= INT)||LA46_0==LONG||LA46_0==OUTPUT||LA46_0==RANGE||LA46_0==REAL||LA46_0==RESTRICT||(LA46_0 >= SHORT && LA46_0 <= SIGNED)||LA46_0==STRUCT||LA46_0==TYPEOF||(LA46_0 >= UNION && LA46_0 <= UNSIGNED)||(LA46_0 >= VOID && LA46_0 <= VOLATILE)) ) {
					alt46=1;
				}

				switch (alt46) {
				case 1 :
					// CivlCParser.g:782:7: typeSpecifierOrQualifier
					{
					pushFollow(FOLLOW_typeSpecifierOrQualifier_in_specifierQualifierList4720);
					typeSpecifierOrQualifier232=typeSpecifierOrQualifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeSpecifierOrQualifier.add(typeSpecifierOrQualifier232.getTree());
					}
					break;

				default :
					if ( cnt46 >= 1 ) break loop46;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(46, input);
					throw eee;
				}
				cnt46++;
			}

			// AST REWRITE
			// elements: typeSpecifierOrQualifier
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 783:7: -> ^( SPECIFIER_QUALIFIER_LIST ( typeSpecifierOrQualifier )+ )
			{
				// CivlCParser.g:783:10: ^( SPECIFIER_QUALIFIER_LIST ( typeSpecifierOrQualifier )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(SPECIFIER_QUALIFIER_LIST, "SPECIFIER_QUALIFIER_LIST"), root_1);
				if ( !(stream_typeSpecifierOrQualifier.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_typeSpecifierOrQualifier.hasNext() ) {
					adaptor.addChild(root_1, stream_typeSpecifierOrQualifier.nextTree());
				}
				stream_typeSpecifierOrQualifier.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "specifierQualifierList"


	public static class structDeclaratorList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "structDeclaratorList"
	// CivlCParser.g:790:1: structDeclaratorList :s+= structDeclarator ( COMMA s+= structDeclarator )* -> ^( STRUCT_DECLARATOR_LIST ( $s)+ ) ;
	public final OmpParser_CivlCParser.structDeclaratorList_return structDeclaratorList() throws RecognitionException {
		OmpParser_CivlCParser.structDeclaratorList_return retval = new OmpParser_CivlCParser.structDeclaratorList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMMA233=null;
		List<Object> list_s=null;
		RuleReturnScope s = null;
		Object COMMA233_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_structDeclarator=new RewriteRuleSubtreeStream(adaptor,"rule structDeclarator");

		try {
			// CivlCParser.g:791:5: (s+= structDeclarator ( COMMA s+= structDeclarator )* -> ^( STRUCT_DECLARATOR_LIST ( $s)+ ) )
			// CivlCParser.g:791:7: s+= structDeclarator ( COMMA s+= structDeclarator )*
			{
			pushFollow(FOLLOW_structDeclarator_in_structDeclaratorList4757);
			s=structDeclarator();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_structDeclarator.add(s.getTree());
			if (list_s==null) list_s=new ArrayList<Object>();
			list_s.add(s.getTree());
			// CivlCParser.g:791:27: ( COMMA s+= structDeclarator )*
			loop47:
			while (true) {
				int alt47=2;
				int LA47_0 = input.LA(1);
				if ( (LA47_0==COMMA) ) {
					alt47=1;
				}

				switch (alt47) {
				case 1 :
					// CivlCParser.g:791:28: COMMA s+= structDeclarator
					{
					COMMA233=(Token)match(input,COMMA,FOLLOW_COMMA_in_structDeclaratorList4760); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA233);

					pushFollow(FOLLOW_structDeclarator_in_structDeclaratorList4764);
					s=structDeclarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_structDeclarator.add(s.getTree());
					if (list_s==null) list_s=new ArrayList<Object>();
					list_s.add(s.getTree());
					}
					break;

				default :
					break loop47;
				}
			}

			// AST REWRITE
			// elements: s
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: s
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"token s",list_s);
			root_0 = (Object)adaptor.nil();
			// 792:7: -> ^( STRUCT_DECLARATOR_LIST ( $s)+ )
			{
				// CivlCParser.g:792:10: ^( STRUCT_DECLARATOR_LIST ( $s)+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STRUCT_DECLARATOR_LIST, "STRUCT_DECLARATOR_LIST"), root_1);
				if ( !(stream_s.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_s.hasNext() ) {
					adaptor.addChild(root_1, stream_s.nextTree());
				}
				stream_s.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "structDeclaratorList"


	public static class structDeclarator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "structDeclarator"
	// CivlCParser.g:800:1: structDeclarator : ( declarator ( -> ^( STRUCT_DECLARATOR declarator ABSENT ) | COLON constantExpression -> ^( STRUCT_DECLARATOR declarator constantExpression ) ) | COLON constantExpression -> ^( STRUCT_DECLARATOR ABSENT constantExpression ) );
	public final OmpParser_CivlCParser.structDeclarator_return structDeclarator() throws RecognitionException {
		OmpParser_CivlCParser.structDeclarator_return retval = new OmpParser_CivlCParser.structDeclarator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COLON235=null;
		Token COLON237=null;
		ParserRuleReturnScope declarator234 =null;
		ParserRuleReturnScope constantExpression236 =null;
		ParserRuleReturnScope constantExpression238 =null;

		Object COLON235_tree=null;
		Object COLON237_tree=null;
		RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
		RewriteRuleSubtreeStream stream_declarator=new RewriteRuleSubtreeStream(adaptor,"rule declarator");
		RewriteRuleSubtreeStream stream_constantExpression=new RewriteRuleSubtreeStream(adaptor,"rule constantExpression");

		try {
			// CivlCParser.g:801:5: ( declarator ( -> ^( STRUCT_DECLARATOR declarator ABSENT ) | COLON constantExpression -> ^( STRUCT_DECLARATOR declarator constantExpression ) ) | COLON constantExpression -> ^( STRUCT_DECLARATOR ABSENT constantExpression ) )
			int alt49=2;
			int LA49_0 = input.LA(1);
			if ( (LA49_0==IDENTIFIER||LA49_0==LPAREN||LA49_0==STAR) ) {
				alt49=1;
			}
			else if ( (LA49_0==COLON) ) {
				alt49=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 49, 0, input);
				throw nvae;
			}

			switch (alt49) {
				case 1 :
					// CivlCParser.g:801:7: declarator ( -> ^( STRUCT_DECLARATOR declarator ABSENT ) | COLON constantExpression -> ^( STRUCT_DECLARATOR declarator constantExpression ) )
					{
					pushFollow(FOLLOW_declarator_in_structDeclarator4801);
					declarator234=declarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_declarator.add(declarator234.getTree());
					// CivlCParser.g:802:7: ( -> ^( STRUCT_DECLARATOR declarator ABSENT ) | COLON constantExpression -> ^( STRUCT_DECLARATOR declarator constantExpression ) )
					int alt48=2;
					int LA48_0 = input.LA(1);
					if ( (LA48_0==COMMA||LA48_0==SEMI) ) {
						alt48=1;
					}
					else if ( (LA48_0==COLON) ) {
						alt48=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 48, 0, input);
						throw nvae;
					}

					switch (alt48) {
						case 1 :
							// CivlCParser.g:802:10: 
							{
							// AST REWRITE
							// elements: declarator
							// token labels: 
							// rule labels: retval
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 802:10: -> ^( STRUCT_DECLARATOR declarator ABSENT )
							{
								// CivlCParser.g:802:13: ^( STRUCT_DECLARATOR declarator ABSENT )
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STRUCT_DECLARATOR, "STRUCT_DECLARATOR"), root_1);
								adaptor.addChild(root_1, stream_declarator.nextTree());
								adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;
						case 2 :
							// CivlCParser.g:803:9: COLON constantExpression
							{
							COLON235=(Token)match(input,COLON,FOLLOW_COLON_in_structDeclarator4830); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_COLON.add(COLON235);

							pushFollow(FOLLOW_constantExpression_in_structDeclarator4832);
							constantExpression236=constantExpression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_constantExpression.add(constantExpression236.getTree());
							// AST REWRITE
							// elements: constantExpression, declarator
							// token labels: 
							// rule labels: retval
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 804:10: -> ^( STRUCT_DECLARATOR declarator constantExpression )
							{
								// CivlCParser.g:804:13: ^( STRUCT_DECLARATOR declarator constantExpression )
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STRUCT_DECLARATOR, "STRUCT_DECLARATOR"), root_1);
								adaptor.addChild(root_1, stream_declarator.nextTree());
								adaptor.addChild(root_1, stream_constantExpression.nextTree());
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;

					}

					}
					break;
				case 2 :
					// CivlCParser.g:806:7: COLON constantExpression
					{
					COLON237=(Token)match(input,COLON,FOLLOW_COLON_in_structDeclarator4867); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COLON.add(COLON237);

					pushFollow(FOLLOW_constantExpression_in_structDeclarator4869);
					constantExpression238=constantExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_constantExpression.add(constantExpression238.getTree());
					// AST REWRITE
					// elements: constantExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 807:7: -> ^( STRUCT_DECLARATOR ABSENT constantExpression )
					{
						// CivlCParser.g:807:10: ^( STRUCT_DECLARATOR ABSENT constantExpression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STRUCT_DECLARATOR, "STRUCT_DECLARATOR"), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_1, stream_constantExpression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "structDeclarator"


	public static class enumSpecifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "enumSpecifier"
	// CivlCParser.g:815:1: enumSpecifier : ENUM ( IDENTIFIER -> ^( ENUM IDENTIFIER ABSENT ) | IDENTIFIER LCURLY enumeratorList ( COMMA )? RCURLY -> ^( ENUM IDENTIFIER enumeratorList ) | LCURLY enumeratorList ( COMMA )? RCURLY -> ^( ENUM ABSENT enumeratorList ) ) ;
	public final OmpParser_CivlCParser.enumSpecifier_return enumSpecifier() throws RecognitionException {
		OmpParser_CivlCParser.enumSpecifier_return retval = new OmpParser_CivlCParser.enumSpecifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ENUM239=null;
		Token IDENTIFIER240=null;
		Token IDENTIFIER241=null;
		Token LCURLY242=null;
		Token COMMA244=null;
		Token RCURLY245=null;
		Token LCURLY246=null;
		Token COMMA248=null;
		Token RCURLY249=null;
		ParserRuleReturnScope enumeratorList243 =null;
		ParserRuleReturnScope enumeratorList247 =null;

		Object ENUM239_tree=null;
		Object IDENTIFIER240_tree=null;
		Object IDENTIFIER241_tree=null;
		Object LCURLY242_tree=null;
		Object COMMA244_tree=null;
		Object RCURLY245_tree=null;
		Object LCURLY246_tree=null;
		Object COMMA248_tree=null;
		Object RCURLY249_tree=null;
		RewriteRuleTokenStream stream_LCURLY=new RewriteRuleTokenStream(adaptor,"token LCURLY");
		RewriteRuleTokenStream stream_ENUM=new RewriteRuleTokenStream(adaptor,"token ENUM");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
		RewriteRuleTokenStream stream_RCURLY=new RewriteRuleTokenStream(adaptor,"token RCURLY");
		RewriteRuleSubtreeStream stream_enumeratorList=new RewriteRuleSubtreeStream(adaptor,"rule enumeratorList");

		try {
			// CivlCParser.g:816:5: ( ENUM ( IDENTIFIER -> ^( ENUM IDENTIFIER ABSENT ) | IDENTIFIER LCURLY enumeratorList ( COMMA )? RCURLY -> ^( ENUM IDENTIFIER enumeratorList ) | LCURLY enumeratorList ( COMMA )? RCURLY -> ^( ENUM ABSENT enumeratorList ) ) )
			// CivlCParser.g:816:7: ENUM ( IDENTIFIER -> ^( ENUM IDENTIFIER ABSENT ) | IDENTIFIER LCURLY enumeratorList ( COMMA )? RCURLY -> ^( ENUM IDENTIFIER enumeratorList ) | LCURLY enumeratorList ( COMMA )? RCURLY -> ^( ENUM ABSENT enumeratorList ) )
			{
			ENUM239=(Token)match(input,ENUM,FOLLOW_ENUM_in_enumSpecifier4904); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ENUM.add(ENUM239);

			// CivlCParser.g:817:9: ( IDENTIFIER -> ^( ENUM IDENTIFIER ABSENT ) | IDENTIFIER LCURLY enumeratorList ( COMMA )? RCURLY -> ^( ENUM IDENTIFIER enumeratorList ) | LCURLY enumeratorList ( COMMA )? RCURLY -> ^( ENUM ABSENT enumeratorList ) )
			int alt52=3;
			int LA52_0 = input.LA(1);
			if ( (LA52_0==IDENTIFIER) ) {
				int LA52_1 = input.LA(2);
				if ( (LA52_1==LCURLY) ) {
					alt52=2;
				}
				else if ( (LA52_1==EOF||(LA52_1 >= ABSTRACT && LA52_1 <= ALIGNAS)||(LA52_1 >= ATOMIC && LA52_1 <= AUTO)||LA52_1==BOOL||LA52_1==CHAR||(LA52_1 >= COLON && LA52_1 <= COMMA)||(LA52_1 >= COMPLEX && LA52_1 <= CONST)||LA52_1==DEVICE||LA52_1==DOMAIN||LA52_1==DOUBLE||LA52_1==ENUM||LA52_1==EXTERN||(LA52_1 >= FATOMIC && LA52_1 <= FLOAT)||LA52_1==GLOBAL||LA52_1==IDENTIFIER||(LA52_1 >= INLINE && LA52_1 <= INT)||(LA52_1 >= LONG && LA52_1 <= LPAREN)||LA52_1==LSQUARE||LA52_1==NORETURN||LA52_1==OUTPUT||LA52_1==PURE||LA52_1==RANGE||(LA52_1 >= REAL && LA52_1 <= REGISTER)||LA52_1==RESTRICT||LA52_1==RPAREN||(LA52_1 >= SEMI && LA52_1 <= SHARED)||(LA52_1 >= SHORT && LA52_1 <= SIGNED)||LA52_1==STAR||LA52_1==STATIC||LA52_1==STRUCT||(LA52_1 >= SYSTEM && LA52_1 <= THREADLOCAL)||(LA52_1 >= TYPEDEF && LA52_1 <= TYPEOF)||(LA52_1 >= UNION && LA52_1 <= UNSIGNED)||(LA52_1 >= VOID && LA52_1 <= VOLATILE)) ) {
					alt52=1;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 52, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}
			else if ( (LA52_0==LCURLY) ) {
				alt52=3;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 52, 0, input);
				throw nvae;
			}

			switch (alt52) {
				case 1 :
					// CivlCParser.g:817:11: IDENTIFIER
					{
					IDENTIFIER240=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_enumSpecifier4917); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER240);

					// AST REWRITE
					// elements: IDENTIFIER, ENUM
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 818:11: -> ^( ENUM IDENTIFIER ABSENT )
					{
						// CivlCParser.g:818:14: ^( ENUM IDENTIFIER ABSENT )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ENUM.nextNode(), root_1);
						adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:819:11: IDENTIFIER LCURLY enumeratorList ( COMMA )? RCURLY
					{
					IDENTIFIER241=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_enumSpecifier4950); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER241);

					LCURLY242=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_enumSpecifier4952); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY242);

					pushFollow(FOLLOW_enumeratorList_in_enumSpecifier4954);
					enumeratorList243=enumeratorList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_enumeratorList.add(enumeratorList243.getTree());
					// CivlCParser.g:819:44: ( COMMA )?
					int alt50=2;
					int LA50_0 = input.LA(1);
					if ( (LA50_0==COMMA) ) {
						alt50=1;
					}
					switch (alt50) {
						case 1 :
							// CivlCParser.g:819:44: COMMA
							{
							COMMA244=(Token)match(input,COMMA,FOLLOW_COMMA_in_enumSpecifier4956); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_COMMA.add(COMMA244);

							}
							break;

					}

					RCURLY245=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_enumSpecifier4959); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY245);

					// AST REWRITE
					// elements: ENUM, enumeratorList, IDENTIFIER
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 820:11: -> ^( ENUM IDENTIFIER enumeratorList )
					{
						// CivlCParser.g:820:14: ^( ENUM IDENTIFIER enumeratorList )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ENUM.nextNode(), root_1);
						adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
						adaptor.addChild(root_1, stream_enumeratorList.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// CivlCParser.g:821:11: LCURLY enumeratorList ( COMMA )? RCURLY
					{
					LCURLY246=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_enumSpecifier4991); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY246);

					pushFollow(FOLLOW_enumeratorList_in_enumSpecifier4993);
					enumeratorList247=enumeratorList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_enumeratorList.add(enumeratorList247.getTree());
					// CivlCParser.g:821:33: ( COMMA )?
					int alt51=2;
					int LA51_0 = input.LA(1);
					if ( (LA51_0==COMMA) ) {
						alt51=1;
					}
					switch (alt51) {
						case 1 :
							// CivlCParser.g:821:33: COMMA
							{
							COMMA248=(Token)match(input,COMMA,FOLLOW_COMMA_in_enumSpecifier4995); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_COMMA.add(COMMA248);

							}
							break;

					}

					RCURLY249=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_enumSpecifier4998); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY249);

					// AST REWRITE
					// elements: enumeratorList, ENUM
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 822:11: -> ^( ENUM ABSENT enumeratorList )
					{
						// CivlCParser.g:822:14: ^( ENUM ABSENT enumeratorList )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ENUM.nextNode(), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_1, stream_enumeratorList.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "enumSpecifier"


	public static class enumeratorList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "enumeratorList"
	// CivlCParser.g:830:1: enumeratorList : enumerator ( COMMA enumerator )* -> ^( ENUMERATOR_LIST ( enumerator )+ ) ;
	public final OmpParser_CivlCParser.enumeratorList_return enumeratorList() throws RecognitionException {
		OmpParser_CivlCParser.enumeratorList_return retval = new OmpParser_CivlCParser.enumeratorList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMMA251=null;
		ParserRuleReturnScope enumerator250 =null;
		ParserRuleReturnScope enumerator252 =null;

		Object COMMA251_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_enumerator=new RewriteRuleSubtreeStream(adaptor,"rule enumerator");

		try {
			// CivlCParser.g:831:5: ( enumerator ( COMMA enumerator )* -> ^( ENUMERATOR_LIST ( enumerator )+ ) )
			// CivlCParser.g:831:7: enumerator ( COMMA enumerator )*
			{
			pushFollow(FOLLOW_enumerator_in_enumeratorList5047);
			enumerator250=enumerator();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_enumerator.add(enumerator250.getTree());
			// CivlCParser.g:831:18: ( COMMA enumerator )*
			loop53:
			while (true) {
				int alt53=2;
				int LA53_0 = input.LA(1);
				if ( (LA53_0==COMMA) ) {
					int LA53_1 = input.LA(2);
					if ( (LA53_1==IDENTIFIER) ) {
						alt53=1;
					}

				}

				switch (alt53) {
				case 1 :
					// CivlCParser.g:831:19: COMMA enumerator
					{
					COMMA251=(Token)match(input,COMMA,FOLLOW_COMMA_in_enumeratorList5050); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA251);

					pushFollow(FOLLOW_enumerator_in_enumeratorList5052);
					enumerator252=enumerator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_enumerator.add(enumerator252.getTree());
					}
					break;

				default :
					break loop53;
				}
			}

			// AST REWRITE
			// elements: enumerator
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 832:7: -> ^( ENUMERATOR_LIST ( enumerator )+ )
			{
				// CivlCParser.g:832:10: ^( ENUMERATOR_LIST ( enumerator )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ENUMERATOR_LIST, "ENUMERATOR_LIST"), root_1);
				if ( !(stream_enumerator.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_enumerator.hasNext() ) {
					adaptor.addChild(root_1, stream_enumerator.nextTree());
				}
				stream_enumerator.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "enumeratorList"


	public static class enumerator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "enumerator"
	// CivlCParser.g:840:1: enumerator : IDENTIFIER ( -> ^( ENUMERATOR IDENTIFIER ABSENT ) | ( ASSIGN constantExpression ) -> ^( ENUMERATOR IDENTIFIER constantExpression ) ) ;
	public final OmpParser_CivlCParser.enumerator_return enumerator() throws RecognitionException {
		OmpParser_CivlCParser.enumerator_return retval = new OmpParser_CivlCParser.enumerator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token IDENTIFIER253=null;
		Token ASSIGN254=null;
		ParserRuleReturnScope constantExpression255 =null;

		Object IDENTIFIER253_tree=null;
		Object ASSIGN254_tree=null;
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
		RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
		RewriteRuleSubtreeStream stream_constantExpression=new RewriteRuleSubtreeStream(adaptor,"rule constantExpression");

		try {
			// CivlCParser.g:841:2: ( IDENTIFIER ( -> ^( ENUMERATOR IDENTIFIER ABSENT ) | ( ASSIGN constantExpression ) -> ^( ENUMERATOR IDENTIFIER constantExpression ) ) )
			// CivlCParser.g:841:4: IDENTIFIER ( -> ^( ENUMERATOR IDENTIFIER ABSENT ) | ( ASSIGN constantExpression ) -> ^( ENUMERATOR IDENTIFIER constantExpression ) )
			{
			IDENTIFIER253=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_enumerator5085); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER253);

			if ( state.backtracking==0 ) {
			    		Symbols_stack.peek().enumerationConstants.add((IDENTIFIER253!=null?IDENTIFIER253.getText():null));
					// System.err.println("define enum constant "+(IDENTIFIER253!=null?IDENTIFIER253.getText():null));	
			    	  }
			// CivlCParser.g:846:8: ( -> ^( ENUMERATOR IDENTIFIER ABSENT ) | ( ASSIGN constantExpression ) -> ^( ENUMERATOR IDENTIFIER constantExpression ) )
			int alt54=2;
			int LA54_0 = input.LA(1);
			if ( (LA54_0==COMMA||LA54_0==RCURLY) ) {
				alt54=1;
			}
			else if ( (LA54_0==ASSIGN) ) {
				alt54=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 54, 0, input);
				throw nvae;
			}

			switch (alt54) {
				case 1 :
					// CivlCParser.g:846:11: 
					{
					// AST REWRITE
					// elements: IDENTIFIER
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 846:11: -> ^( ENUMERATOR IDENTIFIER ABSENT )
					{
						// CivlCParser.g:846:14: ^( ENUMERATOR IDENTIFIER ABSENT )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ENUMERATOR, "ENUMERATOR"), root_1);
						adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:847:10: ( ASSIGN constantExpression )
					{
					// CivlCParser.g:847:10: ( ASSIGN constantExpression )
					// CivlCParser.g:847:11: ASSIGN constantExpression
					{
					ASSIGN254=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_enumerator5126); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(ASSIGN254);

					pushFollow(FOLLOW_constantExpression_in_enumerator5128);
					constantExpression255=constantExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_constantExpression.add(constantExpression255.getTree());
					}

					// AST REWRITE
					// elements: constantExpression, IDENTIFIER
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 848:11: -> ^( ENUMERATOR IDENTIFIER constantExpression )
					{
						// CivlCParser.g:848:14: ^( ENUMERATOR IDENTIFIER constantExpression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ENUMERATOR, "ENUMERATOR"), root_1);
						adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
						adaptor.addChild(root_1, stream_constantExpression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "enumerator"


	public static class atomicTypeSpecifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "atomicTypeSpecifier"
	// CivlCParser.g:853:1: atomicTypeSpecifier : ATOMIC LPAREN typeName RPAREN -> ^( ATOMIC typeName ) ;
	public final OmpParser_CivlCParser.atomicTypeSpecifier_return atomicTypeSpecifier() throws RecognitionException {
		OmpParser_CivlCParser.atomicTypeSpecifier_return retval = new OmpParser_CivlCParser.atomicTypeSpecifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ATOMIC256=null;
		Token LPAREN257=null;
		Token RPAREN259=null;
		ParserRuleReturnScope typeName258 =null;

		Object ATOMIC256_tree=null;
		Object LPAREN257_tree=null;
		Object RPAREN259_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_ATOMIC=new RewriteRuleTokenStream(adaptor,"token ATOMIC");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_typeName=new RewriteRuleSubtreeStream(adaptor,"rule typeName");

		try {
			// CivlCParser.g:854:5: ( ATOMIC LPAREN typeName RPAREN -> ^( ATOMIC typeName ) )
			// CivlCParser.g:854:7: ATOMIC LPAREN typeName RPAREN
			{
			ATOMIC256=(Token)match(input,ATOMIC,FOLLOW_ATOMIC_in_atomicTypeSpecifier5174); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ATOMIC.add(ATOMIC256);

			LPAREN257=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_atomicTypeSpecifier5176); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN257);

			pushFollow(FOLLOW_typeName_in_atomicTypeSpecifier5178);
			typeName258=typeName();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_typeName.add(typeName258.getTree());
			RPAREN259=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_atomicTypeSpecifier5180); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN259);

			// AST REWRITE
			// elements: ATOMIC, typeName
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 855:7: -> ^( ATOMIC typeName )
			{
				// CivlCParser.g:855:10: ^( ATOMIC typeName )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_ATOMIC.nextNode(), root_1);
				adaptor.addChild(root_1, stream_typeName.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "atomicTypeSpecifier"


	public static class typeQualifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "typeQualifier"
	// CivlCParser.g:859:1: typeQualifier : ( CONST | RESTRICT | VOLATILE | ATOMIC | INPUT | OUTPUT );
	public final OmpParser_CivlCParser.typeQualifier_return typeQualifier() throws RecognitionException {
		OmpParser_CivlCParser.typeQualifier_return retval = new OmpParser_CivlCParser.typeQualifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set260=null;

		Object set260_tree=null;

		try {
			// CivlCParser.g:860:5: ( CONST | RESTRICT | VOLATILE | ATOMIC | INPUT | OUTPUT )
			// CivlCParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set260=input.LT(1);
			if ( input.LA(1)==ATOMIC||input.LA(1)==CONST||input.LA(1)==INPUT||input.LA(1)==OUTPUT||input.LA(1)==RESTRICT||input.LA(1)==VOLATILE ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set260));
				state.errorRecovery=false;
				state.failed=false;
			}
			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				MismatchedSetException mse = new MismatchedSetException(null,input);
				throw mse;
			}
			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "typeQualifier"


	public static class functionSpecifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "functionSpecifier"
	// CivlCParser.g:867:1: functionSpecifier : ( INLINE | NORETURN | ABSTRACT CONTIN LPAREN INTEGER_CONSTANT RPAREN -> ^( ABSTRACT INTEGER_CONSTANT ) | ABSTRACT -> ^( ABSTRACT ) | SYSTEM -> ^( SYSTEM ) | FATOMIC -> ^( FATOMIC ) | PURE -> ^( PURE ) | DEVICE | GLOBAL );
	public final OmpParser_CivlCParser.functionSpecifier_return functionSpecifier() throws RecognitionException {
		OmpParser_CivlCParser.functionSpecifier_return retval = new OmpParser_CivlCParser.functionSpecifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token INLINE261=null;
		Token NORETURN262=null;
		Token ABSTRACT263=null;
		Token CONTIN264=null;
		Token LPAREN265=null;
		Token INTEGER_CONSTANT266=null;
		Token RPAREN267=null;
		Token ABSTRACT268=null;
		Token SYSTEM269=null;
		Token FATOMIC270=null;
		Token PURE271=null;
		Token DEVICE272=null;
		Token GLOBAL273=null;

		Object INLINE261_tree=null;
		Object NORETURN262_tree=null;
		Object ABSTRACT263_tree=null;
		Object CONTIN264_tree=null;
		Object LPAREN265_tree=null;
		Object INTEGER_CONSTANT266_tree=null;
		Object RPAREN267_tree=null;
		Object ABSTRACT268_tree=null;
		Object SYSTEM269_tree=null;
		Object FATOMIC270_tree=null;
		Object PURE271_tree=null;
		Object DEVICE272_tree=null;
		Object GLOBAL273_tree=null;
		RewriteRuleTokenStream stream_FATOMIC=new RewriteRuleTokenStream(adaptor,"token FATOMIC");
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_PURE=new RewriteRuleTokenStream(adaptor,"token PURE");
		RewriteRuleTokenStream stream_ABSTRACT=new RewriteRuleTokenStream(adaptor,"token ABSTRACT");
		RewriteRuleTokenStream stream_SYSTEM=new RewriteRuleTokenStream(adaptor,"token SYSTEM");
		RewriteRuleTokenStream stream_INTEGER_CONSTANT=new RewriteRuleTokenStream(adaptor,"token INTEGER_CONSTANT");
		RewriteRuleTokenStream stream_CONTIN=new RewriteRuleTokenStream(adaptor,"token CONTIN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");

		try {
			// CivlCParser.g:868:5: ( INLINE | NORETURN | ABSTRACT CONTIN LPAREN INTEGER_CONSTANT RPAREN -> ^( ABSTRACT INTEGER_CONSTANT ) | ABSTRACT -> ^( ABSTRACT ) | SYSTEM -> ^( SYSTEM ) | FATOMIC -> ^( FATOMIC ) | PURE -> ^( PURE ) | DEVICE | GLOBAL )
			int alt55=9;
			switch ( input.LA(1) ) {
			case INLINE:
				{
				alt55=1;
				}
				break;
			case NORETURN:
				{
				alt55=2;
				}
				break;
			case ABSTRACT:
				{
				int LA55_3 = input.LA(2);
				if ( (LA55_3==CONTIN) ) {
					alt55=3;
				}
				else if ( ((LA55_3 >= ABSTRACT && LA55_3 <= ALIGNAS)||(LA55_3 >= ATOMIC && LA55_3 <= AUTO)||LA55_3==BOOL||LA55_3==CHAR||LA55_3==COMMA||(LA55_3 >= COMPLEX && LA55_3 <= CONST)||LA55_3==DEVICE||LA55_3==DOMAIN||LA55_3==DOUBLE||LA55_3==ENUM||LA55_3==EXTERN||(LA55_3 >= FATOMIC && LA55_3 <= FLOAT)||LA55_3==GLOBAL||LA55_3==IDENTIFIER||(LA55_3 >= INLINE && LA55_3 <= INT)||(LA55_3 >= LONG && LA55_3 <= LPAREN)||LA55_3==LSQUARE||LA55_3==NORETURN||LA55_3==OUTPUT||LA55_3==PURE||LA55_3==RANGE||(LA55_3 >= REAL && LA55_3 <= REGISTER)||LA55_3==RESTRICT||LA55_3==RPAREN||(LA55_3 >= SEMI && LA55_3 <= SHARED)||(LA55_3 >= SHORT && LA55_3 <= SIGNED)||LA55_3==STAR||LA55_3==STATIC||LA55_3==STRUCT||(LA55_3 >= SYSTEM && LA55_3 <= THREADLOCAL)||(LA55_3 >= TYPEDEF && LA55_3 <= TYPEOF)||(LA55_3 >= UNION && LA55_3 <= UNSIGNED)||(LA55_3 >= VOID && LA55_3 <= VOLATILE)) ) {
					alt55=4;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 55, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case SYSTEM:
				{
				alt55=5;
				}
				break;
			case FATOMIC:
				{
				alt55=6;
				}
				break;
			case PURE:
				{
				alt55=7;
				}
				break;
			case DEVICE:
				{
				alt55=8;
				}
				break;
			case GLOBAL:
				{
				alt55=9;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 55, 0, input);
				throw nvae;
			}
			switch (alt55) {
				case 1 :
					// CivlCParser.g:868:7: INLINE
					{
					root_0 = (Object)adaptor.nil();


					INLINE261=(Token)match(input,INLINE,FOLLOW_INLINE_in_functionSpecifier5252); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INLINE261_tree = (Object)adaptor.create(INLINE261);
					adaptor.addChild(root_0, INLINE261_tree);
					}

					}
					break;
				case 2 :
					// CivlCParser.g:868:16: NORETURN
					{
					root_0 = (Object)adaptor.nil();


					NORETURN262=(Token)match(input,NORETURN,FOLLOW_NORETURN_in_functionSpecifier5256); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					NORETURN262_tree = (Object)adaptor.create(NORETURN262);
					adaptor.addChild(root_0, NORETURN262_tree);
					}

					}
					break;
				case 3 :
					// CivlCParser.g:869:7: ABSTRACT CONTIN LPAREN INTEGER_CONSTANT RPAREN
					{
					ABSTRACT263=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_functionSpecifier5264); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ABSTRACT.add(ABSTRACT263);

					CONTIN264=(Token)match(input,CONTIN,FOLLOW_CONTIN_in_functionSpecifier5266); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CONTIN.add(CONTIN264);

					LPAREN265=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_functionSpecifier5268); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN265);

					INTEGER_CONSTANT266=(Token)match(input,INTEGER_CONSTANT,FOLLOW_INTEGER_CONSTANT_in_functionSpecifier5270); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_INTEGER_CONSTANT.add(INTEGER_CONSTANT266);

					RPAREN267=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_functionSpecifier5272); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN267);

					// AST REWRITE
					// elements: INTEGER_CONSTANT, ABSTRACT
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 870:7: -> ^( ABSTRACT INTEGER_CONSTANT )
					{
						// CivlCParser.g:870:10: ^( ABSTRACT INTEGER_CONSTANT )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ABSTRACT.nextNode(), root_1);
						adaptor.addChild(root_1, stream_INTEGER_CONSTANT.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// CivlCParser.g:871:7: ABSTRACT
					{
					ABSTRACT268=(Token)match(input,ABSTRACT,FOLLOW_ABSTRACT_in_functionSpecifier5295); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ABSTRACT.add(ABSTRACT268);

					// AST REWRITE
					// elements: ABSTRACT
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 871:16: -> ^( ABSTRACT )
					{
						// CivlCParser.g:871:19: ^( ABSTRACT )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ABSTRACT.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 5 :
					// CivlCParser.g:872:7: SYSTEM
					{
					SYSTEM269=(Token)match(input,SYSTEM,FOLLOW_SYSTEM_in_functionSpecifier5309); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SYSTEM.add(SYSTEM269);

					// AST REWRITE
					// elements: SYSTEM
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 872:15: -> ^( SYSTEM )
					{
						// CivlCParser.g:872:18: ^( SYSTEM )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_SYSTEM.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 6 :
					// CivlCParser.g:873:7: FATOMIC
					{
					FATOMIC270=(Token)match(input,FATOMIC,FOLLOW_FATOMIC_in_functionSpecifier5324); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_FATOMIC.add(FATOMIC270);

					// AST REWRITE
					// elements: FATOMIC
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 873:15: -> ^( FATOMIC )
					{
						// CivlCParser.g:873:18: ^( FATOMIC )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_FATOMIC.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 7 :
					// CivlCParser.g:874:7: PURE
					{
					PURE271=(Token)match(input,PURE,FOLLOW_PURE_in_functionSpecifier5338); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_PURE.add(PURE271);

					// AST REWRITE
					// elements: PURE
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 874:12: -> ^( PURE )
					{
						// CivlCParser.g:874:15: ^( PURE )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_PURE.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 8 :
					// CivlCParser.g:875:7: DEVICE
					{
					root_0 = (Object)adaptor.nil();


					DEVICE272=(Token)match(input,DEVICE,FOLLOW_DEVICE_in_functionSpecifier5352); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					DEVICE272_tree = (Object)adaptor.create(DEVICE272);
					adaptor.addChild(root_0, DEVICE272_tree);
					}

					}
					break;
				case 9 :
					// CivlCParser.g:876:7: GLOBAL
					{
					root_0 = (Object)adaptor.nil();


					GLOBAL273=(Token)match(input,GLOBAL,FOLLOW_GLOBAL_in_functionSpecifier5360); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					GLOBAL273_tree = (Object)adaptor.create(GLOBAL273);
					adaptor.addChild(root_0, GLOBAL273_tree);
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "functionSpecifier"


	public static class alignmentSpecifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "alignmentSpecifier"
	// CivlCParser.g:885:1: alignmentSpecifier : ALIGNAS LPAREN ( typeName RPAREN -> ^( ALIGNAS TYPE typeName ) | constantExpression RPAREN -> ^( ALIGNAS EXPR constantExpression ) ) ;
	public final OmpParser_CivlCParser.alignmentSpecifier_return alignmentSpecifier() throws RecognitionException {
		OmpParser_CivlCParser.alignmentSpecifier_return retval = new OmpParser_CivlCParser.alignmentSpecifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ALIGNAS274=null;
		Token LPAREN275=null;
		Token RPAREN277=null;
		Token RPAREN279=null;
		ParserRuleReturnScope typeName276 =null;
		ParserRuleReturnScope constantExpression278 =null;

		Object ALIGNAS274_tree=null;
		Object LPAREN275_tree=null;
		Object RPAREN277_tree=null;
		Object RPAREN279_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_ALIGNAS=new RewriteRuleTokenStream(adaptor,"token ALIGNAS");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_typeName=new RewriteRuleSubtreeStream(adaptor,"rule typeName");
		RewriteRuleSubtreeStream stream_constantExpression=new RewriteRuleSubtreeStream(adaptor,"rule constantExpression");

		try {
			// CivlCParser.g:886:5: ( ALIGNAS LPAREN ( typeName RPAREN -> ^( ALIGNAS TYPE typeName ) | constantExpression RPAREN -> ^( ALIGNAS EXPR constantExpression ) ) )
			// CivlCParser.g:886:7: ALIGNAS LPAREN ( typeName RPAREN -> ^( ALIGNAS TYPE typeName ) | constantExpression RPAREN -> ^( ALIGNAS EXPR constantExpression ) )
			{
			ALIGNAS274=(Token)match(input,ALIGNAS,FOLLOW_ALIGNAS_in_alignmentSpecifier5379); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ALIGNAS.add(ALIGNAS274);

			LPAREN275=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_alignmentSpecifier5381); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN275);

			// CivlCParser.g:887:9: ( typeName RPAREN -> ^( ALIGNAS TYPE typeName ) | constantExpression RPAREN -> ^( ALIGNAS EXPR constantExpression ) )
			int alt56=2;
			switch ( input.LA(1) ) {
			case ATOMIC:
			case BOOL:
			case CHAR:
			case COMPLEX:
			case CONST:
			case DOMAIN:
			case DOUBLE:
			case ENUM:
			case FLOAT:
			case INPUT:
			case INT:
			case LONG:
			case OUTPUT:
			case RANGE:
			case REAL:
			case RESTRICT:
			case SHORT:
			case SIGNED:
			case STRUCT:
			case TYPEOF:
			case UNION:
			case UNSIGNED:
			case VOID:
			case VOLATILE:
				{
				alt56=1;
				}
				break;
			case IDENTIFIER:
				{
				int LA56_17 = input.LA(2);
				if ( ((!DeclarationScope_stack.peek().typedefNameUsed && isTypeName(input.LT(1).getText()))) ) {
					alt56=1;
				}
				else if ( (true) ) {
					alt56=2;
				}

				}
				break;
			case ALIGNOF:
			case AMPERSAND:
			case BIG_O:
			case CALLS:
			case CHARACTER_CONSTANT:
			case DERIV:
			case ELLIPSIS:
			case FALSE:
			case FLOATING_CONSTANT:
			case GENERIC:
			case HERE:
			case INTEGER_CONSTANT:
			case LPAREN:
			case MINUSMINUS:
			case NOT:
			case PLUS:
			case PLUSPLUS:
			case PROCNULL:
			case RESULT:
			case SCOPEOF:
			case SELF:
			case SIZEOF:
			case SPAWN:
			case STAR:
			case STRING_LITERAL:
			case SUB:
			case TILDE:
			case TRUE:
			case ROOT:
				{
				alt56=2;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 56, 0, input);
				throw nvae;
			}
			switch (alt56) {
				case 1 :
					// CivlCParser.g:887:11: typeName RPAREN
					{
					pushFollow(FOLLOW_typeName_in_alignmentSpecifier5394);
					typeName276=typeName();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeName.add(typeName276.getTree());
					RPAREN277=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_alignmentSpecifier5396); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN277);

					// AST REWRITE
					// elements: ALIGNAS, typeName
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 888:11: -> ^( ALIGNAS TYPE typeName )
					{
						// CivlCParser.g:888:14: ^( ALIGNAS TYPE typeName )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ALIGNAS.nextNode(), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(TYPE, "TYPE"));
						adaptor.addChild(root_1, stream_typeName.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:889:11: constantExpression RPAREN
					{
					pushFollow(FOLLOW_constantExpression_in_alignmentSpecifier5428);
					constantExpression278=constantExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_constantExpression.add(constantExpression278.getTree());
					RPAREN279=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_alignmentSpecifier5430); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN279);

					// AST REWRITE
					// elements: constantExpression, ALIGNAS
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 890:11: -> ^( ALIGNAS EXPR constantExpression )
					{
						// CivlCParser.g:890:14: ^( ALIGNAS EXPR constantExpression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ALIGNAS.nextNode(), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(EXPR, "EXPR"));
						adaptor.addChild(root_1, stream_constantExpression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "alignmentSpecifier"


	public static class declarator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "declarator"
	// CivlCParser.g:899:1: declarator : (d= directDeclarator -> ^( DECLARATOR ABSENT $d) | pointer d= directDeclarator -> ^( DECLARATOR pointer $d) );
	public final OmpParser_CivlCParser.declarator_return declarator() throws RecognitionException {
		OmpParser_CivlCParser.declarator_return retval = new OmpParser_CivlCParser.declarator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope d =null;
		ParserRuleReturnScope pointer280 =null;

		RewriteRuleSubtreeStream stream_directDeclarator=new RewriteRuleSubtreeStream(adaptor,"rule directDeclarator");
		RewriteRuleSubtreeStream stream_pointer=new RewriteRuleSubtreeStream(adaptor,"rule pointer");

		try {
			// CivlCParser.g:900:2: (d= directDeclarator -> ^( DECLARATOR ABSENT $d) | pointer d= directDeclarator -> ^( DECLARATOR pointer $d) )
			int alt57=2;
			int LA57_0 = input.LA(1);
			if ( (LA57_0==IDENTIFIER||LA57_0==LPAREN) ) {
				alt57=1;
			}
			else if ( (LA57_0==STAR) ) {
				alt57=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 57, 0, input);
				throw nvae;
			}

			switch (alt57) {
				case 1 :
					// CivlCParser.g:900:4: d= directDeclarator
					{
					pushFollow(FOLLOW_directDeclarator_in_declarator5479);
					d=directDeclarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_directDeclarator.add(d.getTree());
					// AST REWRITE
					// elements: d
					// token labels: 
					// rule labels: retval, d
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_d=new RewriteRuleSubtreeStream(adaptor,"rule d",d!=null?d.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 901:4: -> ^( DECLARATOR ABSENT $d)
					{
						// CivlCParser.g:901:7: ^( DECLARATOR ABSENT $d)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DECLARATOR, "DECLARATOR"), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_1, stream_d.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:902:4: pointer d= directDeclarator
					{
					pushFollow(FOLLOW_pointer_in_declarator5498);
					pointer280=pointer();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_pointer.add(pointer280.getTree());
					pushFollow(FOLLOW_directDeclarator_in_declarator5502);
					d=directDeclarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_directDeclarator.add(d.getTree());
					// AST REWRITE
					// elements: d, pointer
					// token labels: 
					// rule labels: retval, d
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_d=new RewriteRuleSubtreeStream(adaptor,"rule d",d!=null?d.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 903:4: -> ^( DECLARATOR pointer $d)
					{
						// CivlCParser.g:903:7: ^( DECLARATOR pointer $d)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DECLARATOR, "DECLARATOR"), root_1);
						adaptor.addChild(root_1, stream_pointer.nextTree());
						adaptor.addChild(root_1, stream_d.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "declarator"


	public static class directDeclarator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "directDeclarator"
	// CivlCParser.g:911:1: directDeclarator : p= directDeclaratorPrefix ( -> ^( DIRECT_DECLARATOR $p) | (s+= directDeclaratorSuffix )+ -> ^( DIRECT_DECLARATOR $p ( $s)+ ) ) ;
	public final OmpParser_CivlCParser.directDeclarator_return directDeclarator() throws RecognitionException {
		OmpParser_CivlCParser.directDeclarator_return retval = new OmpParser_CivlCParser.directDeclarator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		List<Object> list_s=null;
		ParserRuleReturnScope p =null;
		RuleReturnScope s = null;
		RewriteRuleSubtreeStream stream_directDeclaratorSuffix=new RewriteRuleSubtreeStream(adaptor,"rule directDeclaratorSuffix");
		RewriteRuleSubtreeStream stream_directDeclaratorPrefix=new RewriteRuleSubtreeStream(adaptor,"rule directDeclaratorPrefix");

		try {
			// CivlCParser.g:912:2: (p= directDeclaratorPrefix ( -> ^( DIRECT_DECLARATOR $p) | (s+= directDeclaratorSuffix )+ -> ^( DIRECT_DECLARATOR $p ( $s)+ ) ) )
			// CivlCParser.g:912:4: p= directDeclaratorPrefix ( -> ^( DIRECT_DECLARATOR $p) | (s+= directDeclaratorSuffix )+ -> ^( DIRECT_DECLARATOR $p ( $s)+ ) )
			{
			pushFollow(FOLLOW_directDeclaratorPrefix_in_directDeclarator5531);
			p=directDeclaratorPrefix();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_directDeclaratorPrefix.add(p.getTree());
			// CivlCParser.g:913:4: ( -> ^( DIRECT_DECLARATOR $p) | (s+= directDeclaratorSuffix )+ -> ^( DIRECT_DECLARATOR $p ( $s)+ ) )
			int alt59=2;
			int LA59_0 = input.LA(1);
			if ( (LA59_0==EOF||(LA59_0 >= ABSTRACT && LA59_0 <= ALIGNAS)||(LA59_0 >= ASSIGN && LA59_0 <= ASSIGNS)||(LA59_0 >= ATOMIC && LA59_0 <= AUTO)||LA59_0==BOOL||LA59_0==CHAR||(LA59_0 >= COLON && LA59_0 <= COMMA)||(LA59_0 >= COMPLEX && LA59_0 <= CONST)||LA59_0==DEPENDS||LA59_0==DEVICE||LA59_0==DOMAIN||LA59_0==DOUBLE||(LA59_0 >= ENSURES && LA59_0 <= ENUM)||LA59_0==EXTERN||(LA59_0 >= FATOMIC && LA59_0 <= FLOAT)||LA59_0==GLOBAL||LA59_0==GUARD||LA59_0==IDENTIFIER||(LA59_0 >= INLINE && LA59_0 <= INT)||LA59_0==LCURLY||LA59_0==LONG||LA59_0==NORETURN||LA59_0==OUTPUT||LA59_0==PURE||LA59_0==RANGE||(LA59_0 >= READS && LA59_0 <= RESTRICT)||LA59_0==RPAREN||(LA59_0 >= SEMI && LA59_0 <= SHARED)||(LA59_0 >= SHORT && LA59_0 <= SIGNED)||(LA59_0 >= STATIC && LA59_0 <= STATICASSERT)||LA59_0==STRUCT||(LA59_0 >= SYSTEM && LA59_0 <= THREADLOCAL)||(LA59_0 >= TYPEDEF && LA59_0 <= TYPEOF)||(LA59_0 >= UNION && LA59_0 <= UNSIGNED)||(LA59_0 >= VOID && LA59_0 <= VOLATILE)) ) {
				alt59=1;
			}
			else if ( (LA59_0==LPAREN||LA59_0==LSQUARE) ) {
				alt59=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 59, 0, input);
				throw nvae;
			}

			switch (alt59) {
				case 1 :
					// CivlCParser.g:913:6: 
					{
					// AST REWRITE
					// elements: p
					// token labels: 
					// rule labels: retval, p
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_p=new RewriteRuleSubtreeStream(adaptor,"rule p",p!=null?p.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 913:6: -> ^( DIRECT_DECLARATOR $p)
					{
						// CivlCParser.g:913:9: ^( DIRECT_DECLARATOR $p)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DIRECT_DECLARATOR, "DIRECT_DECLARATOR"), root_1);
						adaptor.addChild(root_1, stream_p.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:914:6: (s+= directDeclaratorSuffix )+
					{
					// CivlCParser.g:914:7: (s+= directDeclaratorSuffix )+
					int cnt58=0;
					loop58:
					while (true) {
						int alt58=2;
						int LA58_0 = input.LA(1);
						if ( (LA58_0==LPAREN||LA58_0==LSQUARE) ) {
							alt58=1;
						}

						switch (alt58) {
						case 1 :
							// CivlCParser.g:914:7: s+= directDeclaratorSuffix
							{
							pushFollow(FOLLOW_directDeclaratorSuffix_in_directDeclarator5554);
							s=directDeclaratorSuffix();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_directDeclaratorSuffix.add(s.getTree());
							if (list_s==null) list_s=new ArrayList<Object>();
							list_s.add(s.getTree());
							}
							break;

						default :
							if ( cnt58 >= 1 ) break loop58;
							if (state.backtracking>0) {state.failed=true; return retval;}
							EarlyExitException eee = new EarlyExitException(58, input);
							throw eee;
						}
						cnt58++;
					}

					// AST REWRITE
					// elements: p, s
					// token labels: 
					// rule labels: retval, p
					// token list labels: 
					// rule list labels: s
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_p=new RewriteRuleSubtreeStream(adaptor,"rule p",p!=null?p.getTree():null);
					RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"token s",list_s);
					root_0 = (Object)adaptor.nil();
					// 914:33: -> ^( DIRECT_DECLARATOR $p ( $s)+ )
					{
						// CivlCParser.g:914:35: ^( DIRECT_DECLARATOR $p ( $s)+ )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DIRECT_DECLARATOR, "DIRECT_DECLARATOR"), root_1);
						adaptor.addChild(root_1, stream_p.nextTree());
						if ( !(stream_s.hasNext()) ) {
							throw new RewriteEarlyExitException();
						}
						while ( stream_s.hasNext() ) {
							adaptor.addChild(root_1, stream_s.nextTree());
						}
						stream_s.reset();

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "directDeclarator"


	public static class directDeclaratorPrefix_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "directDeclaratorPrefix"
	// CivlCParser.g:921:1: directDeclaratorPrefix : ( IDENTIFIER | LPAREN ! declarator RPAREN !);
	public final OmpParser_CivlCParser.directDeclaratorPrefix_return directDeclaratorPrefix() throws RecognitionException {
		OmpParser_CivlCParser.directDeclaratorPrefix_return retval = new OmpParser_CivlCParser.directDeclaratorPrefix_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token IDENTIFIER281=null;
		Token LPAREN282=null;
		Token RPAREN284=null;
		ParserRuleReturnScope declarator283 =null;

		Object IDENTIFIER281_tree=null;
		Object LPAREN282_tree=null;
		Object RPAREN284_tree=null;

		try {
			// CivlCParser.g:922:2: ( IDENTIFIER | LPAREN ! declarator RPAREN !)
			int alt60=2;
			int LA60_0 = input.LA(1);
			if ( (LA60_0==IDENTIFIER) ) {
				alt60=1;
			}
			else if ( (LA60_0==LPAREN) ) {
				alt60=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 60, 0, input);
				throw nvae;
			}

			switch (alt60) {
				case 1 :
					// CivlCParser.g:922:4: IDENTIFIER
					{
					root_0 = (Object)adaptor.nil();


					IDENTIFIER281=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_directDeclaratorPrefix5585); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					IDENTIFIER281_tree = (Object)adaptor.create(IDENTIFIER281);
					adaptor.addChild(root_0, IDENTIFIER281_tree);
					}

					if ( state.backtracking==0 ) {
								if (DeclarationScope_stack.peek().isTypedef) {
									Symbols_stack.peek().types.add((IDENTIFIER281!=null?IDENTIFIER281.getText():null));
					                //System.err.println("define type "+(IDENTIFIER281!=null?IDENTIFIER281.getText():null));
								}else{
					                //Symbols_stack.peek().types.remove((IDENTIFIER281!=null?IDENTIFIER281.getText():null));
					            }
							}
					}
					break;
				case 2 :
					// CivlCParser.g:931:4: LPAREN ! declarator RPAREN !
					{
					root_0 = (Object)adaptor.nil();


					LPAREN282=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_directDeclaratorPrefix5595); if (state.failed) return retval;
					pushFollow(FOLLOW_declarator_in_directDeclaratorPrefix5598);
					declarator283=declarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, declarator283.getTree());

					RPAREN284=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_directDeclaratorPrefix5600); if (state.failed) return retval;
					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "directDeclaratorPrefix"


	public static class directDeclaratorSuffix_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "directDeclaratorSuffix"
	// CivlCParser.g:935:1: directDeclaratorSuffix : ( directDeclaratorArraySuffix | directDeclaratorFunctionSuffix );
	public final OmpParser_CivlCParser.directDeclaratorSuffix_return directDeclaratorSuffix() throws RecognitionException {
		OmpParser_CivlCParser.directDeclaratorSuffix_return retval = new OmpParser_CivlCParser.directDeclaratorSuffix_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope directDeclaratorArraySuffix285 =null;
		ParserRuleReturnScope directDeclaratorFunctionSuffix286 =null;


		try {
			// CivlCParser.g:936:2: ( directDeclaratorArraySuffix | directDeclaratorFunctionSuffix )
			int alt61=2;
			int LA61_0 = input.LA(1);
			if ( (LA61_0==LSQUARE) ) {
				alt61=1;
			}
			else if ( (LA61_0==LPAREN) ) {
				alt61=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 61, 0, input);
				throw nvae;
			}

			switch (alt61) {
				case 1 :
					// CivlCParser.g:936:4: directDeclaratorArraySuffix
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_directDeclaratorArraySuffix_in_directDeclaratorSuffix5613);
					directDeclaratorArraySuffix285=directDeclaratorArraySuffix();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, directDeclaratorArraySuffix285.getTree());

					}
					break;
				case 2 :
					// CivlCParser.g:937:4: directDeclaratorFunctionSuffix
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_directDeclaratorFunctionSuffix_in_directDeclaratorSuffix5618);
					directDeclaratorFunctionSuffix286=directDeclaratorFunctionSuffix();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, directDeclaratorFunctionSuffix286.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "directDeclaratorSuffix"


	public static class directDeclaratorArraySuffix_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "directDeclaratorArraySuffix"
	// CivlCParser.g:949:1: directDeclaratorArraySuffix : LSQUARE ( typeQualifierList_opt assignmentExpression_opt RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt assignmentExpression_opt RSQUARE ) | STATIC typeQualifierList_opt assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt assignmentExpression RSQUARE ) | typeQualifierList STATIC assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression RSQUARE ) | typeQualifierList_opt STAR RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt STAR RSQUARE ) ) ;
	public final OmpParser_CivlCParser.directDeclaratorArraySuffix_return directDeclaratorArraySuffix() throws RecognitionException {
		OmpParser_CivlCParser.directDeclaratorArraySuffix_return retval = new OmpParser_CivlCParser.directDeclaratorArraySuffix_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LSQUARE287=null;
		Token RSQUARE290=null;
		Token STATIC291=null;
		Token RSQUARE294=null;
		Token STATIC296=null;
		Token RSQUARE298=null;
		Token STAR300=null;
		Token RSQUARE301=null;
		ParserRuleReturnScope typeQualifierList_opt288 =null;
		ParserRuleReturnScope assignmentExpression_opt289 =null;
		ParserRuleReturnScope typeQualifierList_opt292 =null;
		ParserRuleReturnScope assignmentExpression293 =null;
		ParserRuleReturnScope typeQualifierList295 =null;
		ParserRuleReturnScope assignmentExpression297 =null;
		ParserRuleReturnScope typeQualifierList_opt299 =null;

		Object LSQUARE287_tree=null;
		Object RSQUARE290_tree=null;
		Object STATIC291_tree=null;
		Object RSQUARE294_tree=null;
		Object STATIC296_tree=null;
		Object RSQUARE298_tree=null;
		Object STAR300_tree=null;
		Object RSQUARE301_tree=null;
		RewriteRuleTokenStream stream_STAR=new RewriteRuleTokenStream(adaptor,"token STAR");
		RewriteRuleTokenStream stream_LSQUARE=new RewriteRuleTokenStream(adaptor,"token LSQUARE");
		RewriteRuleTokenStream stream_RSQUARE=new RewriteRuleTokenStream(adaptor,"token RSQUARE");
		RewriteRuleTokenStream stream_STATIC=new RewriteRuleTokenStream(adaptor,"token STATIC");
		RewriteRuleSubtreeStream stream_typeQualifierList=new RewriteRuleSubtreeStream(adaptor,"rule typeQualifierList");
		RewriteRuleSubtreeStream stream_assignmentExpression_opt=new RewriteRuleSubtreeStream(adaptor,"rule assignmentExpression_opt");
		RewriteRuleSubtreeStream stream_assignmentExpression=new RewriteRuleSubtreeStream(adaptor,"rule assignmentExpression");
		RewriteRuleSubtreeStream stream_typeQualifierList_opt=new RewriteRuleSubtreeStream(adaptor,"rule typeQualifierList_opt");

		try {
			// CivlCParser.g:950:2: ( LSQUARE ( typeQualifierList_opt assignmentExpression_opt RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt assignmentExpression_opt RSQUARE ) | STATIC typeQualifierList_opt assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt assignmentExpression RSQUARE ) | typeQualifierList STATIC assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression RSQUARE ) | typeQualifierList_opt STAR RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt STAR RSQUARE ) ) )
			// CivlCParser.g:950:4: LSQUARE ( typeQualifierList_opt assignmentExpression_opt RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt assignmentExpression_opt RSQUARE ) | STATIC typeQualifierList_opt assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt assignmentExpression RSQUARE ) | typeQualifierList STATIC assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression RSQUARE ) | typeQualifierList_opt STAR RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt STAR RSQUARE ) )
			{
			LSQUARE287=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_directDeclaratorArraySuffix5631); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LSQUARE.add(LSQUARE287);

			// CivlCParser.g:951:4: ( typeQualifierList_opt assignmentExpression_opt RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt assignmentExpression_opt RSQUARE ) | STATIC typeQualifierList_opt assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt assignmentExpression RSQUARE ) | typeQualifierList STATIC assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression RSQUARE ) | typeQualifierList_opt STAR RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt STAR RSQUARE ) )
			int alt62=4;
			alt62 = dfa62.predict(input);
			switch (alt62) {
				case 1 :
					// CivlCParser.g:951:6: typeQualifierList_opt assignmentExpression_opt RSQUARE
					{
					pushFollow(FOLLOW_typeQualifierList_opt_in_directDeclaratorArraySuffix5638);
					typeQualifierList_opt288=typeQualifierList_opt();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeQualifierList_opt.add(typeQualifierList_opt288.getTree());
					pushFollow(FOLLOW_assignmentExpression_opt_in_directDeclaratorArraySuffix5640);
					assignmentExpression_opt289=assignmentExpression_opt();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_assignmentExpression_opt.add(assignmentExpression_opt289.getTree());
					RSQUARE290=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_directDeclaratorArraySuffix5642); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE290);

					// AST REWRITE
					// elements: typeQualifierList_opt, LSQUARE, assignmentExpression_opt, RSQUARE
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 952:6: -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt assignmentExpression_opt RSQUARE )
					{
						// CivlCParser.g:952:9: ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt assignmentExpression_opt RSQUARE )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARRAY_SUFFIX, "ARRAY_SUFFIX"), root_1);
						adaptor.addChild(root_1, stream_LSQUARE.nextNode());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_1, stream_typeQualifierList_opt.nextTree());
						adaptor.addChild(root_1, stream_assignmentExpression_opt.nextTree());
						adaptor.addChild(root_1, stream_RSQUARE.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:954:6: STATIC typeQualifierList_opt assignmentExpression RSQUARE
					{
					STATIC291=(Token)match(input,STATIC,FOLLOW_STATIC_in_directDeclaratorArraySuffix5680); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_STATIC.add(STATIC291);

					pushFollow(FOLLOW_typeQualifierList_opt_in_directDeclaratorArraySuffix5682);
					typeQualifierList_opt292=typeQualifierList_opt();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeQualifierList_opt.add(typeQualifierList_opt292.getTree());
					pushFollow(FOLLOW_assignmentExpression_in_directDeclaratorArraySuffix5684);
					assignmentExpression293=assignmentExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression293.getTree());
					RSQUARE294=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_directDeclaratorArraySuffix5686); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE294);

					// AST REWRITE
					// elements: LSQUARE, RSQUARE, typeQualifierList_opt, STATIC, assignmentExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 955:6: -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt assignmentExpression RSQUARE )
					{
						// CivlCParser.g:955:9: ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt assignmentExpression RSQUARE )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARRAY_SUFFIX, "ARRAY_SUFFIX"), root_1);
						adaptor.addChild(root_1, stream_LSQUARE.nextNode());
						adaptor.addChild(root_1, stream_STATIC.nextNode());
						adaptor.addChild(root_1, stream_typeQualifierList_opt.nextTree());
						adaptor.addChild(root_1, stream_assignmentExpression.nextTree());
						adaptor.addChild(root_1, stream_RSQUARE.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// CivlCParser.g:957:8: typeQualifierList STATIC assignmentExpression RSQUARE
					{
					pushFollow(FOLLOW_typeQualifierList_in_directDeclaratorArraySuffix5726);
					typeQualifierList295=typeQualifierList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeQualifierList.add(typeQualifierList295.getTree());
					STATIC296=(Token)match(input,STATIC,FOLLOW_STATIC_in_directDeclaratorArraySuffix5728); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_STATIC.add(STATIC296);

					pushFollow(FOLLOW_assignmentExpression_in_directDeclaratorArraySuffix5730);
					assignmentExpression297=assignmentExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression297.getTree());
					RSQUARE298=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_directDeclaratorArraySuffix5732); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE298);

					// AST REWRITE
					// elements: LSQUARE, assignmentExpression, RSQUARE, typeQualifierList, STATIC
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 958:6: -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression RSQUARE )
					{
						// CivlCParser.g:958:9: ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression RSQUARE )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARRAY_SUFFIX, "ARRAY_SUFFIX"), root_1);
						adaptor.addChild(root_1, stream_LSQUARE.nextNode());
						adaptor.addChild(root_1, stream_STATIC.nextNode());
						adaptor.addChild(root_1, stream_typeQualifierList.nextTree());
						adaptor.addChild(root_1, stream_assignmentExpression.nextTree());
						adaptor.addChild(root_1, stream_RSQUARE.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// CivlCParser.g:960:8: typeQualifierList_opt STAR RSQUARE
					{
					pushFollow(FOLLOW_typeQualifierList_opt_in_directDeclaratorArraySuffix5772);
					typeQualifierList_opt299=typeQualifierList_opt();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeQualifierList_opt.add(typeQualifierList_opt299.getTree());
					STAR300=(Token)match(input,STAR,FOLLOW_STAR_in_directDeclaratorArraySuffix5774); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_STAR.add(STAR300);

					RSQUARE301=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_directDeclaratorArraySuffix5776); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE301);

					// AST REWRITE
					// elements: RSQUARE, STAR, LSQUARE, typeQualifierList_opt
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 961:6: -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt STAR RSQUARE )
					{
						// CivlCParser.g:961:9: ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt STAR RSQUARE )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARRAY_SUFFIX, "ARRAY_SUFFIX"), root_1);
						adaptor.addChild(root_1, stream_LSQUARE.nextNode());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_1, stream_typeQualifierList_opt.nextTree());
						adaptor.addChild(root_1, stream_STAR.nextNode());
						adaptor.addChild(root_1, stream_RSQUARE.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "directDeclaratorArraySuffix"


	public static class directDeclaratorFunctionSuffix_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "directDeclaratorFunctionSuffix"
	// CivlCParser.g:972:1: directDeclaratorFunctionSuffix : LPAREN ( parameterTypeList RPAREN -> ^( FUNCTION_SUFFIX LPAREN parameterTypeList RPAREN ) | identifierList RPAREN -> ^( FUNCTION_SUFFIX LPAREN identifierList RPAREN ) | RPAREN -> ^( FUNCTION_SUFFIX LPAREN ABSENT RPAREN ) ) ;
	public final OmpParser_CivlCParser.directDeclaratorFunctionSuffix_return directDeclaratorFunctionSuffix() throws RecognitionException {
		DeclarationScope_stack.push(new DeclarationScope_scope());

		OmpParser_CivlCParser.directDeclaratorFunctionSuffix_return retval = new OmpParser_CivlCParser.directDeclaratorFunctionSuffix_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LPAREN302=null;
		Token RPAREN304=null;
		Token RPAREN306=null;
		Token RPAREN307=null;
		ParserRuleReturnScope parameterTypeList303 =null;
		ParserRuleReturnScope identifierList305 =null;

		Object LPAREN302_tree=null;
		Object RPAREN304_tree=null;
		Object RPAREN306_tree=null;
		Object RPAREN307_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_identifierList=new RewriteRuleSubtreeStream(adaptor,"rule identifierList");
		RewriteRuleSubtreeStream stream_parameterTypeList=new RewriteRuleSubtreeStream(adaptor,"rule parameterTypeList");


		    DeclarationScope_stack.peek().isTypedef = false;
		    DeclarationScope_stack.peek().typedefNameUsed = false;

		try {
			// CivlCParser.g:978:2: ( LPAREN ( parameterTypeList RPAREN -> ^( FUNCTION_SUFFIX LPAREN parameterTypeList RPAREN ) | identifierList RPAREN -> ^( FUNCTION_SUFFIX LPAREN identifierList RPAREN ) | RPAREN -> ^( FUNCTION_SUFFIX LPAREN ABSENT RPAREN ) ) )
			// CivlCParser.g:978:4: LPAREN ( parameterTypeList RPAREN -> ^( FUNCTION_SUFFIX LPAREN parameterTypeList RPAREN ) | identifierList RPAREN -> ^( FUNCTION_SUFFIX LPAREN identifierList RPAREN ) | RPAREN -> ^( FUNCTION_SUFFIX LPAREN ABSENT RPAREN ) )
			{
			LPAREN302=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_directDeclaratorFunctionSuffix5835); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN302);

			// CivlCParser.g:979:4: ( parameterTypeList RPAREN -> ^( FUNCTION_SUFFIX LPAREN parameterTypeList RPAREN ) | identifierList RPAREN -> ^( FUNCTION_SUFFIX LPAREN identifierList RPAREN ) | RPAREN -> ^( FUNCTION_SUFFIX LPAREN ABSENT RPAREN ) )
			int alt63=3;
			alt63 = dfa63.predict(input);
			switch (alt63) {
				case 1 :
					// CivlCParser.g:979:6: parameterTypeList RPAREN
					{
					pushFollow(FOLLOW_parameterTypeList_in_directDeclaratorFunctionSuffix5842);
					parameterTypeList303=parameterTypeList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_parameterTypeList.add(parameterTypeList303.getTree());
					RPAREN304=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_directDeclaratorFunctionSuffix5844); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN304);

					// AST REWRITE
					// elements: LPAREN, parameterTypeList, RPAREN
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 980:6: -> ^( FUNCTION_SUFFIX LPAREN parameterTypeList RPAREN )
					{
						// CivlCParser.g:980:9: ^( FUNCTION_SUFFIX LPAREN parameterTypeList RPAREN )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FUNCTION_SUFFIX, "FUNCTION_SUFFIX"), root_1);
						adaptor.addChild(root_1, stream_LPAREN.nextNode());
						adaptor.addChild(root_1, stream_parameterTypeList.nextTree());
						adaptor.addChild(root_1, stream_RPAREN.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:981:6: identifierList RPAREN
					{
					pushFollow(FOLLOW_identifierList_in_directDeclaratorFunctionSuffix5870);
					identifierList305=identifierList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_identifierList.add(identifierList305.getTree());
					RPAREN306=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_directDeclaratorFunctionSuffix5872); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN306);

					// AST REWRITE
					// elements: RPAREN, LPAREN, identifierList
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 982:6: -> ^( FUNCTION_SUFFIX LPAREN identifierList RPAREN )
					{
						// CivlCParser.g:982:9: ^( FUNCTION_SUFFIX LPAREN identifierList RPAREN )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FUNCTION_SUFFIX, "FUNCTION_SUFFIX"), root_1);
						adaptor.addChild(root_1, stream_LPAREN.nextNode());
						adaptor.addChild(root_1, stream_identifierList.nextTree());
						adaptor.addChild(root_1, stream_RPAREN.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// CivlCParser.g:983:6: RPAREN
					{
					RPAREN307=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_directDeclaratorFunctionSuffix5896); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN307);

					// AST REWRITE
					// elements: LPAREN, RPAREN
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 983:13: -> ^( FUNCTION_SUFFIX LPAREN ABSENT RPAREN )
					{
						// CivlCParser.g:983:16: ^( FUNCTION_SUFFIX LPAREN ABSENT RPAREN )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FUNCTION_SUFFIX, "FUNCTION_SUFFIX"), root_1);
						adaptor.addChild(root_1, stream_LPAREN.nextNode());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_1, stream_RPAREN.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
			DeclarationScope_stack.pop();

		}
		return retval;
	}
	// $ANTLR end "directDeclaratorFunctionSuffix"


	public static class typeQualifierList_opt_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "typeQualifierList_opt"
	// CivlCParser.g:991:1: typeQualifierList_opt : ( typeQualifier )* -> ^( TYPE_QUALIFIER_LIST ( typeQualifier )* ) ;
	public final OmpParser_CivlCParser.typeQualifierList_opt_return typeQualifierList_opt() throws RecognitionException {
		OmpParser_CivlCParser.typeQualifierList_opt_return retval = new OmpParser_CivlCParser.typeQualifierList_opt_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope typeQualifier308 =null;

		RewriteRuleSubtreeStream stream_typeQualifier=new RewriteRuleSubtreeStream(adaptor,"rule typeQualifier");

		try {
			// CivlCParser.g:992:2: ( ( typeQualifier )* -> ^( TYPE_QUALIFIER_LIST ( typeQualifier )* ) )
			// CivlCParser.g:992:4: ( typeQualifier )*
			{
			// CivlCParser.g:992:4: ( typeQualifier )*
			loop64:
			while (true) {
				int alt64=2;
				int LA64_0 = input.LA(1);
				if ( (LA64_0==ATOMIC||LA64_0==CONST||LA64_0==INPUT||LA64_0==OUTPUT||LA64_0==RESTRICT||LA64_0==VOLATILE) ) {
					alt64=1;
				}

				switch (alt64) {
				case 1 :
					// CivlCParser.g:992:4: typeQualifier
					{
					pushFollow(FOLLOW_typeQualifier_in_typeQualifierList_opt5926);
					typeQualifier308=typeQualifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeQualifier.add(typeQualifier308.getTree());
					}
					break;

				default :
					break loop64;
				}
			}

			// AST REWRITE
			// elements: typeQualifier
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 992:19: -> ^( TYPE_QUALIFIER_LIST ( typeQualifier )* )
			{
				// CivlCParser.g:992:22: ^( TYPE_QUALIFIER_LIST ( typeQualifier )* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TYPE_QUALIFIER_LIST, "TYPE_QUALIFIER_LIST"), root_1);
				// CivlCParser.g:992:44: ( typeQualifier )*
				while ( stream_typeQualifier.hasNext() ) {
					adaptor.addChild(root_1, stream_typeQualifier.nextTree());
				}
				stream_typeQualifier.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "typeQualifierList_opt"


	public static class assignmentExpression_opt_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "assignmentExpression_opt"
	// CivlCParser.g:998:1: assignmentExpression_opt : ( -> ABSENT | assignmentExpression );
	public final OmpParser_CivlCParser.assignmentExpression_opt_return assignmentExpression_opt() throws RecognitionException {
		OmpParser_CivlCParser.assignmentExpression_opt_return retval = new OmpParser_CivlCParser.assignmentExpression_opt_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope assignmentExpression309 =null;


		try {
			// CivlCParser.g:999:2: ( -> ABSENT | assignmentExpression )
			int alt65=2;
			int LA65_0 = input.LA(1);
			if ( (LA65_0==RSQUARE) ) {
				alt65=1;
			}
			else if ( ((LA65_0 >= ALIGNOF && LA65_0 <= AMPERSAND)||LA65_0==BIG_O||LA65_0==CALLS||LA65_0==CHARACTER_CONSTANT||LA65_0==DERIV||LA65_0==ELLIPSIS||LA65_0==EXISTS||LA65_0==FALSE||LA65_0==FLOATING_CONSTANT||LA65_0==FORALL||LA65_0==GENERIC||LA65_0==HERE||LA65_0==IDENTIFIER||LA65_0==INTEGER_CONSTANT||LA65_0==LPAREN||LA65_0==MINUSMINUS||LA65_0==NOT||LA65_0==PLUS||LA65_0==PLUSPLUS||LA65_0==PROCNULL||LA65_0==RESULT||LA65_0==SCOPEOF||LA65_0==SELF||(LA65_0 >= SIZEOF && LA65_0 <= STAR)||LA65_0==STRING_LITERAL||LA65_0==SUB||(LA65_0 >= TILDE && LA65_0 <= TRUE)||LA65_0==UNIFORM||LA65_0==ROOT) ) {
				alt65=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 65, 0, input);
				throw nvae;
			}

			switch (alt65) {
				case 1 :
					// CivlCParser.g:999:5: 
					{
					// AST REWRITE
					// elements: 
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 999:5: -> ABSENT
					{
						adaptor.addChild(root_0, (Object)adaptor.create(ABSENT, "ABSENT"));
					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1000:4: assignmentExpression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_assignmentExpression_in_assignmentExpression_opt5957);
					assignmentExpression309=assignmentExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, assignmentExpression309.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "assignmentExpression_opt"


	public static class pointer_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "pointer"
	// CivlCParser.g:1007:1: pointer : ( pointer_part )+ -> ^( POINTER ( pointer_part )+ ) ;
	public final OmpParser_CivlCParser.pointer_return pointer() throws RecognitionException {
		OmpParser_CivlCParser.pointer_return retval = new OmpParser_CivlCParser.pointer_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope pointer_part310 =null;

		RewriteRuleSubtreeStream stream_pointer_part=new RewriteRuleSubtreeStream(adaptor,"rule pointer_part");

		try {
			// CivlCParser.g:1008:5: ( ( pointer_part )+ -> ^( POINTER ( pointer_part )+ ) )
			// CivlCParser.g:1008:7: ( pointer_part )+
			{
			// CivlCParser.g:1008:7: ( pointer_part )+
			int cnt66=0;
			loop66:
			while (true) {
				int alt66=2;
				int LA66_0 = input.LA(1);
				if ( (LA66_0==STAR) ) {
					alt66=1;
				}

				switch (alt66) {
				case 1 :
					// CivlCParser.g:1008:7: pointer_part
					{
					pushFollow(FOLLOW_pointer_part_in_pointer5973);
					pointer_part310=pointer_part();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_pointer_part.add(pointer_part310.getTree());
					}
					break;

				default :
					if ( cnt66 >= 1 ) break loop66;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(66, input);
					throw eee;
				}
				cnt66++;
			}

			// AST REWRITE
			// elements: pointer_part
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1008:21: -> ^( POINTER ( pointer_part )+ )
			{
				// CivlCParser.g:1008:24: ^( POINTER ( pointer_part )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(POINTER, "POINTER"), root_1);
				if ( !(stream_pointer_part.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_pointer_part.hasNext() ) {
					adaptor.addChild(root_1, stream_pointer_part.nextTree());
				}
				stream_pointer_part.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "pointer"


	public static class pointer_part_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "pointer_part"
	// CivlCParser.g:1015:1: pointer_part : STAR typeQualifierList_opt -> ^( STAR typeQualifierList_opt ) ;
	public final OmpParser_CivlCParser.pointer_part_return pointer_part() throws RecognitionException {
		OmpParser_CivlCParser.pointer_part_return retval = new OmpParser_CivlCParser.pointer_part_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token STAR311=null;
		ParserRuleReturnScope typeQualifierList_opt312 =null;

		Object STAR311_tree=null;
		RewriteRuleTokenStream stream_STAR=new RewriteRuleTokenStream(adaptor,"token STAR");
		RewriteRuleSubtreeStream stream_typeQualifierList_opt=new RewriteRuleSubtreeStream(adaptor,"rule typeQualifierList_opt");

		try {
			// CivlCParser.g:1016:2: ( STAR typeQualifierList_opt -> ^( STAR typeQualifierList_opt ) )
			// CivlCParser.g:1016:4: STAR typeQualifierList_opt
			{
			STAR311=(Token)match(input,STAR,FOLLOW_STAR_in_pointer_part5999); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_STAR.add(STAR311);

			pushFollow(FOLLOW_typeQualifierList_opt_in_pointer_part6001);
			typeQualifierList_opt312=typeQualifierList_opt();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_typeQualifierList_opt.add(typeQualifierList_opt312.getTree());
			// AST REWRITE
			// elements: STAR, typeQualifierList_opt
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1017:2: -> ^( STAR typeQualifierList_opt )
			{
				// CivlCParser.g:1017:5: ^( STAR typeQualifierList_opt )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_STAR.nextNode(), root_1);
				adaptor.addChild(root_1, stream_typeQualifierList_opt.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "pointer_part"


	public static class typeQualifierList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "typeQualifierList"
	// CivlCParser.g:1024:1: typeQualifierList : ( typeQualifier )+ -> ^( TYPE_QUALIFIER_LIST ( typeQualifier )+ ) ;
	public final OmpParser_CivlCParser.typeQualifierList_return typeQualifierList() throws RecognitionException {
		OmpParser_CivlCParser.typeQualifierList_return retval = new OmpParser_CivlCParser.typeQualifierList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope typeQualifier313 =null;

		RewriteRuleSubtreeStream stream_typeQualifier=new RewriteRuleSubtreeStream(adaptor,"rule typeQualifier");

		try {
			// CivlCParser.g:1025:5: ( ( typeQualifier )+ -> ^( TYPE_QUALIFIER_LIST ( typeQualifier )+ ) )
			// CivlCParser.g:1025:7: ( typeQualifier )+
			{
			// CivlCParser.g:1025:7: ( typeQualifier )+
			int cnt67=0;
			loop67:
			while (true) {
				int alt67=2;
				int LA67_0 = input.LA(1);
				if ( (LA67_0==ATOMIC||LA67_0==CONST||LA67_0==INPUT||LA67_0==OUTPUT||LA67_0==RESTRICT||LA67_0==VOLATILE) ) {
					alt67=1;
				}

				switch (alt67) {
				case 1 :
					// CivlCParser.g:1025:7: typeQualifier
					{
					pushFollow(FOLLOW_typeQualifier_in_typeQualifierList6026);
					typeQualifier313=typeQualifier();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeQualifier.add(typeQualifier313.getTree());
					}
					break;

				default :
					if ( cnt67 >= 1 ) break loop67;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(67, input);
					throw eee;
				}
				cnt67++;
			}

			// AST REWRITE
			// elements: typeQualifier
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1025:22: -> ^( TYPE_QUALIFIER_LIST ( typeQualifier )+ )
			{
				// CivlCParser.g:1025:25: ^( TYPE_QUALIFIER_LIST ( typeQualifier )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TYPE_QUALIFIER_LIST, "TYPE_QUALIFIER_LIST"), root_1);
				if ( !(stream_typeQualifier.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_typeQualifier.hasNext() ) {
					adaptor.addChild(root_1, stream_typeQualifier.nextTree());
				}
				stream_typeQualifier.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "typeQualifierList"


	public static class parameterTypeList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "parameterTypeList"
	// CivlCParser.g:1039:1: parameterTypeList : ({...}? parameterTypeListWithoutScope | parameterTypeListWithScope );
	public final OmpParser_CivlCParser.parameterTypeList_return parameterTypeList() throws RecognitionException {
		OmpParser_CivlCParser.parameterTypeList_return retval = new OmpParser_CivlCParser.parameterTypeList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope parameterTypeListWithoutScope314 =null;
		ParserRuleReturnScope parameterTypeListWithScope315 =null;


		try {
			// CivlCParser.g:1040:2: ({...}? parameterTypeListWithoutScope | parameterTypeListWithScope )
			int alt68=2;
			switch ( input.LA(1) ) {
			case TYPEDEF:
				{
				int LA68_1 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case AUTO:
			case EXTERN:
			case REGISTER:
			case SHARED:
			case STATIC:
			case THREADLOCAL:
				{
				int LA68_2 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 2, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case VOID:
				{
				int LA68_3 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case CHAR:
				{
				int LA68_4 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 4, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case SHORT:
				{
				int LA68_5 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 5, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case INT:
				{
				int LA68_6 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 6, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case LONG:
				{
				int LA68_7 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 7, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case FLOAT:
				{
				int LA68_8 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 8, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case DOUBLE:
				{
				int LA68_9 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 9, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case SIGNED:
				{
				int LA68_10 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 10, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case UNSIGNED:
				{
				int LA68_11 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 11, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case BOOL:
				{
				int LA68_12 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 12, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case COMPLEX:
				{
				int LA68_13 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 13, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case REAL:
				{
				int LA68_14 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 14, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case RANGE:
				{
				int LA68_15 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 15, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case ATOMIC:
				{
				int LA68_16 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 16, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case STRUCT:
			case UNION:
				{
				int LA68_17 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 17, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case ENUM:
				{
				int LA68_18 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 18, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case IDENTIFIER:
				{
				int LA68_19 = input.LA(2);
				if ( ((((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))&&(!DeclarationScope_stack.peek().typedefNameUsed && isTypeName(input.LT(1).getText())))) ) {
					alt68=1;
				}
				else if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(!DeclarationScope_stack.peek().typedefNameUsed && isTypeName(input.LT(1).getText())))) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 19, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case DOMAIN:
				{
				int LA68_20 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 20, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case TYPEOF:
				{
				int LA68_21 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 21, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case CONST:
			case INPUT:
			case OUTPUT:
			case RESTRICT:
			case VOLATILE:
				{
				int LA68_22 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 22, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case INLINE:
				{
				int LA68_23 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 23, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case NORETURN:
				{
				int LA68_24 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 24, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case ABSTRACT:
				{
				int LA68_25 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 25, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case SYSTEM:
				{
				int LA68_26 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 26, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case FATOMIC:
				{
				int LA68_27 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 27, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case PURE:
				{
				int LA68_28 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 28, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case DEVICE:
				{
				int LA68_29 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 29, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case GLOBAL:
				{
				int LA68_30 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 30, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case ALIGNAS:
				{
				int LA68_31 = input.LA(2);
				if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(Symbols_stack.peek().isFunctionDefinition))) ) {
					alt68=1;
				}
				else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {
					alt68=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 68, 31, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 68, 0, input);
				throw nvae;
			}
			switch (alt68) {
				case 1 :
					// CivlCParser.g:1040:4: {...}? parameterTypeListWithoutScope
					{
					root_0 = (Object)adaptor.nil();


					if ( !((Symbols_stack.peek().isFunctionDefinition)) ) {
						if (state.backtracking>0) {state.failed=true; return retval;}
						throw new FailedPredicateException(input, "parameterTypeList", "$Symbols::isFunctionDefinition");
					}
					pushFollow(FOLLOW_parameterTypeListWithoutScope_in_parameterTypeList6056);
					parameterTypeListWithoutScope314=parameterTypeListWithoutScope();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, parameterTypeListWithoutScope314.getTree());

					}
					break;
				case 2 :
					// CivlCParser.g:1041:4: parameterTypeListWithScope
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_parameterTypeListWithScope_in_parameterTypeList6061);
					parameterTypeListWithScope315=parameterTypeListWithScope();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, parameterTypeListWithScope315.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "parameterTypeList"


	public static class parameterTypeListWithScope_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "parameterTypeListWithScope"
	// CivlCParser.g:1044:1: parameterTypeListWithScope : parameterTypeListWithoutScope ;
	public final OmpParser_CivlCParser.parameterTypeListWithScope_return parameterTypeListWithScope() throws RecognitionException {
		Symbols_stack.push(new Symbols_scope());

		OmpParser_CivlCParser.parameterTypeListWithScope_return retval = new OmpParser_CivlCParser.parameterTypeListWithScope_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope parameterTypeListWithoutScope316 =null;



			Symbols_stack.peek().types = new HashSet<String>();
			Symbols_stack.peek().enumerationConstants = new HashSet<String>();
			Symbols_stack.peek().isFunctionDefinition = false;

		try {
			// CivlCParser.g:1051:2: ( parameterTypeListWithoutScope )
			// CivlCParser.g:1051:4: parameterTypeListWithoutScope
			{
			root_0 = (Object)adaptor.nil();


			pushFollow(FOLLOW_parameterTypeListWithoutScope_in_parameterTypeListWithScope6082);
			parameterTypeListWithoutScope316=parameterTypeListWithoutScope();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, parameterTypeListWithoutScope316.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
			Symbols_stack.pop();

		}
		return retval;
	}
	// $ANTLR end "parameterTypeListWithScope"


	public static class parameterTypeListWithoutScope_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "parameterTypeListWithoutScope"
	// CivlCParser.g:1054:1: parameterTypeListWithoutScope : parameterList ( -> ^( PARAMETER_TYPE_LIST parameterList ABSENT ) | COMMA ELLIPSIS -> ^( PARAMETER_TYPE_LIST parameterList ELLIPSIS ) ) ;
	public final OmpParser_CivlCParser.parameterTypeListWithoutScope_return parameterTypeListWithoutScope() throws RecognitionException {
		OmpParser_CivlCParser.parameterTypeListWithoutScope_return retval = new OmpParser_CivlCParser.parameterTypeListWithoutScope_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMMA318=null;
		Token ELLIPSIS319=null;
		ParserRuleReturnScope parameterList317 =null;

		Object COMMA318_tree=null;
		Object ELLIPSIS319_tree=null;
		RewriteRuleTokenStream stream_ELLIPSIS=new RewriteRuleTokenStream(adaptor,"token ELLIPSIS");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_parameterList=new RewriteRuleSubtreeStream(adaptor,"rule parameterList");

		try {
			// CivlCParser.g:1055:5: ( parameterList ( -> ^( PARAMETER_TYPE_LIST parameterList ABSENT ) | COMMA ELLIPSIS -> ^( PARAMETER_TYPE_LIST parameterList ELLIPSIS ) ) )
			// CivlCParser.g:1055:7: parameterList ( -> ^( PARAMETER_TYPE_LIST parameterList ABSENT ) | COMMA ELLIPSIS -> ^( PARAMETER_TYPE_LIST parameterList ELLIPSIS ) )
			{
			pushFollow(FOLLOW_parameterList_in_parameterTypeListWithoutScope6096);
			parameterList317=parameterList();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_parameterList.add(parameterList317.getTree());
			// CivlCParser.g:1056:7: ( -> ^( PARAMETER_TYPE_LIST parameterList ABSENT ) | COMMA ELLIPSIS -> ^( PARAMETER_TYPE_LIST parameterList ELLIPSIS ) )
			int alt69=2;
			int LA69_0 = input.LA(1);
			if ( (LA69_0==RPAREN) ) {
				alt69=1;
			}
			else if ( (LA69_0==COMMA) ) {
				alt69=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 69, 0, input);
				throw nvae;
			}

			switch (alt69) {
				case 1 :
					// CivlCParser.g:1056:9: 
					{
					// AST REWRITE
					// elements: parameterList
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1056:9: -> ^( PARAMETER_TYPE_LIST parameterList ABSENT )
					{
						// CivlCParser.g:1056:12: ^( PARAMETER_TYPE_LIST parameterList ABSENT )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(PARAMETER_TYPE_LIST, "PARAMETER_TYPE_LIST"), root_1);
						adaptor.addChild(root_1, stream_parameterList.nextTree());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1057:9: COMMA ELLIPSIS
					{
					COMMA318=(Token)match(input,COMMA,FOLLOW_COMMA_in_parameterTypeListWithoutScope6124); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA318);

					ELLIPSIS319=(Token)match(input,ELLIPSIS,FOLLOW_ELLIPSIS_in_parameterTypeListWithoutScope6126); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ELLIPSIS.add(ELLIPSIS319);

					// AST REWRITE
					// elements: ELLIPSIS, parameterList
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1058:9: -> ^( PARAMETER_TYPE_LIST parameterList ELLIPSIS )
					{
						// CivlCParser.g:1058:12: ^( PARAMETER_TYPE_LIST parameterList ELLIPSIS )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(PARAMETER_TYPE_LIST, "PARAMETER_TYPE_LIST"), root_1);
						adaptor.addChild(root_1, stream_parameterList.nextTree());
						adaptor.addChild(root_1, stream_ELLIPSIS.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "parameterTypeListWithoutScope"


	public static class parameterList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "parameterList"
	// CivlCParser.g:1066:1: parameterList : parameterDeclaration ( COMMA parameterDeclaration )* -> ^( PARAMETER_LIST ( parameterDeclaration )+ ) ;
	public final OmpParser_CivlCParser.parameterList_return parameterList() throws RecognitionException {
		OmpParser_CivlCParser.parameterList_return retval = new OmpParser_CivlCParser.parameterList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMMA321=null;
		ParserRuleReturnScope parameterDeclaration320 =null;
		ParserRuleReturnScope parameterDeclaration322 =null;

		Object COMMA321_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_parameterDeclaration=new RewriteRuleSubtreeStream(adaptor,"rule parameterDeclaration");

		try {
			// CivlCParser.g:1067:5: ( parameterDeclaration ( COMMA parameterDeclaration )* -> ^( PARAMETER_LIST ( parameterDeclaration )+ ) )
			// CivlCParser.g:1067:7: parameterDeclaration ( COMMA parameterDeclaration )*
			{
			pushFollow(FOLLOW_parameterDeclaration_in_parameterList6171);
			parameterDeclaration320=parameterDeclaration();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_parameterDeclaration.add(parameterDeclaration320.getTree());
			// CivlCParser.g:1067:28: ( COMMA parameterDeclaration )*
			loop70:
			while (true) {
				int alt70=2;
				int LA70_0 = input.LA(1);
				if ( (LA70_0==COMMA) ) {
					int LA70_2 = input.LA(2);
					if ( ((LA70_2 >= ABSTRACT && LA70_2 <= ALIGNAS)||(LA70_2 >= ATOMIC && LA70_2 <= AUTO)||LA70_2==BOOL||LA70_2==CHAR||(LA70_2 >= COMPLEX && LA70_2 <= CONST)||LA70_2==DEVICE||LA70_2==DOMAIN||LA70_2==DOUBLE||LA70_2==ENUM||LA70_2==EXTERN||(LA70_2 >= FATOMIC && LA70_2 <= FLOAT)||LA70_2==GLOBAL||LA70_2==IDENTIFIER||(LA70_2 >= INLINE && LA70_2 <= INT)||LA70_2==LONG||LA70_2==NORETURN||LA70_2==OUTPUT||LA70_2==PURE||LA70_2==RANGE||(LA70_2 >= REAL && LA70_2 <= REGISTER)||LA70_2==RESTRICT||LA70_2==SHARED||(LA70_2 >= SHORT && LA70_2 <= SIGNED)||LA70_2==STATIC||LA70_2==STRUCT||(LA70_2 >= SYSTEM && LA70_2 <= THREADLOCAL)||(LA70_2 >= TYPEDEF && LA70_2 <= TYPEOF)||(LA70_2 >= UNION && LA70_2 <= UNSIGNED)||(LA70_2 >= VOID && LA70_2 <= VOLATILE)) ) {
						alt70=1;
					}

				}

				switch (alt70) {
				case 1 :
					// CivlCParser.g:1067:29: COMMA parameterDeclaration
					{
					COMMA321=(Token)match(input,COMMA,FOLLOW_COMMA_in_parameterList6174); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA321);

					pushFollow(FOLLOW_parameterDeclaration_in_parameterList6176);
					parameterDeclaration322=parameterDeclaration();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_parameterDeclaration.add(parameterDeclaration322.getTree());
					}
					break;

				default :
					break loop70;
				}
			}

			// AST REWRITE
			// elements: parameterDeclaration
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1068:7: -> ^( PARAMETER_LIST ( parameterDeclaration )+ )
			{
				// CivlCParser.g:1068:10: ^( PARAMETER_LIST ( parameterDeclaration )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(PARAMETER_LIST, "PARAMETER_LIST"), root_1);
				if ( !(stream_parameterDeclaration.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_parameterDeclaration.hasNext() ) {
					adaptor.addChild(root_1, stream_parameterDeclaration.nextTree());
				}
				stream_parameterDeclaration.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "parameterList"


	public static class parameterDeclaration_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "parameterDeclaration"
	// CivlCParser.g:1076:1: parameterDeclaration : declarationSpecifiers ( -> ^( PARAMETER_DECLARATION declarationSpecifiers ABSENT ) | declaratorOrAbstractDeclarator -> ^( PARAMETER_DECLARATION declarationSpecifiers declaratorOrAbstractDeclarator ) ) ;
	public final OmpParser_CivlCParser.parameterDeclaration_return parameterDeclaration() throws RecognitionException {
		DeclarationScope_stack.push(new DeclarationScope_scope());

		OmpParser_CivlCParser.parameterDeclaration_return retval = new OmpParser_CivlCParser.parameterDeclaration_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope declarationSpecifiers323 =null;
		ParserRuleReturnScope declaratorOrAbstractDeclarator324 =null;

		RewriteRuleSubtreeStream stream_declaratorOrAbstractDeclarator=new RewriteRuleSubtreeStream(adaptor,"rule declaratorOrAbstractDeclarator");
		RewriteRuleSubtreeStream stream_declarationSpecifiers=new RewriteRuleSubtreeStream(adaptor,"rule declarationSpecifiers");


		    DeclarationScope_stack.peek().isTypedef = false;
		    DeclarationScope_stack.peek().typedefNameUsed = false;
		    //System.err.println("parameter declaration start");

		try {
			// CivlCParser.g:1083:5: ( declarationSpecifiers ( -> ^( PARAMETER_DECLARATION declarationSpecifiers ABSENT ) | declaratorOrAbstractDeclarator -> ^( PARAMETER_DECLARATION declarationSpecifiers declaratorOrAbstractDeclarator ) ) )
			// CivlCParser.g:1083:7: declarationSpecifiers ( -> ^( PARAMETER_DECLARATION declarationSpecifiers ABSENT ) | declaratorOrAbstractDeclarator -> ^( PARAMETER_DECLARATION declarationSpecifiers declaratorOrAbstractDeclarator ) )
			{
			pushFollow(FOLLOW_declarationSpecifiers_in_parameterDeclaration6222);
			declarationSpecifiers323=declarationSpecifiers();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_declarationSpecifiers.add(declarationSpecifiers323.getTree());
			// CivlCParser.g:1084:7: ( -> ^( PARAMETER_DECLARATION declarationSpecifiers ABSENT ) | declaratorOrAbstractDeclarator -> ^( PARAMETER_DECLARATION declarationSpecifiers declaratorOrAbstractDeclarator ) )
			int alt71=2;
			int LA71_0 = input.LA(1);
			if ( (LA71_0==COMMA||LA71_0==RPAREN) ) {
				alt71=1;
			}
			else if ( (LA71_0==IDENTIFIER||LA71_0==LPAREN||LA71_0==LSQUARE||LA71_0==STAR) ) {
				alt71=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 71, 0, input);
				throw nvae;
			}

			switch (alt71) {
				case 1 :
					// CivlCParser.g:1084:9: 
					{
					// AST REWRITE
					// elements: declarationSpecifiers
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1084:9: -> ^( PARAMETER_DECLARATION declarationSpecifiers ABSENT )
					{
						// CivlCParser.g:1084:12: ^( PARAMETER_DECLARATION declarationSpecifiers ABSENT )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(PARAMETER_DECLARATION, "PARAMETER_DECLARATION"), root_1);
						adaptor.addChild(root_1, stream_declarationSpecifiers.nextTree());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1085:9: declaratorOrAbstractDeclarator
					{
					pushFollow(FOLLOW_declaratorOrAbstractDeclarator_in_parameterDeclaration6250);
					declaratorOrAbstractDeclarator324=declaratorOrAbstractDeclarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_declaratorOrAbstractDeclarator.add(declaratorOrAbstractDeclarator324.getTree());
					// AST REWRITE
					// elements: declaratorOrAbstractDeclarator, declarationSpecifiers
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1086:9: -> ^( PARAMETER_DECLARATION declarationSpecifiers declaratorOrAbstractDeclarator )
					{
						// CivlCParser.g:1086:12: ^( PARAMETER_DECLARATION declarationSpecifiers declaratorOrAbstractDeclarator )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(PARAMETER_DECLARATION, "PARAMETER_DECLARATION"), root_1);
						adaptor.addChild(root_1, stream_declarationSpecifiers.nextTree());
						adaptor.addChild(root_1, stream_declaratorOrAbstractDeclarator.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
			DeclarationScope_stack.pop();

		}
		return retval;
	}
	// $ANTLR end "parameterDeclaration"


	public static class declaratorOrAbstractDeclarator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "declaratorOrAbstractDeclarator"
	// CivlCParser.g:1094:1: declaratorOrAbstractDeclarator : ( ( declarator )=> declarator | abstractDeclarator );
	public final OmpParser_CivlCParser.declaratorOrAbstractDeclarator_return declaratorOrAbstractDeclarator() throws RecognitionException {
		OmpParser_CivlCParser.declaratorOrAbstractDeclarator_return retval = new OmpParser_CivlCParser.declaratorOrAbstractDeclarator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope declarator325 =null;
		ParserRuleReturnScope abstractDeclarator326 =null;


		try {
			// CivlCParser.g:1095:2: ( ( declarator )=> declarator | abstractDeclarator )
			int alt72=2;
			int LA72_0 = input.LA(1);
			if ( (LA72_0==IDENTIFIER) && (synpred6_CivlCParser())) {
				alt72=1;
			}
			else if ( (LA72_0==LPAREN) ) {
				int LA72_2 = input.LA(2);
				if ( (synpred6_CivlCParser()) ) {
					alt72=1;
				}
				else if ( (true) ) {
					alt72=2;
				}

			}
			else if ( (LA72_0==STAR) ) {
				int LA72_3 = input.LA(2);
				if ( (synpred6_CivlCParser()) ) {
					alt72=1;
				}
				else if ( (true) ) {
					alt72=2;
				}

			}
			else if ( (LA72_0==LSQUARE) ) {
				alt72=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 72, 0, input);
				throw nvae;
			}

			switch (alt72) {
				case 1 :
					// CivlCParser.g:1095:4: ( declarator )=> declarator
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_declarator_in_declaratorOrAbstractDeclarator6311);
					declarator325=declarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, declarator325.getTree());

					}
					break;
				case 2 :
					// CivlCParser.g:1096:4: abstractDeclarator
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_abstractDeclarator_in_declaratorOrAbstractDeclarator6316);
					abstractDeclarator326=abstractDeclarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, abstractDeclarator326.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "declaratorOrAbstractDeclarator"


	public static class identifierList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "identifierList"
	// CivlCParser.g:1104:1: identifierList : IDENTIFIER ( COMMA IDENTIFIER )* -> ^( IDENTIFIER_LIST ( IDENTIFIER )+ ) ;
	public final OmpParser_CivlCParser.identifierList_return identifierList() throws RecognitionException {
		OmpParser_CivlCParser.identifierList_return retval = new OmpParser_CivlCParser.identifierList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token IDENTIFIER327=null;
		Token COMMA328=null;
		Token IDENTIFIER329=null;

		Object IDENTIFIER327_tree=null;
		Object COMMA328_tree=null;
		Object IDENTIFIER329_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");

		try {
			// CivlCParser.g:1105:5: ( IDENTIFIER ( COMMA IDENTIFIER )* -> ^( IDENTIFIER_LIST ( IDENTIFIER )+ ) )
			// CivlCParser.g:1105:7: IDENTIFIER ( COMMA IDENTIFIER )*
			{
			IDENTIFIER327=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifierList6334); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER327);

			// CivlCParser.g:1105:18: ( COMMA IDENTIFIER )*
			loop73:
			while (true) {
				int alt73=2;
				int LA73_0 = input.LA(1);
				if ( (LA73_0==COMMA) ) {
					alt73=1;
				}

				switch (alt73) {
				case 1 :
					// CivlCParser.g:1105:20: COMMA IDENTIFIER
					{
					COMMA328=(Token)match(input,COMMA,FOLLOW_COMMA_in_identifierList6338); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA328);

					IDENTIFIER329=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifierList6340); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER329);

					}
					break;

				default :
					break loop73;
				}
			}

			// AST REWRITE
			// elements: IDENTIFIER
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1106:7: -> ^( IDENTIFIER_LIST ( IDENTIFIER )+ )
			{
				// CivlCParser.g:1106:10: ^( IDENTIFIER_LIST ( IDENTIFIER )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(IDENTIFIER_LIST, "IDENTIFIER_LIST"), root_1);
				if ( !(stream_IDENTIFIER.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_IDENTIFIER.hasNext() ) {
					adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
				}
				stream_IDENTIFIER.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "identifierList"


	public static class typeName_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "typeName"
	// CivlCParser.g:1115:1: typeName : specifierQualifierList ( -> ^( TYPE_NAME specifierQualifierList ABSENT ) | abstractDeclarator -> ^( TYPE_NAME specifierQualifierList abstractDeclarator ) ) ;
	public final OmpParser_CivlCParser.typeName_return typeName() throws RecognitionException {
		OmpParser_CivlCParser.typeName_return retval = new OmpParser_CivlCParser.typeName_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope specifierQualifierList330 =null;
		ParserRuleReturnScope abstractDeclarator331 =null;

		RewriteRuleSubtreeStream stream_specifierQualifierList=new RewriteRuleSubtreeStream(adaptor,"rule specifierQualifierList");
		RewriteRuleSubtreeStream stream_abstractDeclarator=new RewriteRuleSubtreeStream(adaptor,"rule abstractDeclarator");

		try {
			// CivlCParser.g:1116:5: ( specifierQualifierList ( -> ^( TYPE_NAME specifierQualifierList ABSENT ) | abstractDeclarator -> ^( TYPE_NAME specifierQualifierList abstractDeclarator ) ) )
			// CivlCParser.g:1116:7: specifierQualifierList ( -> ^( TYPE_NAME specifierQualifierList ABSENT ) | abstractDeclarator -> ^( TYPE_NAME specifierQualifierList abstractDeclarator ) )
			{
			pushFollow(FOLLOW_specifierQualifierList_in_typeName6377);
			specifierQualifierList330=specifierQualifierList();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_specifierQualifierList.add(specifierQualifierList330.getTree());
			// CivlCParser.g:1117:7: ( -> ^( TYPE_NAME specifierQualifierList ABSENT ) | abstractDeclarator -> ^( TYPE_NAME specifierQualifierList abstractDeclarator ) )
			int alt74=2;
			int LA74_0 = input.LA(1);
			if ( (LA74_0==EOF||LA74_0==COLON||LA74_0==IDENTIFIER||LA74_0==RPAREN) ) {
				alt74=1;
			}
			else if ( (LA74_0==LPAREN||LA74_0==LSQUARE||LA74_0==STAR) ) {
				alt74=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 74, 0, input);
				throw nvae;
			}

			switch (alt74) {
				case 1 :
					// CivlCParser.g:1117:9: 
					{
					// AST REWRITE
					// elements: specifierQualifierList
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1117:9: -> ^( TYPE_NAME specifierQualifierList ABSENT )
					{
						// CivlCParser.g:1117:12: ^( TYPE_NAME specifierQualifierList ABSENT )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TYPE_NAME, "TYPE_NAME"), root_1);
						adaptor.addChild(root_1, stream_specifierQualifierList.nextTree());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1118:9: abstractDeclarator
					{
					pushFollow(FOLLOW_abstractDeclarator_in_typeName6405);
					abstractDeclarator331=abstractDeclarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_abstractDeclarator.add(abstractDeclarator331.getTree());
					// AST REWRITE
					// elements: specifierQualifierList, abstractDeclarator
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1119:9: -> ^( TYPE_NAME specifierQualifierList abstractDeclarator )
					{
						// CivlCParser.g:1119:12: ^( TYPE_NAME specifierQualifierList abstractDeclarator )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TYPE_NAME, "TYPE_NAME"), root_1);
						adaptor.addChild(root_1, stream_specifierQualifierList.nextTree());
						adaptor.addChild(root_1, stream_abstractDeclarator.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "typeName"


	public static class abstractDeclarator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "abstractDeclarator"
	// CivlCParser.g:1131:1: abstractDeclarator : ( pointer -> ^( ABSTRACT_DECLARATOR pointer ABSENT ) | directAbstractDeclarator -> ^( ABSTRACT_DECLARATOR ABSENT directAbstractDeclarator ) | pointer directAbstractDeclarator -> ^( ABSTRACT_DECLARATOR pointer directAbstractDeclarator ) );
	public final OmpParser_CivlCParser.abstractDeclarator_return abstractDeclarator() throws RecognitionException {
		OmpParser_CivlCParser.abstractDeclarator_return retval = new OmpParser_CivlCParser.abstractDeclarator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope pointer332 =null;
		ParserRuleReturnScope directAbstractDeclarator333 =null;
		ParserRuleReturnScope pointer334 =null;
		ParserRuleReturnScope directAbstractDeclarator335 =null;

		RewriteRuleSubtreeStream stream_pointer=new RewriteRuleSubtreeStream(adaptor,"rule pointer");
		RewriteRuleSubtreeStream stream_directAbstractDeclarator=new RewriteRuleSubtreeStream(adaptor,"rule directAbstractDeclarator");

		try {
			// CivlCParser.g:1132:5: ( pointer -> ^( ABSTRACT_DECLARATOR pointer ABSENT ) | directAbstractDeclarator -> ^( ABSTRACT_DECLARATOR ABSENT directAbstractDeclarator ) | pointer directAbstractDeclarator -> ^( ABSTRACT_DECLARATOR pointer directAbstractDeclarator ) )
			int alt75=3;
			alt75 = dfa75.predict(input);
			switch (alt75) {
				case 1 :
					// CivlCParser.g:1132:7: pointer
					{
					pushFollow(FOLLOW_pointer_in_abstractDeclarator6450);
					pointer332=pointer();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_pointer.add(pointer332.getTree());
					// AST REWRITE
					// elements: pointer
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1133:7: -> ^( ABSTRACT_DECLARATOR pointer ABSENT )
					{
						// CivlCParser.g:1133:10: ^( ABSTRACT_DECLARATOR pointer ABSENT )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ABSTRACT_DECLARATOR, "ABSTRACT_DECLARATOR"), root_1);
						adaptor.addChild(root_1, stream_pointer.nextTree());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1134:7: directAbstractDeclarator
					{
					pushFollow(FOLLOW_directAbstractDeclarator_in_abstractDeclarator6474);
					directAbstractDeclarator333=directAbstractDeclarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_directAbstractDeclarator.add(directAbstractDeclarator333.getTree());
					// AST REWRITE
					// elements: directAbstractDeclarator
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1135:7: -> ^( ABSTRACT_DECLARATOR ABSENT directAbstractDeclarator )
					{
						// CivlCParser.g:1135:10: ^( ABSTRACT_DECLARATOR ABSENT directAbstractDeclarator )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ABSTRACT_DECLARATOR, "ABSTRACT_DECLARATOR"), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_1, stream_directAbstractDeclarator.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// CivlCParser.g:1136:7: pointer directAbstractDeclarator
					{
					pushFollow(FOLLOW_pointer_in_abstractDeclarator6498);
					pointer334=pointer();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_pointer.add(pointer334.getTree());
					pushFollow(FOLLOW_directAbstractDeclarator_in_abstractDeclarator6500);
					directAbstractDeclarator335=directAbstractDeclarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_directAbstractDeclarator.add(directAbstractDeclarator335.getTree());
					// AST REWRITE
					// elements: directAbstractDeclarator, pointer
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1137:7: -> ^( ABSTRACT_DECLARATOR pointer directAbstractDeclarator )
					{
						// CivlCParser.g:1137:10: ^( ABSTRACT_DECLARATOR pointer directAbstractDeclarator )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ABSTRACT_DECLARATOR, "ABSTRACT_DECLARATOR"), root_1);
						adaptor.addChild(root_1, stream_pointer.nextTree());
						adaptor.addChild(root_1, stream_directAbstractDeclarator.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "abstractDeclarator"


	public static class directAbstractDeclarator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "directAbstractDeclarator"
	// CivlCParser.g:1150:1: directAbstractDeclarator : ( LPAREN abstractDeclarator RPAREN ( directAbstractDeclaratorSuffix )* -> ^( DIRECT_ABSTRACT_DECLARATOR abstractDeclarator ( directAbstractDeclaratorSuffix )* ) | ( directAbstractDeclaratorSuffix )+ -> ^( DIRECT_ABSTRACT_DECLARATOR ABSENT ( directAbstractDeclaratorSuffix )+ ) );
	public final OmpParser_CivlCParser.directAbstractDeclarator_return directAbstractDeclarator() throws RecognitionException {
		OmpParser_CivlCParser.directAbstractDeclarator_return retval = new OmpParser_CivlCParser.directAbstractDeclarator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LPAREN336=null;
		Token RPAREN338=null;
		ParserRuleReturnScope abstractDeclarator337 =null;
		ParserRuleReturnScope directAbstractDeclaratorSuffix339 =null;
		ParserRuleReturnScope directAbstractDeclaratorSuffix340 =null;

		Object LPAREN336_tree=null;
		Object RPAREN338_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_directAbstractDeclaratorSuffix=new RewriteRuleSubtreeStream(adaptor,"rule directAbstractDeclaratorSuffix");
		RewriteRuleSubtreeStream stream_abstractDeclarator=new RewriteRuleSubtreeStream(adaptor,"rule abstractDeclarator");

		try {
			// CivlCParser.g:1151:5: ( LPAREN abstractDeclarator RPAREN ( directAbstractDeclaratorSuffix )* -> ^( DIRECT_ABSTRACT_DECLARATOR abstractDeclarator ( directAbstractDeclaratorSuffix )* ) | ( directAbstractDeclaratorSuffix )+ -> ^( DIRECT_ABSTRACT_DECLARATOR ABSENT ( directAbstractDeclaratorSuffix )+ ) )
			int alt78=2;
			int LA78_0 = input.LA(1);
			if ( (LA78_0==LPAREN) ) {
				int LA78_1 = input.LA(2);
				if ( (LA78_1==LPAREN||LA78_1==LSQUARE||LA78_1==STAR) ) {
					alt78=1;
				}
				else if ( ((LA78_1 >= ABSTRACT && LA78_1 <= ALIGNAS)||(LA78_1 >= ATOMIC && LA78_1 <= AUTO)||LA78_1==BOOL||LA78_1==CHAR||(LA78_1 >= COMPLEX && LA78_1 <= CONST)||LA78_1==DEVICE||LA78_1==DOMAIN||LA78_1==DOUBLE||LA78_1==ENUM||LA78_1==EXTERN||(LA78_1 >= FATOMIC && LA78_1 <= FLOAT)||LA78_1==GLOBAL||LA78_1==IDENTIFIER||(LA78_1 >= INLINE && LA78_1 <= INT)||LA78_1==LONG||LA78_1==NORETURN||LA78_1==OUTPUT||LA78_1==PURE||LA78_1==RANGE||(LA78_1 >= REAL && LA78_1 <= REGISTER)||LA78_1==RESTRICT||LA78_1==RPAREN||LA78_1==SHARED||(LA78_1 >= SHORT && LA78_1 <= SIGNED)||LA78_1==STATIC||LA78_1==STRUCT||(LA78_1 >= SYSTEM && LA78_1 <= THREADLOCAL)||(LA78_1 >= TYPEDEF && LA78_1 <= TYPEOF)||(LA78_1 >= UNION && LA78_1 <= UNSIGNED)||(LA78_1 >= VOID && LA78_1 <= VOLATILE)) ) {
					alt78=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 78, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}
			else if ( (LA78_0==LSQUARE) ) {
				alt78=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 78, 0, input);
				throw nvae;
			}

			switch (alt78) {
				case 1 :
					// CivlCParser.g:1151:7: LPAREN abstractDeclarator RPAREN ( directAbstractDeclaratorSuffix )*
					{
					LPAREN336=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_directAbstractDeclarator6535); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN336);

					pushFollow(FOLLOW_abstractDeclarator_in_directAbstractDeclarator6537);
					abstractDeclarator337=abstractDeclarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_abstractDeclarator.add(abstractDeclarator337.getTree());
					RPAREN338=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_directAbstractDeclarator6539); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN338);

					// CivlCParser.g:1151:40: ( directAbstractDeclaratorSuffix )*
					loop76:
					while (true) {
						int alt76=2;
						int LA76_0 = input.LA(1);
						if ( (LA76_0==LPAREN||LA76_0==LSQUARE) ) {
							alt76=1;
						}

						switch (alt76) {
						case 1 :
							// CivlCParser.g:1151:40: directAbstractDeclaratorSuffix
							{
							pushFollow(FOLLOW_directAbstractDeclaratorSuffix_in_directAbstractDeclarator6541);
							directAbstractDeclaratorSuffix339=directAbstractDeclaratorSuffix();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_directAbstractDeclaratorSuffix.add(directAbstractDeclaratorSuffix339.getTree());
							}
							break;

						default :
							break loop76;
						}
					}

					// AST REWRITE
					// elements: abstractDeclarator, directAbstractDeclaratorSuffix
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1152:7: -> ^( DIRECT_ABSTRACT_DECLARATOR abstractDeclarator ( directAbstractDeclaratorSuffix )* )
					{
						// CivlCParser.g:1152:10: ^( DIRECT_ABSTRACT_DECLARATOR abstractDeclarator ( directAbstractDeclaratorSuffix )* )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DIRECT_ABSTRACT_DECLARATOR, "DIRECT_ABSTRACT_DECLARATOR"), root_1);
						adaptor.addChild(root_1, stream_abstractDeclarator.nextTree());
						// CivlCParser.g:1153:12: ( directAbstractDeclaratorSuffix )*
						while ( stream_directAbstractDeclaratorSuffix.hasNext() ) {
							adaptor.addChild(root_1, stream_directAbstractDeclaratorSuffix.nextTree());
						}
						stream_directAbstractDeclaratorSuffix.reset();

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1154:7: ( directAbstractDeclaratorSuffix )+
					{
					// CivlCParser.g:1154:7: ( directAbstractDeclaratorSuffix )+
					int cnt77=0;
					loop77:
					while (true) {
						int alt77=2;
						int LA77_0 = input.LA(1);
						if ( (LA77_0==LPAREN||LA77_0==LSQUARE) ) {
							alt77=1;
						}

						switch (alt77) {
						case 1 :
							// CivlCParser.g:1154:7: directAbstractDeclaratorSuffix
							{
							pushFollow(FOLLOW_directAbstractDeclaratorSuffix_in_directAbstractDeclarator6578);
							directAbstractDeclaratorSuffix340=directAbstractDeclaratorSuffix();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_directAbstractDeclaratorSuffix.add(directAbstractDeclaratorSuffix340.getTree());
							}
							break;

						default :
							if ( cnt77 >= 1 ) break loop77;
							if (state.backtracking>0) {state.failed=true; return retval;}
							EarlyExitException eee = new EarlyExitException(77, input);
							throw eee;
						}
						cnt77++;
					}

					// AST REWRITE
					// elements: directAbstractDeclaratorSuffix
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1155:7: -> ^( DIRECT_ABSTRACT_DECLARATOR ABSENT ( directAbstractDeclaratorSuffix )+ )
					{
						// CivlCParser.g:1155:10: ^( DIRECT_ABSTRACT_DECLARATOR ABSENT ( directAbstractDeclaratorSuffix )+ )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DIRECT_ABSTRACT_DECLARATOR, "DIRECT_ABSTRACT_DECLARATOR"), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						if ( !(stream_directAbstractDeclaratorSuffix.hasNext()) ) {
							throw new RewriteEarlyExitException();
						}
						while ( stream_directAbstractDeclaratorSuffix.hasNext() ) {
							adaptor.addChild(root_1, stream_directAbstractDeclaratorSuffix.nextTree());
						}
						stream_directAbstractDeclaratorSuffix.reset();

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "directAbstractDeclarator"


	public static class typedefName_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "typedefName"
	// CivlCParser.g:1179:1: typedefName :{...}? IDENTIFIER -> ^( TYPEDEF_NAME IDENTIFIER ) ;
	public final OmpParser_CivlCParser.typedefName_return typedefName() throws RecognitionException {
		OmpParser_CivlCParser.typedefName_return retval = new OmpParser_CivlCParser.typedefName_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token IDENTIFIER341=null;

		Object IDENTIFIER341_tree=null;
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");

		try {
			// CivlCParser.g:1184:5: ({...}? IDENTIFIER -> ^( TYPEDEF_NAME IDENTIFIER ) )
			// CivlCParser.g:1184:7: {...}? IDENTIFIER
			{
			if ( !((!DeclarationScope_stack.peek().typedefNameUsed && isTypeName(input.LT(1).getText()))) ) {
				if (state.backtracking>0) {state.failed=true; return retval;}
				throw new FailedPredicateException(input, "typedefName", "!$DeclarationScope::typedefNameUsed && isTypeName(input.LT(1).getText())");
			}
			IDENTIFIER341=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_typedefName6629); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER341);

			// AST REWRITE
			// elements: IDENTIFIER
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1186:7: -> ^( TYPEDEF_NAME IDENTIFIER )
			{
				// CivlCParser.g:1186:10: ^( TYPEDEF_NAME IDENTIFIER )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TYPEDEF_NAME, "TYPEDEF_NAME"), root_1);
				adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
			if ( state.backtracking==0 ) {
			    if(!DeclarationScope_stack.peek().typedefNameUsed)
			    	DeclarationScope_stack.peek().typedefNameUsed =true;
			}
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
	// $ANTLR end "typedefName"


	public static class directAbstractDeclaratorSuffix_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "directAbstractDeclaratorSuffix"
	// CivlCParser.g:1200:1: directAbstractDeclaratorSuffix : ( LSQUARE ( typeQualifierList_opt assignmentExpression_opt RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt assignmentExpression_opt ) | STATIC typeQualifierList_opt assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt assignmentExpression ) | typeQualifierList STATIC assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression ) | STAR RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT ABSENT STAR ) ) | LPAREN ( parameterTypeList RPAREN -> ^( FUNCTION_SUFFIX LPAREN parameterTypeList RPAREN ) | RPAREN -> ^( FUNCTION_SUFFIX LPAREN ABSENT RPAREN ) ) );
	public final OmpParser_CivlCParser.directAbstractDeclaratorSuffix_return directAbstractDeclaratorSuffix() throws RecognitionException {
		OmpParser_CivlCParser.directAbstractDeclaratorSuffix_return retval = new OmpParser_CivlCParser.directAbstractDeclaratorSuffix_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LSQUARE342=null;
		Token RSQUARE345=null;
		Token STATIC346=null;
		Token RSQUARE349=null;
		Token STATIC351=null;
		Token RSQUARE353=null;
		Token STAR354=null;
		Token RSQUARE355=null;
		Token LPAREN356=null;
		Token RPAREN358=null;
		Token RPAREN359=null;
		ParserRuleReturnScope typeQualifierList_opt343 =null;
		ParserRuleReturnScope assignmentExpression_opt344 =null;
		ParserRuleReturnScope typeQualifierList_opt347 =null;
		ParserRuleReturnScope assignmentExpression348 =null;
		ParserRuleReturnScope typeQualifierList350 =null;
		ParserRuleReturnScope assignmentExpression352 =null;
		ParserRuleReturnScope parameterTypeList357 =null;

		Object LSQUARE342_tree=null;
		Object RSQUARE345_tree=null;
		Object STATIC346_tree=null;
		Object RSQUARE349_tree=null;
		Object STATIC351_tree=null;
		Object RSQUARE353_tree=null;
		Object STAR354_tree=null;
		Object RSQUARE355_tree=null;
		Object LPAREN356_tree=null;
		Object RPAREN358_tree=null;
		Object RPAREN359_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_STAR=new RewriteRuleTokenStream(adaptor,"token STAR");
		RewriteRuleTokenStream stream_LSQUARE=new RewriteRuleTokenStream(adaptor,"token LSQUARE");
		RewriteRuleTokenStream stream_RSQUARE=new RewriteRuleTokenStream(adaptor,"token RSQUARE");
		RewriteRuleTokenStream stream_STATIC=new RewriteRuleTokenStream(adaptor,"token STATIC");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_typeQualifierList=new RewriteRuleSubtreeStream(adaptor,"rule typeQualifierList");
		RewriteRuleSubtreeStream stream_assignmentExpression_opt=new RewriteRuleSubtreeStream(adaptor,"rule assignmentExpression_opt");
		RewriteRuleSubtreeStream stream_assignmentExpression=new RewriteRuleSubtreeStream(adaptor,"rule assignmentExpression");
		RewriteRuleSubtreeStream stream_typeQualifierList_opt=new RewriteRuleSubtreeStream(adaptor,"rule typeQualifierList_opt");
		RewriteRuleSubtreeStream stream_parameterTypeList=new RewriteRuleSubtreeStream(adaptor,"rule parameterTypeList");

		try {
			// CivlCParser.g:1201:5: ( LSQUARE ( typeQualifierList_opt assignmentExpression_opt RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt assignmentExpression_opt ) | STATIC typeQualifierList_opt assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt assignmentExpression ) | typeQualifierList STATIC assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression ) | STAR RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT ABSENT STAR ) ) | LPAREN ( parameterTypeList RPAREN -> ^( FUNCTION_SUFFIX LPAREN parameterTypeList RPAREN ) | RPAREN -> ^( FUNCTION_SUFFIX LPAREN ABSENT RPAREN ) ) )
			int alt81=2;
			int LA81_0 = input.LA(1);
			if ( (LA81_0==LSQUARE) ) {
				alt81=1;
			}
			else if ( (LA81_0==LPAREN) ) {
				alt81=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 81, 0, input);
				throw nvae;
			}

			switch (alt81) {
				case 1 :
					// CivlCParser.g:1201:7: LSQUARE ( typeQualifierList_opt assignmentExpression_opt RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt assignmentExpression_opt ) | STATIC typeQualifierList_opt assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt assignmentExpression ) | typeQualifierList STATIC assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression ) | STAR RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT ABSENT STAR ) )
					{
					LSQUARE342=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_directAbstractDeclaratorSuffix6662); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LSQUARE.add(LSQUARE342);

					// CivlCParser.g:1202:7: ( typeQualifierList_opt assignmentExpression_opt RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt assignmentExpression_opt ) | STATIC typeQualifierList_opt assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt assignmentExpression ) | typeQualifierList STATIC assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression ) | STAR RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT ABSENT STAR ) )
					int alt79=4;
					alt79 = dfa79.predict(input);
					switch (alt79) {
						case 1 :
							// CivlCParser.g:1202:9: typeQualifierList_opt assignmentExpression_opt RSQUARE
							{
							pushFollow(FOLLOW_typeQualifierList_opt_in_directAbstractDeclaratorSuffix6672);
							typeQualifierList_opt343=typeQualifierList_opt();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_typeQualifierList_opt.add(typeQualifierList_opt343.getTree());
							pushFollow(FOLLOW_assignmentExpression_opt_in_directAbstractDeclaratorSuffix6674);
							assignmentExpression_opt344=assignmentExpression_opt();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_assignmentExpression_opt.add(assignmentExpression_opt344.getTree());
							RSQUARE345=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_directAbstractDeclaratorSuffix6676); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE345);

							// AST REWRITE
							// elements: assignmentExpression_opt, typeQualifierList_opt, LSQUARE
							// token labels: 
							// rule labels: retval
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 1203:9: -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt assignmentExpression_opt )
							{
								// CivlCParser.g:1203:12: ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt assignmentExpression_opt )
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARRAY_SUFFIX, "ARRAY_SUFFIX"), root_1);
								adaptor.addChild(root_1, stream_LSQUARE.nextNode());
								adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
								adaptor.addChild(root_1, stream_typeQualifierList_opt.nextTree());
								adaptor.addChild(root_1, stream_assignmentExpression_opt.nextTree());
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;
						case 2 :
							// CivlCParser.g:1205:9: STATIC typeQualifierList_opt assignmentExpression RSQUARE
							{
							STATIC346=(Token)match(input,STATIC,FOLLOW_STATIC_in_directAbstractDeclaratorSuffix6721); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_STATIC.add(STATIC346);

							pushFollow(FOLLOW_typeQualifierList_opt_in_directAbstractDeclaratorSuffix6723);
							typeQualifierList_opt347=typeQualifierList_opt();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_typeQualifierList_opt.add(typeQualifierList_opt347.getTree());
							pushFollow(FOLLOW_assignmentExpression_in_directAbstractDeclaratorSuffix6725);
							assignmentExpression348=assignmentExpression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression348.getTree());
							RSQUARE349=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_directAbstractDeclaratorSuffix6727); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE349);

							// AST REWRITE
							// elements: assignmentExpression, typeQualifierList_opt, STATIC, LSQUARE
							// token labels: 
							// rule labels: retval
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 1206:9: -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt assignmentExpression )
							{
								// CivlCParser.g:1206:12: ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt assignmentExpression )
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARRAY_SUFFIX, "ARRAY_SUFFIX"), root_1);
								adaptor.addChild(root_1, stream_LSQUARE.nextNode());
								adaptor.addChild(root_1, stream_STATIC.nextNode());
								adaptor.addChild(root_1, stream_typeQualifierList_opt.nextTree());
								adaptor.addChild(root_1, stream_assignmentExpression.nextTree());
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;
						case 3 :
							// CivlCParser.g:1208:9: typeQualifierList STATIC assignmentExpression RSQUARE
							{
							pushFollow(FOLLOW_typeQualifierList_in_directAbstractDeclaratorSuffix6772);
							typeQualifierList350=typeQualifierList();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_typeQualifierList.add(typeQualifierList350.getTree());
							STATIC351=(Token)match(input,STATIC,FOLLOW_STATIC_in_directAbstractDeclaratorSuffix6774); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_STATIC.add(STATIC351);

							pushFollow(FOLLOW_assignmentExpression_in_directAbstractDeclaratorSuffix6776);
							assignmentExpression352=assignmentExpression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression352.getTree());
							RSQUARE353=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_directAbstractDeclaratorSuffix6778); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE353);

							// AST REWRITE
							// elements: STATIC, assignmentExpression, LSQUARE, typeQualifierList
							// token labels: 
							// rule labels: retval
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 1209:9: -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression )
							{
								// CivlCParser.g:1209:12: ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression )
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARRAY_SUFFIX, "ARRAY_SUFFIX"), root_1);
								adaptor.addChild(root_1, stream_LSQUARE.nextNode());
								adaptor.addChild(root_1, stream_STATIC.nextNode());
								adaptor.addChild(root_1, stream_typeQualifierList.nextTree());
								adaptor.addChild(root_1, stream_assignmentExpression.nextTree());
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;
						case 4 :
							// CivlCParser.g:1210:9: STAR RSQUARE
							{
							STAR354=(Token)match(input,STAR,FOLLOW_STAR_in_directAbstractDeclaratorSuffix6810); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_STAR.add(STAR354);

							RSQUARE355=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_directAbstractDeclaratorSuffix6812); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE355);

							// AST REWRITE
							// elements: STAR, LSQUARE
							// token labels: 
							// rule labels: retval
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 1211:9: -> ^( ARRAY_SUFFIX LSQUARE ABSENT ABSENT STAR )
							{
								// CivlCParser.g:1211:12: ^( ARRAY_SUFFIX LSQUARE ABSENT ABSENT STAR )
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARRAY_SUFFIX, "ARRAY_SUFFIX"), root_1);
								adaptor.addChild(root_1, stream_LSQUARE.nextNode());
								adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
								adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
								adaptor.addChild(root_1, stream_STAR.nextNode());
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;

					}

					}
					break;
				case 2 :
					// CivlCParser.g:1213:7: LPAREN ( parameterTypeList RPAREN -> ^( FUNCTION_SUFFIX LPAREN parameterTypeList RPAREN ) | RPAREN -> ^( FUNCTION_SUFFIX LPAREN ABSENT RPAREN ) )
					{
					LPAREN356=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_directAbstractDeclaratorSuffix6850); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN356);

					// CivlCParser.g:1214:7: ( parameterTypeList RPAREN -> ^( FUNCTION_SUFFIX LPAREN parameterTypeList RPAREN ) | RPAREN -> ^( FUNCTION_SUFFIX LPAREN ABSENT RPAREN ) )
					int alt80=2;
					int LA80_0 = input.LA(1);
					if ( ((LA80_0 >= ABSTRACT && LA80_0 <= ALIGNAS)||(LA80_0 >= ATOMIC && LA80_0 <= AUTO)||LA80_0==BOOL||LA80_0==CHAR||(LA80_0 >= COMPLEX && LA80_0 <= CONST)||LA80_0==DEVICE||LA80_0==DOMAIN||LA80_0==DOUBLE||LA80_0==ENUM||LA80_0==EXTERN||(LA80_0 >= FATOMIC && LA80_0 <= FLOAT)||LA80_0==GLOBAL||LA80_0==IDENTIFIER||(LA80_0 >= INLINE && LA80_0 <= INT)||LA80_0==LONG||LA80_0==NORETURN||LA80_0==OUTPUT||LA80_0==PURE||LA80_0==RANGE||(LA80_0 >= REAL && LA80_0 <= REGISTER)||LA80_0==RESTRICT||LA80_0==SHARED||(LA80_0 >= SHORT && LA80_0 <= SIGNED)||LA80_0==STATIC||LA80_0==STRUCT||(LA80_0 >= SYSTEM && LA80_0 <= THREADLOCAL)||(LA80_0 >= TYPEDEF && LA80_0 <= TYPEOF)||(LA80_0 >= UNION && LA80_0 <= UNSIGNED)||(LA80_0 >= VOID && LA80_0 <= VOLATILE)) ) {
						alt80=1;
					}
					else if ( (LA80_0==RPAREN) ) {
						alt80=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 80, 0, input);
						throw nvae;
					}

					switch (alt80) {
						case 1 :
							// CivlCParser.g:1214:9: parameterTypeList RPAREN
							{
							pushFollow(FOLLOW_parameterTypeList_in_directAbstractDeclaratorSuffix6860);
							parameterTypeList357=parameterTypeList();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_parameterTypeList.add(parameterTypeList357.getTree());
							RPAREN358=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_directAbstractDeclaratorSuffix6862); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN358);

							// AST REWRITE
							// elements: LPAREN, parameterTypeList, RPAREN
							// token labels: 
							// rule labels: retval
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 1215:9: -> ^( FUNCTION_SUFFIX LPAREN parameterTypeList RPAREN )
							{
								// CivlCParser.g:1215:12: ^( FUNCTION_SUFFIX LPAREN parameterTypeList RPAREN )
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FUNCTION_SUFFIX, "FUNCTION_SUFFIX"), root_1);
								adaptor.addChild(root_1, stream_LPAREN.nextNode());
								adaptor.addChild(root_1, stream_parameterTypeList.nextTree());
								adaptor.addChild(root_1, stream_RPAREN.nextNode());
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;
						case 2 :
							// CivlCParser.g:1216:9: RPAREN
							{
							RPAREN359=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_directAbstractDeclaratorSuffix6892); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN359);

							// AST REWRITE
							// elements: RPAREN, LPAREN
							// token labels: 
							// rule labels: retval
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 1217:9: -> ^( FUNCTION_SUFFIX LPAREN ABSENT RPAREN )
							{
								// CivlCParser.g:1217:12: ^( FUNCTION_SUFFIX LPAREN ABSENT RPAREN )
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FUNCTION_SUFFIX, "FUNCTION_SUFFIX"), root_1);
								adaptor.addChild(root_1, stream_LPAREN.nextNode());
								adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
								adaptor.addChild(root_1, stream_RPAREN.nextNode());
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;

					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "directAbstractDeclaratorSuffix"


	public static class initializer_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "initializer"
	// CivlCParser.g:1222:1: initializer : ( assignmentExpression -> ^( SCALAR_INITIALIZER assignmentExpression ) | LCURLY initializerList ( RCURLY | COMMA RCURLY ) -> initializerList );
	public final OmpParser_CivlCParser.initializer_return initializer() throws RecognitionException {
		OmpParser_CivlCParser.initializer_return retval = new OmpParser_CivlCParser.initializer_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LCURLY361=null;
		Token RCURLY363=null;
		Token COMMA364=null;
		Token RCURLY365=null;
		ParserRuleReturnScope assignmentExpression360 =null;
		ParserRuleReturnScope initializerList362 =null;

		Object LCURLY361_tree=null;
		Object RCURLY363_tree=null;
		Object COMMA364_tree=null;
		Object RCURLY365_tree=null;
		RewriteRuleTokenStream stream_LCURLY=new RewriteRuleTokenStream(adaptor,"token LCURLY");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_RCURLY=new RewriteRuleTokenStream(adaptor,"token RCURLY");
		RewriteRuleSubtreeStream stream_assignmentExpression=new RewriteRuleSubtreeStream(adaptor,"rule assignmentExpression");
		RewriteRuleSubtreeStream stream_initializerList=new RewriteRuleSubtreeStream(adaptor,"rule initializerList");

		try {
			// CivlCParser.g:1223:5: ( assignmentExpression -> ^( SCALAR_INITIALIZER assignmentExpression ) | LCURLY initializerList ( RCURLY | COMMA RCURLY ) -> initializerList )
			int alt83=2;
			int LA83_0 = input.LA(1);
			if ( ((LA83_0 >= ALIGNOF && LA83_0 <= AMPERSAND)||LA83_0==BIG_O||LA83_0==CALLS||LA83_0==CHARACTER_CONSTANT||LA83_0==DERIV||LA83_0==ELLIPSIS||LA83_0==EXISTS||LA83_0==FALSE||LA83_0==FLOATING_CONSTANT||LA83_0==FORALL||LA83_0==GENERIC||LA83_0==HERE||LA83_0==IDENTIFIER||LA83_0==INTEGER_CONSTANT||LA83_0==LPAREN||LA83_0==MINUSMINUS||LA83_0==NOT||LA83_0==PLUS||LA83_0==PLUSPLUS||LA83_0==PROCNULL||LA83_0==RESULT||LA83_0==SCOPEOF||LA83_0==SELF||(LA83_0 >= SIZEOF && LA83_0 <= STAR)||LA83_0==STRING_LITERAL||LA83_0==SUB||(LA83_0 >= TILDE && LA83_0 <= TRUE)||LA83_0==UNIFORM||LA83_0==ROOT) ) {
				alt83=1;
			}
			else if ( (LA83_0==LCURLY) ) {
				alt83=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 83, 0, input);
				throw nvae;
			}

			switch (alt83) {
				case 1 :
					// CivlCParser.g:1223:7: assignmentExpression
					{
					pushFollow(FOLLOW_assignmentExpression_in_initializer6939);
					assignmentExpression360=assignmentExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression360.getTree());
					// AST REWRITE
					// elements: assignmentExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1223:28: -> ^( SCALAR_INITIALIZER assignmentExpression )
					{
						// CivlCParser.g:1223:31: ^( SCALAR_INITIALIZER assignmentExpression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(SCALAR_INITIALIZER, "SCALAR_INITIALIZER"), root_1);
						adaptor.addChild(root_1, stream_assignmentExpression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1224:7: LCURLY initializerList ( RCURLY | COMMA RCURLY )
					{
					LCURLY361=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_initializer6955); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY361);

					pushFollow(FOLLOW_initializerList_in_initializer6957);
					initializerList362=initializerList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_initializerList.add(initializerList362.getTree());
					// CivlCParser.g:1225:9: ( RCURLY | COMMA RCURLY )
					int alt82=2;
					int LA82_0 = input.LA(1);
					if ( (LA82_0==RCURLY) ) {
						alt82=1;
					}
					else if ( (LA82_0==COMMA) ) {
						alt82=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 82, 0, input);
						throw nvae;
					}

					switch (alt82) {
						case 1 :
							// CivlCParser.g:1225:13: RCURLY
							{
							RCURLY363=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_initializer6971); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY363);

							}
							break;
						case 2 :
							// CivlCParser.g:1226:13: COMMA RCURLY
							{
							COMMA364=(Token)match(input,COMMA,FOLLOW_COMMA_in_initializer6985); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_COMMA.add(COMMA364);

							RCURLY365=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_initializer6987); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY365);

							}
							break;

					}

					// AST REWRITE
					// elements: initializerList
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1228:7: -> initializerList
					{
						adaptor.addChild(root_0, stream_initializerList.nextTree());
					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "initializer"


	public static class initializerList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "initializerList"
	// CivlCParser.g:1232:1: initializerList : designatedInitializer ( COMMA designatedInitializer )* -> ^( INITIALIZER_LIST ( designatedInitializer )+ ) ;
	public final OmpParser_CivlCParser.initializerList_return initializerList() throws RecognitionException {
		OmpParser_CivlCParser.initializerList_return retval = new OmpParser_CivlCParser.initializerList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMMA367=null;
		ParserRuleReturnScope designatedInitializer366 =null;
		ParserRuleReturnScope designatedInitializer368 =null;

		Object COMMA367_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_designatedInitializer=new RewriteRuleSubtreeStream(adaptor,"rule designatedInitializer");

		try {
			// CivlCParser.g:1233:5: ( designatedInitializer ( COMMA designatedInitializer )* -> ^( INITIALIZER_LIST ( designatedInitializer )+ ) )
			// CivlCParser.g:1233:7: designatedInitializer ( COMMA designatedInitializer )*
			{
			pushFollow(FOLLOW_designatedInitializer_in_initializerList7026);
			designatedInitializer366=designatedInitializer();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_designatedInitializer.add(designatedInitializer366.getTree());
			// CivlCParser.g:1233:29: ( COMMA designatedInitializer )*
			loop84:
			while (true) {
				int alt84=2;
				int LA84_0 = input.LA(1);
				if ( (LA84_0==COMMA) ) {
					int LA84_2 = input.LA(2);
					if ( ((LA84_2 >= ALIGNOF && LA84_2 <= AMPERSAND)||LA84_2==BIG_O||LA84_2==CALLS||LA84_2==CHARACTER_CONSTANT||LA84_2==DERIV||LA84_2==DOT||LA84_2==ELLIPSIS||LA84_2==EXISTS||LA84_2==FALSE||LA84_2==FLOATING_CONSTANT||LA84_2==FORALL||LA84_2==GENERIC||LA84_2==HERE||LA84_2==IDENTIFIER||LA84_2==INTEGER_CONSTANT||LA84_2==LCURLY||LA84_2==LPAREN||LA84_2==LSQUARE||LA84_2==MINUSMINUS||LA84_2==NOT||LA84_2==PLUS||LA84_2==PLUSPLUS||LA84_2==PROCNULL||LA84_2==RESULT||LA84_2==SCOPEOF||LA84_2==SELF||(LA84_2 >= SIZEOF && LA84_2 <= STAR)||LA84_2==STRING_LITERAL||LA84_2==SUB||(LA84_2 >= TILDE && LA84_2 <= TRUE)||LA84_2==UNIFORM||LA84_2==ROOT) ) {
						alt84=1;
					}

				}

				switch (alt84) {
				case 1 :
					// CivlCParser.g:1233:30: COMMA designatedInitializer
					{
					COMMA367=(Token)match(input,COMMA,FOLLOW_COMMA_in_initializerList7029); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA367);

					pushFollow(FOLLOW_designatedInitializer_in_initializerList7031);
					designatedInitializer368=designatedInitializer();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_designatedInitializer.add(designatedInitializer368.getTree());
					}
					break;

				default :
					break loop84;
				}
			}

			// AST REWRITE
			// elements: designatedInitializer
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1234:7: -> ^( INITIALIZER_LIST ( designatedInitializer )+ )
			{
				// CivlCParser.g:1234:10: ^( INITIALIZER_LIST ( designatedInitializer )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(INITIALIZER_LIST, "INITIALIZER_LIST"), root_1);
				if ( !(stream_designatedInitializer.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_designatedInitializer.hasNext() ) {
					adaptor.addChild(root_1, stream_designatedInitializer.nextTree());
				}
				stream_designatedInitializer.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "initializerList"


	public static class designatedInitializer_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "designatedInitializer"
	// CivlCParser.g:1237:1: designatedInitializer : ( initializer -> ^( DESIGNATED_INITIALIZER ABSENT initializer ) | designation initializer -> ^( DESIGNATED_INITIALIZER designation initializer ) );
	public final OmpParser_CivlCParser.designatedInitializer_return designatedInitializer() throws RecognitionException {
		OmpParser_CivlCParser.designatedInitializer_return retval = new OmpParser_CivlCParser.designatedInitializer_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope initializer369 =null;
		ParserRuleReturnScope designation370 =null;
		ParserRuleReturnScope initializer371 =null;

		RewriteRuleSubtreeStream stream_designation=new RewriteRuleSubtreeStream(adaptor,"rule designation");
		RewriteRuleSubtreeStream stream_initializer=new RewriteRuleSubtreeStream(adaptor,"rule initializer");

		try {
			// CivlCParser.g:1238:2: ( initializer -> ^( DESIGNATED_INITIALIZER ABSENT initializer ) | designation initializer -> ^( DESIGNATED_INITIALIZER designation initializer ) )
			int alt85=2;
			int LA85_0 = input.LA(1);
			if ( ((LA85_0 >= ALIGNOF && LA85_0 <= AMPERSAND)||LA85_0==BIG_O||LA85_0==CALLS||LA85_0==CHARACTER_CONSTANT||LA85_0==DERIV||LA85_0==ELLIPSIS||LA85_0==EXISTS||LA85_0==FALSE||LA85_0==FLOATING_CONSTANT||LA85_0==FORALL||LA85_0==GENERIC||LA85_0==HERE||LA85_0==IDENTIFIER||LA85_0==INTEGER_CONSTANT||LA85_0==LCURLY||LA85_0==LPAREN||LA85_0==MINUSMINUS||LA85_0==NOT||LA85_0==PLUS||LA85_0==PLUSPLUS||LA85_0==PROCNULL||LA85_0==RESULT||LA85_0==SCOPEOF||LA85_0==SELF||(LA85_0 >= SIZEOF && LA85_0 <= STAR)||LA85_0==STRING_LITERAL||LA85_0==SUB||(LA85_0 >= TILDE && LA85_0 <= TRUE)||LA85_0==UNIFORM||LA85_0==ROOT) ) {
				alt85=1;
			}
			else if ( (LA85_0==DOT||LA85_0==LSQUARE) ) {
				alt85=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 85, 0, input);
				throw nvae;
			}

			switch (alt85) {
				case 1 :
					// CivlCParser.g:1238:4: initializer
					{
					pushFollow(FOLLOW_initializer_in_designatedInitializer7062);
					initializer369=initializer();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_initializer.add(initializer369.getTree());
					// AST REWRITE
					// elements: initializer
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1239:4: -> ^( DESIGNATED_INITIALIZER ABSENT initializer )
					{
						// CivlCParser.g:1239:7: ^( DESIGNATED_INITIALIZER ABSENT initializer )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DESIGNATED_INITIALIZER, "DESIGNATED_INITIALIZER"), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_1, stream_initializer.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1240:4: designation initializer
					{
					pushFollow(FOLLOW_designation_in_designatedInitializer7080);
					designation370=designation();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_designation.add(designation370.getTree());
					pushFollow(FOLLOW_initializer_in_designatedInitializer7082);
					initializer371=initializer();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_initializer.add(initializer371.getTree());
					// AST REWRITE
					// elements: initializer, designation
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1241:4: -> ^( DESIGNATED_INITIALIZER designation initializer )
					{
						// CivlCParser.g:1241:7: ^( DESIGNATED_INITIALIZER designation initializer )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DESIGNATED_INITIALIZER, "DESIGNATED_INITIALIZER"), root_1);
						adaptor.addChild(root_1, stream_designation.nextTree());
						adaptor.addChild(root_1, stream_initializer.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "designatedInitializer"


	public static class designation_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "designation"
	// CivlCParser.g:1245:1: designation : designatorList ASSIGN -> ^( DESIGNATION designatorList ) ;
	public final OmpParser_CivlCParser.designation_return designation() throws RecognitionException {
		OmpParser_CivlCParser.designation_return retval = new OmpParser_CivlCParser.designation_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ASSIGN373=null;
		ParserRuleReturnScope designatorList372 =null;

		Object ASSIGN373_tree=null;
		RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
		RewriteRuleSubtreeStream stream_designatorList=new RewriteRuleSubtreeStream(adaptor,"rule designatorList");

		try {
			// CivlCParser.g:1246:5: ( designatorList ASSIGN -> ^( DESIGNATION designatorList ) )
			// CivlCParser.g:1246:7: designatorList ASSIGN
			{
			pushFollow(FOLLOW_designatorList_in_designation7111);
			designatorList372=designatorList();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_designatorList.add(designatorList372.getTree());
			ASSIGN373=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_designation7113); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ASSIGN.add(ASSIGN373);

			// AST REWRITE
			// elements: designatorList
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1246:29: -> ^( DESIGNATION designatorList )
			{
				// CivlCParser.g:1246:32: ^( DESIGNATION designatorList )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DESIGNATION, "DESIGNATION"), root_1);
				adaptor.addChild(root_1, stream_designatorList.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "designation"


	public static class designatorList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "designatorList"
	// CivlCParser.g:1250:1: designatorList : ( designator )+ ;
	public final OmpParser_CivlCParser.designatorList_return designatorList() throws RecognitionException {
		OmpParser_CivlCParser.designatorList_return retval = new OmpParser_CivlCParser.designatorList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope designator374 =null;


		try {
			// CivlCParser.g:1251:5: ( ( designator )+ )
			// CivlCParser.g:1251:7: ( designator )+
			{
			root_0 = (Object)adaptor.nil();


			// CivlCParser.g:1251:7: ( designator )+
			int cnt86=0;
			loop86:
			while (true) {
				int alt86=2;
				int LA86_0 = input.LA(1);
				if ( (LA86_0==DOT||LA86_0==LSQUARE) ) {
					alt86=1;
				}

				switch (alt86) {
				case 1 :
					// CivlCParser.g:1251:7: designator
					{
					pushFollow(FOLLOW_designator_in_designatorList7140);
					designator374=designator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, designator374.getTree());

					}
					break;

				default :
					if ( cnt86 >= 1 ) break loop86;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(86, input);
					throw eee;
				}
				cnt86++;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "designatorList"


	public static class designator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "designator"
	// CivlCParser.g:1255:1: designator : ( LSQUARE constantExpression RSQUARE -> ^( ARRAY_ELEMENT_DESIGNATOR constantExpression ) | DOT IDENTIFIER -> ^( FIELD_DESIGNATOR IDENTIFIER ) );
	public final OmpParser_CivlCParser.designator_return designator() throws RecognitionException {
		OmpParser_CivlCParser.designator_return retval = new OmpParser_CivlCParser.designator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LSQUARE375=null;
		Token RSQUARE377=null;
		Token DOT378=null;
		Token IDENTIFIER379=null;
		ParserRuleReturnScope constantExpression376 =null;

		Object LSQUARE375_tree=null;
		Object RSQUARE377_tree=null;
		Object DOT378_tree=null;
		Object IDENTIFIER379_tree=null;
		RewriteRuleTokenStream stream_LSQUARE=new RewriteRuleTokenStream(adaptor,"token LSQUARE");
		RewriteRuleTokenStream stream_RSQUARE=new RewriteRuleTokenStream(adaptor,"token RSQUARE");
		RewriteRuleTokenStream stream_DOT=new RewriteRuleTokenStream(adaptor,"token DOT");
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
		RewriteRuleSubtreeStream stream_constantExpression=new RewriteRuleSubtreeStream(adaptor,"rule constantExpression");

		try {
			// CivlCParser.g:1256:5: ( LSQUARE constantExpression RSQUARE -> ^( ARRAY_ELEMENT_DESIGNATOR constantExpression ) | DOT IDENTIFIER -> ^( FIELD_DESIGNATOR IDENTIFIER ) )
			int alt87=2;
			int LA87_0 = input.LA(1);
			if ( (LA87_0==LSQUARE) ) {
				alt87=1;
			}
			else if ( (LA87_0==DOT) ) {
				alt87=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 87, 0, input);
				throw nvae;
			}

			switch (alt87) {
				case 1 :
					// CivlCParser.g:1256:7: LSQUARE constantExpression RSQUARE
					{
					LSQUARE375=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_designator7160); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LSQUARE.add(LSQUARE375);

					pushFollow(FOLLOW_constantExpression_in_designator7162);
					constantExpression376=constantExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_constantExpression.add(constantExpression376.getTree());
					RSQUARE377=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_designator7164); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE377);

					// AST REWRITE
					// elements: constantExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1257:7: -> ^( ARRAY_ELEMENT_DESIGNATOR constantExpression )
					{
						// CivlCParser.g:1257:10: ^( ARRAY_ELEMENT_DESIGNATOR constantExpression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARRAY_ELEMENT_DESIGNATOR, "ARRAY_ELEMENT_DESIGNATOR"), root_1);
						adaptor.addChild(root_1, stream_constantExpression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1258:7: DOT IDENTIFIER
					{
					DOT378=(Token)match(input,DOT,FOLLOW_DOT_in_designator7186); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(DOT378);

					IDENTIFIER379=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_designator7188); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER379);

					// AST REWRITE
					// elements: IDENTIFIER
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1259:7: -> ^( FIELD_DESIGNATOR IDENTIFIER )
					{
						// CivlCParser.g:1259:10: ^( FIELD_DESIGNATOR IDENTIFIER )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FIELD_DESIGNATOR, "FIELD_DESIGNATOR"), root_1);
						adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "designator"


	public static class staticAssertDeclaration_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "staticAssertDeclaration"
	// CivlCParser.g:1263:1: staticAssertDeclaration : STATICASSERT LPAREN constantExpression COMMA STRING_LITERAL RPAREN SEMI -> ^( STATICASSERT constantExpression STRING_LITERAL ) ;
	public final OmpParser_CivlCParser.staticAssertDeclaration_return staticAssertDeclaration() throws RecognitionException {
		OmpParser_CivlCParser.staticAssertDeclaration_return retval = new OmpParser_CivlCParser.staticAssertDeclaration_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token STATICASSERT380=null;
		Token LPAREN381=null;
		Token COMMA383=null;
		Token STRING_LITERAL384=null;
		Token RPAREN385=null;
		Token SEMI386=null;
		ParserRuleReturnScope constantExpression382 =null;

		Object STATICASSERT380_tree=null;
		Object LPAREN381_tree=null;
		Object COMMA383_tree=null;
		Object STRING_LITERAL384_tree=null;
		Object RPAREN385_tree=null;
		Object SEMI386_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_STRING_LITERAL=new RewriteRuleTokenStream(adaptor,"token STRING_LITERAL");
		RewriteRuleTokenStream stream_STATICASSERT=new RewriteRuleTokenStream(adaptor,"token STATICASSERT");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_constantExpression=new RewriteRuleSubtreeStream(adaptor,"rule constantExpression");

		try {
			// CivlCParser.g:1264:5: ( STATICASSERT LPAREN constantExpression COMMA STRING_LITERAL RPAREN SEMI -> ^( STATICASSERT constantExpression STRING_LITERAL ) )
			// CivlCParser.g:1264:7: STATICASSERT LPAREN constantExpression COMMA STRING_LITERAL RPAREN SEMI
			{
			STATICASSERT380=(Token)match(input,STATICASSERT,FOLLOW_STATICASSERT_in_staticAssertDeclaration7221); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_STATICASSERT.add(STATICASSERT380);

			LPAREN381=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_staticAssertDeclaration7223); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN381);

			pushFollow(FOLLOW_constantExpression_in_staticAssertDeclaration7225);
			constantExpression382=constantExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_constantExpression.add(constantExpression382.getTree());
			COMMA383=(Token)match(input,COMMA,FOLLOW_COMMA_in_staticAssertDeclaration7227); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_COMMA.add(COMMA383);

			STRING_LITERAL384=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_staticAssertDeclaration7229); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_STRING_LITERAL.add(STRING_LITERAL384);

			RPAREN385=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_staticAssertDeclaration7237); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN385);

			SEMI386=(Token)match(input,SEMI,FOLLOW_SEMI_in_staticAssertDeclaration7239); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_SEMI.add(SEMI386);

			// AST REWRITE
			// elements: STRING_LITERAL, STATICASSERT, constantExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1266:7: -> ^( STATICASSERT constantExpression STRING_LITERAL )
			{
				// CivlCParser.g:1266:10: ^( STATICASSERT constantExpression STRING_LITERAL )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_STATICASSERT.nextNode(), root_1);
				adaptor.addChild(root_1, stream_constantExpression.nextTree());
				adaptor.addChild(root_1, stream_STRING_LITERAL.nextNode());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "staticAssertDeclaration"


	public static class domainSpecifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "domainSpecifier"
	// CivlCParser.g:1270:1: domainSpecifier : DOMAIN ( -> ^( DOMAIN ) | LPAREN INTEGER_CONSTANT RPAREN -> ^( DOMAIN INTEGER_CONSTANT RPAREN ) ) ;
	public final OmpParser_CivlCParser.domainSpecifier_return domainSpecifier() throws RecognitionException {
		OmpParser_CivlCParser.domainSpecifier_return retval = new OmpParser_CivlCParser.domainSpecifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token DOMAIN387=null;
		Token LPAREN388=null;
		Token INTEGER_CONSTANT389=null;
		Token RPAREN390=null;

		Object DOMAIN387_tree=null;
		Object LPAREN388_tree=null;
		Object INTEGER_CONSTANT389_tree=null;
		Object RPAREN390_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_INTEGER_CONSTANT=new RewriteRuleTokenStream(adaptor,"token INTEGER_CONSTANT");
		RewriteRuleTokenStream stream_DOMAIN=new RewriteRuleTokenStream(adaptor,"token DOMAIN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");

		try {
			// CivlCParser.g:1271:2: ( DOMAIN ( -> ^( DOMAIN ) | LPAREN INTEGER_CONSTANT RPAREN -> ^( DOMAIN INTEGER_CONSTANT RPAREN ) ) )
			// CivlCParser.g:1271:4: DOMAIN ( -> ^( DOMAIN ) | LPAREN INTEGER_CONSTANT RPAREN -> ^( DOMAIN INTEGER_CONSTANT RPAREN ) )
			{
			DOMAIN387=(Token)match(input,DOMAIN,FOLLOW_DOMAIN_in_domainSpecifier7271); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_DOMAIN.add(DOMAIN387);

			// CivlCParser.g:1272:4: ( -> ^( DOMAIN ) | LPAREN INTEGER_CONSTANT RPAREN -> ^( DOMAIN INTEGER_CONSTANT RPAREN ) )
			int alt88=2;
			int LA88_0 = input.LA(1);
			if ( (LA88_0==EOF||(LA88_0 >= ABSTRACT && LA88_0 <= ALIGNAS)||(LA88_0 >= ATOMIC && LA88_0 <= AUTO)||LA88_0==BOOL||LA88_0==CHAR||(LA88_0 >= COLON && LA88_0 <= COMMA)||(LA88_0 >= COMPLEX && LA88_0 <= CONST)||LA88_0==DEVICE||LA88_0==DOMAIN||LA88_0==DOUBLE||LA88_0==ENUM||LA88_0==EXTERN||(LA88_0 >= FATOMIC && LA88_0 <= FLOAT)||LA88_0==GLOBAL||LA88_0==IDENTIFIER||(LA88_0 >= INLINE && LA88_0 <= INT)||LA88_0==LONG||LA88_0==LSQUARE||LA88_0==NORETURN||LA88_0==OUTPUT||LA88_0==PURE||LA88_0==RANGE||(LA88_0 >= REAL && LA88_0 <= REGISTER)||LA88_0==RESTRICT||LA88_0==RPAREN||(LA88_0 >= SEMI && LA88_0 <= SHARED)||(LA88_0 >= SHORT && LA88_0 <= SIGNED)||LA88_0==STAR||LA88_0==STATIC||LA88_0==STRUCT||(LA88_0 >= SYSTEM && LA88_0 <= THREADLOCAL)||(LA88_0 >= TYPEDEF && LA88_0 <= TYPEOF)||(LA88_0 >= UNION && LA88_0 <= UNSIGNED)||(LA88_0 >= VOID && LA88_0 <= VOLATILE)) ) {
				alt88=1;
			}
			else if ( (LA88_0==LPAREN) ) {
				int LA88_2 = input.LA(2);
				if ( (LA88_2==INTEGER_CONSTANT) ) {
					alt88=2;
				}
				else if ( ((LA88_2 >= ABSTRACT && LA88_2 <= ALIGNAS)||(LA88_2 >= ATOMIC && LA88_2 <= AUTO)||LA88_2==BOOL||LA88_2==CHAR||(LA88_2 >= COMPLEX && LA88_2 <= CONST)||LA88_2==DEVICE||LA88_2==DOMAIN||LA88_2==DOUBLE||LA88_2==ENUM||LA88_2==EXTERN||(LA88_2 >= FATOMIC && LA88_2 <= FLOAT)||LA88_2==GLOBAL||LA88_2==IDENTIFIER||(LA88_2 >= INLINE && LA88_2 <= INT)||(LA88_2 >= LONG && LA88_2 <= LPAREN)||LA88_2==LSQUARE||LA88_2==NORETURN||LA88_2==OUTPUT||LA88_2==PURE||LA88_2==RANGE||(LA88_2 >= REAL && LA88_2 <= REGISTER)||LA88_2==RESTRICT||LA88_2==RPAREN||LA88_2==SHARED||(LA88_2 >= SHORT && LA88_2 <= SIGNED)||LA88_2==STAR||LA88_2==STATIC||LA88_2==STRUCT||(LA88_2 >= SYSTEM && LA88_2 <= THREADLOCAL)||(LA88_2 >= TYPEDEF && LA88_2 <= TYPEOF)||(LA88_2 >= UNION && LA88_2 <= UNSIGNED)||(LA88_2 >= VOID && LA88_2 <= VOLATILE)) ) {
					alt88=1;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 88, 2, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 88, 0, input);
				throw nvae;
			}

			switch (alt88) {
				case 1 :
					// CivlCParser.g:1272:6: 
					{
					// AST REWRITE
					// elements: DOMAIN
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1272:6: -> ^( DOMAIN )
					{
						// CivlCParser.g:1272:9: ^( DOMAIN )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_DOMAIN.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1273:6: LPAREN INTEGER_CONSTANT RPAREN
					{
					LPAREN388=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_domainSpecifier7289); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN388);

					INTEGER_CONSTANT389=(Token)match(input,INTEGER_CONSTANT,FOLLOW_INTEGER_CONSTANT_in_domainSpecifier7291); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_INTEGER_CONSTANT.add(INTEGER_CONSTANT389);

					RPAREN390=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_domainSpecifier7293); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN390);

					// AST REWRITE
					// elements: INTEGER_CONSTANT, DOMAIN, RPAREN
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1273:37: -> ^( DOMAIN INTEGER_CONSTANT RPAREN )
					{
						// CivlCParser.g:1273:40: ^( DOMAIN INTEGER_CONSTANT RPAREN )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_DOMAIN.nextNode(), root_1);
						adaptor.addChild(root_1, stream_INTEGER_CONSTANT.nextNode());
						adaptor.addChild(root_1, stream_RPAREN.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "domainSpecifier"


	public static class statement_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "statement"
	// CivlCParser.g:1281:1: statement : ( labeledStatement -> ^( STATEMENT labeledStatement ) | compoundStatement -> ^( STATEMENT compoundStatement ) | expressionStatement -> ^( STATEMENT expressionStatement ) | selectionStatement -> ^( STATEMENT selectionStatement ) | iterationStatement -> ^( STATEMENT iterationStatement ) | jumpStatement -> ^( STATEMENT jumpStatement ) | whenStatement -> ^( STATEMENT whenStatement ) | chooseStatement -> ^( STATEMENT chooseStatement ) | atomicStatement -> ^( STATEMENT atomicStatement ) | datomicStatement -> ^( STATEMENT datomicStatement ) );
	public final OmpParser_CivlCParser.statement_return statement() throws RecognitionException {
		OmpParser_CivlCParser.statement_return retval = new OmpParser_CivlCParser.statement_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope labeledStatement391 =null;
		ParserRuleReturnScope compoundStatement392 =null;
		ParserRuleReturnScope expressionStatement393 =null;
		ParserRuleReturnScope selectionStatement394 =null;
		ParserRuleReturnScope iterationStatement395 =null;
		ParserRuleReturnScope jumpStatement396 =null;
		ParserRuleReturnScope whenStatement397 =null;
		ParserRuleReturnScope chooseStatement398 =null;
		ParserRuleReturnScope atomicStatement399 =null;
		ParserRuleReturnScope datomicStatement400 =null;

		RewriteRuleSubtreeStream stream_datomicStatement=new RewriteRuleSubtreeStream(adaptor,"rule datomicStatement");
		RewriteRuleSubtreeStream stream_labeledStatement=new RewriteRuleSubtreeStream(adaptor,"rule labeledStatement");
		RewriteRuleSubtreeStream stream_whenStatement=new RewriteRuleSubtreeStream(adaptor,"rule whenStatement");
		RewriteRuleSubtreeStream stream_compoundStatement=new RewriteRuleSubtreeStream(adaptor,"rule compoundStatement");
		RewriteRuleSubtreeStream stream_jumpStatement=new RewriteRuleSubtreeStream(adaptor,"rule jumpStatement");
		RewriteRuleSubtreeStream stream_expressionStatement=new RewriteRuleSubtreeStream(adaptor,"rule expressionStatement");
		RewriteRuleSubtreeStream stream_selectionStatement=new RewriteRuleSubtreeStream(adaptor,"rule selectionStatement");
		RewriteRuleSubtreeStream stream_atomicStatement=new RewriteRuleSubtreeStream(adaptor,"rule atomicStatement");
		RewriteRuleSubtreeStream stream_iterationStatement=new RewriteRuleSubtreeStream(adaptor,"rule iterationStatement");
		RewriteRuleSubtreeStream stream_chooseStatement=new RewriteRuleSubtreeStream(adaptor,"rule chooseStatement");

		try {
			// CivlCParser.g:1282:5: ( labeledStatement -> ^( STATEMENT labeledStatement ) | compoundStatement -> ^( STATEMENT compoundStatement ) | expressionStatement -> ^( STATEMENT expressionStatement ) | selectionStatement -> ^( STATEMENT selectionStatement ) | iterationStatement -> ^( STATEMENT iterationStatement ) | jumpStatement -> ^( STATEMENT jumpStatement ) | whenStatement -> ^( STATEMENT whenStatement ) | chooseStatement -> ^( STATEMENT chooseStatement ) | atomicStatement -> ^( STATEMENT atomicStatement ) | datomicStatement -> ^( STATEMENT datomicStatement ) )
			int alt89=10;
			switch ( input.LA(1) ) {
			case IDENTIFIER:
				{
				int LA89_1 = input.LA(2);
				if ( (LA89_1==COLON) ) {
					alt89=1;
				}
				else if ( ((LA89_1 >= AMPERSAND && LA89_1 <= ASSIGN)||LA89_1==AT||(LA89_1 >= BITANDEQ && LA89_1 <= BITXOREQ)||LA89_1==COMMA||(LA89_1 >= DIV && LA89_1 <= DIVEQ)||(LA89_1 >= DOT && LA89_1 <= DOTDOT)||LA89_1==EQUALS||(LA89_1 >= GT && LA89_1 <= GTE)||LA89_1==IMPLIES||LA89_1==LEXCON||LA89_1==LPAREN||(LA89_1 >= LSQUARE && LA89_1 <= LTE)||(LA89_1 >= MINUSMINUS && LA89_1 <= NEQ)||LA89_1==OR||(LA89_1 >= PLUS && LA89_1 <= PLUSPLUS)||LA89_1==QMARK||LA89_1==SEMI||(LA89_1 >= SHIFTLEFT && LA89_1 <= SHIFTRIGHTEQ)||(LA89_1 >= STAR && LA89_1 <= STAREQ)||(LA89_1 >= SUB && LA89_1 <= SUBEQ)) ) {
					alt89=3;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 89, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case CASE:
			case DEFAULT:
				{
				alt89=1;
				}
				break;
			case LCURLY:
				{
				alt89=2;
				}
				break;
			case ALIGNOF:
			case AMPERSAND:
			case BIG_O:
			case CALLS:
			case CHARACTER_CONSTANT:
			case COLLECTIVE:
			case DERIV:
			case ELLIPSIS:
			case EXISTS:
			case FALSE:
			case FLOATING_CONSTANT:
			case FORALL:
			case GENERIC:
			case HERE:
			case INTEGER_CONSTANT:
			case LPAREN:
			case MINUSMINUS:
			case NOT:
			case PLUS:
			case PLUSPLUS:
			case PROCNULL:
			case RESULT:
			case SCOPEOF:
			case SELF:
			case SEMI:
			case SIZEOF:
			case SPAWN:
			case STAR:
			case STRING_LITERAL:
			case SUB:
			case TILDE:
			case TRUE:
			case UNIFORM:
			case ROOT:
				{
				alt89=3;
				}
				break;
			case IF:
			case SWITCH:
				{
				alt89=4;
				}
				break;
			case CIVLFOR:
			case DO:
			case FOR:
			case PARFOR:
			case WHILE:
				{
				alt89=5;
				}
				break;
			case BREAK:
			case CONTINUE:
			case GOTO:
			case RETURN:
				{
				alt89=6;
				}
				break;
			case WHEN:
				{
				alt89=7;
				}
				break;
			case CHOOSE:
				{
				alt89=8;
				}
				break;
			case CIVLATOMIC:
				{
				alt89=9;
				}
				break;
			case CIVLATOM:
				{
				alt89=10;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 89, 0, input);
				throw nvae;
			}
			switch (alt89) {
				case 1 :
					// CivlCParser.g:1282:7: labeledStatement
					{
					pushFollow(FOLLOW_labeledStatement_in_statement7328);
					labeledStatement391=labeledStatement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_labeledStatement.add(labeledStatement391.getTree());
					// AST REWRITE
					// elements: labeledStatement
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1282:24: -> ^( STATEMENT labeledStatement )
					{
						// CivlCParser.g:1282:27: ^( STATEMENT labeledStatement )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STATEMENT, "STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_labeledStatement.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1283:7: compoundStatement
					{
					pushFollow(FOLLOW_compoundStatement_in_statement7344);
					compoundStatement392=compoundStatement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_compoundStatement.add(compoundStatement392.getTree());
					// AST REWRITE
					// elements: compoundStatement
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1283:25: -> ^( STATEMENT compoundStatement )
					{
						// CivlCParser.g:1283:28: ^( STATEMENT compoundStatement )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STATEMENT, "STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_compoundStatement.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// CivlCParser.g:1284:7: expressionStatement
					{
					pushFollow(FOLLOW_expressionStatement_in_statement7360);
					expressionStatement393=expressionStatement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expressionStatement.add(expressionStatement393.getTree());
					// AST REWRITE
					// elements: expressionStatement
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1284:27: -> ^( STATEMENT expressionStatement )
					{
						// CivlCParser.g:1284:30: ^( STATEMENT expressionStatement )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STATEMENT, "STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_expressionStatement.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// CivlCParser.g:1285:7: selectionStatement
					{
					pushFollow(FOLLOW_selectionStatement_in_statement7376);
					selectionStatement394=selectionStatement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_selectionStatement.add(selectionStatement394.getTree());
					// AST REWRITE
					// elements: selectionStatement
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1285:26: -> ^( STATEMENT selectionStatement )
					{
						// CivlCParser.g:1285:29: ^( STATEMENT selectionStatement )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STATEMENT, "STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_selectionStatement.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 5 :
					// CivlCParser.g:1286:7: iterationStatement
					{
					pushFollow(FOLLOW_iterationStatement_in_statement7392);
					iterationStatement395=iterationStatement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_iterationStatement.add(iterationStatement395.getTree());
					// AST REWRITE
					// elements: iterationStatement
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1286:26: -> ^( STATEMENT iterationStatement )
					{
						// CivlCParser.g:1286:29: ^( STATEMENT iterationStatement )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STATEMENT, "STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_iterationStatement.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 6 :
					// CivlCParser.g:1287:7: jumpStatement
					{
					pushFollow(FOLLOW_jumpStatement_in_statement7408);
					jumpStatement396=jumpStatement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_jumpStatement.add(jumpStatement396.getTree());
					// AST REWRITE
					// elements: jumpStatement
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1287:21: -> ^( STATEMENT jumpStatement )
					{
						// CivlCParser.g:1287:24: ^( STATEMENT jumpStatement )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STATEMENT, "STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_jumpStatement.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 7 :
					// CivlCParser.g:1289:7: whenStatement
					{
					pushFollow(FOLLOW_whenStatement_in_statement7425);
					whenStatement397=whenStatement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_whenStatement.add(whenStatement397.getTree());
					// AST REWRITE
					// elements: whenStatement
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1289:21: -> ^( STATEMENT whenStatement )
					{
						// CivlCParser.g:1289:24: ^( STATEMENT whenStatement )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STATEMENT, "STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_whenStatement.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 8 :
					// CivlCParser.g:1290:7: chooseStatement
					{
					pushFollow(FOLLOW_chooseStatement_in_statement7441);
					chooseStatement398=chooseStatement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_chooseStatement.add(chooseStatement398.getTree());
					// AST REWRITE
					// elements: chooseStatement
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1290:23: -> ^( STATEMENT chooseStatement )
					{
						// CivlCParser.g:1290:26: ^( STATEMENT chooseStatement )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STATEMENT, "STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_chooseStatement.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 9 :
					// CivlCParser.g:1291:7: atomicStatement
					{
					pushFollow(FOLLOW_atomicStatement_in_statement7457);
					atomicStatement399=atomicStatement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_atomicStatement.add(atomicStatement399.getTree());
					// AST REWRITE
					// elements: atomicStatement
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1291:23: -> ^( STATEMENT atomicStatement )
					{
						// CivlCParser.g:1291:26: ^( STATEMENT atomicStatement )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STATEMENT, "STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_atomicStatement.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 10 :
					// CivlCParser.g:1292:7: datomicStatement
					{
					pushFollow(FOLLOW_datomicStatement_in_statement7473);
					datomicStatement400=datomicStatement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_datomicStatement.add(datomicStatement400.getTree());
					// AST REWRITE
					// elements: datomicStatement
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1292:24: -> ^( STATEMENT datomicStatement )
					{
						// CivlCParser.g:1292:27: ^( STATEMENT datomicStatement )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(STATEMENT, "STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_datomicStatement.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "statement"


	public static class statementWithScope_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "statementWithScope"
	// CivlCParser.g:1295:1: statementWithScope : statement ;
	public final OmpParser_CivlCParser.statementWithScope_return statementWithScope() throws RecognitionException {
		Symbols_stack.push(new Symbols_scope());

		OmpParser_CivlCParser.statementWithScope_return retval = new OmpParser_CivlCParser.statementWithScope_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope statement401 =null;



			Symbols_stack.peek().types = new HashSet<String>();
			Symbols_stack.peek().enumerationConstants = new HashSet<String>();
		        Symbols_stack.peek().isFunctionDefinition = false;

		try {
			// CivlCParser.g:1302:2: ( statement )
			// CivlCParser.g:1302:4: statement
			{
			root_0 = (Object)adaptor.nil();


			pushFollow(FOLLOW_statement_in_statementWithScope7505);
			statement401=statement();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, statement401.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
			Symbols_stack.pop();

		}
		return retval;
	}
	// $ANTLR end "statementWithScope"


	public static class labeledStatement_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "labeledStatement"
	// CivlCParser.g:1321:1: labeledStatement : ( IDENTIFIER COLON statement -> ^( IDENTIFIER_LABELED_STATEMENT IDENTIFIER statement ) | CASE constantExpression COLON statement -> ^( CASE_LABELED_STATEMENT CASE constantExpression statement ) | DEFAULT COLON statement -> ^( DEFAULT_LABELED_STATEMENT DEFAULT statement ) );
	public final OmpParser_CivlCParser.labeledStatement_return labeledStatement() throws RecognitionException {
		OmpParser_CivlCParser.labeledStatement_return retval = new OmpParser_CivlCParser.labeledStatement_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token IDENTIFIER402=null;
		Token COLON403=null;
		Token CASE405=null;
		Token COLON407=null;
		Token DEFAULT409=null;
		Token COLON410=null;
		ParserRuleReturnScope statement404 =null;
		ParserRuleReturnScope constantExpression406 =null;
		ParserRuleReturnScope statement408 =null;
		ParserRuleReturnScope statement411 =null;

		Object IDENTIFIER402_tree=null;
		Object COLON403_tree=null;
		Object CASE405_tree=null;
		Object COLON407_tree=null;
		Object DEFAULT409_tree=null;
		Object COLON410_tree=null;
		RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
		RewriteRuleTokenStream stream_DEFAULT=new RewriteRuleTokenStream(adaptor,"token DEFAULT");
		RewriteRuleTokenStream stream_CASE=new RewriteRuleTokenStream(adaptor,"token CASE");
		RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");
		RewriteRuleSubtreeStream stream_constantExpression=new RewriteRuleSubtreeStream(adaptor,"rule constantExpression");

		try {
			// CivlCParser.g:1322:5: ( IDENTIFIER COLON statement -> ^( IDENTIFIER_LABELED_STATEMENT IDENTIFIER statement ) | CASE constantExpression COLON statement -> ^( CASE_LABELED_STATEMENT CASE constantExpression statement ) | DEFAULT COLON statement -> ^( DEFAULT_LABELED_STATEMENT DEFAULT statement ) )
			int alt90=3;
			switch ( input.LA(1) ) {
			case IDENTIFIER:
				{
				alt90=1;
				}
				break;
			case CASE:
				{
				alt90=2;
				}
				break;
			case DEFAULT:
				{
				alt90=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 90, 0, input);
				throw nvae;
			}
			switch (alt90) {
				case 1 :
					// CivlCParser.g:1322:7: IDENTIFIER COLON statement
					{
					IDENTIFIER402=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_labeledStatement7521); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER402);

					COLON403=(Token)match(input,COLON,FOLLOW_COLON_in_labeledStatement7523); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COLON.add(COLON403);

					pushFollow(FOLLOW_statement_in_labeledStatement7525);
					statement404=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statement.add(statement404.getTree());
					// AST REWRITE
					// elements: IDENTIFIER, statement
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1323:7: -> ^( IDENTIFIER_LABELED_STATEMENT IDENTIFIER statement )
					{
						// CivlCParser.g:1323:10: ^( IDENTIFIER_LABELED_STATEMENT IDENTIFIER statement )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(IDENTIFIER_LABELED_STATEMENT, "IDENTIFIER_LABELED_STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
						adaptor.addChild(root_1, stream_statement.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1324:7: CASE constantExpression COLON statement
					{
					CASE405=(Token)match(input,CASE,FOLLOW_CASE_in_labeledStatement7549); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CASE.add(CASE405);

					pushFollow(FOLLOW_constantExpression_in_labeledStatement7551);
					constantExpression406=constantExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_constantExpression.add(constantExpression406.getTree());
					COLON407=(Token)match(input,COLON,FOLLOW_COLON_in_labeledStatement7553); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COLON.add(COLON407);

					pushFollow(FOLLOW_statement_in_labeledStatement7555);
					statement408=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statement.add(statement408.getTree());
					// AST REWRITE
					// elements: CASE, statement, constantExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1325:7: -> ^( CASE_LABELED_STATEMENT CASE constantExpression statement )
					{
						// CivlCParser.g:1325:10: ^( CASE_LABELED_STATEMENT CASE constantExpression statement )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CASE_LABELED_STATEMENT, "CASE_LABELED_STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_CASE.nextNode());
						adaptor.addChild(root_1, stream_constantExpression.nextTree());
						adaptor.addChild(root_1, stream_statement.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// CivlCParser.g:1326:7: DEFAULT COLON statement
					{
					DEFAULT409=(Token)match(input,DEFAULT,FOLLOW_DEFAULT_in_labeledStatement7581); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DEFAULT.add(DEFAULT409);

					COLON410=(Token)match(input,COLON,FOLLOW_COLON_in_labeledStatement7583); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COLON.add(COLON410);

					pushFollow(FOLLOW_statement_in_labeledStatement7585);
					statement411=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statement.add(statement411.getTree());
					// AST REWRITE
					// elements: statement, DEFAULT
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1327:7: -> ^( DEFAULT_LABELED_STATEMENT DEFAULT statement )
					{
						// CivlCParser.g:1327:10: ^( DEFAULT_LABELED_STATEMENT DEFAULT statement )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DEFAULT_LABELED_STATEMENT, "DEFAULT_LABELED_STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_DEFAULT.nextNode());
						adaptor.addChild(root_1, stream_statement.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "labeledStatement"


	public static class compoundStatement_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "compoundStatement"
	// CivlCParser.g:1336:1: compoundStatement : LCURLY ( RCURLY -> ^( COMPOUND_STATEMENT LCURLY ABSENT RCURLY ) | blockItemList RCURLY -> ^( COMPOUND_STATEMENT LCURLY blockItemList RCURLY ) ) ;
	public final OmpParser_CivlCParser.compoundStatement_return compoundStatement() throws RecognitionException {
		Symbols_stack.push(new Symbols_scope());
		DeclarationScope_stack.push(new DeclarationScope_scope());

		OmpParser_CivlCParser.compoundStatement_return retval = new OmpParser_CivlCParser.compoundStatement_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LCURLY412=null;
		Token RCURLY413=null;
		Token RCURLY415=null;
		ParserRuleReturnScope blockItemList414 =null;

		Object LCURLY412_tree=null;
		Object RCURLY413_tree=null;
		Object RCURLY415_tree=null;
		RewriteRuleTokenStream stream_LCURLY=new RewriteRuleTokenStream(adaptor,"token LCURLY");
		RewriteRuleTokenStream stream_RCURLY=new RewriteRuleTokenStream(adaptor,"token RCURLY");
		RewriteRuleSubtreeStream stream_blockItemList=new RewriteRuleSubtreeStream(adaptor,"rule blockItemList");


			Symbols_stack.peek().types = new HashSet<String>();
			Symbols_stack.peek().enumerationConstants = new HashSet<String>();
		        Symbols_stack.peek().isFunctionDefinition = false;
		        DeclarationScope_stack.peek().isTypedef = false;
		        DeclarationScope_stack.peek().typedefNameUsed = false;	

		try {
			// CivlCParser.g:1346:5: ( LCURLY ( RCURLY -> ^( COMPOUND_STATEMENT LCURLY ABSENT RCURLY ) | blockItemList RCURLY -> ^( COMPOUND_STATEMENT LCURLY blockItemList RCURLY ) ) )
			// CivlCParser.g:1346:7: LCURLY ( RCURLY -> ^( COMPOUND_STATEMENT LCURLY ABSENT RCURLY ) | blockItemList RCURLY -> ^( COMPOUND_STATEMENT LCURLY blockItemList RCURLY ) )
			{
			LCURLY412=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_compoundStatement7635); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY412);

			// CivlCParser.g:1347:7: ( RCURLY -> ^( COMPOUND_STATEMENT LCURLY ABSENT RCURLY ) | blockItemList RCURLY -> ^( COMPOUND_STATEMENT LCURLY blockItemList RCURLY ) )
			int alt91=2;
			int LA91_0 = input.LA(1);
			if ( (LA91_0==RCURLY) ) {
				alt91=1;
			}
			else if ( ((LA91_0 >= ABSTRACT && LA91_0 <= AMPERSAND)||(LA91_0 >= ATOMIC && LA91_0 <= BIG_O)||(LA91_0 >= BOOL && LA91_0 <= BREAK)||(LA91_0 >= CALLS && LA91_0 <= CASE)||(LA91_0 >= CHAR && LA91_0 <= COLLECTIVE)||(LA91_0 >= COMPLEX && LA91_0 <= CONST)||(LA91_0 >= CONTINUE && LA91_0 <= DEFAULT)||(LA91_0 >= DERIV && LA91_0 <= DEVICE)||(LA91_0 >= DO && LA91_0 <= DOMAIN)||LA91_0==DOUBLE||LA91_0==ELLIPSIS||LA91_0==ENUM||(LA91_0 >= EXISTS && LA91_0 <= EXTERN)||(LA91_0 >= FALSE && LA91_0 <= FORALL)||(LA91_0 >= GENERIC && LA91_0 <= GOTO)||LA91_0==HERE||(LA91_0 >= IDENTIFIER && LA91_0 <= IF)||(LA91_0 >= INLINE && LA91_0 <= INTEGER_CONSTANT)||LA91_0==LCURLY||(LA91_0 >= LONG && LA91_0 <= LPAREN)||LA91_0==MINUSMINUS||(LA91_0 >= NORETURN && LA91_0 <= NOT)||LA91_0==OUTPUT||LA91_0==PARFOR||LA91_0==PLUS||LA91_0==PLUSPLUS||(LA91_0 >= PRAGMA && LA91_0 <= PROCNULL)||LA91_0==PURE||LA91_0==RANGE||(LA91_0 >= REAL && LA91_0 <= REGISTER)||(LA91_0 >= RESTRICT && LA91_0 <= RETURN)||LA91_0==SCOPEOF||(LA91_0 >= SELF && LA91_0 <= SHARED)||(LA91_0 >= SHORT && LA91_0 <= STAR)||(LA91_0 >= STATIC && LA91_0 <= SUB)||(LA91_0 >= SWITCH && LA91_0 <= UNSIGNED)||(LA91_0 >= VOID && LA91_0 <= WHILE)||LA91_0==ROOT) ) {
				alt91=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 91, 0, input);
				throw nvae;
			}

			switch (alt91) {
				case 1 :
					// CivlCParser.g:1347:9: RCURLY
					{
					RCURLY413=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_compoundStatement7645); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY413);

					// AST REWRITE
					// elements: LCURLY, RCURLY
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1348:9: -> ^( COMPOUND_STATEMENT LCURLY ABSENT RCURLY )
					{
						// CivlCParser.g:1348:12: ^( COMPOUND_STATEMENT LCURLY ABSENT RCURLY )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(COMPOUND_STATEMENT, "COMPOUND_STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_LCURLY.nextNode());
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_1, stream_RCURLY.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1349:9: blockItemList RCURLY
					{
					pushFollow(FOLLOW_blockItemList_in_compoundStatement7675);
					blockItemList414=blockItemList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_blockItemList.add(blockItemList414.getTree());
					RCURLY415=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_compoundStatement7677); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY415);

					// AST REWRITE
					// elements: blockItemList, RCURLY, LCURLY
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1350:9: -> ^( COMPOUND_STATEMENT LCURLY blockItemList RCURLY )
					{
						// CivlCParser.g:1350:12: ^( COMPOUND_STATEMENT LCURLY blockItemList RCURLY )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(COMPOUND_STATEMENT, "COMPOUND_STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_LCURLY.nextNode());
						adaptor.addChild(root_1, stream_blockItemList.nextTree());
						adaptor.addChild(root_1, stream_RCURLY.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
			Symbols_stack.pop();
			DeclarationScope_stack.pop();

		}
		return retval;
	}
	// $ANTLR end "compoundStatement"


	public static class blockItemList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "blockItemList"
	// CivlCParser.g:1355:1: blockItemList : ( blockItem )+ -> ^( BLOCK_ITEM_LIST ( blockItem )+ ) ;
	public final OmpParser_CivlCParser.blockItemList_return blockItemList() throws RecognitionException {
		OmpParser_CivlCParser.blockItemList_return retval = new OmpParser_CivlCParser.blockItemList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope blockItem416 =null;

		RewriteRuleSubtreeStream stream_blockItem=new RewriteRuleSubtreeStream(adaptor,"rule blockItem");

		try {
			// CivlCParser.g:1356:5: ( ( blockItem )+ -> ^( BLOCK_ITEM_LIST ( blockItem )+ ) )
			// CivlCParser.g:1356:7: ( blockItem )+
			{
			// CivlCParser.g:1356:7: ( blockItem )+
			int cnt92=0;
			loop92:
			while (true) {
				int alt92=2;
				int LA92_0 = input.LA(1);
				if ( ((LA92_0 >= ABSTRACT && LA92_0 <= AMPERSAND)||(LA92_0 >= ATOMIC && LA92_0 <= BIG_O)||(LA92_0 >= BOOL && LA92_0 <= BREAK)||(LA92_0 >= CALLS && LA92_0 <= CASE)||(LA92_0 >= CHAR && LA92_0 <= COLLECTIVE)||(LA92_0 >= COMPLEX && LA92_0 <= CONST)||(LA92_0 >= CONTINUE && LA92_0 <= DEFAULT)||(LA92_0 >= DERIV && LA92_0 <= DEVICE)||(LA92_0 >= DO && LA92_0 <= DOMAIN)||LA92_0==DOUBLE||LA92_0==ELLIPSIS||LA92_0==ENUM||(LA92_0 >= EXISTS && LA92_0 <= EXTERN)||(LA92_0 >= FALSE && LA92_0 <= FORALL)||(LA92_0 >= GENERIC && LA92_0 <= GOTO)||LA92_0==HERE||(LA92_0 >= IDENTIFIER && LA92_0 <= IF)||(LA92_0 >= INLINE && LA92_0 <= INTEGER_CONSTANT)||LA92_0==LCURLY||(LA92_0 >= LONG && LA92_0 <= LPAREN)||LA92_0==MINUSMINUS||(LA92_0 >= NORETURN && LA92_0 <= NOT)||LA92_0==OUTPUT||LA92_0==PARFOR||LA92_0==PLUS||LA92_0==PLUSPLUS||(LA92_0 >= PRAGMA && LA92_0 <= PROCNULL)||LA92_0==PURE||LA92_0==RANGE||(LA92_0 >= REAL && LA92_0 <= REGISTER)||(LA92_0 >= RESTRICT && LA92_0 <= RETURN)||LA92_0==SCOPEOF||(LA92_0 >= SELF && LA92_0 <= SHARED)||(LA92_0 >= SHORT && LA92_0 <= STAR)||(LA92_0 >= STATIC && LA92_0 <= SUB)||(LA92_0 >= SWITCH && LA92_0 <= UNSIGNED)||(LA92_0 >= VOID && LA92_0 <= WHILE)||LA92_0==ROOT) ) {
					alt92=1;
				}

				switch (alt92) {
				case 1 :
					// CivlCParser.g:1356:7: blockItem
					{
					pushFollow(FOLLOW_blockItem_in_blockItemList7724);
					blockItem416=blockItem();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_blockItem.add(blockItem416.getTree());
					}
					break;

				default :
					if ( cnt92 >= 1 ) break loop92;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(92, input);
					throw eee;
				}
				cnt92++;
			}

			// AST REWRITE
			// elements: blockItem
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1356:18: -> ^( BLOCK_ITEM_LIST ( blockItem )+ )
			{
				// CivlCParser.g:1356:21: ^( BLOCK_ITEM_LIST ( blockItem )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(BLOCK_ITEM_LIST, "BLOCK_ITEM_LIST"), root_1);
				if ( !(stream_blockItem.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_blockItem.hasNext() ) {
					adaptor.addChild(root_1, stream_blockItem.nextTree());
				}
				stream_blockItem.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "blockItemList"


	public static class expressionStatement_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "expressionStatement"
	// CivlCParser.g:1366:1: expressionStatement : ( expression SEMI -> ^( EXPRESSION_STATEMENT expression SEMI ) | SEMI -> ^( EXPRESSION_STATEMENT ABSENT SEMI ) );
	public final OmpParser_CivlCParser.expressionStatement_return expressionStatement() throws RecognitionException {
		OmpParser_CivlCParser.expressionStatement_return retval = new OmpParser_CivlCParser.expressionStatement_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SEMI418=null;
		Token SEMI419=null;
		ParserRuleReturnScope expression417 =null;

		Object SEMI418_tree=null;
		Object SEMI419_tree=null;
		RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");

		try {
			// CivlCParser.g:1367:5: ( expression SEMI -> ^( EXPRESSION_STATEMENT expression SEMI ) | SEMI -> ^( EXPRESSION_STATEMENT ABSENT SEMI ) )
			int alt93=2;
			int LA93_0 = input.LA(1);
			if ( ((LA93_0 >= ALIGNOF && LA93_0 <= AMPERSAND)||LA93_0==BIG_O||LA93_0==CALLS||LA93_0==CHARACTER_CONSTANT||LA93_0==COLLECTIVE||LA93_0==DERIV||LA93_0==ELLIPSIS||LA93_0==EXISTS||LA93_0==FALSE||LA93_0==FLOATING_CONSTANT||LA93_0==FORALL||LA93_0==GENERIC||LA93_0==HERE||LA93_0==IDENTIFIER||LA93_0==INTEGER_CONSTANT||LA93_0==LPAREN||LA93_0==MINUSMINUS||LA93_0==NOT||LA93_0==PLUS||LA93_0==PLUSPLUS||LA93_0==PROCNULL||LA93_0==RESULT||LA93_0==SCOPEOF||LA93_0==SELF||(LA93_0 >= SIZEOF && LA93_0 <= STAR)||LA93_0==STRING_LITERAL||LA93_0==SUB||(LA93_0 >= TILDE && LA93_0 <= TRUE)||LA93_0==UNIFORM||LA93_0==ROOT) ) {
				alt93=1;
			}
			else if ( (LA93_0==SEMI) ) {
				alt93=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 93, 0, input);
				throw nvae;
			}

			switch (alt93) {
				case 1 :
					// CivlCParser.g:1367:7: expression SEMI
					{
					pushFollow(FOLLOW_expression_in_expressionStatement7755);
					expression417=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression417.getTree());
					SEMI418=(Token)match(input,SEMI,FOLLOW_SEMI_in_expressionStatement7757); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMI.add(SEMI418);

					// AST REWRITE
					// elements: SEMI, expression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1367:23: -> ^( EXPRESSION_STATEMENT expression SEMI )
					{
						// CivlCParser.g:1367:26: ^( EXPRESSION_STATEMENT expression SEMI )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(EXPRESSION_STATEMENT, "EXPRESSION_STATEMENT"), root_1);
						adaptor.addChild(root_1, stream_expression.nextTree());
						adaptor.addChild(root_1, stream_SEMI.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1368:7: SEMI
					{
					SEMI419=(Token)match(input,SEMI,FOLLOW_SEMI_in_expressionStatement7775); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMI.add(SEMI419);

					// AST REWRITE
					// elements: SEMI
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1368:12: -> ^( EXPRESSION_STATEMENT ABSENT SEMI )
					{
						// CivlCParser.g:1368:15: ^( EXPRESSION_STATEMENT ABSENT SEMI )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(EXPRESSION_STATEMENT, "EXPRESSION_STATEMENT"), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
						adaptor.addChild(root_1, stream_SEMI.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "expressionStatement"


	public static class selectionStatement_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "selectionStatement"
	// CivlCParser.g:1383:1: selectionStatement : ( IF LPAREN expression RPAREN s1= statementWithScope ( ( ELSE )=> ELSE s2= statementWithScope -> ^( IF expression $s1 $s2) | -> ^( IF expression $s1 ABSENT ) ) | SWITCH LPAREN expression RPAREN s= statementWithScope -> ^( SWITCH expression $s) );
	public final OmpParser_CivlCParser.selectionStatement_return selectionStatement() throws RecognitionException {
		Symbols_stack.push(new Symbols_scope());

		OmpParser_CivlCParser.selectionStatement_return retval = new OmpParser_CivlCParser.selectionStatement_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token IF420=null;
		Token LPAREN421=null;
		Token RPAREN423=null;
		Token ELSE424=null;
		Token SWITCH425=null;
		Token LPAREN426=null;
		Token RPAREN428=null;
		ParserRuleReturnScope s1 =null;
		ParserRuleReturnScope s2 =null;
		ParserRuleReturnScope s =null;
		ParserRuleReturnScope expression422 =null;
		ParserRuleReturnScope expression427 =null;

		Object IF420_tree=null;
		Object LPAREN421_tree=null;
		Object RPAREN423_tree=null;
		Object ELSE424_tree=null;
		Object SWITCH425_tree=null;
		Object LPAREN426_tree=null;
		Object RPAREN428_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_SWITCH=new RewriteRuleTokenStream(adaptor,"token SWITCH");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleTokenStream stream_IF=new RewriteRuleTokenStream(adaptor,"token IF");
		RewriteRuleTokenStream stream_ELSE=new RewriteRuleTokenStream(adaptor,"token ELSE");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_statementWithScope=new RewriteRuleSubtreeStream(adaptor,"rule statementWithScope");


			Symbols_stack.peek().types = new HashSet<String>();
			Symbols_stack.peek().enumerationConstants = new HashSet<String>();
		        Symbols_stack.peek().isFunctionDefinition = false;

		try {
			// CivlCParser.g:1390:5: ( IF LPAREN expression RPAREN s1= statementWithScope ( ( ELSE )=> ELSE s2= statementWithScope -> ^( IF expression $s1 $s2) | -> ^( IF expression $s1 ABSENT ) ) | SWITCH LPAREN expression RPAREN s= statementWithScope -> ^( SWITCH expression $s) )
			int alt95=2;
			int LA95_0 = input.LA(1);
			if ( (LA95_0==IF) ) {
				alt95=1;
			}
			else if ( (LA95_0==SWITCH) ) {
				alt95=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 95, 0, input);
				throw nvae;
			}

			switch (alt95) {
				case 1 :
					// CivlCParser.g:1390:7: IF LPAREN expression RPAREN s1= statementWithScope ( ( ELSE )=> ELSE s2= statementWithScope -> ^( IF expression $s1 $s2) | -> ^( IF expression $s1 ABSENT ) )
					{
					IF420=(Token)match(input,IF,FOLLOW_IF_in_selectionStatement7814); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IF.add(IF420);

					LPAREN421=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_selectionStatement7816); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN421);

					pushFollow(FOLLOW_expression_in_selectionStatement7818);
					expression422=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression422.getTree());
					RPAREN423=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_selectionStatement7820); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN423);

					pushFollow(FOLLOW_statementWithScope_in_selectionStatement7824);
					s1=statementWithScope();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statementWithScope.add(s1.getTree());
					// CivlCParser.g:1391:9: ( ( ELSE )=> ELSE s2= statementWithScope -> ^( IF expression $s1 $s2) | -> ^( IF expression $s1 ABSENT ) )
					int alt94=2;
					int LA94_0 = input.LA(1);
					if ( (LA94_0==ELSE) ) {
						int LA94_1 = input.LA(2);
						if ( (synpred7_CivlCParser()) ) {
							alt94=1;
						}
						else if ( (true) ) {
							alt94=2;
						}

					}
					else if ( (LA94_0==EOF||(LA94_0 >= ABSTRACT && LA94_0 <= AMPERSAND)||(LA94_0 >= ATOMIC && LA94_0 <= BIG_O)||(LA94_0 >= BOOL && LA94_0 <= BREAK)||(LA94_0 >= CALLS && LA94_0 <= CASE)||(LA94_0 >= CHAR && LA94_0 <= COLLECTIVE)||(LA94_0 >= COMPLEX && LA94_0 <= CONST)||(LA94_0 >= CONTINUE && LA94_0 <= DEFAULT)||(LA94_0 >= DERIV && LA94_0 <= DEVICE)||(LA94_0 >= DO && LA94_0 <= DOMAIN)||LA94_0==DOUBLE||LA94_0==ELLIPSIS||LA94_0==ENUM||(LA94_0 >= EXISTS && LA94_0 <= EXTERN)||(LA94_0 >= FALSE && LA94_0 <= FORALL)||(LA94_0 >= GENERIC && LA94_0 <= GOTO)||LA94_0==HERE||(LA94_0 >= IDENTIFIER && LA94_0 <= IF)||(LA94_0 >= INLINE && LA94_0 <= INTEGER_CONSTANT)||LA94_0==LCURLY||(LA94_0 >= LONG && LA94_0 <= LPAREN)||LA94_0==MINUSMINUS||(LA94_0 >= NORETURN && LA94_0 <= NOT)||LA94_0==OUTPUT||LA94_0==PARFOR||LA94_0==PLUS||LA94_0==PLUSPLUS||(LA94_0 >= PRAGMA && LA94_0 <= PROCNULL)||LA94_0==PURE||(LA94_0 >= RANGE && LA94_0 <= RCURLY)||(LA94_0 >= REAL && LA94_0 <= REGISTER)||(LA94_0 >= RESTRICT && LA94_0 <= RETURN)||LA94_0==SCOPEOF||(LA94_0 >= SELF && LA94_0 <= SHARED)||(LA94_0 >= SHORT && LA94_0 <= STAR)||(LA94_0 >= STATIC && LA94_0 <= SUB)||(LA94_0 >= SWITCH && LA94_0 <= UNSIGNED)||(LA94_0 >= VOID && LA94_0 <= WHILE)||LA94_0==ROOT) ) {
						alt94=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 94, 0, input);
						throw nvae;
					}

					switch (alt94) {
						case 1 :
							// CivlCParser.g:1391:11: ( ELSE )=> ELSE s2= statementWithScope
							{
							ELSE424=(Token)match(input,ELSE,FOLLOW_ELSE_in_selectionStatement7841); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_ELSE.add(ELSE424);

							pushFollow(FOLLOW_statementWithScope_in_selectionStatement7845);
							s2=statementWithScope();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_statementWithScope.add(s2.getTree());
							// AST REWRITE
							// elements: s2, expression, s1, IF
							// token labels: 
							// rule labels: retval, s2, s1
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
							RewriteRuleSubtreeStream stream_s2=new RewriteRuleSubtreeStream(adaptor,"rule s2",s2!=null?s2.getTree():null);
							RewriteRuleSubtreeStream stream_s1=new RewriteRuleSubtreeStream(adaptor,"rule s1",s1!=null?s1.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 1392:11: -> ^( IF expression $s1 $s2)
							{
								// CivlCParser.g:1392:14: ^( IF expression $s1 $s2)
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot(stream_IF.nextNode(), root_1);
								adaptor.addChild(root_1, stream_expression.nextTree());
								adaptor.addChild(root_1, stream_s1.nextTree());
								adaptor.addChild(root_1, stream_s2.nextTree());
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;
						case 2 :
							// CivlCParser.g:1393:11: 
							{
							// AST REWRITE
							// elements: s1, IF, expression
							// token labels: 
							// rule labels: retval, s1
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
							RewriteRuleSubtreeStream stream_s1=new RewriteRuleSubtreeStream(adaptor,"rule s1",s1!=null?s1.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 1393:11: -> ^( IF expression $s1 ABSENT )
							{
								// CivlCParser.g:1393:14: ^( IF expression $s1 ABSENT )
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot(stream_IF.nextNode(), root_1);
								adaptor.addChild(root_1, stream_expression.nextTree());
								adaptor.addChild(root_1, stream_s1.nextTree());
								adaptor.addChild(root_1, (Object)adaptor.create(ABSENT, "ABSENT"));
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;

					}

					}
					break;
				case 2 :
					// CivlCParser.g:1395:7: SWITCH LPAREN expression RPAREN s= statementWithScope
					{
					SWITCH425=(Token)match(input,SWITCH,FOLLOW_SWITCH_in_selectionStatement7910); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SWITCH.add(SWITCH425);

					LPAREN426=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_selectionStatement7912); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN426);

					pushFollow(FOLLOW_expression_in_selectionStatement7914);
					expression427=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression427.getTree());
					RPAREN428=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_selectionStatement7916); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN428);

					pushFollow(FOLLOW_statementWithScope_in_selectionStatement7920);
					s=statementWithScope();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statementWithScope.add(s.getTree());
					// AST REWRITE
					// elements: s, expression, SWITCH
					// token labels: 
					// rule labels: retval, s
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"rule s",s!=null?s.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1396:7: -> ^( SWITCH expression $s)
					{
						// CivlCParser.g:1396:10: ^( SWITCH expression $s)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_SWITCH.nextNode(), root_1);
						adaptor.addChild(root_1, stream_expression.nextTree());
						adaptor.addChild(root_1, stream_s.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
			Symbols_stack.pop();

		}
		return retval;
	}
	// $ANTLR end "selectionStatement"


	public static class iterationStatement_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "iterationStatement"
	// CivlCParser.g:1418:1: iterationStatement : ( WHILE LPAREN expression RPAREN invariant_opt s= statementWithScope -> ^( WHILE expression $s invariant_opt ) | DO s= statementWithScope WHILE LPAREN expression RPAREN invariant_opt SEMI -> ^( DO $s expression invariant_opt ) | FOR LPAREN (d= declaration e1= expression_opt SEMI e2= expression_opt RPAREN i= invariant_opt s= statementWithScope -> ^( FOR $d $e1 $e2 $s $i) |e0= expression_opt SEMI e1= expression_opt SEMI e2= expression_opt RPAREN i= invariant_opt s= statementWithScope -> ^( FOR $e0 $e1 $e2 $s $i) ) | (f= CIVLFOR |f= PARFOR ) LPAREN t= typeName_opt v= identifierList COLON e= expression RPAREN i= invariant_opt s= statementWithScope -> ^( $f $t $v $e $s $i) );
	public final OmpParser_CivlCParser.iterationStatement_return iterationStatement() throws RecognitionException {
		Symbols_stack.push(new Symbols_scope());

		OmpParser_CivlCParser.iterationStatement_return retval = new OmpParser_CivlCParser.iterationStatement_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token f=null;
		Token WHILE429=null;
		Token LPAREN430=null;
		Token RPAREN432=null;
		Token DO434=null;
		Token WHILE435=null;
		Token LPAREN436=null;
		Token RPAREN438=null;
		Token SEMI440=null;
		Token FOR441=null;
		Token LPAREN442=null;
		Token SEMI443=null;
		Token RPAREN444=null;
		Token SEMI445=null;
		Token SEMI446=null;
		Token RPAREN447=null;
		Token LPAREN448=null;
		Token COLON449=null;
		Token RPAREN450=null;
		ParserRuleReturnScope s =null;
		ParserRuleReturnScope d =null;
		ParserRuleReturnScope e1 =null;
		ParserRuleReturnScope e2 =null;
		ParserRuleReturnScope i =null;
		ParserRuleReturnScope e0 =null;
		ParserRuleReturnScope t =null;
		ParserRuleReturnScope v =null;
		ParserRuleReturnScope e =null;
		ParserRuleReturnScope expression431 =null;
		ParserRuleReturnScope invariant_opt433 =null;
		ParserRuleReturnScope expression437 =null;
		ParserRuleReturnScope invariant_opt439 =null;

		Object f_tree=null;
		Object WHILE429_tree=null;
		Object LPAREN430_tree=null;
		Object RPAREN432_tree=null;
		Object DO434_tree=null;
		Object WHILE435_tree=null;
		Object LPAREN436_tree=null;
		Object RPAREN438_tree=null;
		Object SEMI440_tree=null;
		Object FOR441_tree=null;
		Object LPAREN442_tree=null;
		Object SEMI443_tree=null;
		Object RPAREN444_tree=null;
		Object SEMI445_tree=null;
		Object SEMI446_tree=null;
		Object RPAREN447_tree=null;
		Object LPAREN448_tree=null;
		Object COLON449_tree=null;
		Object RPAREN450_tree=null;
		RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
		RewriteRuleTokenStream stream_FOR=new RewriteRuleTokenStream(adaptor,"token FOR");
		RewriteRuleTokenStream stream_DO=new RewriteRuleTokenStream(adaptor,"token DO");
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_PARFOR=new RewriteRuleTokenStream(adaptor,"token PARFOR");
		RewriteRuleTokenStream stream_CIVLFOR=new RewriteRuleTokenStream(adaptor,"token CIVLFOR");
		RewriteRuleTokenStream stream_WHILE=new RewriteRuleTokenStream(adaptor,"token WHILE");
		RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_declaration=new RewriteRuleSubtreeStream(adaptor,"rule declaration");
		RewriteRuleSubtreeStream stream_identifierList=new RewriteRuleSubtreeStream(adaptor,"rule identifierList");
		RewriteRuleSubtreeStream stream_expression_opt=new RewriteRuleSubtreeStream(adaptor,"rule expression_opt");
		RewriteRuleSubtreeStream stream_invariant_opt=new RewriteRuleSubtreeStream(adaptor,"rule invariant_opt");
		RewriteRuleSubtreeStream stream_statementWithScope=new RewriteRuleSubtreeStream(adaptor,"rule statementWithScope");
		RewriteRuleSubtreeStream stream_typeName_opt=new RewriteRuleSubtreeStream(adaptor,"rule typeName_opt");


			Symbols_stack.peek().types = new HashSet<String>();
			Symbols_stack.peek().enumerationConstants = new HashSet<String>();
		        Symbols_stack.peek().isFunctionDefinition = false;

		try {
			// CivlCParser.g:1425:2: ( WHILE LPAREN expression RPAREN invariant_opt s= statementWithScope -> ^( WHILE expression $s invariant_opt ) | DO s= statementWithScope WHILE LPAREN expression RPAREN invariant_opt SEMI -> ^( DO $s expression invariant_opt ) | FOR LPAREN (d= declaration e1= expression_opt SEMI e2= expression_opt RPAREN i= invariant_opt s= statementWithScope -> ^( FOR $d $e1 $e2 $s $i) |e0= expression_opt SEMI e1= expression_opt SEMI e2= expression_opt RPAREN i= invariant_opt s= statementWithScope -> ^( FOR $e0 $e1 $e2 $s $i) ) | (f= CIVLFOR |f= PARFOR ) LPAREN t= typeName_opt v= identifierList COLON e= expression RPAREN i= invariant_opt s= statementWithScope -> ^( $f $t $v $e $s $i) )
			int alt98=4;
			switch ( input.LA(1) ) {
			case WHILE:
				{
				alt98=1;
				}
				break;
			case DO:
				{
				alt98=2;
				}
				break;
			case FOR:
				{
				alt98=3;
				}
				break;
			case CIVLFOR:
			case PARFOR:
				{
				alt98=4;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 98, 0, input);
				throw nvae;
			}
			switch (alt98) {
				case 1 :
					// CivlCParser.g:1425:4: WHILE LPAREN expression RPAREN invariant_opt s= statementWithScope
					{
					WHILE429=(Token)match(input,WHILE,FOLLOW_WHILE_in_iterationStatement7963); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_WHILE.add(WHILE429);

					LPAREN430=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_iterationStatement7965); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN430);

					pushFollow(FOLLOW_expression_in_iterationStatement7967);
					expression431=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression431.getTree());
					RPAREN432=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_iterationStatement7969); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN432);

					pushFollow(FOLLOW_invariant_opt_in_iterationStatement7971);
					invariant_opt433=invariant_opt();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_invariant_opt.add(invariant_opt433.getTree());
					pushFollow(FOLLOW_statementWithScope_in_iterationStatement7979);
					s=statementWithScope();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statementWithScope.add(s.getTree());
					// AST REWRITE
					// elements: invariant_opt, expression, WHILE, s
					// token labels: 
					// rule labels: retval, s
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"rule s",s!=null?s.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1427:4: -> ^( WHILE expression $s invariant_opt )
					{
						// CivlCParser.g:1427:7: ^( WHILE expression $s invariant_opt )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_WHILE.nextNode(), root_1);
						adaptor.addChild(root_1, stream_expression.nextTree());
						adaptor.addChild(root_1, stream_s.nextTree());
						adaptor.addChild(root_1, stream_invariant_opt.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1428:4: DO s= statementWithScope WHILE LPAREN expression RPAREN invariant_opt SEMI
					{
					DO434=(Token)match(input,DO,FOLLOW_DO_in_iterationStatement8000); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DO.add(DO434);

					pushFollow(FOLLOW_statementWithScope_in_iterationStatement8004);
					s=statementWithScope();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statementWithScope.add(s.getTree());
					WHILE435=(Token)match(input,WHILE,FOLLOW_WHILE_in_iterationStatement8006); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_WHILE.add(WHILE435);

					LPAREN436=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_iterationStatement8008); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN436);

					pushFollow(FOLLOW_expression_in_iterationStatement8010);
					expression437=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression437.getTree());
					RPAREN438=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_iterationStatement8012); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN438);

					pushFollow(FOLLOW_invariant_opt_in_iterationStatement8018);
					invariant_opt439=invariant_opt();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_invariant_opt.add(invariant_opt439.getTree());
					SEMI440=(Token)match(input,SEMI,FOLLOW_SEMI_in_iterationStatement8020); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMI.add(SEMI440);

					// AST REWRITE
					// elements: s, invariant_opt, expression, DO
					// token labels: 
					// rule labels: retval, s
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"rule s",s!=null?s.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1430:4: -> ^( DO $s expression invariant_opt )
					{
						// CivlCParser.g:1430:7: ^( DO $s expression invariant_opt )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_DO.nextNode(), root_1);
						adaptor.addChild(root_1, stream_s.nextTree());
						adaptor.addChild(root_1, stream_expression.nextTree());
						adaptor.addChild(root_1, stream_invariant_opt.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// CivlCParser.g:1431:4: FOR LPAREN (d= declaration e1= expression_opt SEMI e2= expression_opt RPAREN i= invariant_opt s= statementWithScope -> ^( FOR $d $e1 $e2 $s $i) |e0= expression_opt SEMI e1= expression_opt SEMI e2= expression_opt RPAREN i= invariant_opt s= statementWithScope -> ^( FOR $e0 $e1 $e2 $s $i) )
					{
					FOR441=(Token)match(input,FOR,FOLLOW_FOR_in_iterationStatement8041); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_FOR.add(FOR441);

					LPAREN442=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_iterationStatement8043); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN442);

					// CivlCParser.g:1432:4: (d= declaration e1= expression_opt SEMI e2= expression_opt RPAREN i= invariant_opt s= statementWithScope -> ^( FOR $d $e1 $e2 $s $i) |e0= expression_opt SEMI e1= expression_opt SEMI e2= expression_opt RPAREN i= invariant_opt s= statementWithScope -> ^( FOR $e0 $e1 $e2 $s $i) )
					int alt96=2;
					switch ( input.LA(1) ) {
					case ABSTRACT:
					case ALIGNAS:
					case ATOMIC:
					case AUTO:
					case BOOL:
					case CHAR:
					case COMPLEX:
					case CONST:
					case DEVICE:
					case DOMAIN:
					case DOUBLE:
					case ENUM:
					case EXTERN:
					case FATOMIC:
					case FLOAT:
					case GLOBAL:
					case INLINE:
					case INPUT:
					case INT:
					case LONG:
					case NORETURN:
					case OUTPUT:
					case PURE:
					case RANGE:
					case REAL:
					case REGISTER:
					case RESTRICT:
					case SHARED:
					case SHORT:
					case SIGNED:
					case STATIC:
					case STATICASSERT:
					case STRUCT:
					case SYSTEM:
					case THREADLOCAL:
					case TYPEDEF:
					case TYPEOF:
					case UNION:
					case UNSIGNED:
					case VOID:
					case VOLATILE:
						{
						alt96=1;
						}
						break;
					case IDENTIFIER:
						{
						int LA96_19 = input.LA(2);
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(!DeclarationScope_stack.peek().typedefNameUsed && isTypeName(input.LT(1).getText())))) ) {
							alt96=1;
						}
						else if ( (true) ) {
							alt96=2;
						}

						}
						break;
					case ALIGNOF:
					case AMPERSAND:
					case BIG_O:
					case CALLS:
					case CHARACTER_CONSTANT:
					case COLLECTIVE:
					case DERIV:
					case ELLIPSIS:
					case EXISTS:
					case FALSE:
					case FLOATING_CONSTANT:
					case FORALL:
					case GENERIC:
					case HERE:
					case INTEGER_CONSTANT:
					case LPAREN:
					case MINUSMINUS:
					case NOT:
					case PLUS:
					case PLUSPLUS:
					case PROCNULL:
					case RESULT:
					case SCOPEOF:
					case SELF:
					case SEMI:
					case SIZEOF:
					case SPAWN:
					case STAR:
					case STRING_LITERAL:
					case SUB:
					case TILDE:
					case TRUE:
					case UNIFORM:
					case ROOT:
						{
						alt96=2;
						}
						break;
					default:
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 96, 0, input);
						throw nvae;
					}
					switch (alt96) {
						case 1 :
							// CivlCParser.g:1433:6: d= declaration e1= expression_opt SEMI e2= expression_opt RPAREN i= invariant_opt s= statementWithScope
							{
							pushFollow(FOLLOW_declaration_in_iterationStatement8059);
							d=declaration();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_declaration.add(d.getTree());
							pushFollow(FOLLOW_expression_opt_in_iterationStatement8063);
							e1=expression_opt();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expression_opt.add(e1.getTree());
							SEMI443=(Token)match(input,SEMI,FOLLOW_SEMI_in_iterationStatement8065); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_SEMI.add(SEMI443);

							pushFollow(FOLLOW_expression_opt_in_iterationStatement8069);
							e2=expression_opt();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expression_opt.add(e2.getTree());
							RPAREN444=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_iterationStatement8076); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN444);

							pushFollow(FOLLOW_invariant_opt_in_iterationStatement8080);
							i=invariant_opt();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_invariant_opt.add(i.getTree());
							pushFollow(FOLLOW_statementWithScope_in_iterationStatement8084);
							s=statementWithScope();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_statementWithScope.add(s.getTree());
							// AST REWRITE
							// elements: e2, i, s, d, FOR, e1
							// token labels: 
							// rule labels: retval, e1, d, e2, s, i
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
							RewriteRuleSubtreeStream stream_e1=new RewriteRuleSubtreeStream(adaptor,"rule e1",e1!=null?e1.getTree():null);
							RewriteRuleSubtreeStream stream_d=new RewriteRuleSubtreeStream(adaptor,"rule d",d!=null?d.getTree():null);
							RewriteRuleSubtreeStream stream_e2=new RewriteRuleSubtreeStream(adaptor,"rule e2",e2!=null?e2.getTree():null);
							RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"rule s",s!=null?s.getTree():null);
							RewriteRuleSubtreeStream stream_i=new RewriteRuleSubtreeStream(adaptor,"rule i",i!=null?i.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 1435:6: -> ^( FOR $d $e1 $e2 $s $i)
							{
								// CivlCParser.g:1435:9: ^( FOR $d $e1 $e2 $s $i)
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot(stream_FOR.nextNode(), root_1);
								adaptor.addChild(root_1, stream_d.nextTree());
								adaptor.addChild(root_1, stream_e1.nextTree());
								adaptor.addChild(root_1, stream_e2.nextTree());
								adaptor.addChild(root_1, stream_s.nextTree());
								adaptor.addChild(root_1, stream_i.nextTree());
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;
						case 2 :
							// CivlCParser.g:1436:6: e0= expression_opt SEMI e1= expression_opt SEMI e2= expression_opt RPAREN i= invariant_opt s= statementWithScope
							{
							pushFollow(FOLLOW_expression_opt_in_iterationStatement8119);
							e0=expression_opt();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expression_opt.add(e0.getTree());
							SEMI445=(Token)match(input,SEMI,FOLLOW_SEMI_in_iterationStatement8121); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_SEMI.add(SEMI445);

							pushFollow(FOLLOW_expression_opt_in_iterationStatement8125);
							e1=expression_opt();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expression_opt.add(e1.getTree());
							SEMI446=(Token)match(input,SEMI,FOLLOW_SEMI_in_iterationStatement8127); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_SEMI.add(SEMI446);

							pushFollow(FOLLOW_expression_opt_in_iterationStatement8136);
							e2=expression_opt();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expression_opt.add(e2.getTree());
							RPAREN447=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_iterationStatement8138); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN447);

							pushFollow(FOLLOW_invariant_opt_in_iterationStatement8142);
							i=invariant_opt();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_invariant_opt.add(i.getTree());
							pushFollow(FOLLOW_statementWithScope_in_iterationStatement8151);
							s=statementWithScope();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_statementWithScope.add(s.getTree());
							// AST REWRITE
							// elements: i, s, e0, FOR, e2, e1
							// token labels: 
							// rule labels: retval, e1, e2, s, e0, i
							// token list labels: 
							// rule list labels: 
							// wildcard labels: 
							if ( state.backtracking==0 ) {
							retval.tree = root_0;
							RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
							RewriteRuleSubtreeStream stream_e1=new RewriteRuleSubtreeStream(adaptor,"rule e1",e1!=null?e1.getTree():null);
							RewriteRuleSubtreeStream stream_e2=new RewriteRuleSubtreeStream(adaptor,"rule e2",e2!=null?e2.getTree():null);
							RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"rule s",s!=null?s.getTree():null);
							RewriteRuleSubtreeStream stream_e0=new RewriteRuleSubtreeStream(adaptor,"rule e0",e0!=null?e0.getTree():null);
							RewriteRuleSubtreeStream stream_i=new RewriteRuleSubtreeStream(adaptor,"rule i",i!=null?i.getTree():null);

							root_0 = (Object)adaptor.nil();
							// 1439:6: -> ^( FOR $e0 $e1 $e2 $s $i)
							{
								// CivlCParser.g:1439:9: ^( FOR $e0 $e1 $e2 $s $i)
								{
								Object root_1 = (Object)adaptor.nil();
								root_1 = (Object)adaptor.becomeRoot(stream_FOR.nextNode(), root_1);
								adaptor.addChild(root_1, stream_e0.nextTree());
								adaptor.addChild(root_1, stream_e1.nextTree());
								adaptor.addChild(root_1, stream_e2.nextTree());
								adaptor.addChild(root_1, stream_s.nextTree());
								adaptor.addChild(root_1, stream_i.nextTree());
								adaptor.addChild(root_0, root_1);
								}

							}


							retval.tree = root_0;
							}

							}
							break;

					}

					}
					break;
				case 4 :
					// CivlCParser.g:1441:4: (f= CIVLFOR |f= PARFOR ) LPAREN t= typeName_opt v= identifierList COLON e= expression RPAREN i= invariant_opt s= statementWithScope
					{
					// CivlCParser.g:1441:4: (f= CIVLFOR |f= PARFOR )
					int alt97=2;
					int LA97_0 = input.LA(1);
					if ( (LA97_0==CIVLFOR) ) {
						alt97=1;
					}
					else if ( (LA97_0==PARFOR) ) {
						alt97=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						NoViableAltException nvae =
							new NoViableAltException("", 97, 0, input);
						throw nvae;
					}

					switch (alt97) {
						case 1 :
							// CivlCParser.g:1441:5: f= CIVLFOR
							{
							f=(Token)match(input,CIVLFOR,FOLLOW_CIVLFOR_in_iterationStatement8190); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_CIVLFOR.add(f);

							}
							break;
						case 2 :
							// CivlCParser.g:1441:17: f= PARFOR
							{
							f=(Token)match(input,PARFOR,FOLLOW_PARFOR_in_iterationStatement8196); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_PARFOR.add(f);

							}
							break;

					}

					LPAREN448=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_iterationStatement8199); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN448);

					pushFollow(FOLLOW_typeName_opt_in_iterationStatement8208);
					t=typeName_opt();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_typeName_opt.add(t.getTree());
					pushFollow(FOLLOW_identifierList_in_iterationStatement8212);
					v=identifierList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_identifierList.add(v.getTree());
					COLON449=(Token)match(input,COLON,FOLLOW_COLON_in_iterationStatement8214); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COLON.add(COLON449);

					pushFollow(FOLLOW_expression_in_iterationStatement8218);
					e=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(e.getTree());
					RPAREN450=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_iterationStatement8220); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN450);

					pushFollow(FOLLOW_invariant_opt_in_iterationStatement8229);
					i=invariant_opt();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_invariant_opt.add(i.getTree());
					pushFollow(FOLLOW_statementWithScope_in_iterationStatement8233);
					s=statementWithScope();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statementWithScope.add(s.getTree());
					// AST REWRITE
					// elements: e, s, i, v, t, f
					// token labels: f
					// rule labels: v, retval, t, e, s, i
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleTokenStream stream_f=new RewriteRuleTokenStream(adaptor,"token f",f);
					RewriteRuleSubtreeStream stream_v=new RewriteRuleSubtreeStream(adaptor,"rule v",v!=null?v.getTree():null);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_t=new RewriteRuleSubtreeStream(adaptor,"rule t",t!=null?t.getTree():null);
					RewriteRuleSubtreeStream stream_e=new RewriteRuleSubtreeStream(adaptor,"rule e",e!=null?e.getTree():null);
					RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"rule s",s!=null?s.getTree():null);
					RewriteRuleSubtreeStream stream_i=new RewriteRuleSubtreeStream(adaptor,"rule i",i!=null?i.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1444:6: -> ^( $f $t $v $e $s $i)
					{
						// CivlCParser.g:1444:9: ^( $f $t $v $e $s $i)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_f.nextNode(), root_1);
						adaptor.addChild(root_1, stream_t.nextTree());
						adaptor.addChild(root_1, stream_v.nextTree());
						adaptor.addChild(root_1, stream_e.nextTree());
						adaptor.addChild(root_1, stream_s.nextTree());
						adaptor.addChild(root_1, stream_i.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
			Symbols_stack.pop();

		}
		return retval;
	}
	// $ANTLR end "iterationStatement"


	public static class expression_opt_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "expression_opt"
	// CivlCParser.g:1447:1: expression_opt : ( expression | -> ABSENT );
	public final OmpParser_CivlCParser.expression_opt_return expression_opt() throws RecognitionException {
		OmpParser_CivlCParser.expression_opt_return retval = new OmpParser_CivlCParser.expression_opt_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope expression451 =null;


		try {
			// CivlCParser.g:1448:2: ( expression | -> ABSENT )
			int alt99=2;
			int LA99_0 = input.LA(1);
			if ( ((LA99_0 >= ALIGNOF && LA99_0 <= AMPERSAND)||LA99_0==BIG_O||LA99_0==CALLS||LA99_0==CHARACTER_CONSTANT||LA99_0==COLLECTIVE||LA99_0==DERIV||LA99_0==ELLIPSIS||LA99_0==EXISTS||LA99_0==FALSE||LA99_0==FLOATING_CONSTANT||LA99_0==FORALL||LA99_0==GENERIC||LA99_0==HERE||LA99_0==IDENTIFIER||LA99_0==INTEGER_CONSTANT||LA99_0==LPAREN||LA99_0==MINUSMINUS||LA99_0==NOT||LA99_0==PLUS||LA99_0==PLUSPLUS||LA99_0==PROCNULL||LA99_0==RESULT||LA99_0==SCOPEOF||LA99_0==SELF||(LA99_0 >= SIZEOF && LA99_0 <= STAR)||LA99_0==STRING_LITERAL||LA99_0==SUB||(LA99_0 >= TILDE && LA99_0 <= TRUE)||LA99_0==UNIFORM||LA99_0==ROOT) ) {
				alt99=1;
			}
			else if ( (LA99_0==RPAREN||LA99_0==SEMI) ) {
				alt99=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 99, 0, input);
				throw nvae;
			}

			switch (alt99) {
				case 1 :
					// CivlCParser.g:1448:4: expression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_expression_in_expression_opt8271);
					expression451=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, expression451.getTree());

					}
					break;
				case 2 :
					// CivlCParser.g:1449:4: 
					{
					// AST REWRITE
					// elements: 
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1449:4: -> ABSENT
					{
						adaptor.addChild(root_0, (Object)adaptor.create(ABSENT, "ABSENT"));
					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "expression_opt"


	public static class invariant_opt_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "invariant_opt"
	// CivlCParser.g:1452:1: invariant_opt : ( -> ABSENT | INVARIANT LPAREN expression RPAREN -> ^( INVARIANT expression ) );
	public final OmpParser_CivlCParser.invariant_opt_return invariant_opt() throws RecognitionException {
		OmpParser_CivlCParser.invariant_opt_return retval = new OmpParser_CivlCParser.invariant_opt_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token INVARIANT452=null;
		Token LPAREN453=null;
		Token RPAREN455=null;
		ParserRuleReturnScope expression454 =null;

		Object INVARIANT452_tree=null;
		Object LPAREN453_tree=null;
		Object RPAREN455_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleTokenStream stream_INVARIANT=new RewriteRuleTokenStream(adaptor,"token INVARIANT");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");

		try {
			// CivlCParser.g:1453:2: ( -> ABSENT | INVARIANT LPAREN expression RPAREN -> ^( INVARIANT expression ) )
			int alt100=2;
			int LA100_0 = input.LA(1);
			if ( ((LA100_0 >= ALIGNOF && LA100_0 <= AMPERSAND)||LA100_0==BIG_O||LA100_0==BREAK||(LA100_0 >= CALLS && LA100_0 <= CASE)||(LA100_0 >= CHARACTER_CONSTANT && LA100_0 <= COLLECTIVE)||(LA100_0 >= CONTINUE && LA100_0 <= DEFAULT)||LA100_0==DERIV||LA100_0==DO||LA100_0==ELLIPSIS||LA100_0==EXISTS||LA100_0==FALSE||(LA100_0 >= FLOATING_CONSTANT && LA100_0 <= FORALL)||LA100_0==GENERIC||LA100_0==GOTO||LA100_0==HERE||(LA100_0 >= IDENTIFIER && LA100_0 <= IF)||LA100_0==INTEGER_CONSTANT||LA100_0==LCURLY||LA100_0==LPAREN||LA100_0==MINUSMINUS||LA100_0==NOT||LA100_0==PARFOR||LA100_0==PLUS||LA100_0==PLUSPLUS||LA100_0==PROCNULL||(LA100_0 >= RESULT && LA100_0 <= RETURN)||LA100_0==SCOPEOF||(LA100_0 >= SELF && LA100_0 <= SEMI)||(LA100_0 >= SIZEOF && LA100_0 <= STAR)||LA100_0==STRING_LITERAL||LA100_0==SUB||LA100_0==SWITCH||(LA100_0 >= TILDE && LA100_0 <= TRUE)||LA100_0==UNIFORM||(LA100_0 >= WHEN && LA100_0 <= WHILE)||LA100_0==ROOT) ) {
				alt100=1;
			}
			else if ( (LA100_0==INVARIANT) ) {
				alt100=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 100, 0, input);
				throw nvae;
			}

			switch (alt100) {
				case 1 :
					// CivlCParser.g:1453:4: 
					{
					// AST REWRITE
					// elements: 
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1453:4: -> ABSENT
					{
						adaptor.addChild(root_0, (Object)adaptor.create(ABSENT, "ABSENT"));
					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1454:4: INVARIANT LPAREN expression RPAREN
					{
					INVARIANT452=(Token)match(input,INVARIANT,FOLLOW_INVARIANT_in_invariant_opt8296); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_INVARIANT.add(INVARIANT452);

					LPAREN453=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_invariant_opt8298); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN453);

					pushFollow(FOLLOW_expression_in_invariant_opt8300);
					expression454=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression454.getTree());
					RPAREN455=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_invariant_opt8302); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN455);

					// AST REWRITE
					// elements: INVARIANT, expression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1455:3: -> ^( INVARIANT expression )
					{
						// CivlCParser.g:1455:6: ^( INVARIANT expression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_INVARIANT.nextNode(), root_1);
						adaptor.addChild(root_1, stream_expression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "invariant_opt"


	public static class typeName_opt_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "typeName_opt"
	// CivlCParser.g:1458:1: typeName_opt : ( typeName | -> ABSENT );
	public final OmpParser_CivlCParser.typeName_opt_return typeName_opt() throws RecognitionException {
		OmpParser_CivlCParser.typeName_opt_return retval = new OmpParser_CivlCParser.typeName_opt_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope typeName456 =null;


		try {
			// CivlCParser.g:1459:2: ( typeName | -> ABSENT )
			int alt101=2;
			int LA101_0 = input.LA(1);
			if ( (LA101_0==ATOMIC||LA101_0==BOOL||LA101_0==CHAR||(LA101_0 >= COMPLEX && LA101_0 <= CONST)||LA101_0==DOMAIN||LA101_0==DOUBLE||LA101_0==ENUM||LA101_0==FLOAT||(LA101_0 >= INPUT && LA101_0 <= INT)||LA101_0==LONG||LA101_0==OUTPUT||LA101_0==RANGE||LA101_0==REAL||LA101_0==RESTRICT||(LA101_0 >= SHORT && LA101_0 <= SIGNED)||LA101_0==STRUCT||LA101_0==TYPEOF||(LA101_0 >= UNION && LA101_0 <= UNSIGNED)||(LA101_0 >= VOID && LA101_0 <= VOLATILE)) ) {
				alt101=1;
			}
			else if ( (LA101_0==IDENTIFIER) ) {
				int LA101_2 = input.LA(2);
				if ( (LA101_2==ATOMIC||LA101_2==BOOL||LA101_2==CHAR||(LA101_2 >= COMPLEX && LA101_2 <= CONST)||LA101_2==DOMAIN||LA101_2==DOUBLE||LA101_2==ENUM||LA101_2==FLOAT||LA101_2==IDENTIFIER||(LA101_2 >= INPUT && LA101_2 <= INT)||(LA101_2 >= LONG && LA101_2 <= LPAREN)||LA101_2==LSQUARE||LA101_2==OUTPUT||LA101_2==RANGE||LA101_2==REAL||LA101_2==RESTRICT||(LA101_2 >= SHORT && LA101_2 <= SIGNED)||LA101_2==STAR||LA101_2==STRUCT||LA101_2==TYPEOF||(LA101_2 >= UNION && LA101_2 <= UNSIGNED)||(LA101_2 >= VOID && LA101_2 <= VOLATILE)) ) {
					alt101=1;
				}
				else if ( ((LA101_2 >= COLON && LA101_2 <= COMMA)) ) {
					alt101=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 101, 2, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 101, 0, input);
				throw nvae;
			}

			switch (alt101) {
				case 1 :
					// CivlCParser.g:1459:4: typeName
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_typeName_in_typeName_opt8323);
					typeName456=typeName();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, typeName456.getTree());

					}
					break;
				case 2 :
					// CivlCParser.g:1460:4: 
					{
					// AST REWRITE
					// elements: 
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1460:4: -> ABSENT
					{
						adaptor.addChild(root_0, (Object)adaptor.create(ABSENT, "ABSENT"));
					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "typeName_opt"


	public static class jumpStatement_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "jumpStatement"
	// CivlCParser.g:1480:1: jumpStatement : ( GOTO IDENTIFIER SEMI -> ^( GOTO IDENTIFIER SEMI ) | CONTINUE SEMI -> ^( CONTINUE SEMI ) | BREAK SEMI -> ^( BREAK SEMI ) | RETURN expression_opt SEMI -> ^( RETURN expression_opt SEMI ) );
	public final OmpParser_CivlCParser.jumpStatement_return jumpStatement() throws RecognitionException {
		OmpParser_CivlCParser.jumpStatement_return retval = new OmpParser_CivlCParser.jumpStatement_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token GOTO457=null;
		Token IDENTIFIER458=null;
		Token SEMI459=null;
		Token CONTINUE460=null;
		Token SEMI461=null;
		Token BREAK462=null;
		Token SEMI463=null;
		Token RETURN464=null;
		Token SEMI466=null;
		ParserRuleReturnScope expression_opt465 =null;

		Object GOTO457_tree=null;
		Object IDENTIFIER458_tree=null;
		Object SEMI459_tree=null;
		Object CONTINUE460_tree=null;
		Object SEMI461_tree=null;
		Object BREAK462_tree=null;
		Object SEMI463_tree=null;
		Object RETURN464_tree=null;
		Object SEMI466_tree=null;
		RewriteRuleTokenStream stream_GOTO=new RewriteRuleTokenStream(adaptor,"token GOTO");
		RewriteRuleTokenStream stream_CONTINUE=new RewriteRuleTokenStream(adaptor,"token CONTINUE");
		RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
		RewriteRuleTokenStream stream_BREAK=new RewriteRuleTokenStream(adaptor,"token BREAK");
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
		RewriteRuleTokenStream stream_RETURN=new RewriteRuleTokenStream(adaptor,"token RETURN");
		RewriteRuleSubtreeStream stream_expression_opt=new RewriteRuleSubtreeStream(adaptor,"rule expression_opt");

		try {
			// CivlCParser.g:1481:5: ( GOTO IDENTIFIER SEMI -> ^( GOTO IDENTIFIER SEMI ) | CONTINUE SEMI -> ^( CONTINUE SEMI ) | BREAK SEMI -> ^( BREAK SEMI ) | RETURN expression_opt SEMI -> ^( RETURN expression_opt SEMI ) )
			int alt102=4;
			switch ( input.LA(1) ) {
			case GOTO:
				{
				alt102=1;
				}
				break;
			case CONTINUE:
				{
				alt102=2;
				}
				break;
			case BREAK:
				{
				alt102=3;
				}
				break;
			case RETURN:
				{
				alt102=4;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 102, 0, input);
				throw nvae;
			}
			switch (alt102) {
				case 1 :
					// CivlCParser.g:1481:7: GOTO IDENTIFIER SEMI
					{
					GOTO457=(Token)match(input,GOTO,FOLLOW_GOTO_in_jumpStatement8346); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_GOTO.add(GOTO457);

					IDENTIFIER458=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_jumpStatement8348); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER458);

					SEMI459=(Token)match(input,SEMI,FOLLOW_SEMI_in_jumpStatement8350); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMI.add(SEMI459);

					// AST REWRITE
					// elements: GOTO, IDENTIFIER, SEMI
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1481:28: -> ^( GOTO IDENTIFIER SEMI )
					{
						// CivlCParser.g:1481:31: ^( GOTO IDENTIFIER SEMI )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_GOTO.nextNode(), root_1);
						adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
						adaptor.addChild(root_1, stream_SEMI.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1482:7: CONTINUE SEMI
					{
					CONTINUE460=(Token)match(input,CONTINUE,FOLLOW_CONTINUE_in_jumpStatement8368); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CONTINUE.add(CONTINUE460);

					SEMI461=(Token)match(input,SEMI,FOLLOW_SEMI_in_jumpStatement8370); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMI.add(SEMI461);

					// AST REWRITE
					// elements: CONTINUE, SEMI
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1482:21: -> ^( CONTINUE SEMI )
					{
						// CivlCParser.g:1482:24: ^( CONTINUE SEMI )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_CONTINUE.nextNode(), root_1);
						adaptor.addChild(root_1, stream_SEMI.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// CivlCParser.g:1483:7: BREAK SEMI
					{
					BREAK462=(Token)match(input,BREAK,FOLLOW_BREAK_in_jumpStatement8386); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BREAK.add(BREAK462);

					SEMI463=(Token)match(input,SEMI,FOLLOW_SEMI_in_jumpStatement8388); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMI.add(SEMI463);

					// AST REWRITE
					// elements: SEMI, BREAK
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1483:18: -> ^( BREAK SEMI )
					{
						// CivlCParser.g:1483:21: ^( BREAK SEMI )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_BREAK.nextNode(), root_1);
						adaptor.addChild(root_1, stream_SEMI.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// CivlCParser.g:1484:7: RETURN expression_opt SEMI
					{
					RETURN464=(Token)match(input,RETURN,FOLLOW_RETURN_in_jumpStatement8404); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RETURN.add(RETURN464);

					pushFollow(FOLLOW_expression_opt_in_jumpStatement8406);
					expression_opt465=expression_opt();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression_opt.add(expression_opt465.getTree());
					SEMI466=(Token)match(input,SEMI,FOLLOW_SEMI_in_jumpStatement8408); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMI.add(SEMI466);

					// AST REWRITE
					// elements: expression_opt, RETURN, SEMI
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1484:34: -> ^( RETURN expression_opt SEMI )
					{
						// CivlCParser.g:1484:37: ^( RETURN expression_opt SEMI )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_RETURN.nextNode(), root_1);
						adaptor.addChild(root_1, stream_expression_opt.nextTree());
						adaptor.addChild(root_1, stream_SEMI.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "jumpStatement"


	public static class pragma_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "pragma"
	// CivlCParser.g:1497:1: pragma : ( PRAGMA IDENTIFIER NEWLINE -> ^( PRAGMA IDENTIFIER ^( TOKEN_LIST ) NEWLINE ) | PRAGMA IDENTIFIER pragmaBody NEWLINE -> ^( PRAGMA IDENTIFIER ^( TOKEN_LIST pragmaBody ) NEWLINE ) );
	public final OmpParser_CivlCParser.pragma_return pragma() throws RecognitionException {
		OmpParser_CivlCParser.pragma_return retval = new OmpParser_CivlCParser.pragma_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PRAGMA467=null;
		Token IDENTIFIER468=null;
		Token NEWLINE469=null;
		Token PRAGMA470=null;
		Token IDENTIFIER471=null;
		Token NEWLINE473=null;
		ParserRuleReturnScope pragmaBody472 =null;

		Object PRAGMA467_tree=null;
		Object IDENTIFIER468_tree=null;
		Object NEWLINE469_tree=null;
		Object PRAGMA470_tree=null;
		Object IDENTIFIER471_tree=null;
		Object NEWLINE473_tree=null;
		RewriteRuleTokenStream stream_NEWLINE=new RewriteRuleTokenStream(adaptor,"token NEWLINE");
		RewriteRuleTokenStream stream_IDENTIFIER=new RewriteRuleTokenStream(adaptor,"token IDENTIFIER");
		RewriteRuleTokenStream stream_PRAGMA=new RewriteRuleTokenStream(adaptor,"token PRAGMA");
		RewriteRuleSubtreeStream stream_pragmaBody=new RewriteRuleSubtreeStream(adaptor,"rule pragmaBody");

		try {
			// CivlCParser.g:1498:5: ( PRAGMA IDENTIFIER NEWLINE -> ^( PRAGMA IDENTIFIER ^( TOKEN_LIST ) NEWLINE ) | PRAGMA IDENTIFIER pragmaBody NEWLINE -> ^( PRAGMA IDENTIFIER ^( TOKEN_LIST pragmaBody ) NEWLINE ) )
			int alt103=2;
			int LA103_0 = input.LA(1);
			if ( (LA103_0==PRAGMA) ) {
				int LA103_1 = input.LA(2);
				if ( (LA103_1==IDENTIFIER) ) {
					int LA103_2 = input.LA(3);
					if ( (LA103_2==NEWLINE) ) {
						alt103=1;
					}
					else if ( ((LA103_2 >= ABSTRACT && LA103_2 <= NEQ)||(LA103_2 >= NORETURN && LA103_2 <= 520)) ) {
						alt103=2;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 103, 2, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 103, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 103, 0, input);
				throw nvae;
			}

			switch (alt103) {
				case 1 :
					// CivlCParser.g:1498:7: PRAGMA IDENTIFIER NEWLINE
					{
					PRAGMA467=(Token)match(input,PRAGMA,FOLLOW_PRAGMA_in_pragma8437); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_PRAGMA.add(PRAGMA467);

					IDENTIFIER468=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_pragma8439); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER468);

					NEWLINE469=(Token)match(input,NEWLINE,FOLLOW_NEWLINE_in_pragma8441); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_NEWLINE.add(NEWLINE469);

					// AST REWRITE
					// elements: PRAGMA, NEWLINE, IDENTIFIER
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1499:9: -> ^( PRAGMA IDENTIFIER ^( TOKEN_LIST ) NEWLINE )
					{
						// CivlCParser.g:1499:12: ^( PRAGMA IDENTIFIER ^( TOKEN_LIST ) NEWLINE )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_PRAGMA.nextNode(), root_1);
						adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
						// CivlCParser.g:1499:32: ^( TOKEN_LIST )
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(TOKEN_LIST, "TOKEN_LIST"), root_2);
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_1, stream_NEWLINE.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1500:7: PRAGMA IDENTIFIER pragmaBody NEWLINE
					{
					PRAGMA470=(Token)match(input,PRAGMA,FOLLOW_PRAGMA_in_pragma8471); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_PRAGMA.add(PRAGMA470);

					IDENTIFIER471=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_pragma8473); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IDENTIFIER.add(IDENTIFIER471);

					pushFollow(FOLLOW_pragmaBody_in_pragma8475);
					pragmaBody472=pragmaBody();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_pragmaBody.add(pragmaBody472.getTree());
					NEWLINE473=(Token)match(input,NEWLINE,FOLLOW_NEWLINE_in_pragma8477); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_NEWLINE.add(NEWLINE473);

					// AST REWRITE
					// elements: pragmaBody, PRAGMA, IDENTIFIER, NEWLINE
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1501:9: -> ^( PRAGMA IDENTIFIER ^( TOKEN_LIST pragmaBody ) NEWLINE )
					{
						// CivlCParser.g:1501:12: ^( PRAGMA IDENTIFIER ^( TOKEN_LIST pragmaBody ) NEWLINE )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_PRAGMA.nextNode(), root_1);
						adaptor.addChild(root_1, stream_IDENTIFIER.nextNode());
						// CivlCParser.g:1501:32: ^( TOKEN_LIST pragmaBody )
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(TOKEN_LIST, "TOKEN_LIST"), root_2);
						adaptor.addChild(root_2, stream_pragmaBody.nextTree());
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_1, stream_NEWLINE.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "pragma"


	public static class pragmaBody_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "pragmaBody"
	// CivlCParser.g:1507:1: pragmaBody : (~ NEWLINE )+ ;
	public final OmpParser_CivlCParser.pragmaBody_return pragmaBody() throws RecognitionException {
		OmpParser_CivlCParser.pragmaBody_return retval = new OmpParser_CivlCParser.pragmaBody_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set474=null;

		Object set474_tree=null;

		try {
			// CivlCParser.g:1508:2: ( (~ NEWLINE )+ )
			// CivlCParser.g:1508:4: (~ NEWLINE )+
			{
			root_0 = (Object)adaptor.nil();


			// CivlCParser.g:1508:4: (~ NEWLINE )+
			int cnt104=0;
			loop104:
			while (true) {
				int alt104=2;
				int LA104_0 = input.LA(1);
				if ( ((LA104_0 >= ABSTRACT && LA104_0 <= NEQ)||(LA104_0 >= NORETURN && LA104_0 <= 520)) ) {
					alt104=1;
				}

				switch (alt104) {
				case 1 :
					// CivlCParser.g:
					{
					set474=input.LT(1);
					if ( (input.LA(1) >= ABSTRACT && input.LA(1) <= NEQ)||(input.LA(1) >= NORETURN && input.LA(1) <= 520) ) {
						input.consume();
						if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set474));
						state.errorRecovery=false;
						state.failed=false;
					}
					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						MismatchedSetException mse = new MismatchedSetException(null,input);
						throw mse;
					}
					}
					break;

				default :
					if ( cnt104 >= 1 ) break loop104;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(104, input);
					throw eee;
				}
				cnt104++;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "pragmaBody"


	public static class whenStatement_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "whenStatement"
	// CivlCParser.g:1519:1: whenStatement : WHEN LPAREN expression RPAREN statement -> ^( WHEN expression statement ) ;
	public final OmpParser_CivlCParser.whenStatement_return whenStatement() throws RecognitionException {
		OmpParser_CivlCParser.whenStatement_return retval = new OmpParser_CivlCParser.whenStatement_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token WHEN475=null;
		Token LPAREN476=null;
		Token RPAREN478=null;
		ParserRuleReturnScope expression477 =null;
		ParserRuleReturnScope statement479 =null;

		Object WHEN475_tree=null;
		Object LPAREN476_tree=null;
		Object RPAREN478_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_WHEN=new RewriteRuleTokenStream(adaptor,"token WHEN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");

		try {
			// CivlCParser.g:1520:2: ( WHEN LPAREN expression RPAREN statement -> ^( WHEN expression statement ) )
			// CivlCParser.g:1520:4: WHEN LPAREN expression RPAREN statement
			{
			WHEN475=(Token)match(input,WHEN,FOLLOW_WHEN_in_whenStatement8532); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_WHEN.add(WHEN475);

			LPAREN476=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_whenStatement8534); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN476);

			pushFollow(FOLLOW_expression_in_whenStatement8536);
			expression477=expression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_expression.add(expression477.getTree());
			RPAREN478=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_whenStatement8538); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN478);

			pushFollow(FOLLOW_statement_in_whenStatement8540);
			statement479=statement();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_statement.add(statement479.getTree());
			// AST REWRITE
			// elements: expression, statement, WHEN
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1521:3: -> ^( WHEN expression statement )
			{
				// CivlCParser.g:1521:6: ^( WHEN expression statement )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_WHEN.nextNode(), root_1);
				adaptor.addChild(root_1, stream_expression.nextTree());
				adaptor.addChild(root_1, stream_statement.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "whenStatement"


	public static class chooseStatement_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "chooseStatement"
	// CivlCParser.g:1530:1: chooseStatement : CHOOSE LCURLY ( statement )+ RCURLY -> ^( CHOOSE ( statement )+ ) ;
	public final OmpParser_CivlCParser.chooseStatement_return chooseStatement() throws RecognitionException {
		OmpParser_CivlCParser.chooseStatement_return retval = new OmpParser_CivlCParser.chooseStatement_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token CHOOSE480=null;
		Token LCURLY481=null;
		Token RCURLY483=null;
		ParserRuleReturnScope statement482 =null;

		Object CHOOSE480_tree=null;
		Object LCURLY481_tree=null;
		Object RCURLY483_tree=null;
		RewriteRuleTokenStream stream_LCURLY=new RewriteRuleTokenStream(adaptor,"token LCURLY");
		RewriteRuleTokenStream stream_CHOOSE=new RewriteRuleTokenStream(adaptor,"token CHOOSE");
		RewriteRuleTokenStream stream_RCURLY=new RewriteRuleTokenStream(adaptor,"token RCURLY");
		RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");

		try {
			// CivlCParser.g:1531:2: ( CHOOSE LCURLY ( statement )+ RCURLY -> ^( CHOOSE ( statement )+ ) )
			// CivlCParser.g:1531:4: CHOOSE LCURLY ( statement )+ RCURLY
			{
			CHOOSE480=(Token)match(input,CHOOSE,FOLLOW_CHOOSE_in_chooseStatement8565); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_CHOOSE.add(CHOOSE480);

			LCURLY481=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_chooseStatement8567); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY481);

			// CivlCParser.g:1531:18: ( statement )+
			int cnt105=0;
			loop105:
			while (true) {
				int alt105=2;
				int LA105_0 = input.LA(1);
				if ( ((LA105_0 >= ALIGNOF && LA105_0 <= AMPERSAND)||LA105_0==BIG_O||LA105_0==BREAK||(LA105_0 >= CALLS && LA105_0 <= CASE)||(LA105_0 >= CHARACTER_CONSTANT && LA105_0 <= COLLECTIVE)||(LA105_0 >= CONTINUE && LA105_0 <= DEFAULT)||LA105_0==DERIV||LA105_0==DO||LA105_0==ELLIPSIS||LA105_0==EXISTS||LA105_0==FALSE||(LA105_0 >= FLOATING_CONSTANT && LA105_0 <= FORALL)||LA105_0==GENERIC||LA105_0==GOTO||LA105_0==HERE||(LA105_0 >= IDENTIFIER && LA105_0 <= IF)||LA105_0==INTEGER_CONSTANT||LA105_0==LCURLY||LA105_0==LPAREN||LA105_0==MINUSMINUS||LA105_0==NOT||LA105_0==PARFOR||LA105_0==PLUS||LA105_0==PLUSPLUS||LA105_0==PROCNULL||(LA105_0 >= RESULT && LA105_0 <= RETURN)||LA105_0==SCOPEOF||(LA105_0 >= SELF && LA105_0 <= SEMI)||(LA105_0 >= SIZEOF && LA105_0 <= STAR)||LA105_0==STRING_LITERAL||LA105_0==SUB||LA105_0==SWITCH||(LA105_0 >= TILDE && LA105_0 <= TRUE)||LA105_0==UNIFORM||(LA105_0 >= WHEN && LA105_0 <= WHILE)||LA105_0==ROOT) ) {
					alt105=1;
				}

				switch (alt105) {
				case 1 :
					// CivlCParser.g:1531:18: statement
					{
					pushFollow(FOLLOW_statement_in_chooseStatement8569);
					statement482=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_statement.add(statement482.getTree());
					}
					break;

				default :
					if ( cnt105 >= 1 ) break loop105;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(105, input);
					throw eee;
				}
				cnt105++;
			}

			RCURLY483=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_chooseStatement8572); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY483);

			// AST REWRITE
			// elements: statement, CHOOSE
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1532:3: -> ^( CHOOSE ( statement )+ )
			{
				// CivlCParser.g:1532:6: ^( CHOOSE ( statement )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_CHOOSE.nextNode(), root_1);
				if ( !(stream_statement.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_statement.hasNext() ) {
					adaptor.addChild(root_1, stream_statement.nextTree());
				}
				stream_statement.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "chooseStatement"


	public static class atomicStatement_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "atomicStatement"
	// CivlCParser.g:1541:1: atomicStatement : CIVLATOMIC s= statementWithScope -> ^( CIVLATOMIC $s) ;
	public final OmpParser_CivlCParser.atomicStatement_return atomicStatement() throws RecognitionException {
		OmpParser_CivlCParser.atomicStatement_return retval = new OmpParser_CivlCParser.atomicStatement_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token CIVLATOMIC484=null;
		ParserRuleReturnScope s =null;

		Object CIVLATOMIC484_tree=null;
		RewriteRuleTokenStream stream_CIVLATOMIC=new RewriteRuleTokenStream(adaptor,"token CIVLATOMIC");
		RewriteRuleSubtreeStream stream_statementWithScope=new RewriteRuleSubtreeStream(adaptor,"rule statementWithScope");

		try {
			// CivlCParser.g:1542:2: ( CIVLATOMIC s= statementWithScope -> ^( CIVLATOMIC $s) )
			// CivlCParser.g:1542:4: CIVLATOMIC s= statementWithScope
			{
			CIVLATOMIC484=(Token)match(input,CIVLATOMIC,FOLLOW_CIVLATOMIC_in_atomicStatement8597); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_CIVLATOMIC.add(CIVLATOMIC484);

			pushFollow(FOLLOW_statementWithScope_in_atomicStatement8601);
			s=statementWithScope();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_statementWithScope.add(s.getTree());
			// AST REWRITE
			// elements: s, CIVLATOMIC
			// token labels: 
			// rule labels: retval, s
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"rule s",s!=null?s.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1543:3: -> ^( CIVLATOMIC $s)
			{
				// CivlCParser.g:1543:6: ^( CIVLATOMIC $s)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_CIVLATOMIC.nextNode(), root_1);
				adaptor.addChild(root_1, stream_s.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "atomicStatement"


	public static class datomicStatement_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "datomicStatement"
	// CivlCParser.g:1552:1: datomicStatement : CIVLATOM s= statementWithScope -> ^( CIVLATOM $s) ;
	public final OmpParser_CivlCParser.datomicStatement_return datomicStatement() throws RecognitionException {
		OmpParser_CivlCParser.datomicStatement_return retval = new OmpParser_CivlCParser.datomicStatement_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token CIVLATOM485=null;
		ParserRuleReturnScope s =null;

		Object CIVLATOM485_tree=null;
		RewriteRuleTokenStream stream_CIVLATOM=new RewriteRuleTokenStream(adaptor,"token CIVLATOM");
		RewriteRuleSubtreeStream stream_statementWithScope=new RewriteRuleSubtreeStream(adaptor,"rule statementWithScope");

		try {
			// CivlCParser.g:1553:2: ( CIVLATOM s= statementWithScope -> ^( CIVLATOM $s) )
			// CivlCParser.g:1553:4: CIVLATOM s= statementWithScope
			{
			CIVLATOM485=(Token)match(input,CIVLATOM,FOLLOW_CIVLATOM_in_datomicStatement8625); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_CIVLATOM.add(CIVLATOM485);

			pushFollow(FOLLOW_statementWithScope_in_datomicStatement8629);
			s=statementWithScope();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_statementWithScope.add(s.getTree());
			// AST REWRITE
			// elements: s, CIVLATOM
			// token labels: 
			// rule labels: retval, s
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_s=new RewriteRuleSubtreeStream(adaptor,"rule s",s!=null?s.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1554:3: -> ^( CIVLATOM $s)
			{
				// CivlCParser.g:1554:6: ^( CIVLATOM $s)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_CIVLATOM.nextNode(), root_1);
				adaptor.addChild(root_1, stream_s.nextTree());
				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "datomicStatement"


	public static class functionDefinition_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "functionDefinition"
	// CivlCParser.g:1566:1: functionDefinition : ( declarator contract declarationList_opt compoundStatement -> ^( FUNCTION_DEFINITION ^( DECLARATION_SPECIFIERS ) declarator declarationList_opt compoundStatement contract ) | declarationSpecifiers declarator contract declarationList_opt compoundStatement -> ^( FUNCTION_DEFINITION declarationSpecifiers declarator declarationList_opt compoundStatement contract ) );
	public final OmpParser_CivlCParser.functionDefinition_return functionDefinition() throws RecognitionException {
		Symbols_stack.push(new Symbols_scope());
		DeclarationScope_stack.push(new DeclarationScope_scope());

		OmpParser_CivlCParser.functionDefinition_return retval = new OmpParser_CivlCParser.functionDefinition_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope declarator486 =null;
		ParserRuleReturnScope contract487 =null;
		ParserRuleReturnScope declarationList_opt488 =null;
		ParserRuleReturnScope compoundStatement489 =null;
		ParserRuleReturnScope declarationSpecifiers490 =null;
		ParserRuleReturnScope declarator491 =null;
		ParserRuleReturnScope contract492 =null;
		ParserRuleReturnScope declarationList_opt493 =null;
		ParserRuleReturnScope compoundStatement494 =null;

		RewriteRuleSubtreeStream stream_declarator=new RewriteRuleSubtreeStream(adaptor,"rule declarator");
		RewriteRuleSubtreeStream stream_compoundStatement=new RewriteRuleSubtreeStream(adaptor,"rule compoundStatement");
		RewriteRuleSubtreeStream stream_contract=new RewriteRuleSubtreeStream(adaptor,"rule contract");
		RewriteRuleSubtreeStream stream_declarationSpecifiers=new RewriteRuleSubtreeStream(adaptor,"rule declarationSpecifiers");
		RewriteRuleSubtreeStream stream_declarationList_opt=new RewriteRuleSubtreeStream(adaptor,"rule declarationList_opt");


		    Symbols_stack.peek().types = new HashSet<String>();
		    Symbols_stack.peek().enumerationConstants = new HashSet<String>();
		    Symbols_stack.peek().isFunctionDefinition = true;
		    DeclarationScope_stack.peek().isTypedef = false;
		    DeclarationScope_stack.peek().typedefNameUsed =false;

		try {
			// CivlCParser.g:1576:2: ( declarator contract declarationList_opt compoundStatement -> ^( FUNCTION_DEFINITION ^( DECLARATION_SPECIFIERS ) declarator declarationList_opt compoundStatement contract ) | declarationSpecifiers declarator contract declarationList_opt compoundStatement -> ^( FUNCTION_DEFINITION declarationSpecifiers declarator declarationList_opt compoundStatement contract ) )
			int alt106=2;
			switch ( input.LA(1) ) {
			case IDENTIFIER:
				{
				int LA106_1 = input.LA(2);
				if ( (!((((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(!DeclarationScope_stack.peek().typedefNameUsed && isTypeName(input.LT(1).getText())))))) ) {
					alt106=1;
				}
				else if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(!DeclarationScope_stack.peek().typedefNameUsed && isTypeName(input.LT(1).getText())))) ) {
					alt106=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 106, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case LPAREN:
			case STAR:
				{
				alt106=1;
				}
				break;
			case ABSTRACT:
			case ALIGNAS:
			case ATOMIC:
			case AUTO:
			case BOOL:
			case CHAR:
			case COMPLEX:
			case CONST:
			case DEVICE:
			case DOMAIN:
			case DOUBLE:
			case ENUM:
			case EXTERN:
			case FATOMIC:
			case FLOAT:
			case GLOBAL:
			case INLINE:
			case INPUT:
			case INT:
			case LONG:
			case NORETURN:
			case OUTPUT:
			case PURE:
			case RANGE:
			case REAL:
			case REGISTER:
			case RESTRICT:
			case SHARED:
			case SHORT:
			case SIGNED:
			case STATIC:
			case STRUCT:
			case SYSTEM:
			case THREADLOCAL:
			case TYPEDEF:
			case TYPEOF:
			case UNION:
			case UNSIGNED:
			case VOID:
			case VOLATILE:
				{
				alt106=2;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 106, 0, input);
				throw nvae;
			}
			switch (alt106) {
				case 1 :
					// CivlCParser.g:1576:4: declarator contract declarationList_opt compoundStatement
					{
					pushFollow(FOLLOW_declarator_in_functionDefinition8669);
					declarator486=declarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_declarator.add(declarator486.getTree());
					pushFollow(FOLLOW_contract_in_functionDefinition8674);
					contract487=contract();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_contract.add(contract487.getTree());
					pushFollow(FOLLOW_declarationList_opt_in_functionDefinition8679);
					declarationList_opt488=declarationList_opt();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_declarationList_opt.add(declarationList_opt488.getTree());
					pushFollow(FOLLOW_compoundStatement_in_functionDefinition8684);
					compoundStatement489=compoundStatement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_compoundStatement.add(compoundStatement489.getTree());
					// AST REWRITE
					// elements: declarator, compoundStatement, declarationList_opt, contract
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1580:4: -> ^( FUNCTION_DEFINITION ^( DECLARATION_SPECIFIERS ) declarator declarationList_opt compoundStatement contract )
					{
						// CivlCParser.g:1580:7: ^( FUNCTION_DEFINITION ^( DECLARATION_SPECIFIERS ) declarator declarationList_opt compoundStatement contract )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FUNCTION_DEFINITION, "FUNCTION_DEFINITION"), root_1);
						// CivlCParser.g:1580:29: ^( DECLARATION_SPECIFIERS )
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(DECLARATION_SPECIFIERS, "DECLARATION_SPECIFIERS"), root_2);
						adaptor.addChild(root_1, root_2);
						}

						adaptor.addChild(root_1, stream_declarator.nextTree());
						adaptor.addChild(root_1, stream_declarationList_opt.nextTree());
						adaptor.addChild(root_1, stream_compoundStatement.nextTree());
						adaptor.addChild(root_1, stream_contract.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1583:7: declarationSpecifiers declarator contract declarationList_opt compoundStatement
					{
					pushFollow(FOLLOW_declarationSpecifiers_in_functionDefinition8729);
					declarationSpecifiers490=declarationSpecifiers();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_declarationSpecifiers.add(declarationSpecifiers490.getTree());
					pushFollow(FOLLOW_declarator_in_functionDefinition8734);
					declarator491=declarator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_declarator.add(declarator491.getTree());
					pushFollow(FOLLOW_contract_in_functionDefinition8739);
					contract492=contract();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_contract.add(contract492.getTree());
					pushFollow(FOLLOW_declarationList_opt_in_functionDefinition8744);
					declarationList_opt493=declarationList_opt();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_declarationList_opt.add(declarationList_opt493.getTree());
					pushFollow(FOLLOW_compoundStatement_in_functionDefinition8749);
					compoundStatement494=compoundStatement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_compoundStatement.add(compoundStatement494.getTree());
					// AST REWRITE
					// elements: contract, compoundStatement, declarationSpecifiers, declarator, declarationList_opt
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1588:4: -> ^( FUNCTION_DEFINITION declarationSpecifiers declarator declarationList_opt compoundStatement contract )
					{
						// CivlCParser.g:1588:7: ^( FUNCTION_DEFINITION declarationSpecifiers declarator declarationList_opt compoundStatement contract )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FUNCTION_DEFINITION, "FUNCTION_DEFINITION"), root_1);
						adaptor.addChild(root_1, stream_declarationSpecifiers.nextTree());
						adaptor.addChild(root_1, stream_declarator.nextTree());
						adaptor.addChild(root_1, stream_declarationList_opt.nextTree());
						adaptor.addChild(root_1, stream_compoundStatement.nextTree());
						adaptor.addChild(root_1, stream_contract.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
			Symbols_stack.pop();
			DeclarationScope_stack.pop();

		}
		return retval;
	}
	// $ANTLR end "functionDefinition"


	public static class declarationList_opt_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "declarationList_opt"
	// CivlCParser.g:1598:1: declarationList_opt : ( declaration )* -> ^( DECLARATION_LIST ( declaration )* ) ;
	public final OmpParser_CivlCParser.declarationList_opt_return declarationList_opt() throws RecognitionException {
		OmpParser_CivlCParser.declarationList_opt_return retval = new OmpParser_CivlCParser.declarationList_opt_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope declaration495 =null;

		RewriteRuleSubtreeStream stream_declaration=new RewriteRuleSubtreeStream(adaptor,"rule declaration");

		try {
			// CivlCParser.g:1599:2: ( ( declaration )* -> ^( DECLARATION_LIST ( declaration )* ) )
			// CivlCParser.g:1599:4: ( declaration )*
			{
			// CivlCParser.g:1599:4: ( declaration )*
			loop107:
			while (true) {
				int alt107=2;
				int LA107_0 = input.LA(1);
				if ( ((LA107_0 >= ABSTRACT && LA107_0 <= ALIGNAS)||(LA107_0 >= ATOMIC && LA107_0 <= AUTO)||LA107_0==BOOL||LA107_0==CHAR||(LA107_0 >= COMPLEX && LA107_0 <= CONST)||LA107_0==DEVICE||LA107_0==DOMAIN||LA107_0==DOUBLE||LA107_0==ENUM||LA107_0==EXTERN||(LA107_0 >= FATOMIC && LA107_0 <= FLOAT)||LA107_0==GLOBAL||LA107_0==IDENTIFIER||(LA107_0 >= INLINE && LA107_0 <= INT)||LA107_0==LONG||LA107_0==NORETURN||LA107_0==OUTPUT||LA107_0==PURE||LA107_0==RANGE||(LA107_0 >= REAL && LA107_0 <= REGISTER)||LA107_0==RESTRICT||LA107_0==SHARED||(LA107_0 >= SHORT && LA107_0 <= SIGNED)||(LA107_0 >= STATIC && LA107_0 <= STATICASSERT)||LA107_0==STRUCT||(LA107_0 >= SYSTEM && LA107_0 <= THREADLOCAL)||(LA107_0 >= TYPEDEF && LA107_0 <= TYPEOF)||(LA107_0 >= UNION && LA107_0 <= UNSIGNED)||(LA107_0 >= VOID && LA107_0 <= VOLATILE)) ) {
					alt107=1;
				}

				switch (alt107) {
				case 1 :
					// CivlCParser.g:1599:4: declaration
					{
					pushFollow(FOLLOW_declaration_in_declarationList_opt8798);
					declaration495=declaration();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_declaration.add(declaration495.getTree());
					}
					break;

				default :
					break loop107;
				}
			}

			// AST REWRITE
			// elements: declaration
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1599:17: -> ^( DECLARATION_LIST ( declaration )* )
			{
				// CivlCParser.g:1599:20: ^( DECLARATION_LIST ( declaration )* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(DECLARATION_LIST, "DECLARATION_LIST"), root_1);
				// CivlCParser.g:1599:39: ( declaration )*
				while ( stream_declaration.hasNext() ) {
					adaptor.addChild(root_1, stream_declaration.nextTree());
				}
				stream_declaration.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "declarationList_opt"


	public static class contractItem_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "contractItem"
	// CivlCParser.g:1607:1: contractItem : ( separationLogicItem | porItem );
	public final OmpParser_CivlCParser.contractItem_return contractItem() throws RecognitionException {
		OmpParser_CivlCParser.contractItem_return retval = new OmpParser_CivlCParser.contractItem_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope separationLogicItem496 =null;
		ParserRuleReturnScope porItem497 =null;


		try {
			// CivlCParser.g:1608:2: ( separationLogicItem | porItem )
			int alt108=2;
			int LA108_0 = input.LA(1);
			if ( (LA108_0==ENSURES||LA108_0==REQUIRES) ) {
				alt108=1;
			}
			else if ( (LA108_0==ASSIGNS||LA108_0==DEPENDS||LA108_0==GUARD||LA108_0==READS) ) {
				alt108=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 108, 0, input);
				throw nvae;
			}

			switch (alt108) {
				case 1 :
					// CivlCParser.g:1608:4: separationLogicItem
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_separationLogicItem_in_contractItem8821);
					separationLogicItem496=separationLogicItem();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, separationLogicItem496.getTree());

					}
					break;
				case 2 :
					// CivlCParser.g:1609:7: porItem
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_porItem_in_contractItem8829);
					porItem497=porItem();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, porItem497.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "contractItem"


	public static class separationLogicItem_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "separationLogicItem"
	// CivlCParser.g:1612:1: separationLogicItem : ( REQUIRES LCURLY expression RCURLY -> ^( REQUIRES expression RCURLY ) | ENSURES LCURLY expression RCURLY -> ^( ENSURES expression RCURLY ) );
	public final OmpParser_CivlCParser.separationLogicItem_return separationLogicItem() throws RecognitionException {
		OmpParser_CivlCParser.separationLogicItem_return retval = new OmpParser_CivlCParser.separationLogicItem_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token REQUIRES498=null;
		Token LCURLY499=null;
		Token RCURLY501=null;
		Token ENSURES502=null;
		Token LCURLY503=null;
		Token RCURLY505=null;
		ParserRuleReturnScope expression500 =null;
		ParserRuleReturnScope expression504 =null;

		Object REQUIRES498_tree=null;
		Object LCURLY499_tree=null;
		Object RCURLY501_tree=null;
		Object ENSURES502_tree=null;
		Object LCURLY503_tree=null;
		Object RCURLY505_tree=null;
		RewriteRuleTokenStream stream_ENSURES=new RewriteRuleTokenStream(adaptor,"token ENSURES");
		RewriteRuleTokenStream stream_LCURLY=new RewriteRuleTokenStream(adaptor,"token LCURLY");
		RewriteRuleTokenStream stream_REQUIRES=new RewriteRuleTokenStream(adaptor,"token REQUIRES");
		RewriteRuleTokenStream stream_RCURLY=new RewriteRuleTokenStream(adaptor,"token RCURLY");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");

		try {
			// CivlCParser.g:1613:5: ( REQUIRES LCURLY expression RCURLY -> ^( REQUIRES expression RCURLY ) | ENSURES LCURLY expression RCURLY -> ^( ENSURES expression RCURLY ) )
			int alt109=2;
			int LA109_0 = input.LA(1);
			if ( (LA109_0==REQUIRES) ) {
				alt109=1;
			}
			else if ( (LA109_0==ENSURES) ) {
				alt109=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 109, 0, input);
				throw nvae;
			}

			switch (alt109) {
				case 1 :
					// CivlCParser.g:1614:7: REQUIRES LCURLY expression RCURLY
					{
					REQUIRES498=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_separationLogicItem8849); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_REQUIRES.add(REQUIRES498);

					LCURLY499=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_separationLogicItem8851); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY499);

					pushFollow(FOLLOW_expression_in_separationLogicItem8853);
					expression500=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression500.getTree());
					RCURLY501=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_separationLogicItem8855); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY501);

					// AST REWRITE
					// elements: REQUIRES, RCURLY, expression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1614:41: -> ^( REQUIRES expression RCURLY )
					{
						// CivlCParser.g:1614:44: ^( REQUIRES expression RCURLY )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_REQUIRES.nextNode(), root_1);
						adaptor.addChild(root_1, stream_expression.nextTree());
						adaptor.addChild(root_1, stream_RCURLY.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1615:4: ENSURES LCURLY expression RCURLY
					{
					ENSURES502=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_separationLogicItem8870); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ENSURES.add(ENSURES502);

					LCURLY503=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_separationLogicItem8872); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY503);

					pushFollow(FOLLOW_expression_in_separationLogicItem8874);
					expression504=expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_expression.add(expression504.getTree());
					RCURLY505=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_separationLogicItem8876); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY505);

					// AST REWRITE
					// elements: ENSURES, expression, RCURLY
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1615:37: -> ^( ENSURES expression RCURLY )
					{
						// CivlCParser.g:1615:40: ^( ENSURES expression RCURLY )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ENSURES.nextNode(), root_1);
						adaptor.addChild(root_1, stream_expression.nextTree());
						adaptor.addChild(root_1, stream_RCURLY.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "separationLogicItem"


	public static class porItem_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "porItem"
	// CivlCParser.g:1618:1: porItem : ( DEPENDS ( LSQUARE expression RSQUARE )? LCURLY argumentExpressionList RCURLY -> ^( DEPENDS ( expression )? argumentExpressionList ) | GUARD ( LSQUARE expression RSQUARE )? LCURLY argumentExpressionList RCURLY -> ^( GUARD ( expression )? argumentExpressionList ) | ASSIGNS ( LSQUARE expression RSQUARE )? LCURLY argumentExpressionList RCURLY -> ^( ASSIGNS ( expression )? argumentExpressionList ) | READS ( LSQUARE expression RSQUARE )? LCURLY argumentExpressionList RCURLY -> ^( READS ( expression )? argumentExpressionList ) );
	public final OmpParser_CivlCParser.porItem_return porItem() throws RecognitionException {
		OmpParser_CivlCParser.porItem_return retval = new OmpParser_CivlCParser.porItem_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token DEPENDS506=null;
		Token LSQUARE507=null;
		Token RSQUARE509=null;
		Token LCURLY510=null;
		Token RCURLY512=null;
		Token GUARD513=null;
		Token LSQUARE514=null;
		Token RSQUARE516=null;
		Token LCURLY517=null;
		Token RCURLY519=null;
		Token ASSIGNS520=null;
		Token LSQUARE521=null;
		Token RSQUARE523=null;
		Token LCURLY524=null;
		Token RCURLY526=null;
		Token READS527=null;
		Token LSQUARE528=null;
		Token RSQUARE530=null;
		Token LCURLY531=null;
		Token RCURLY533=null;
		ParserRuleReturnScope expression508 =null;
		ParserRuleReturnScope argumentExpressionList511 =null;
		ParserRuleReturnScope expression515 =null;
		ParserRuleReturnScope argumentExpressionList518 =null;
		ParserRuleReturnScope expression522 =null;
		ParserRuleReturnScope argumentExpressionList525 =null;
		ParserRuleReturnScope expression529 =null;
		ParserRuleReturnScope argumentExpressionList532 =null;

		Object DEPENDS506_tree=null;
		Object LSQUARE507_tree=null;
		Object RSQUARE509_tree=null;
		Object LCURLY510_tree=null;
		Object RCURLY512_tree=null;
		Object GUARD513_tree=null;
		Object LSQUARE514_tree=null;
		Object RSQUARE516_tree=null;
		Object LCURLY517_tree=null;
		Object RCURLY519_tree=null;
		Object ASSIGNS520_tree=null;
		Object LSQUARE521_tree=null;
		Object RSQUARE523_tree=null;
		Object LCURLY524_tree=null;
		Object RCURLY526_tree=null;
		Object READS527_tree=null;
		Object LSQUARE528_tree=null;
		Object RSQUARE530_tree=null;
		Object LCURLY531_tree=null;
		Object RCURLY533_tree=null;
		RewriteRuleTokenStream stream_LCURLY=new RewriteRuleTokenStream(adaptor,"token LCURLY");
		RewriteRuleTokenStream stream_GUARD=new RewriteRuleTokenStream(adaptor,"token GUARD");
		RewriteRuleTokenStream stream_DEPENDS=new RewriteRuleTokenStream(adaptor,"token DEPENDS");
		RewriteRuleTokenStream stream_LSQUARE=new RewriteRuleTokenStream(adaptor,"token LSQUARE");
		RewriteRuleTokenStream stream_RSQUARE=new RewriteRuleTokenStream(adaptor,"token RSQUARE");
		RewriteRuleTokenStream stream_ASSIGNS=new RewriteRuleTokenStream(adaptor,"token ASSIGNS");
		RewriteRuleTokenStream stream_RCURLY=new RewriteRuleTokenStream(adaptor,"token RCURLY");
		RewriteRuleTokenStream stream_READS=new RewriteRuleTokenStream(adaptor,"token READS");
		RewriteRuleSubtreeStream stream_expression=new RewriteRuleSubtreeStream(adaptor,"rule expression");
		RewriteRuleSubtreeStream stream_argumentExpressionList=new RewriteRuleSubtreeStream(adaptor,"rule argumentExpressionList");

		try {
			// CivlCParser.g:1619:5: ( DEPENDS ( LSQUARE expression RSQUARE )? LCURLY argumentExpressionList RCURLY -> ^( DEPENDS ( expression )? argumentExpressionList ) | GUARD ( LSQUARE expression RSQUARE )? LCURLY argumentExpressionList RCURLY -> ^( GUARD ( expression )? argumentExpressionList ) | ASSIGNS ( LSQUARE expression RSQUARE )? LCURLY argumentExpressionList RCURLY -> ^( ASSIGNS ( expression )? argumentExpressionList ) | READS ( LSQUARE expression RSQUARE )? LCURLY argumentExpressionList RCURLY -> ^( READS ( expression )? argumentExpressionList ) )
			int alt114=4;
			switch ( input.LA(1) ) {
			case DEPENDS:
				{
				alt114=1;
				}
				break;
			case GUARD:
				{
				alt114=2;
				}
				break;
			case ASSIGNS:
				{
				alt114=3;
				}
				break;
			case READS:
				{
				alt114=4;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 114, 0, input);
				throw nvae;
			}
			switch (alt114) {
				case 1 :
					// CivlCParser.g:1620:7: DEPENDS ( LSQUARE expression RSQUARE )? LCURLY argumentExpressionList RCURLY
					{
					DEPENDS506=(Token)match(input,DEPENDS,FOLLOW_DEPENDS_in_porItem8909); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DEPENDS.add(DEPENDS506);

					// CivlCParser.g:1620:15: ( LSQUARE expression RSQUARE )?
					int alt110=2;
					int LA110_0 = input.LA(1);
					if ( (LA110_0==LSQUARE) ) {
						alt110=1;
					}
					switch (alt110) {
						case 1 :
							// CivlCParser.g:1620:16: LSQUARE expression RSQUARE
							{
							LSQUARE507=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_porItem8912); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_LSQUARE.add(LSQUARE507);

							pushFollow(FOLLOW_expression_in_porItem8914);
							expression508=expression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expression.add(expression508.getTree());
							RSQUARE509=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_porItem8916); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE509);

							}
							break;

					}

					LCURLY510=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_porItem8920); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY510);

					pushFollow(FOLLOW_argumentExpressionList_in_porItem8922);
					argumentExpressionList511=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList511.getTree());
					RCURLY512=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_porItem8924); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY512);

					// AST REWRITE
					// elements: expression, DEPENDS, argumentExpressionList
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1620:82: -> ^( DEPENDS ( expression )? argumentExpressionList )
					{
						// CivlCParser.g:1620:85: ^( DEPENDS ( expression )? argumentExpressionList )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_DEPENDS.nextNode(), root_1);
						// CivlCParser.g:1620:95: ( expression )?
						if ( stream_expression.hasNext() ) {
							adaptor.addChild(root_1, stream_expression.nextTree());
						}
						stream_expression.reset();

						adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// CivlCParser.g:1621:7: GUARD ( LSQUARE expression RSQUARE )? LCURLY argumentExpressionList RCURLY
					{
					GUARD513=(Token)match(input,GUARD,FOLLOW_GUARD_in_porItem8943); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_GUARD.add(GUARD513);

					// CivlCParser.g:1621:13: ( LSQUARE expression RSQUARE )?
					int alt111=2;
					int LA111_0 = input.LA(1);
					if ( (LA111_0==LSQUARE) ) {
						alt111=1;
					}
					switch (alt111) {
						case 1 :
							// CivlCParser.g:1621:14: LSQUARE expression RSQUARE
							{
							LSQUARE514=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_porItem8946); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_LSQUARE.add(LSQUARE514);

							pushFollow(FOLLOW_expression_in_porItem8948);
							expression515=expression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expression.add(expression515.getTree());
							RSQUARE516=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_porItem8950); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE516);

							}
							break;

					}

					LCURLY517=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_porItem8954); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY517);

					pushFollow(FOLLOW_argumentExpressionList_in_porItem8956);
					argumentExpressionList518=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList518.getTree());
					RCURLY519=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_porItem8958); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY519);

					// AST REWRITE
					// elements: expression, argumentExpressionList, GUARD
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1621:80: -> ^( GUARD ( expression )? argumentExpressionList )
					{
						// CivlCParser.g:1621:83: ^( GUARD ( expression )? argumentExpressionList )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_GUARD.nextNode(), root_1);
						// CivlCParser.g:1621:91: ( expression )?
						if ( stream_expression.hasNext() ) {
							adaptor.addChild(root_1, stream_expression.nextTree());
						}
						stream_expression.reset();

						adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// CivlCParser.g:1622:7: ASSIGNS ( LSQUARE expression RSQUARE )? LCURLY argumentExpressionList RCURLY
					{
					ASSIGNS520=(Token)match(input,ASSIGNS,FOLLOW_ASSIGNS_in_porItem8977); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGNS.add(ASSIGNS520);

					// CivlCParser.g:1622:15: ( LSQUARE expression RSQUARE )?
					int alt112=2;
					int LA112_0 = input.LA(1);
					if ( (LA112_0==LSQUARE) ) {
						alt112=1;
					}
					switch (alt112) {
						case 1 :
							// CivlCParser.g:1622:16: LSQUARE expression RSQUARE
							{
							LSQUARE521=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_porItem8980); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_LSQUARE.add(LSQUARE521);

							pushFollow(FOLLOW_expression_in_porItem8982);
							expression522=expression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expression.add(expression522.getTree());
							RSQUARE523=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_porItem8984); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE523);

							}
							break;

					}

					LCURLY524=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_porItem8988); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY524);

					pushFollow(FOLLOW_argumentExpressionList_in_porItem8990);
					argumentExpressionList525=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList525.getTree());
					RCURLY526=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_porItem8992); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY526);

					// AST REWRITE
					// elements: argumentExpressionList, ASSIGNS, expression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1622:82: -> ^( ASSIGNS ( expression )? argumentExpressionList )
					{
						// CivlCParser.g:1622:85: ^( ASSIGNS ( expression )? argumentExpressionList )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ASSIGNS.nextNode(), root_1);
						// CivlCParser.g:1622:95: ( expression )?
						if ( stream_expression.hasNext() ) {
							adaptor.addChild(root_1, stream_expression.nextTree());
						}
						stream_expression.reset();

						adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// CivlCParser.g:1623:7: READS ( LSQUARE expression RSQUARE )? LCURLY argumentExpressionList RCURLY
					{
					READS527=(Token)match(input,READS,FOLLOW_READS_in_porItem9011); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_READS.add(READS527);

					// CivlCParser.g:1623:13: ( LSQUARE expression RSQUARE )?
					int alt113=2;
					int LA113_0 = input.LA(1);
					if ( (LA113_0==LSQUARE) ) {
						alt113=1;
					}
					switch (alt113) {
						case 1 :
							// CivlCParser.g:1623:14: LSQUARE expression RSQUARE
							{
							LSQUARE528=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_porItem9014); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_LSQUARE.add(LSQUARE528);

							pushFollow(FOLLOW_expression_in_porItem9016);
							expression529=expression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_expression.add(expression529.getTree());
							RSQUARE530=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_porItem9018); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE530);

							}
							break;

					}

					LCURLY531=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_porItem9022); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY531);

					pushFollow(FOLLOW_argumentExpressionList_in_porItem9024);
					argumentExpressionList532=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList532.getTree());
					RCURLY533=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_porItem9026); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY533);

					// AST REWRITE
					// elements: argumentExpressionList, expression, READS
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 1623:80: -> ^( READS ( expression )? argumentExpressionList )
					{
						// CivlCParser.g:1623:83: ^( READS ( expression )? argumentExpressionList )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_READS.nextNode(), root_1);
						// CivlCParser.g:1623:91: ( expression )?
						if ( stream_expression.hasNext() ) {
							adaptor.addChild(root_1, stream_expression.nextTree());
						}
						stream_expression.reset();

						adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "porItem"


	public static class contract_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "contract"
	// CivlCParser.g:1632:1: contract : ( contractItem )* -> ^( CONTRACT ( contractItem )* ) ;
	public final OmpParser_CivlCParser.contract_return contract() throws RecognitionException {
		OmpParser_CivlCParser.contract_return retval = new OmpParser_CivlCParser.contract_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope contractItem534 =null;

		RewriteRuleSubtreeStream stream_contractItem=new RewriteRuleSubtreeStream(adaptor,"rule contractItem");

		try {
			// CivlCParser.g:1633:2: ( ( contractItem )* -> ^( CONTRACT ( contractItem )* ) )
			// CivlCParser.g:1633:4: ( contractItem )*
			{
			// CivlCParser.g:1633:4: ( contractItem )*
			loop115:
			while (true) {
				int alt115=2;
				int LA115_0 = input.LA(1);
				if ( (LA115_0==ASSIGNS||LA115_0==DEPENDS||LA115_0==ENSURES||LA115_0==GUARD||LA115_0==READS||LA115_0==REQUIRES) ) {
					alt115=1;
				}

				switch (alt115) {
				case 1 :
					// CivlCParser.g:1633:4: contractItem
					{
					pushFollow(FOLLOW_contractItem_in_contract9054);
					contractItem534=contractItem();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_contractItem.add(contractItem534.getTree());
					}
					break;

				default :
					break loop115;
				}
			}

			// AST REWRITE
			// elements: contractItem
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1633:18: -> ^( CONTRACT ( contractItem )* )
			{
				// CivlCParser.g:1633:21: ^( CONTRACT ( contractItem )* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CONTRACT, "CONTRACT"), root_1);
				// CivlCParser.g:1633:32: ( contractItem )*
				while ( stream_contractItem.hasNext() ) {
					adaptor.addChild(root_1, stream_contractItem.nextTree());
				}
				stream_contractItem.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "contract"


	public static class blockItemWithScope_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "blockItemWithScope"
	// CivlCParser.g:1640:1: blockItemWithScope : blockItem ;
	public final OmpParser_CivlCParser.blockItemWithScope_return blockItemWithScope() throws RecognitionException {
		DeclarationScope_stack.push(new DeclarationScope_scope());

		OmpParser_CivlCParser.blockItemWithScope_return retval = new OmpParser_CivlCParser.blockItemWithScope_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope blockItem535 =null;



		  DeclarationScope_stack.peek().isTypedef = false;
		  DeclarationScope_stack.peek().typedefNameUsed = false;

		try {
			// CivlCParser.g:1646:2: ( blockItem )
			// CivlCParser.g:1646:4: blockItem
			{
			root_0 = (Object)adaptor.nil();


			pushFollow(FOLLOW_blockItem_in_blockItemWithScope9088);
			blockItem535=blockItem();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, blockItem535.getTree());

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
			DeclarationScope_stack.pop();

		}
		return retval;
	}
	// $ANTLR end "blockItemWithScope"


	public static class blockItem_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "blockItem"
	// CivlCParser.g:1652:1: blockItem : ( ( declarator contract declarationList_opt LCURLY )=> functionDefinition | ( declarationSpecifiers declarator contract declarationList_opt LCURLY )=> functionDefinition | declaration | pragma | statement );
	public final OmpParser_CivlCParser.blockItem_return blockItem() throws RecognitionException {
		OmpParser_CivlCParser.blockItem_return retval = new OmpParser_CivlCParser.blockItem_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope functionDefinition536 =null;
		ParserRuleReturnScope functionDefinition537 =null;
		ParserRuleReturnScope declaration538 =null;
		ParserRuleReturnScope pragma539 =null;
		ParserRuleReturnScope statement540 =null;


		try {
			// CivlCParser.g:1653:2: ( ( declarator contract declarationList_opt LCURLY )=> functionDefinition | ( declarationSpecifiers declarator contract declarationList_opt LCURLY )=> functionDefinition | declaration | pragma | statement )
			int alt116=5;
			alt116 = dfa116.predict(input);
			switch (alt116) {
				case 1 :
					// CivlCParser.g:1654:4: ( declarator contract declarationList_opt LCURLY )=> functionDefinition
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_functionDefinition_in_blockItem9123);
					functionDefinition536=functionDefinition();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, functionDefinition536.getTree());

					}
					break;
				case 2 :
					// CivlCParser.g:1657:7: ( declarationSpecifiers declarator contract declarationList_opt LCURLY )=> functionDefinition
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_functionDefinition_in_blockItem9154);
					functionDefinition537=functionDefinition();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, functionDefinition537.getTree());

					}
					break;
				case 3 :
					// CivlCParser.g:1660:4: declaration
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_declaration_in_blockItem9159);
					declaration538=declaration();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, declaration538.getTree());

					}
					break;
				case 4 :
					// CivlCParser.g:1661:4: pragma
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_pragma_in_blockItem9165);
					pragma539=pragma();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, pragma539.getTree());

					}
					break;
				case 5 :
					// CivlCParser.g:1662:7: statement
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_statement_in_blockItem9173);
					statement540=statement();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, statement540.getTree());

					}
					break;

			}
			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
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
	// $ANTLR end "blockItem"


	public static class translationUnit_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "translationUnit"
	// CivlCParser.g:1677:1: translationUnit : ( blockItem )* EOF -> ^( TRANSLATION_UNIT ( blockItem )* ) ;
	public final OmpParser_CivlCParser.translationUnit_return translationUnit() throws RecognitionException {
		Symbols_stack.push(new Symbols_scope());
		DeclarationScope_stack.push(new DeclarationScope_scope());

		OmpParser_CivlCParser.translationUnit_return retval = new OmpParser_CivlCParser.translationUnit_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token EOF542=null;
		ParserRuleReturnScope blockItem541 =null;

		Object EOF542_tree=null;
		RewriteRuleTokenStream stream_EOF=new RewriteRuleTokenStream(adaptor,"token EOF");
		RewriteRuleSubtreeStream stream_blockItem=new RewriteRuleSubtreeStream(adaptor,"rule blockItem");


		    Symbols_stack.peek().types = new HashSet<String>();
		    Symbols_stack.peek().enumerationConstants = new HashSet<String>();
		    Symbols_stack.peek().isFunctionDefinition = false;
		    DeclarationScope_stack.peek().isTypedef = false;
		    DeclarationScope_stack.peek().typedefNameUsed = false;

		try {
			// CivlCParser.g:1687:2: ( ( blockItem )* EOF -> ^( TRANSLATION_UNIT ( blockItem )* ) )
			// CivlCParser.g:1687:4: ( blockItem )* EOF
			{
			// CivlCParser.g:1687:4: ( blockItem )*
			loop117:
			while (true) {
				int alt117=2;
				int LA117_0 = input.LA(1);
				if ( ((LA117_0 >= ABSTRACT && LA117_0 <= AMPERSAND)||(LA117_0 >= ATOMIC && LA117_0 <= BIG_O)||(LA117_0 >= BOOL && LA117_0 <= BREAK)||(LA117_0 >= CALLS && LA117_0 <= CASE)||(LA117_0 >= CHAR && LA117_0 <= COLLECTIVE)||(LA117_0 >= COMPLEX && LA117_0 <= CONST)||(LA117_0 >= CONTINUE && LA117_0 <= DEFAULT)||(LA117_0 >= DERIV && LA117_0 <= DEVICE)||(LA117_0 >= DO && LA117_0 <= DOMAIN)||LA117_0==DOUBLE||LA117_0==ELLIPSIS||LA117_0==ENUM||(LA117_0 >= EXISTS && LA117_0 <= EXTERN)||(LA117_0 >= FALSE && LA117_0 <= FORALL)||(LA117_0 >= GENERIC && LA117_0 <= GOTO)||LA117_0==HERE||(LA117_0 >= IDENTIFIER && LA117_0 <= IF)||(LA117_0 >= INLINE && LA117_0 <= INTEGER_CONSTANT)||LA117_0==LCURLY||(LA117_0 >= LONG && LA117_0 <= LPAREN)||LA117_0==MINUSMINUS||(LA117_0 >= NORETURN && LA117_0 <= NOT)||LA117_0==OUTPUT||LA117_0==PARFOR||LA117_0==PLUS||LA117_0==PLUSPLUS||(LA117_0 >= PRAGMA && LA117_0 <= PROCNULL)||LA117_0==PURE||LA117_0==RANGE||(LA117_0 >= REAL && LA117_0 <= REGISTER)||(LA117_0 >= RESTRICT && LA117_0 <= RETURN)||LA117_0==SCOPEOF||(LA117_0 >= SELF && LA117_0 <= SHARED)||(LA117_0 >= SHORT && LA117_0 <= STAR)||(LA117_0 >= STATIC && LA117_0 <= SUB)||(LA117_0 >= SWITCH && LA117_0 <= UNSIGNED)||(LA117_0 >= VOID && LA117_0 <= WHILE)||LA117_0==ROOT) ) {
					alt117=1;
				}

				switch (alt117) {
				case 1 :
					// CivlCParser.g:1687:4: blockItem
					{
					pushFollow(FOLLOW_blockItem_in_translationUnit9203);
					blockItem541=blockItem();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_blockItem.add(blockItem541.getTree());
					}
					break;

				default :
					break loop117;
				}
			}

			EOF542=(Token)match(input,EOF,FOLLOW_EOF_in_translationUnit9206); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_EOF.add(EOF542);

			// AST REWRITE
			// elements: blockItem
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 1688:3: -> ^( TRANSLATION_UNIT ( blockItem )* )
			{
				// CivlCParser.g:1688:6: ^( TRANSLATION_UNIT ( blockItem )* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TRANSLATION_UNIT, "TRANSLATION_UNIT"), root_1);
				// CivlCParser.g:1688:25: ( blockItem )*
				while ( stream_blockItem.hasNext() ) {
					adaptor.addChild(root_1, stream_blockItem.nextTree());
				}
				stream_blockItem.reset();

				adaptor.addChild(root_0, root_1);
				}

			}


			retval.tree = root_0;
			}

			}

			retval.stop = input.LT(-1);

			if ( state.backtracking==0 ) {
			retval.tree = (Object)adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
			retval.tree = (Object)adaptor.errorNode(input, retval.start, input.LT(-1), re);
		}
		finally {
			// do for sure before leaving
			Symbols_stack.pop();
			DeclarationScope_stack.pop();

		}
		return retval;
	}
	// $ANTLR end "translationUnit"

	// $ANTLR start synpred1_CivlCParser
	public final void synpred1_CivlCParser_fragment() throws RecognitionException {
		// CivlCParser.g:284:4: ( LPAREN typeName RPAREN LCURLY )
		// CivlCParser.g:284:5: LPAREN typeName RPAREN LCURLY
		{
		match(input,LPAREN,FOLLOW_LPAREN_in_synpred1_CivlCParser1772); if (state.failed) return;

		pushFollow(FOLLOW_typeName_in_synpred1_CivlCParser1774);
		typeName();
		state._fsp--;
		if (state.failed) return;

		match(input,RPAREN,FOLLOW_RPAREN_in_synpred1_CivlCParser1776); if (state.failed) return;

		match(input,LCURLY,FOLLOW_LCURLY_in_synpred1_CivlCParser1778); if (state.failed) return;

		}

	}
	// $ANTLR end synpred1_CivlCParser

	// $ANTLR start synpred2_CivlCParser
	public final void synpred2_CivlCParser_fragment() throws RecognitionException {
		// CivlCParser.g:316:4: ( SIZEOF LPAREN typeName )
		// CivlCParser.g:316:5: SIZEOF LPAREN typeName
		{
		match(input,SIZEOF,FOLLOW_SIZEOF_in_synpred2_CivlCParser1999); if (state.failed) return;

		match(input,LPAREN,FOLLOW_LPAREN_in_synpred2_CivlCParser2001); if (state.failed) return;

		pushFollow(FOLLOW_typeName_in_synpred2_CivlCParser2003);
		typeName();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred2_CivlCParser

	// $ANTLR start synpred3_CivlCParser
	public final void synpred3_CivlCParser_fragment() throws RecognitionException {
		// CivlCParser.g:360:4: ( LPAREN typeName RPAREN ~ LCURLY )
		// CivlCParser.g:360:5: LPAREN typeName RPAREN ~ LCURLY
		{
		match(input,LPAREN,FOLLOW_LPAREN_in_synpred3_CivlCParser2272); if (state.failed) return;

		pushFollow(FOLLOW_typeName_in_synpred3_CivlCParser2274);
		typeName();
		state._fsp--;
		if (state.failed) return;

		match(input,RPAREN,FOLLOW_RPAREN_in_synpred3_CivlCParser2276); if (state.failed) return;

		if ( (input.LA(1) >= ABSTRACT && input.LA(1) <= IntegerSuffix)||(input.LA(1) >= LEXCON && input.LA(1) <= 520) ) {
			input.consume();
			state.errorRecovery=false;
			state.failed=false;
		}
		else {
			if (state.backtracking>0) {state.failed=true; return;}
			MismatchedSetException mse = new MismatchedSetException(null,input);
			throw mse;
		}
		}

	}
	// $ANTLR end synpred3_CivlCParser

	// $ANTLR start synpred4_CivlCParser
	public final void synpred4_CivlCParser_fragment() throws RecognitionException {
		// CivlCParser.g:535:4: ( unaryExpression assignmentOperator )
		// CivlCParser.g:535:5: unaryExpression assignmentOperator
		{
		pushFollow(FOLLOW_unaryExpression_in_synpred4_CivlCParser3652);
		unaryExpression();
		state._fsp--;
		if (state.failed) return;

		pushFollow(FOLLOW_assignmentOperator_in_synpred4_CivlCParser3654);
		assignmentOperator();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred4_CivlCParser

	// $ANTLR start synpred5_CivlCParser
	public final void synpred5_CivlCParser_fragment() throws RecognitionException {
		// CivlCParser.g:656:4: ( typeSpecifier )
		// CivlCParser.g:656:5: typeSpecifier
		{
		pushFollow(FOLLOW_typeSpecifier_in_synpred5_CivlCParser4090);
		typeSpecifier();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred5_CivlCParser

	// $ANTLR start synpred6_CivlCParser
	public final void synpred6_CivlCParser_fragment() throws RecognitionException {
		// CivlCParser.g:1095:4: ( declarator )
		// CivlCParser.g:1095:5: declarator
		{
		pushFollow(FOLLOW_declarator_in_synpred6_CivlCParser6307);
		declarator();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred6_CivlCParser

	// $ANTLR start synpred7_CivlCParser
	public final void synpred7_CivlCParser_fragment() throws RecognitionException {
		// CivlCParser.g:1391:11: ( ELSE )
		// CivlCParser.g:1391:12: ELSE
		{
		match(input,ELSE,FOLLOW_ELSE_in_synpred7_CivlCParser7837); if (state.failed) return;

		}

	}
	// $ANTLR end synpred7_CivlCParser

	// $ANTLR start synpred8_CivlCParser
	public final void synpred8_CivlCParser_fragment() throws RecognitionException {
		// CivlCParser.g:1654:4: ( declarator contract declarationList_opt LCURLY )
		// CivlCParser.g:1654:5: declarator contract declarationList_opt LCURLY
		{
		pushFollow(FOLLOW_declarator_in_synpred8_CivlCParser9103);
		declarator();
		state._fsp--;
		if (state.failed) return;

		pushFollow(FOLLOW_contract_in_synpred8_CivlCParser9105);
		contract();
		state._fsp--;
		if (state.failed) return;

		pushFollow(FOLLOW_declarationList_opt_in_synpred8_CivlCParser9114);
		declarationList_opt();
		state._fsp--;
		if (state.failed) return;

		match(input,LCURLY,FOLLOW_LCURLY_in_synpred8_CivlCParser9116); if (state.failed) return;

		}

	}
	// $ANTLR end synpred8_CivlCParser

	// $ANTLR start synpred9_CivlCParser
	public final void synpred9_CivlCParser_fragment() throws RecognitionException {
		// CivlCParser.g:1657:7: ( declarationSpecifiers declarator contract declarationList_opt LCURLY )
		// CivlCParser.g:1657:8: declarationSpecifiers declarator contract declarationList_opt LCURLY
		{
		pushFollow(FOLLOW_declarationSpecifiers_in_synpred9_CivlCParser9132);
		declarationSpecifiers();
		state._fsp--;
		if (state.failed) return;

		pushFollow(FOLLOW_declarator_in_synpred9_CivlCParser9134);
		declarator();
		state._fsp--;
		if (state.failed) return;

		pushFollow(FOLLOW_contract_in_synpred9_CivlCParser9136);
		contract();
		state._fsp--;
		if (state.failed) return;

		pushFollow(FOLLOW_declarationList_opt_in_synpred9_CivlCParser9145);
		declarationList_opt();
		state._fsp--;
		if (state.failed) return;

		match(input,LCURLY,FOLLOW_LCURLY_in_synpred9_CivlCParser9147); if (state.failed) return;

		}

	}
	// $ANTLR end synpred9_CivlCParser

	// Delegated rules

	public final boolean synpred3_CivlCParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred3_CivlCParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred2_CivlCParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred2_CivlCParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred9_CivlCParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred9_CivlCParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred7_CivlCParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred7_CivlCParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred6_CivlCParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred6_CivlCParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred5_CivlCParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred5_CivlCParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred8_CivlCParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred8_CivlCParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred4_CivlCParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred4_CivlCParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred1_CivlCParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred1_CivlCParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}


	protected DFA62 dfa62 = new DFA62(this);
	protected DFA63 dfa63 = new DFA63(this);
	protected DFA75 dfa75 = new DFA75(this);
	protected DFA79 dfa79 = new DFA79(this);
	protected DFA116 dfa116 = new DFA116(this);
	static final String DFA62_eotS =
		"\7\uffff";
	static final String DFA62_eofS =
		"\7\uffff";
	static final String DFA62_minS =
		"\2\6\1\uffff\1\6\3\uffff";
	static final String DFA62_maxS =
		"\2\u00cc\1\uffff\1\u00cc\3\uffff";
	static final String DFA62_acceptS =
		"\2\uffff\1\1\1\uffff\1\2\1\3\1\4";
	static final String DFA62_specialS =
		"\7\uffff}>";
	static final String[] DFA62_transitionS = {
			"\2\2\5\uffff\1\1\1\uffff\1\2\10\uffff\1\2\3\uffff\1\2\11\uffff\1\1\5"+
			"\uffff\1\2\13\uffff\1\2\4\uffff\1\2\3\uffff\1\2\2\uffff\1\2\1\uffff\1"+
			"\2\2\uffff\1\2\10\uffff\1\2\7\uffff\1\2\4\uffff\1\1\1\uffff\1\2\6\uffff"+
			"\1\2\6\uffff\1\2\5\uffff\1\2\6\uffff\1\1\16\uffff\1\2\1\uffff\1\2\2\uffff"+
			"\1\2\11\uffff\1\1\1\2\4\uffff\2\2\1\uffff\1\2\10\uffff\2\2\1\3\1\uffff"+
			"\1\4\1\uffff\1\2\1\uffff\1\2\4\uffff\2\2\2\uffff\1\2\5\uffff\1\1\10\uffff"+
			"\1\2",
			"\2\2\5\uffff\1\1\1\uffff\1\2\10\uffff\1\2\3\uffff\1\2\11\uffff\1\1\5"+
			"\uffff\1\2\13\uffff\1\2\4\uffff\1\2\3\uffff\1\2\2\uffff\1\2\1\uffff\1"+
			"\2\2\uffff\1\2\10\uffff\1\2\7\uffff\1\2\4\uffff\1\1\1\uffff\1\2\6\uffff"+
			"\1\2\6\uffff\1\2\5\uffff\1\2\6\uffff\1\1\16\uffff\1\2\1\uffff\1\2\2\uffff"+
			"\1\2\11\uffff\1\1\1\2\4\uffff\2\2\1\uffff\1\2\10\uffff\2\2\1\3\1\uffff"+
			"\1\5\1\uffff\1\2\1\uffff\1\2\4\uffff\2\2\2\uffff\1\2\5\uffff\1\1\10\uffff"+
			"\1\2",
			"",
			"\2\2\7\uffff\1\2\10\uffff\1\2\3\uffff\1\2\17\uffff\1\2\13\uffff\1\2"+
			"\10\uffff\1\2\2\uffff\1\2\4\uffff\1\2\10\uffff\1\2\7\uffff\1\2\6\uffff"+
			"\1\2\6\uffff\1\2\6\uffff\1\2\5\uffff\1\2\25\uffff\1\2\1\uffff\1\2\2\uffff"+
			"\1\2\12\uffff\1\2\4\uffff\1\6\1\2\1\uffff\1\2\10\uffff\3\2\3\uffff\1"+
			"\2\1\uffff\1\2\4\uffff\2\2\21\uffff\1\2",
			"",
			"",
			""
	};

	static final short[] DFA62_eot = DFA.unpackEncodedString(DFA62_eotS);
	static final short[] DFA62_eof = DFA.unpackEncodedString(DFA62_eofS);
	static final char[] DFA62_min = DFA.unpackEncodedStringToUnsignedChars(DFA62_minS);
	static final char[] DFA62_max = DFA.unpackEncodedStringToUnsignedChars(DFA62_maxS);
	static final short[] DFA62_accept = DFA.unpackEncodedString(DFA62_acceptS);
	static final short[] DFA62_special = DFA.unpackEncodedString(DFA62_specialS);
	static final short[][] DFA62_transition;

	static {
		int numStates = DFA62_transitionS.length;
		DFA62_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA62_transition[i] = DFA.unpackEncodedString(DFA62_transitionS[i]);
		}
	}

	protected class DFA62 extends DFA {

		public DFA62(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 62;
			this.eot = DFA62_eot;
			this.eof = DFA62_eof;
			this.min = DFA62_min;
			this.max = DFA62_max;
			this.accept = DFA62_accept;
			this.special = DFA62_special;
			this.transition = DFA62_transition;
		}
		@Override
		public String getDescription() {
			return "951:4: ( typeQualifierList_opt assignmentExpression_opt RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt assignmentExpression_opt RSQUARE ) | STATIC typeQualifierList_opt assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt assignmentExpression RSQUARE ) | typeQualifierList STATIC assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression RSQUARE ) | typeQualifierList_opt STAR RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt STAR RSQUARE ) )";
		}
	}

	static final String DFA63_eotS =
		"\11\uffff";
	static final String DFA63_eofS =
		"\11\uffff";
	static final String DFA63_minS =
		"\1\4\1\uffff\1\4\1\uffff\1\4\1\0\1\4\1\uffff\1\0";
	static final String DFA63_maxS =
		"\1\u00c3\1\uffff\1\u00c3\1\uffff\1\u00c3\1\0\1\u00c3\1\uffff\1\0";
	static final String DFA63_acceptS =
		"\1\uffff\1\1\1\uffff\1\3\3\uffff\1\2\1\uffff";
	static final String DFA63_specialS =
		"\5\uffff\1\1\2\uffff\1\0}>";
	static final String[] DFA63_transitionS = {
			"\2\1\7\uffff\2\1\6\uffff\1\1\5\uffff\1\1\11\uffff\2\1\6\uffff\1\1\3\uffff"+
			"\1\1\2\uffff\1\1\6\uffff\1\1\2\uffff\1\1\3\uffff\2\1\6\uffff\1\1\17\uffff"+
			"\1\2\3\uffff\3\1\6\uffff\1\1\14\uffff\1\1\7\uffff\1\1\25\uffff\1\1\1"+
			"\uffff\1\1\2\uffff\2\1\1\uffff\1\1\3\uffff\1\3\6\uffff\1\1\4\uffff\2"+
			"\1\4\uffff\1\1\2\uffff\1\1\3\uffff\2\1\2\uffff\2\1\1\uffff\2\1\2\uffff"+
			"\2\1",
			"",
			"\2\1\7\uffff\2\1\6\uffff\1\1\5\uffff\1\1\7\uffff\1\4\1\uffff\2\1\6\uffff"+
			"\1\1\3\uffff\1\1\2\uffff\1\1\6\uffff\1\1\2\uffff\1\1\3\uffff\2\1\6\uffff"+
			"\1\1\17\uffff\1\1\3\uffff\3\1\6\uffff\2\1\1\uffff\1\1\11\uffff\1\1\7"+
			"\uffff\1\1\25\uffff\1\1\1\uffff\1\1\2\uffff\2\1\1\uffff\1\1\3\uffff\1"+
			"\5\6\uffff\1\1\4\uffff\2\1\2\uffff\1\1\1\uffff\1\1\2\uffff\1\1\3\uffff"+
			"\2\1\2\uffff\2\1\1\uffff\2\1\2\uffff\2\1",
			"",
			"\2\1\7\uffff\2\1\6\uffff\1\1\5\uffff\1\1\11\uffff\2\1\6\uffff\1\1\3"+
			"\uffff\1\1\2\uffff\1\1\3\uffff\1\1\2\uffff\1\1\2\uffff\1\1\3\uffff\2"+
			"\1\6\uffff\1\1\17\uffff\1\6\3\uffff\3\1\6\uffff\1\1\14\uffff\1\1\7\uffff"+
			"\1\1\25\uffff\1\1\1\uffff\1\1\2\uffff\2\1\1\uffff\1\1\12\uffff\1\1\4"+
			"\uffff\2\1\4\uffff\1\1\2\uffff\1\1\3\uffff\2\1\2\uffff\2\1\1\uffff\2"+
			"\1\2\uffff\2\1",
			"\1\uffff",
			"\2\1\7\uffff\2\1\6\uffff\1\1\5\uffff\1\1\7\uffff\1\4\1\uffff\2\1\6\uffff"+
			"\1\1\3\uffff\1\1\2\uffff\1\1\6\uffff\1\1\2\uffff\1\1\3\uffff\2\1\6\uffff"+
			"\1\1\17\uffff\1\1\3\uffff\3\1\6\uffff\2\1\1\uffff\1\1\11\uffff\1\1\7"+
			"\uffff\1\1\25\uffff\1\1\1\uffff\1\1\2\uffff\2\1\1\uffff\1\1\3\uffff\1"+
			"\10\6\uffff\1\1\4\uffff\2\1\2\uffff\1\1\1\uffff\1\1\2\uffff\1\1\3\uffff"+
			"\2\1\2\uffff\2\1\1\uffff\2\1\2\uffff\2\1",
			"",
			"\1\uffff"
	};

	static final short[] DFA63_eot = DFA.unpackEncodedString(DFA63_eotS);
	static final short[] DFA63_eof = DFA.unpackEncodedString(DFA63_eofS);
	static final char[] DFA63_min = DFA.unpackEncodedStringToUnsignedChars(DFA63_minS);
	static final char[] DFA63_max = DFA.unpackEncodedStringToUnsignedChars(DFA63_maxS);
	static final short[] DFA63_accept = DFA.unpackEncodedString(DFA63_acceptS);
	static final short[] DFA63_special = DFA.unpackEncodedString(DFA63_specialS);
	static final short[][] DFA63_transition;

	static {
		int numStates = DFA63_transitionS.length;
		DFA63_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA63_transition[i] = DFA.unpackEncodedString(DFA63_transitionS[i]);
		}
	}

	protected class DFA63 extends DFA {

		public DFA63(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 63;
			this.eot = DFA63_eot;
			this.eof = DFA63_eof;
			this.min = DFA63_min;
			this.max = DFA63_max;
			this.accept = DFA63_accept;
			this.special = DFA63_special;
			this.transition = DFA63_transition;
		}
		@Override
		public String getDescription() {
			return "979:4: ( parameterTypeList RPAREN -> ^( FUNCTION_SUFFIX LPAREN parameterTypeList RPAREN ) | identifierList RPAREN -> ^( FUNCTION_SUFFIX LPAREN identifierList RPAREN ) | RPAREN -> ^( FUNCTION_SUFFIX LPAREN ABSENT RPAREN ) )";
		}
		@Override
		public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
			TokenStream input = (TokenStream)_input;
			int _s = s;
			switch ( s ) {
					case 0 : 
						int LA63_8 = input.LA(1);
						 
						int index63_8 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(!DeclarationScope_stack.peek().typedefNameUsed && isTypeName(input.LT(1).getText())))) ) {s = 1;}
						else if ( (true) ) {s = 7;}
						 
						input.seek(index63_8);
						if ( s>=0 ) return s;
						break;

					case 1 : 
						int LA63_5 = input.LA(1);
						 
						int index63_5 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(!DeclarationScope_stack.peek().typedefNameUsed && isTypeName(input.LT(1).getText())))) ) {s = 1;}
						else if ( (true) ) {s = 7;}
						 
						input.seek(index63_5);
						if ( s>=0 ) return s;
						break;
			}
			if (state.backtracking>0) {state.failed=true; return -1;}
			NoViableAltException nvae =
				new NoViableAltException(getDescription(), 63, _s, input);
			error(nvae);
			throw nvae;
		}
	}

	static final String DFA75_eotS =
		"\6\uffff";
	static final String DFA75_eofS =
		"\1\uffff\1\4\1\uffff\1\4\2\uffff";
	static final String DFA75_minS =
		"\1\150\1\15\1\uffff\1\15\2\uffff";
	static final String DFA75_maxS =
		"\1\u00ae\1\u00c3\1\uffff\1\u00c3\2\uffff";
	static final String DFA75_acceptS =
		"\2\uffff\1\2\1\uffff\1\1\1\3";
	static final String DFA75_specialS =
		"\6\uffff}>";
	static final String[] DFA75_transitionS = {
			"\1\2\1\uffff\1\2\103\uffff\1\1",
			"\1\3\24\uffff\2\4\2\uffff\1\3\63\uffff\1\4\4\uffff\1\3\10\uffff\1\5"+
			"\1\uffff\1\5\21\uffff\1\3\35\uffff\1\3\3\uffff\1\4\17\uffff\1\1\24\uffff"+
			"\1\3",
			"",
			"\1\3\24\uffff\2\4\2\uffff\1\3\63\uffff\1\4\4\uffff\1\3\10\uffff\1\5"+
			"\1\uffff\1\5\21\uffff\1\3\35\uffff\1\3\3\uffff\1\4\17\uffff\1\1\24\uffff"+
			"\1\3",
			"",
			""
	};

	static final short[] DFA75_eot = DFA.unpackEncodedString(DFA75_eotS);
	static final short[] DFA75_eof = DFA.unpackEncodedString(DFA75_eofS);
	static final char[] DFA75_min = DFA.unpackEncodedStringToUnsignedChars(DFA75_minS);
	static final char[] DFA75_max = DFA.unpackEncodedStringToUnsignedChars(DFA75_maxS);
	static final short[] DFA75_accept = DFA.unpackEncodedString(DFA75_acceptS);
	static final short[] DFA75_special = DFA.unpackEncodedString(DFA75_specialS);
	static final short[][] DFA75_transition;

	static {
		int numStates = DFA75_transitionS.length;
		DFA75_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA75_transition[i] = DFA.unpackEncodedString(DFA75_transitionS[i]);
		}
	}

	protected class DFA75 extends DFA {

		public DFA75(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 75;
			this.eot = DFA75_eot;
			this.eof = DFA75_eof;
			this.min = DFA75_min;
			this.max = DFA75_max;
			this.accept = DFA75_accept;
			this.special = DFA75_special;
			this.transition = DFA75_transition;
		}
		@Override
		public String getDescription() {
			return "1131:1: abstractDeclarator : ( pointer -> ^( ABSTRACT_DECLARATOR pointer ABSENT ) | directAbstractDeclarator -> ^( ABSTRACT_DECLARATOR ABSENT directAbstractDeclarator ) | pointer directAbstractDeclarator -> ^( ABSTRACT_DECLARATOR pointer directAbstractDeclarator ) );";
		}
	}

	static final String DFA79_eotS =
		"\7\uffff";
	static final String DFA79_eofS =
		"\7\uffff";
	static final String DFA79_minS =
		"\2\6\1\uffff\1\6\3\uffff";
	static final String DFA79_maxS =
		"\2\u00cc\1\uffff\1\u00cc\3\uffff";
	static final String DFA79_acceptS =
		"\2\uffff\1\1\1\uffff\1\2\1\3\1\4";
	static final String DFA79_specialS =
		"\7\uffff}>";
	static final String[] DFA79_transitionS = {
			"\2\2\5\uffff\1\1\1\uffff\1\2\10\uffff\1\2\3\uffff\1\2\11\uffff\1\1\5"+
			"\uffff\1\2\13\uffff\1\2\4\uffff\1\2\3\uffff\1\2\2\uffff\1\2\1\uffff\1"+
			"\2\2\uffff\1\2\10\uffff\1\2\7\uffff\1\2\4\uffff\1\1\1\uffff\1\2\6\uffff"+
			"\1\2\6\uffff\1\2\5\uffff\1\2\6\uffff\1\1\16\uffff\1\2\1\uffff\1\2\2\uffff"+
			"\1\2\11\uffff\1\1\1\2\4\uffff\2\2\1\uffff\1\2\10\uffff\2\2\1\3\1\uffff"+
			"\1\4\1\uffff\1\2\1\uffff\1\2\4\uffff\2\2\2\uffff\1\2\5\uffff\1\1\10\uffff"+
			"\1\2",
			"\2\2\5\uffff\1\1\1\uffff\1\2\10\uffff\1\2\3\uffff\1\2\11\uffff\1\1\5"+
			"\uffff\1\2\13\uffff\1\2\4\uffff\1\2\3\uffff\1\2\2\uffff\1\2\1\uffff\1"+
			"\2\2\uffff\1\2\10\uffff\1\2\7\uffff\1\2\4\uffff\1\1\1\uffff\1\2\6\uffff"+
			"\1\2\6\uffff\1\2\5\uffff\1\2\6\uffff\1\1\16\uffff\1\2\1\uffff\1\2\2\uffff"+
			"\1\2\11\uffff\1\1\1\2\4\uffff\2\2\1\uffff\1\2\10\uffff\3\2\1\uffff\1"+
			"\5\1\uffff\1\2\1\uffff\1\2\4\uffff\2\2\2\uffff\1\2\5\uffff\1\1\10\uffff"+
			"\1\2",
			"",
			"\2\2\7\uffff\1\2\10\uffff\1\2\3\uffff\1\2\17\uffff\1\2\13\uffff\1\2"+
			"\10\uffff\1\2\2\uffff\1\2\4\uffff\1\2\10\uffff\1\2\7\uffff\1\2\6\uffff"+
			"\1\2\6\uffff\1\2\6\uffff\1\2\5\uffff\1\2\25\uffff\1\2\1\uffff\1\2\2\uffff"+
			"\1\2\12\uffff\1\2\4\uffff\1\6\1\2\1\uffff\1\2\10\uffff\3\2\3\uffff\1"+
			"\2\1\uffff\1\2\4\uffff\2\2\21\uffff\1\2",
			"",
			"",
			""
	};

	static final short[] DFA79_eot = DFA.unpackEncodedString(DFA79_eotS);
	static final short[] DFA79_eof = DFA.unpackEncodedString(DFA79_eofS);
	static final char[] DFA79_min = DFA.unpackEncodedStringToUnsignedChars(DFA79_minS);
	static final char[] DFA79_max = DFA.unpackEncodedStringToUnsignedChars(DFA79_maxS);
	static final short[] DFA79_accept = DFA.unpackEncodedString(DFA79_acceptS);
	static final short[] DFA79_special = DFA.unpackEncodedString(DFA79_specialS);
	static final short[][] DFA79_transition;

	static {
		int numStates = DFA79_transitionS.length;
		DFA79_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA79_transition[i] = DFA.unpackEncodedString(DFA79_transitionS[i]);
		}
	}

	protected class DFA79 extends DFA {

		public DFA79(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 79;
			this.eot = DFA79_eot;
			this.eof = DFA79_eof;
			this.min = DFA79_min;
			this.max = DFA79_max;
			this.accept = DFA79_accept;
			this.special = DFA79_special;
			this.transition = DFA79_transition;
		}
		@Override
		public String getDescription() {
			return "1202:7: ( typeQualifierList_opt assignmentExpression_opt RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT typeQualifierList_opt assignmentExpression_opt ) | STATIC typeQualifierList_opt assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList_opt assignmentExpression ) | typeQualifierList STATIC assignmentExpression RSQUARE -> ^( ARRAY_SUFFIX LSQUARE STATIC typeQualifierList assignmentExpression ) | STAR RSQUARE -> ^( ARRAY_SUFFIX LSQUARE ABSENT ABSENT STAR ) )";
		}
	}

	static final String DFA116_eotS =
		"\121\uffff";
	static final String DFA116_eofS =
		"\121\uffff";
	static final String DFA116_minS =
		"\1\4\41\0\57\uffff";
	static final String DFA116_maxS =
		"\1\u00cc\41\0\57\uffff";
	static final String DFA116_acceptS =
		"\42\uffff\1\3\1\4\1\5\52\uffff\1\1\1\2";
	static final String DFA116_specialS =
		"\1\uffff\1\0\1\1\1\2\1\3\1\4\1\5\1\6\1\7\1\10\1\11\1\12\1\13\1\14\1\15"+
		"\1\16\1\17\1\20\1\21\1\22\1\23\1\24\1\25\1\26\1\27\1\30\1\31\1\32\1\33"+
		"\1\34\1\35\1\36\1\37\1\40\57\uffff}>";
	static final String[] DFA116_transitionS = {
			"\1\33\1\41\2\44\5\uffff\1\23\1\5\1\44\5\uffff\1\17\1\44\1\uffff\2\44"+
			"\1\uffff\1\7\6\44\3\uffff\1\20\1\30\1\uffff\2\44\2\uffff\1\44\1\37\2"+
			"\uffff\1\44\1\26\2\uffff\1\14\3\uffff\1\44\2\uffff\1\25\1\uffff\1\44"+
			"\1\5\2\uffff\1\44\1\35\1\13\3\44\2\uffff\1\44\1\40\1\44\6\uffff\1\44"+
			"\7\uffff\1\1\1\44\2\uffff\1\31\1\30\1\11\1\44\3\uffff\1\44\1\uffff\1"+
			"\12\1\2\6\uffff\1\44\4\uffff\1\32\1\44\6\uffff\1\30\3\uffff\1\44\12\uffff"+
			"\1\44\1\uffff\1\44\1\uffff\1\43\1\44\1\uffff\1\36\1\uffff\1\22\2\uffff"+
			"\1\21\1\5\1\uffff\1\30\2\44\4\uffff\1\44\1\uffff\2\44\1\5\4\uffff\1\10"+
			"\1\15\2\44\1\3\1\uffff\1\5\1\42\1\44\1\24\1\44\1\uffff\1\44\1\34\1\5"+
			"\2\44\1\4\1\27\1\44\1\24\1\16\2\uffff\1\6\1\30\2\44\6\uffff\1\44",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"\1\uffff",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			"",
			""
	};

	static final short[] DFA116_eot = DFA.unpackEncodedString(DFA116_eotS);
	static final short[] DFA116_eof = DFA.unpackEncodedString(DFA116_eofS);
	static final char[] DFA116_min = DFA.unpackEncodedStringToUnsignedChars(DFA116_minS);
	static final char[] DFA116_max = DFA.unpackEncodedStringToUnsignedChars(DFA116_maxS);
	static final short[] DFA116_accept = DFA.unpackEncodedString(DFA116_acceptS);
	static final short[] DFA116_special = DFA.unpackEncodedString(DFA116_specialS);
	static final short[][] DFA116_transition;

	static {
		int numStates = DFA116_transitionS.length;
		DFA116_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA116_transition[i] = DFA.unpackEncodedString(DFA116_transitionS[i]);
		}
	}

	protected class DFA116 extends DFA {

		public DFA116(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 116;
			this.eot = DFA116_eot;
			this.eof = DFA116_eof;
			this.min = DFA116_min;
			this.max = DFA116_max;
			this.accept = DFA116_accept;
			this.special = DFA116_special;
			this.transition = DFA116_transition;
		}
		@Override
		public String getDescription() {
			return "1652:1: blockItem : ( ( declarator contract declarationList_opt LCURLY )=> functionDefinition | ( declarationSpecifiers declarator contract declarationList_opt LCURLY )=> functionDefinition | declaration | pragma | statement );";
		}
		@Override
		public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
			TokenStream input = (TokenStream)_input;
			int _s = s;
			switch ( s ) {
					case 0 : 
						int LA116_1 = input.LA(1);
						 
						int index116_1 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred8_CivlCParser()) ) {s = 79;}
						else if ( (synpred9_CivlCParser()) ) {s = 80;}
						else if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&(!DeclarationScope_stack.peek().typedefNameUsed && isTypeName(input.LT(1).getText())))) ) {s = 34;}
						else if ( (true) ) {s = 36;}
						 
						input.seek(index116_1);
						if ( s>=0 ) return s;
						break;

					case 1 : 
						int LA116_2 = input.LA(1);
						 
						int index116_2 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred8_CivlCParser()) ) {s = 79;}
						else if ( (synpred9_CivlCParser()) ) {s = 80;}
						else if ( (true) ) {s = 36;}
						 
						input.seek(index116_2);
						if ( s>=0 ) return s;
						break;

					case 2 : 
						int LA116_3 = input.LA(1);
						 
						int index116_3 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred8_CivlCParser()) ) {s = 79;}
						else if ( (synpred9_CivlCParser()) ) {s = 80;}
						else if ( (true) ) {s = 36;}
						 
						input.seek(index116_3);
						if ( s>=0 ) return s;
						break;

					case 3 : 
						int LA116_4 = input.LA(1);
						 
						int index116_4 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_4);
						if ( s>=0 ) return s;
						break;

					case 4 : 
						int LA116_5 = input.LA(1);
						 
						int index116_5 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_5);
						if ( s>=0 ) return s;
						break;

					case 5 : 
						int LA116_6 = input.LA(1);
						 
						int index116_6 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_6);
						if ( s>=0 ) return s;
						break;

					case 6 : 
						int LA116_7 = input.LA(1);
						 
						int index116_7 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_7);
						if ( s>=0 ) return s;
						break;

					case 7 : 
						int LA116_8 = input.LA(1);
						 
						int index116_8 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_8);
						if ( s>=0 ) return s;
						break;

					case 8 : 
						int LA116_9 = input.LA(1);
						 
						int index116_9 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_9);
						if ( s>=0 ) return s;
						break;

					case 9 : 
						int LA116_10 = input.LA(1);
						 
						int index116_10 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_10);
						if ( s>=0 ) return s;
						break;

					case 10 : 
						int LA116_11 = input.LA(1);
						 
						int index116_11 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_11);
						if ( s>=0 ) return s;
						break;

					case 11 : 
						int LA116_12 = input.LA(1);
						 
						int index116_12 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_12);
						if ( s>=0 ) return s;
						break;

					case 12 : 
						int LA116_13 = input.LA(1);
						 
						int index116_13 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_13);
						if ( s>=0 ) return s;
						break;

					case 13 : 
						int LA116_14 = input.LA(1);
						 
						int index116_14 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_14);
						if ( s>=0 ) return s;
						break;

					case 14 : 
						int LA116_15 = input.LA(1);
						 
						int index116_15 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_15);
						if ( s>=0 ) return s;
						break;

					case 15 : 
						int LA116_16 = input.LA(1);
						 
						int index116_16 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_16);
						if ( s>=0 ) return s;
						break;

					case 16 : 
						int LA116_17 = input.LA(1);
						 
						int index116_17 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_17);
						if ( s>=0 ) return s;
						break;

					case 17 : 
						int LA116_18 = input.LA(1);
						 
						int index116_18 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_18);
						if ( s>=0 ) return s;
						break;

					case 18 : 
						int LA116_19 = input.LA(1);
						 
						int index116_19 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_19);
						if ( s>=0 ) return s;
						break;

					case 19 : 
						int LA116_20 = input.LA(1);
						 
						int index116_20 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_20);
						if ( s>=0 ) return s;
						break;

					case 20 : 
						int LA116_21 = input.LA(1);
						 
						int index116_21 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_21);
						if ( s>=0 ) return s;
						break;

					case 21 : 
						int LA116_22 = input.LA(1);
						 
						int index116_22 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_22);
						if ( s>=0 ) return s;
						break;

					case 22 : 
						int LA116_23 = input.LA(1);
						 
						int index116_23 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_23);
						if ( s>=0 ) return s;
						break;

					case 23 : 
						int LA116_24 = input.LA(1);
						 
						int index116_24 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_24);
						if ( s>=0 ) return s;
						break;

					case 24 : 
						int LA116_25 = input.LA(1);
						 
						int index116_25 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_25);
						if ( s>=0 ) return s;
						break;

					case 25 : 
						int LA116_26 = input.LA(1);
						 
						int index116_26 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_26);
						if ( s>=0 ) return s;
						break;

					case 26 : 
						int LA116_27 = input.LA(1);
						 
						int index116_27 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_27);
						if ( s>=0 ) return s;
						break;

					case 27 : 
						int LA116_28 = input.LA(1);
						 
						int index116_28 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_28);
						if ( s>=0 ) return s;
						break;

					case 28 : 
						int LA116_29 = input.LA(1);
						 
						int index116_29 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_29);
						if ( s>=0 ) return s;
						break;

					case 29 : 
						int LA116_30 = input.LA(1);
						 
						int index116_30 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_30);
						if ( s>=0 ) return s;
						break;

					case 30 : 
						int LA116_31 = input.LA(1);
						 
						int index116_31 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_31);
						if ( s>=0 ) return s;
						break;

					case 31 : 
						int LA116_32 = input.LA(1);
						 
						int index116_32 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_32);
						if ( s>=0 ) return s;
						break;

					case 32 : 
						int LA116_33 = input.LA(1);
						 
						int index116_33 = input.index();
						input.rewind();
						s = -1;
						if ( (((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )&&synpred8_CivlCParser())) ) {s = 79;}
						else if ( ((synpred9_CivlCParser()&&(!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI ))) ) {s = 80;}
						else if ( ((!DeclarationScope_stack.peek().isTypedef || input.LT(2).getType() != SEMI )) ) {s = 34;}
						 
						input.seek(index116_33);
						if ( s>=0 ) return s;
						break;
			}
			if (state.backtracking>0) {state.failed=true; return -1;}
			NoViableAltException nvae =
				new NoViableAltException(getDescription(), 116, _s, input);
			error(nvae);
			throw nvae;
		}
	}

	public static final BitSet FOLLOW_enumerationConstant_in_constant997 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INTEGER_CONSTANT_in_constant1002 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FLOATING_CONSTANT_in_constant1007 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_constant1012 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SELF_in_constant1017 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PROCNULL_in_constant1021 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_TRUE_in_constant1025 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FALSE_in_constant1029 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RESULT_in_constant1033 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_HERE_in_constant1038 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ROOT_in_constant1042 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ELLIPSIS_in_constant1046 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENTIFIER_in_enumerationConstant1059 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_constant_in_primaryExpression1083 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENTIFIER_in_primaryExpression1088 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_primaryExpression1093 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_primaryExpression1101 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_compoundStatement_in_primaryExpression1103 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_primaryExpression1105 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_primaryExpression1128 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_primaryExpression1130 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_primaryExpression1132 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_genericSelection_in_primaryExpression1153 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_derivativeExpression_in_primaryExpression1158 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_GENERIC_in_genericSelection1171 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_genericSelection1173 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_assignmentExpression_in_genericSelection1175 = new BitSet(new long[]{0x0000000800000000L});
	public static final BitSet FOLLOW_COMMA_in_genericSelection1177 = new BitSet(new long[]{0x0812026008202000L,0x1000008184000008L,0xD0080C0004900000L,0x000000000000000CL});
	public static final BitSet FOLLOW_genericAssocList_in_genericSelection1179 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_genericSelection1184 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DERIV_in_derivativeExpression1210 = new BitSet(new long[]{0x0000000000000000L,0x0000040000000000L});
	public static final BitSet FOLLOW_LSQUARE_in_derivativeExpression1212 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_derivativeExpression1214 = new BitSet(new long[]{0x0000000800000000L});
	public static final BitSet FOLLOW_COMMA_in_derivativeExpression1216 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_partialList_in_derivativeExpression1218 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_derivativeExpression1220 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_derivativeExpression1226 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A48012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_argumentExpressionList_in_derivativeExpression1228 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_derivativeExpression1230 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_partial_in_partialList1268 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_COMMA_in_partialList1271 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_partial_in_partialList1273 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_LCURLY_in_partial1297 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_partial1299 = new BitSet(new long[]{0x0000000800000000L});
	public static final BitSet FOLLOW_COMMA_in_partial1301 = new BitSet(new long[]{0x0000000000000000L,0x0000000200000000L});
	public static final BitSet FOLLOW_INTEGER_CONSTANT_in_partial1303 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_partial1305 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_genericAssociation_in_genericAssocList1332 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_COMMA_in_genericAssocList1335 = new BitSet(new long[]{0x0812026008202000L,0x1000008184000008L,0xD0080C0004900000L,0x000000000000000CL});
	public static final BitSet FOLLOW_genericAssociation_in_genericAssocList1337 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_typeName_in_genericAssociation1364 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_COLON_in_genericAssociation1366 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_assignmentExpression_in_genericAssociation1368 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DEFAULT_in_genericAssociation1386 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_COLON_in_genericAssociation1388 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_assignmentExpression_in_genericAssociation1390 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_postfixExpressionRoot_in_postfixExpression1417 = new BitSet(new long[]{0x0004000000000202L,0x0000854000000000L,0x0000000000002000L});
	public static final BitSet FOLLOW_LSQUARE_in_postfixExpression1434 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_postfixExpression1436 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_postfixExpression1438 = new BitSet(new long[]{0x0004000000000202L,0x0000854000000000L,0x0000000000002000L});
	public static final BitSet FOLLOW_LPAREN_in_postfixExpression1512 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A48012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_argumentExpressionList_in_postfixExpression1514 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_postfixExpression1516 = new BitSet(new long[]{0x0004000000000202L,0x0000854000000000L,0x0000000000002000L});
	public static final BitSet FOLLOW_LEXCON_in_postfixExpression1560 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A28012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_argumentExpressionList_in_postfixExpression1564 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000020000000L});
	public static final BitSet FOLLOW_REXCON_in_postfixExpression1566 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_postfixExpression1574 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A48012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_argumentExpressionList_in_postfixExpression1578 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_postfixExpression1580 = new BitSet(new long[]{0x0004000000000202L,0x0000854000000000L,0x0000000000002000L});
	public static final BitSet FOLLOW_DOT_in_postfixExpression1613 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_postfixExpression1615 = new BitSet(new long[]{0x0004000000000202L,0x0000854000000000L,0x0000000000002000L});
	public static final BitSet FOLLOW_ARROW_in_postfixExpression1638 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_postfixExpression1640 = new BitSet(new long[]{0x0004000000000202L,0x0000854000000000L,0x0000000000002000L});
	public static final BitSet FOLLOW_PLUSPLUS_in_postfixExpression1665 = new BitSet(new long[]{0x0004000000000202L,0x0000854000000000L,0x0000000000002000L});
	public static final BitSet FOLLOW_MINUSMINUS_in_postfixExpression1721 = new BitSet(new long[]{0x0004000000000202L,0x0000854000000000L,0x0000000000002000L});
	public static final BitSet FOLLOW_LPAREN_in_postfixExpressionRoot1785 = new BitSet(new long[]{0x0812006008202000L,0x1000008184000008L,0xD0080C0004900000L,0x000000000000000CL});
	public static final BitSet FOLLOW_typeName_in_postfixExpressionRoot1787 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_postfixExpressionRoot1789 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_postfixExpressionRoot1791 = new BitSet(new long[]{0x21041000110080C0L,0x0020852204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_initializerList_in_postfixExpressionRoot1793 = new BitSet(new long[]{0x0000000800000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_postfixExpressionRoot1800 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_COMMA_in_postfixExpressionRoot1806 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_postfixExpressionRoot1808 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_primaryExpression_in_postfixExpressionRoot1834 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_assignmentExpression_in_argumentExpressionList1856 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_COMMA_in_argumentExpressionList1859 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_assignmentExpression_in_argumentExpressionList1861 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_postfixExpression_in_unaryExpression1899 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PLUSPLUS_in_unaryExpression1906 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_unaryExpression_in_unaryExpression1908 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MINUSMINUS_in_unaryExpression1941 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_unaryExpression_in_unaryExpression1943 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unaryOperator_in_unaryExpression1974 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_castExpression_in_unaryExpression1976 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SIZEOF_in_unaryExpression2007 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_unaryExpression2009 = new BitSet(new long[]{0x0812006008202000L,0x1000008184000008L,0xD0080C0004900000L,0x000000000000000CL});
	public static final BitSet FOLLOW_typeName_in_unaryExpression2011 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_unaryExpression2013 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SIZEOF_in_unaryExpression2031 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_unaryExpression_in_unaryExpression2033 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SCOPEOF_in_unaryExpression2051 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_unaryExpression_in_unaryExpression2053 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ALIGNOF_in_unaryExpression2069 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_unaryExpression2071 = new BitSet(new long[]{0x0812006008202000L,0x1000008184000008L,0xD0080C0004900000L,0x000000000000000CL});
	public static final BitSet FOLLOW_typeName_in_unaryExpression2073 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_unaryExpression2075 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_spawnExpression_in_unaryExpression2091 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_callsExpression_in_unaryExpression2099 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SPAWN_in_spawnExpression2113 = new BitSet(new long[]{0x0100100010000000L,0x0000010204040212L,0x0404000808010000L,0x0000000000001000L});
	public static final BitSet FOLLOW_postfixExpressionRoot_in_spawnExpression2115 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_spawnExpression2117 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A48012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_argumentExpressionList_in_spawnExpression2123 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_spawnExpression2125 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_CALLS_in_callsExpression2166 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_callsExpression2168 = new BitSet(new long[]{0x0100100010000000L,0x0000010204040212L,0x0404000808010000L,0x0000000000001000L});
	public static final BitSet FOLLOW_postfixExpressionRoot_in_callsExpression2170 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_callsExpression2172 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A48012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_argumentExpressionList_in_callsExpression2178 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_callsExpression2180 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_callsExpression2182 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_castExpression2285 = new BitSet(new long[]{0x0812006008202000L,0x1000008184000008L,0xD0080C0004900000L,0x000000000000000CL});
	public static final BitSet FOLLOW_typeName_in_castExpression2287 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_castExpression2289 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_castExpression_in_castExpression2291 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unaryExpression_in_castExpression2312 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_castExpression_in_remoteExpression2325 = new BitSet(new long[]{0x0000000000001002L});
	public static final BitSet FOLLOW_AT_in_remoteExpression2335 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_castExpression_in_remoteExpression2339 = new BitSet(new long[]{0x0000000000001002L});
	public static final BitSet FOLLOW_remoteExpression_in_multiplicativeExpression2381 = new BitSet(new long[]{0x0000400000000002L,0x0001000000000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_STAR_in_multiplicativeExpression2391 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_remoteExpression_in_multiplicativeExpression2395 = new BitSet(new long[]{0x0000400000000002L,0x0001000000000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_DIV_in_multiplicativeExpression2421 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_remoteExpression_in_multiplicativeExpression2425 = new BitSet(new long[]{0x0000400000000002L,0x0001000000000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_MOD_in_multiplicativeExpression2454 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_remoteExpression_in_multiplicativeExpression2458 = new BitSet(new long[]{0x0000400000000002L,0x0001000000000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_multiplicativeExpression_in_additiveExpression2500 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0010000000000800L});
	public static final BitSet FOLLOW_PLUS_in_additiveExpression2517 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_multiplicativeExpression_in_additiveExpression2521 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0010000000000800L});
	public static final BitSet FOLLOW_SUB_in_additiveExpression2561 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_multiplicativeExpression_in_additiveExpression2565 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0010000000000800L});
	public static final BitSet FOLLOW_additiveExpression_in_rangeExpression2619 = new BitSet(new long[]{0x0008000000000002L});
	public static final BitSet FOLLOW_DOTDOT_in_rangeExpression2634 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_additiveExpression_in_rangeExpression2638 = new BitSet(new long[]{0x0000000000000002L,0x0000000000008000L});
	public static final BitSet FOLLOW_HASH_in_rangeExpression2672 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_additiveExpression_in_rangeExpression2676 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_rangeExpression_in_shiftExpression2737 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000014000000000L});
	public static final BitSet FOLLOW_SHIFTLEFT_in_shiftExpression2754 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_rangeExpression_in_shiftExpression2758 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000014000000000L});
	public static final BitSet FOLLOW_SHIFTRIGHT_in_shiftExpression2798 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_rangeExpression_in_shiftExpression2802 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000014000000000L});
	public static final BitSet FOLLOW_shiftExpression_in_relationalExpression2856 = new BitSet(new long[]{0x0000000000000002L,0x0000180000003000L});
	public static final BitSet FOLLOW_relationalOperator_in_relationalExpression2869 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_shiftExpression_in_relationalExpression2873 = new BitSet(new long[]{0x0000000000000002L,0x0000180000003000L});
	public static final BitSet FOLLOW_relationalExpression_in_equalityExpression2940 = new BitSet(new long[]{0x1000000000000002L,0x0004000000000000L});
	public static final BitSet FOLLOW_equalityOperator_in_equalityExpression2953 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_relationalExpression_in_equalityExpression2957 = new BitSet(new long[]{0x1000000000000002L,0x0004000000000000L});
	public static final BitSet FOLLOW_equalityExpression_in_andExpression3016 = new BitSet(new long[]{0x0000000000000082L});
	public static final BitSet FOLLOW_AMPERSAND_in_andExpression3029 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_equalityExpression_in_andExpression3033 = new BitSet(new long[]{0x0000000000000082L});
	public static final BitSet FOLLOW_andExpression_in_exclusiveOrExpression3077 = new BitSet(new long[]{0x0000000000080002L});
	public static final BitSet FOLLOW_BITXOR_in_exclusiveOrExpression3090 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_andExpression_in_exclusiveOrExpression3094 = new BitSet(new long[]{0x0000000000080002L});
	public static final BitSet FOLLOW_exclusiveOrExpression_in_inclusiveOrExpression3138 = new BitSet(new long[]{0x0000000000020002L});
	public static final BitSet FOLLOW_BITOR_in_inclusiveOrExpression3151 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_exclusiveOrExpression_in_inclusiveOrExpression3155 = new BitSet(new long[]{0x0000000000020002L});
	public static final BitSet FOLLOW_inclusiveOrExpression_in_logicalAndExpression3199 = new BitSet(new long[]{0x0000000000000102L});
	public static final BitSet FOLLOW_AND_in_logicalAndExpression3212 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_inclusiveOrExpression_in_logicalAndExpression3216 = new BitSet(new long[]{0x0000000000000102L});
	public static final BitSet FOLLOW_logicalAndExpression_in_logicalOrExpression3260 = new BitSet(new long[]{0x0000000000000002L,0x0400000000000000L});
	public static final BitSet FOLLOW_OR_in_logicalOrExpression3273 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_logicalAndExpression_in_logicalOrExpression3277 = new BitSet(new long[]{0x0000000000000002L,0x0400000000000000L});
	public static final BitSet FOLLOW_logicalOrExpression_in_logicalImpliesExpression3322 = new BitSet(new long[]{0x0000000000000002L,0x0000000020000000L});
	public static final BitSet FOLLOW_IMPLIES_in_logicalImpliesExpression3335 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_logicalOrExpression_in_logicalImpliesExpression3339 = new BitSet(new long[]{0x0000000000000002L,0x0000000020000000L});
	public static final BitSet FOLLOW_logicalImpliesExpression_in_conditionalExpression3385 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000000080000L});
	public static final BitSet FOLLOW_QMARK_in_conditionalExpression3401 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_conditionalExpression3403 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_COLON_in_conditionalExpression3405 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_conditionalExpression_in_conditionalExpression3407 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifier_in_quantifierExpression3506 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_quantifierExpression3508 = new BitSet(new long[]{0x0812006008202000L,0x1000008184000008L,0xD0080C0004900000L,0x000000000000000CL});
	public static final BitSet FOLLOW_typeName_in_quantifierExpression3512 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_quantifierExpression3516 = new BitSet(new long[]{0x0000000000020000L});
	public static final BitSet FOLLOW_BITOR_in_quantifierExpression3521 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_conditionalExpression_in_quantifierExpression3525 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_quantifierExpression3527 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_assignmentExpression_in_quantifierExpression3535 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifier_in_quantifierExpression3561 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_quantifierExpression3563 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_quantifierExpression3567 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_quantifierExpression3569 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_additiveExpression_in_quantifierExpression3576 = new BitSet(new long[]{0x0008000000000000L});
	public static final BitSet FOLLOW_DOTDOT_in_quantifierExpression3578 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_additiveExpression_in_quantifierExpression3582 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_quantifierExpression3587 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_assignmentExpression_in_quantifierExpression3591 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unaryExpression_in_assignmentExpression3661 = new BitSet(new long[]{0x0000800000150400L,0x0002000000000000L,0x0020828000001000L});
	public static final BitSet FOLLOW_assignmentOperator_in_assignmentExpression3663 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_assignmentExpression_in_assignmentExpression3665 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_conditionalExpression_in_assignmentExpression3697 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifierExpression_in_assignmentExpression3702 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_assignmentExpression_in_commaExpression3771 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_COMMA_in_commaExpression3784 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_assignmentExpression_in_commaExpression3788 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_COLLECTIVE_in_expression3830 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_expression3832 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_conditionalExpression_in_expression3836 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_expression3842 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_conditionalExpression_in_expression3846 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_commaExpression_in_expression3866 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_conditionalExpression_in_constantExpression3883 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_declarationSpecifiers_in_declaration3913 = new BitSet(new long[]{0x0000000000000000L,0x0000010004000000L,0x0000401000000000L});
	public static final BitSet FOLLOW_initDeclaratorList_in_declaration3928 = new BitSet(new long[]{0x0400080000000800L,0x0000000000004000L,0x0000001002400000L});
	public static final BitSet FOLLOW_contract_in_declaration3930 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_SEMI_in_declaration3932 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SEMI_in_declaration3958 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_staticAssertDeclaration_in_declaration3986 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_declarationSpecifierList_in_declarationSpecifiers4002 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_declarationSpecifier_in_declarationSpecifierList4042 = new BitSet(new long[]{0x4812206008206032L,0x10100081C400040CL,0xD9890C2005940000L,0x000000000000000CL});
	public static final BitSet FOLLOW_storageClassSpecifier_in_declarationSpecifier4061 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_typeSpecifierOrQualifier_in_declarationSpecifier4066 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_functionSpecifier_in_declarationSpecifier4071 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_alignmentSpecifier_in_declarationSpecifier4076 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_typeSpecifier_in_typeSpecifierOrQualifier4094 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_typeQualifier_in_typeSpecifierOrQualifier4106 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_initDeclarator_in_initDeclaratorList4121 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_COMMA_in_initDeclaratorList4124 = new BitSet(new long[]{0x0000000000000000L,0x0000010004000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_initDeclarator_in_initDeclaratorList4128 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_declarator_in_initDeclarator4158 = new BitSet(new long[]{0x0000000000000402L});
	public static final BitSet FOLLOW_ASSIGN_in_initDeclarator4183 = new BitSet(new long[]{0x21001000110080C0L,0x0020812204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_initializer_in_initDeclarator4187 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_TYPEDEF_in_storageClassSpecifier4218 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_set_in_storageClassSpecifier4225 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_VOID_in_typeSpecifier4260 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_CHAR_in_typeSpecifier4264 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SHORT_in_typeSpecifier4268 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INT_in_typeSpecifier4272 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LONG_in_typeSpecifier4276 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FLOAT_in_typeSpecifier4280 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DOUBLE_in_typeSpecifier4284 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SIGNED_in_typeSpecifier4289 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_UNSIGNED_in_typeSpecifier4293 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BOOL_in_typeSpecifier4297 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_COMPLEX_in_typeSpecifier4301 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REAL_in_typeSpecifier4305 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RANGE_in_typeSpecifier4309 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_atomicTypeSpecifier_in_typeSpecifier4314 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_structOrUnionSpecifier_in_typeSpecifier4319 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_enumSpecifier_in_typeSpecifier4324 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_typedefName_in_typeSpecifier4329 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_domainSpecifier_in_typeSpecifier4334 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_typeofSpecifier_in_typeSpecifier4343 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_TYPEOF_in_typeofSpecifier4359 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_typeofSpecifier4361 = new BitSet(new long[]{0x291210601920A0C0L,0x102081838404025AL,0xF61C7C0A0C912800L,0x000000000000100CL});
	public static final BitSet FOLLOW_commaExpression_in_typeofSpecifier4373 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_typeofSpecifier4375 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_typeName_in_typeofSpecifier4409 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_typeofSpecifier4411 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_structOrUnion_in_structOrUnionSpecifier4459 = new BitSet(new long[]{0x0000000000000000L,0x0000002004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_structOrUnionSpecifier4468 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_structOrUnionSpecifier4470 = new BitSet(new long[]{0x0812006008202000L,0x1000008184000008L,0xD00A0C0004B00000L,0x000000000000000CL});
	public static final BitSet FOLLOW_structDeclarationList_in_structOrUnionSpecifier4472 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_structOrUnionSpecifier4474 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LCURLY_in_structOrUnionSpecifier4502 = new BitSet(new long[]{0x0812006008202000L,0x1000008184000008L,0xD00A0C0004B00000L,0x000000000000000CL});
	public static final BitSet FOLLOW_structDeclarationList_in_structOrUnionSpecifier4504 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_structOrUnionSpecifier4506 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENTIFIER_in_structOrUnionSpecifier4534 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_structDeclaration_in_structDeclarationList4588 = new BitSet(new long[]{0x0812006008202002L,0x1000008184000008L,0xD00A0C0004900000L,0x000000000000000CL});
	public static final BitSet FOLLOW_specifierQualifierList_in_structDeclaration4629 = new BitSet(new long[]{0x0000000400000000L,0x0000010004000000L,0x0000401000000000L});
	public static final BitSet FOLLOW_structDeclaratorList_in_structDeclaration4658 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_SEMI_in_structDeclaration4693 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_staticAssertDeclaration_in_structDeclaration4701 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_typeSpecifierOrQualifier_in_specifierQualifierList4720 = new BitSet(new long[]{0x0812006008202002L,0x1000008184000008L,0xD0080C0004900000L,0x000000000000000CL});
	public static final BitSet FOLLOW_structDeclarator_in_structDeclaratorList4757 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_COMMA_in_structDeclaratorList4760 = new BitSet(new long[]{0x0000000400000000L,0x0000010004000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_structDeclarator_in_structDeclaratorList4764 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_declarator_in_structDeclarator4801 = new BitSet(new long[]{0x0000000400000002L});
	public static final BitSet FOLLOW_COLON_in_structDeclarator4830 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_constantExpression_in_structDeclarator4832 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_COLON_in_structDeclarator4867 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_constantExpression_in_structDeclarator4869 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ENUM_in_enumSpecifier4904 = new BitSet(new long[]{0x0000000000000000L,0x0000002004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_enumSpecifier4917 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENTIFIER_in_enumSpecifier4950 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_enumSpecifier4952 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_enumeratorList_in_enumSpecifier4954 = new BitSet(new long[]{0x0000000800000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_COMMA_in_enumSpecifier4956 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_enumSpecifier4959 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LCURLY_in_enumSpecifier4991 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_enumeratorList_in_enumSpecifier4993 = new BitSet(new long[]{0x0000000800000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_COMMA_in_enumSpecifier4995 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_enumSpecifier4998 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_enumerator_in_enumeratorList5047 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_COMMA_in_enumeratorList5050 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_enumerator_in_enumeratorList5052 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_IDENTIFIER_in_enumerator5085 = new BitSet(new long[]{0x0000000000000402L});
	public static final BitSet FOLLOW_ASSIGN_in_enumerator5126 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_constantExpression_in_enumerator5128 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ATOMIC_in_atomicTypeSpecifier5174 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_atomicTypeSpecifier5176 = new BitSet(new long[]{0x0812006008202000L,0x1000008184000008L,0xD0080C0004900000L,0x000000000000000CL});
	public static final BitSet FOLLOW_typeName_in_atomicTypeSpecifier5178 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_atomicTypeSpecifier5180 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INLINE_in_functionSpecifier5252 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NORETURN_in_functionSpecifier5256 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ABSTRACT_in_functionSpecifier5264 = new BitSet(new long[]{0x0000008000000000L});
	public static final BitSet FOLLOW_CONTIN_in_functionSpecifier5266 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_functionSpecifier5268 = new BitSet(new long[]{0x0000000000000000L,0x0000000200000000L});
	public static final BitSet FOLLOW_INTEGER_CONSTANT_in_functionSpecifier5270 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_functionSpecifier5272 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ABSTRACT_in_functionSpecifier5295 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SYSTEM_in_functionSpecifier5309 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FATOMIC_in_functionSpecifier5324 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PURE_in_functionSpecifier5338 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DEVICE_in_functionSpecifier5352 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_GLOBAL_in_functionSpecifier5360 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ALIGNAS_in_alignmentSpecifier5379 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_alignmentSpecifier5381 = new BitSet(new long[]{0x091210601920A0C0L,0x102081838404021AL,0xD61C7C0A0C912800L,0x000000000000100CL});
	public static final BitSet FOLLOW_typeName_in_alignmentSpecifier5394 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_alignmentSpecifier5396 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_constantExpression_in_alignmentSpecifier5428 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_alignmentSpecifier5430 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_directDeclarator_in_declarator5479 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_pointer_in_declarator5498 = new BitSet(new long[]{0x0000000000000000L,0x0000010004000000L});
	public static final BitSet FOLLOW_directDeclarator_in_declarator5502 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_directDeclaratorPrefix_in_directDeclarator5531 = new BitSet(new long[]{0x0000000000000002L,0x0000050000000000L});
	public static final BitSet FOLLOW_directDeclaratorSuffix_in_directDeclarator5554 = new BitSet(new long[]{0x0000000000000002L,0x0000050000000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_directDeclaratorPrefix5585 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_directDeclaratorPrefix5595 = new BitSet(new long[]{0x0000000000000000L,0x0000010004000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_declarator_in_directDeclaratorPrefix5598 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_directDeclaratorPrefix5600 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_directDeclaratorArraySuffix_in_directDeclaratorSuffix5613 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_directDeclaratorFunctionSuffix_in_directDeclaratorSuffix5618 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LSQUARE_in_directDeclaratorArraySuffix5631 = new BitSet(new long[]{0x210010401100A0C0L,0x1020810284040252L,0x2615700B0C012800L,0x0000000000001008L});
	public static final BitSet FOLLOW_typeQualifierList_opt_in_directDeclaratorArraySuffix5638 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700B08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_assignmentExpression_opt_in_directDeclaratorArraySuffix5640 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_directDeclaratorArraySuffix5642 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STATIC_in_directDeclaratorArraySuffix5680 = new BitSet(new long[]{0x210010401100A0C0L,0x1020810284040252L,0x2614700A0C012800L,0x0000000000001008L});
	public static final BitSet FOLLOW_typeQualifierList_opt_in_directDeclaratorArraySuffix5682 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_assignmentExpression_in_directDeclaratorArraySuffix5684 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_directDeclaratorArraySuffix5686 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_typeQualifierList_in_directDeclaratorArraySuffix5726 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0001000000000000L});
	public static final BitSet FOLLOW_STATIC_in_directDeclaratorArraySuffix5728 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_assignmentExpression_in_directDeclaratorArraySuffix5730 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_directDeclaratorArraySuffix5732 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_typeQualifierList_opt_in_directDeclaratorArraySuffix5772 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_STAR_in_directDeclaratorArraySuffix5774 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_directDeclaratorArraySuffix5776 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_directDeclaratorFunctionSuffix5835 = new BitSet(new long[]{0x4812206008206030L,0x10100081C400040CL,0xD9890C2045940000L,0x000000000000000CL});
	public static final BitSet FOLLOW_parameterTypeList_in_directDeclaratorFunctionSuffix5842 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_directDeclaratorFunctionSuffix5844 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_identifierList_in_directDeclaratorFunctionSuffix5870 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_directDeclaratorFunctionSuffix5872 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RPAREN_in_directDeclaratorFunctionSuffix5896 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_typeQualifier_in_typeQualifierList_opt5926 = new BitSet(new long[]{0x0000004000002002L,0x1000000080000000L,0x0000000004000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_assignmentExpression_in_assignmentExpression_opt5957 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_pointer_part_in_pointer5973 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_STAR_in_pointer_part5999 = new BitSet(new long[]{0x0000004000002000L,0x1000000080000000L,0x0000000004000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_typeQualifierList_opt_in_pointer_part6001 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_typeQualifier_in_typeQualifierList6026 = new BitSet(new long[]{0x0000004000002002L,0x1000000080000000L,0x0000000004000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_parameterTypeListWithoutScope_in_parameterTypeList6056 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_parameterTypeListWithScope_in_parameterTypeList6061 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_parameterTypeListWithoutScope_in_parameterTypeListWithScope6082 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_parameterList_in_parameterTypeListWithoutScope6096 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_COMMA_in_parameterTypeListWithoutScope6124 = new BitSet(new long[]{0x0100000000000000L});
	public static final BitSet FOLLOW_ELLIPSIS_in_parameterTypeListWithoutScope6126 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_parameterDeclaration_in_parameterList6171 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_COMMA_in_parameterList6174 = new BitSet(new long[]{0x4812206008206030L,0x10100081C400040CL,0xD9890C2005940000L,0x000000000000000CL});
	public static final BitSet FOLLOW_parameterDeclaration_in_parameterList6176 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_declarationSpecifiers_in_parameterDeclaration6222 = new BitSet(new long[]{0x0000000000000002L,0x0000050004000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_declaratorOrAbstractDeclarator_in_parameterDeclaration6250 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_declarator_in_declaratorOrAbstractDeclarator6311 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_abstractDeclarator_in_declaratorOrAbstractDeclarator6316 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENTIFIER_in_identifierList6334 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_COMMA_in_identifierList6338 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_identifierList6340 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_specifierQualifierList_in_typeName6377 = new BitSet(new long[]{0x0000000000000002L,0x0000050000000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_abstractDeclarator_in_typeName6405 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_pointer_in_abstractDeclarator6450 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_directAbstractDeclarator_in_abstractDeclarator6474 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_pointer_in_abstractDeclarator6498 = new BitSet(new long[]{0x0000000000000000L,0x0000050000000000L});
	public static final BitSet FOLLOW_directAbstractDeclarator_in_abstractDeclarator6500 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_directAbstractDeclarator6535 = new BitSet(new long[]{0x0000000000000000L,0x0000050000000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_abstractDeclarator_in_directAbstractDeclarator6537 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_directAbstractDeclarator6539 = new BitSet(new long[]{0x0000000000000002L,0x0000050000000000L});
	public static final BitSet FOLLOW_directAbstractDeclaratorSuffix_in_directAbstractDeclarator6541 = new BitSet(new long[]{0x0000000000000002L,0x0000050000000000L});
	public static final BitSet FOLLOW_directAbstractDeclaratorSuffix_in_directAbstractDeclarator6578 = new BitSet(new long[]{0x0000000000000002L,0x0000050000000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_typedefName6629 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LSQUARE_in_directAbstractDeclaratorSuffix6662 = new BitSet(new long[]{0x210010401100A0C0L,0x1020810284040252L,0x2615700B0C012800L,0x0000000000001008L});
	public static final BitSet FOLLOW_typeQualifierList_opt_in_directAbstractDeclaratorSuffix6672 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700B08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_assignmentExpression_opt_in_directAbstractDeclaratorSuffix6674 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_directAbstractDeclaratorSuffix6676 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STATIC_in_directAbstractDeclaratorSuffix6721 = new BitSet(new long[]{0x210010401100A0C0L,0x1020810284040252L,0x2614700A0C012800L,0x0000000000001008L});
	public static final BitSet FOLLOW_typeQualifierList_opt_in_directAbstractDeclaratorSuffix6723 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_assignmentExpression_in_directAbstractDeclaratorSuffix6725 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_directAbstractDeclaratorSuffix6727 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_typeQualifierList_in_directAbstractDeclaratorSuffix6772 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0001000000000000L});
	public static final BitSet FOLLOW_STATIC_in_directAbstractDeclaratorSuffix6774 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_assignmentExpression_in_directAbstractDeclaratorSuffix6776 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_directAbstractDeclaratorSuffix6778 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STAR_in_directAbstractDeclaratorSuffix6810 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_directAbstractDeclaratorSuffix6812 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_directAbstractDeclaratorSuffix6850 = new BitSet(new long[]{0x4812206008206030L,0x10100081C400040CL,0xD9890C2045940000L,0x000000000000000CL});
	public static final BitSet FOLLOW_parameterTypeList_in_directAbstractDeclaratorSuffix6860 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_directAbstractDeclaratorSuffix6862 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RPAREN_in_directAbstractDeclaratorSuffix6892 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_assignmentExpression_in_initializer6939 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LCURLY_in_initializer6955 = new BitSet(new long[]{0x21041000110080C0L,0x0020852204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_initializerList_in_initializer6957 = new BitSet(new long[]{0x0000000800000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_initializer6971 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_COMMA_in_initializer6985 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_initializer6987 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_designatedInitializer_in_initializerList7026 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_COMMA_in_initializerList7029 = new BitSet(new long[]{0x21041000110080C0L,0x0020852204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_designatedInitializer_in_initializerList7031 = new BitSet(new long[]{0x0000000800000002L});
	public static final BitSet FOLLOW_initializer_in_designatedInitializer7062 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_designation_in_designatedInitializer7080 = new BitSet(new long[]{0x21001000110080C0L,0x0020812204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_initializer_in_designatedInitializer7082 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_designatorList_in_designation7111 = new BitSet(new long[]{0x0000000000000400L});
	public static final BitSet FOLLOW_ASSIGN_in_designation7113 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_designator_in_designatorList7140 = new BitSet(new long[]{0x0004000000000002L,0x0000040000000000L});
	public static final BitSet FOLLOW_LSQUARE_in_designator7160 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_constantExpression_in_designator7162 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_designator7164 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DOT_in_designator7186 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_designator7188 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STATICASSERT_in_staticAssertDeclaration7221 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_staticAssertDeclaration7223 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_constantExpression_in_staticAssertDeclaration7225 = new BitSet(new long[]{0x0000000800000000L});
	public static final BitSet FOLLOW_COMMA_in_staticAssertDeclaration7227 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0004000000000000L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_staticAssertDeclaration7229 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_staticAssertDeclaration7237 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_SEMI_in_staticAssertDeclaration7239 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DOMAIN_in_domainSpecifier7271 = new BitSet(new long[]{0x0000000000000002L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_domainSpecifier7289 = new BitSet(new long[]{0x0000000000000000L,0x0000000200000000L});
	public static final BitSet FOLLOW_INTEGER_CONSTANT_in_domainSpecifier7291 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_domainSpecifier7293 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_labeledStatement_in_statement7328 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_compoundStatement_in_statement7344 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_expressionStatement_in_statement7360 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_selectionStatement_in_statement7376 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_iterationStatement_in_statement7392 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_jumpStatement_in_statement7408 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_whenStatement_in_statement7425 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_chooseStatement_in_statement7441 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_atomicStatement_in_statement7457 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_datomicStatement_in_statement7473 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_statementWithScope7505 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENTIFIER_in_labeledStatement7521 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_COLON_in_labeledStatement7523 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statement_in_labeledStatement7525 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_CASE_in_labeledStatement7549 = new BitSet(new long[]{0x01001000110080C0L,0x0020810204040212L,0x0614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_constantExpression_in_labeledStatement7551 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_COLON_in_labeledStatement7553 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statement_in_labeledStatement7555 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DEFAULT_in_labeledStatement7581 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_COLON_in_labeledStatement7583 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statement_in_labeledStatement7585 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LCURLY_in_compoundStatement7635 = new BitSet(new long[]{0x69133363FB60E0F0L,0x103081A3CC040E7EL,0xFFDF7C3A1DB5A801L,0x000000000000103CL});
	public static final BitSet FOLLOW_RCURLY_in_compoundStatement7645 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_blockItemList_in_compoundStatement7675 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_compoundStatement7677 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_blockItem_in_blockItemList7724 = new BitSet(new long[]{0x69133363FB60E0F2L,0x103081A3CC040E7EL,0xFFDF7C3A1D95A801L,0x000000000000103CL});
	public static final BitSet FOLLOW_expression_in_expressionStatement7755 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_SEMI_in_expressionStatement7757 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SEMI_in_expressionStatement7775 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IF_in_selectionStatement7814 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_selectionStatement7816 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_selectionStatement7818 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_selectionStatement7820 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statementWithScope_in_selectionStatement7824 = new BitSet(new long[]{0x0200000000000002L});
	public static final BitSet FOLLOW_ELSE_in_selectionStatement7841 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statementWithScope_in_selectionStatement7845 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SWITCH_in_selectionStatement7910 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_selectionStatement7912 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_selectionStatement7914 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_selectionStatement7916 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statementWithScope_in_selectionStatement7920 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_WHILE_in_iterationStatement7963 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_iterationStatement7965 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_iterationStatement7967 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_iterationStatement7969 = new BitSet(new long[]{0x21011303F34080C0L,0x002081260C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_invariant_opt_in_iterationStatement7971 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statementWithScope_in_iterationStatement7979 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DO_in_iterationStatement8000 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statementWithScope_in_iterationStatement8004 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000020L});
	public static final BitSet FOLLOW_WHILE_in_iterationStatement8006 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_iterationStatement8008 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_iterationStatement8010 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_iterationStatement8012 = new BitSet(new long[]{0x0000000000000000L,0x0000000400000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_invariant_opt_in_iterationStatement8018 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_SEMI_in_iterationStatement8020 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FOR_in_iterationStatement8041 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_iterationStatement8043 = new BitSet(new long[]{0x691230621920E0F0L,0x10308183C404065EL,0xFF9F7C3A0D952800L,0x000000000000100CL});
	public static final BitSet FOLLOW_declaration_in_iterationStatement8059 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614701A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_opt_in_iterationStatement8063 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_SEMI_in_iterationStatement8065 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A48012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_opt_in_iterationStatement8069 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_iterationStatement8076 = new BitSet(new long[]{0x21011303F34080C0L,0x002081260C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_invariant_opt_in_iterationStatement8080 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statementWithScope_in_iterationStatement8084 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_expression_opt_in_iterationStatement8119 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_SEMI_in_iterationStatement8121 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614701A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_opt_in_iterationStatement8125 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_SEMI_in_iterationStatement8127 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A48012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_opt_in_iterationStatement8136 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_iterationStatement8138 = new BitSet(new long[]{0x21011303F34080C0L,0x002081260C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_invariant_opt_in_iterationStatement8142 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statementWithScope_in_iterationStatement8151 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_CIVLFOR_in_iterationStatement8190 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_PARFOR_in_iterationStatement8196 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_iterationStatement8199 = new BitSet(new long[]{0x0812006008202000L,0x1000008184000008L,0xD0080C0004900000L,0x000000000000000CL});
	public static final BitSet FOLLOW_typeName_opt_in_iterationStatement8208 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_identifierList_in_iterationStatement8212 = new BitSet(new long[]{0x0000000400000000L});
	public static final BitSet FOLLOW_COLON_in_iterationStatement8214 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_iterationStatement8218 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_iterationStatement8220 = new BitSet(new long[]{0x21011303F34080C0L,0x002081260C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_invariant_opt_in_iterationStatement8229 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statementWithScope_in_iterationStatement8233 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_expression_in_expression_opt8271 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INVARIANT_in_invariant_opt8296 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_invariant_opt8298 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_invariant_opt8300 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_invariant_opt8302 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_typeName_in_typeName_opt8323 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_GOTO_in_jumpStatement8346 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_jumpStatement8348 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_SEMI_in_jumpStatement8350 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_CONTINUE_in_jumpStatement8368 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_SEMI_in_jumpStatement8370 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BREAK_in_jumpStatement8386 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_SEMI_in_jumpStatement8388 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RETURN_in_jumpStatement8404 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614701A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_opt_in_jumpStatement8406 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000001000000000L});
	public static final BitSet FOLLOW_SEMI_in_jumpStatement8408 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PRAGMA_in_pragma8437 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_pragma8439 = new BitSet(new long[]{0x0000000000000000L,0x0008000000000000L});
	public static final BitSet FOLLOW_NEWLINE_in_pragma8441 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PRAGMA_in_pragma8471 = new BitSet(new long[]{0x0000000000000000L,0x0000000004000000L});
	public static final BitSet FOLLOW_IDENTIFIER_in_pragma8473 = new BitSet(new long[]{0xFFFFFFFFFFFFFFF0L,0xFFF7FFFFFFFFFFFFL,0xFFFFFFFFFFFFFFFFL,0xFFFFFFFFFFFFFFFFL,0xFFFFFFFFFFFFFFFFL,0xFFFFFFFFFFFFFFFFL,0xFFFFFFFFFFFFFFFFL,0xFFFFFFFFFFFFFFFFL,0x00000000000001FFL});
	public static final BitSet FOLLOW_pragmaBody_in_pragma8475 = new BitSet(new long[]{0x0000000000000000L,0x0008000000000000L});
	public static final BitSet FOLLOW_NEWLINE_in_pragma8477 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_WHEN_in_whenStatement8532 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_whenStatement8534 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_whenStatement8536 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_whenStatement8538 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statement_in_whenStatement8540 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_CHOOSE_in_chooseStatement8565 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_chooseStatement8567 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statement_in_chooseStatement8569 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18212801L,0x0000000000001030L});
	public static final BitSet FOLLOW_RCURLY_in_chooseStatement8572 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_CIVLATOMIC_in_atomicStatement8597 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statementWithScope_in_atomicStatement8601 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_CIVLATOM_in_datomicStatement8625 = new BitSet(new long[]{0x21011303F34080C0L,0x002081220C040A72L,0x2654701A18012801L,0x0000000000001030L});
	public static final BitSet FOLLOW_statementWithScope_in_datomicStatement8629 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_declarator_in_functionDefinition8669 = new BitSet(new long[]{0x4C12286008206830L,0x101000A1C400440CL,0xD98B0C2007D40000L,0x000000000000000CL});
	public static final BitSet FOLLOW_contract_in_functionDefinition8674 = new BitSet(new long[]{0x4812206008206030L,0x101000A1C400040CL,0xD98B0C2005940000L,0x000000000000000CL});
	public static final BitSet FOLLOW_declarationList_opt_in_functionDefinition8679 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_compoundStatement_in_functionDefinition8684 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_declarationSpecifiers_in_functionDefinition8729 = new BitSet(new long[]{0x0000000000000000L,0x0000010004000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_declarator_in_functionDefinition8734 = new BitSet(new long[]{0x4C12286008206830L,0x101000A1C400440CL,0xD98B0C2007D40000L,0x000000000000000CL});
	public static final BitSet FOLLOW_contract_in_functionDefinition8739 = new BitSet(new long[]{0x4812206008206030L,0x101000A1C400040CL,0xD98B0C2005940000L,0x000000000000000CL});
	public static final BitSet FOLLOW_declarationList_opt_in_functionDefinition8744 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_compoundStatement_in_functionDefinition8749 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_declaration_in_declarationList_opt8798 = new BitSet(new long[]{0x4812206008206032L,0x10100081C400040CL,0xD98B0C2005940000L,0x000000000000000CL});
	public static final BitSet FOLLOW_separationLogicItem_in_contractItem8821 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_porItem_in_contractItem8829 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REQUIRES_in_separationLogicItem8849 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_separationLogicItem8851 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_separationLogicItem8853 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_separationLogicItem8855 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ENSURES_in_separationLogicItem8870 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_separationLogicItem8872 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_separationLogicItem8874 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_separationLogicItem8876 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DEPENDS_in_porItem8909 = new BitSet(new long[]{0x0000000000000000L,0x0000042000000000L});
	public static final BitSet FOLLOW_LSQUARE_in_porItem8912 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_porItem8914 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_porItem8916 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_porItem8920 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08212800L,0x0000000000001000L});
	public static final BitSet FOLLOW_argumentExpressionList_in_porItem8922 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_porItem8924 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_GUARD_in_porItem8943 = new BitSet(new long[]{0x0000000000000000L,0x0000042000000000L});
	public static final BitSet FOLLOW_LSQUARE_in_porItem8946 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_porItem8948 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_porItem8950 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_porItem8954 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08212800L,0x0000000000001000L});
	public static final BitSet FOLLOW_argumentExpressionList_in_porItem8956 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_porItem8958 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSIGNS_in_porItem8977 = new BitSet(new long[]{0x0000000000000000L,0x0000042000000000L});
	public static final BitSet FOLLOW_LSQUARE_in_porItem8980 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_porItem8982 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_porItem8984 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_porItem8988 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08212800L,0x0000000000001000L});
	public static final BitSet FOLLOW_argumentExpressionList_in_porItem8990 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_porItem8992 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_READS_in_porItem9011 = new BitSet(new long[]{0x0000000000000000L,0x0000042000000000L});
	public static final BitSet FOLLOW_LSQUARE_in_porItem9014 = new BitSet(new long[]{0x21001002110080C0L,0x0020810204040252L,0x2614700A08012800L,0x0000000000001000L});
	public static final BitSet FOLLOW_expression_in_porItem9016 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_RSQUARE_in_porItem9018 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_porItem9022 = new BitSet(new long[]{0x21001000110080C0L,0x0020810204040252L,0x2614700A08212800L,0x0000000000001000L});
	public static final BitSet FOLLOW_argumentExpressionList_in_porItem9024 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000200000L});
	public static final BitSet FOLLOW_RCURLY_in_porItem9026 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_contractItem_in_contract9054 = new BitSet(new long[]{0x0400080000000802L,0x0000000000004000L,0x0000000002400000L});
	public static final BitSet FOLLOW_blockItem_in_blockItemWithScope9088 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_functionDefinition_in_blockItem9123 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_functionDefinition_in_blockItem9154 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_declaration_in_blockItem9159 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_pragma_in_blockItem9165 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_statement_in_blockItem9173 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_blockItem_in_translationUnit9203 = new BitSet(new long[]{0x69133363FB60E0F0L,0x103081A3CC040E7EL,0xFFDF7C3A1D95A801L,0x000000000000103CL});
	public static final BitSet FOLLOW_EOF_in_translationUnit9206 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_synpred1_CivlCParser1772 = new BitSet(new long[]{0x0812006008202000L,0x1000008184000008L,0xD0080C0004900000L,0x000000000000000CL});
	public static final BitSet FOLLOW_typeName_in_synpred1_CivlCParser1774 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_synpred1_CivlCParser1776 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_synpred1_CivlCParser1778 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SIZEOF_in_synpred2_CivlCParser1999 = new BitSet(new long[]{0x0000000000000000L,0x0000010000000000L});
	public static final BitSet FOLLOW_LPAREN_in_synpred2_CivlCParser2001 = new BitSet(new long[]{0x0812006008202000L,0x1000008184000008L,0xD0080C0004900000L,0x000000000000000CL});
	public static final BitSet FOLLOW_typeName_in_synpred2_CivlCParser2003 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_synpred3_CivlCParser2272 = new BitSet(new long[]{0x0812006008202000L,0x1000008184000008L,0xD0080C0004900000L,0x000000000000000CL});
	public static final BitSet FOLLOW_typeName_in_synpred3_CivlCParser2274 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_synpred3_CivlCParser2276 = new BitSet(new long[]{0xFFFFFFFFFFFFFFF0L,0xFFFFFFDFFFFFFFFFL,0xFFFFFFFFFFFFFFFFL,0xFFFFFFFFFFFFFFFFL,0xFFFFFFFFFFFFFFFFL,0xFFFFFFFFFFFFFFFFL,0xFFFFFFFFFFFFFFFFL,0xFFFFFFFFFFFFFFFFL,0x00000000000001FFL});
	public static final BitSet FOLLOW_set_in_synpred3_CivlCParser2278 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unaryExpression_in_synpred4_CivlCParser3652 = new BitSet(new long[]{0x0000800000150400L,0x0002000000000000L,0x0020828000001000L});
	public static final BitSet FOLLOW_assignmentOperator_in_synpred4_CivlCParser3654 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_typeSpecifier_in_synpred5_CivlCParser4090 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_declarator_in_synpred6_CivlCParser6307 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ELSE_in_synpred7_CivlCParser7837 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_declarator_in_synpred8_CivlCParser9103 = new BitSet(new long[]{0x4C12286008206830L,0x101000A1C400440CL,0xD98B0C2007D40000L,0x000000000000000CL});
	public static final BitSet FOLLOW_contract_in_synpred8_CivlCParser9105 = new BitSet(new long[]{0x4812206008206030L,0x101000A1C400040CL,0xD98B0C2005940000L,0x000000000000000CL});
	public static final BitSet FOLLOW_declarationList_opt_in_synpred8_CivlCParser9114 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_synpred8_CivlCParser9116 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_declarationSpecifiers_in_synpred9_CivlCParser9132 = new BitSet(new long[]{0x0000000000000000L,0x0000010004000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_declarator_in_synpred9_CivlCParser9134 = new BitSet(new long[]{0x4C12286008206830L,0x101000A1C400440CL,0xD98B0C2007D40000L,0x000000000000000CL});
	public static final BitSet FOLLOW_contract_in_synpred9_CivlCParser9136 = new BitSet(new long[]{0x4812206008206030L,0x101000A1C400040CL,0xD98B0C2005940000L,0x000000000000000CL});
	public static final BitSet FOLLOW_declarationList_opt_in_synpred9_CivlCParser9145 = new BitSet(new long[]{0x0000000000000000L,0x0000002000000000L});
	public static final BitSet FOLLOW_LCURLY_in_synpred9_CivlCParser9147 = new BitSet(new long[]{0x0000000000000002L});
}
