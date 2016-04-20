// $ANTLR 3.5.2 PreprocessorExpressionParser.g 2016-04-11 02:06:13

package edu.udel.cis.vsl.abc.front.c.preproc;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

import org.antlr.runtime.tree.*;


@SuppressWarnings("all")
public class PreprocessorExpressionParser extends Parser {
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
		"UnsignedSuffix", "VOID", "VOLATILE", "WHEN", "WHILE", "WS", "Zero", "EXPR", 
		"PROC", "ROOT", "WAIT"
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
	public static final int EXPR=200;
	public static final int PROC=201;
	public static final int ROOT=202;
	public static final int WAIT=203;

	// delegates
	public Parser[] getDelegates() {
		return new Parser[] {};
	}

	// delegators


	public PreprocessorExpressionParser(TokenStream input) {
		this(input, new RecognizerSharedState());
	}
	public PreprocessorExpressionParser(TokenStream input, RecognizerSharedState state) {
		super(input, state);
	}

	protected TreeAdaptor adaptor = new CommonTreeAdaptor();

	public void setTreeAdaptor(TreeAdaptor adaptor) {
		this.adaptor = adaptor;
	}
	public TreeAdaptor getTreeAdaptor() {
		return adaptor;
	}
	@Override public String[] getTokenNames() { return PreprocessorExpressionParser.tokenNames; }
	@Override public String getGrammarFileName() { return "PreprocessorExpressionParser.g"; }


	public static class start_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "start"
	// PreprocessorExpressionParser.g:24:1: start : expr EOF -> expr ;
	public final PreprocessorExpressionParser.start_return start() throws RecognitionException {
		PreprocessorExpressionParser.start_return retval = new PreprocessorExpressionParser.start_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token EOF2=null;
		ParserRuleReturnScope expr1 =null;

		Object EOF2_tree=null;
		RewriteRuleTokenStream stream_EOF=new RewriteRuleTokenStream(adaptor,"token EOF");
		RewriteRuleSubtreeStream stream_expr=new RewriteRuleSubtreeStream(adaptor,"rule expr");

		try {
			// PreprocessorExpressionParser.g:24:8: ( expr EOF -> expr )
			// PreprocessorExpressionParser.g:24:10: expr EOF
			{
			pushFollow(FOLLOW_expr_in_start56);
			expr1=expr();
			state._fsp--;

			stream_expr.add(expr1.getTree());
			EOF2=(Token)match(input,EOF,FOLLOW_EOF_in_start58);  
			stream_EOF.add(EOF2);

			// AST REWRITE
			// elements: expr
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 24:19: -> expr
			{
				adaptor.addChild(root_0, stream_expr.nextTree());
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
	// $ANTLR end "start"


	public static class expr_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "expr"
	// PreprocessorExpressionParser.g:27:1: expr : logical_or_expr ;
	public final PreprocessorExpressionParser.expr_return expr() throws RecognitionException {
		PreprocessorExpressionParser.expr_return retval = new PreprocessorExpressionParser.expr_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope logical_or_expr3 =null;


		try {
			// PreprocessorExpressionParser.g:27:8: ( logical_or_expr )
			// PreprocessorExpressionParser.g:27:10: logical_or_expr
			{
			root_0 = (Object)adaptor.nil();


			pushFollow(FOLLOW_logical_or_expr_in_expr75);
			logical_or_expr3=logical_or_expr();
			state._fsp--;

			adaptor.addChild(root_0, logical_or_expr3.getTree());

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


	public static class logical_or_expr_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "logical_or_expr"
	// PreprocessorExpressionParser.g:36:1: logical_or_expr : ( logical_and_expr -> logical_and_expr ) ( OR arg= logical_and_expr -> ^( OR $logical_or_expr $arg) )* ;
	public final PreprocessorExpressionParser.logical_or_expr_return logical_or_expr() throws RecognitionException {
		PreprocessorExpressionParser.logical_or_expr_return retval = new PreprocessorExpressionParser.logical_or_expr_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token OR5=null;
		ParserRuleReturnScope arg =null;
		ParserRuleReturnScope logical_and_expr4 =null;

		Object OR5_tree=null;
		RewriteRuleTokenStream stream_OR=new RewriteRuleTokenStream(adaptor,"token OR");
		RewriteRuleSubtreeStream stream_logical_and_expr=new RewriteRuleSubtreeStream(adaptor,"rule logical_and_expr");

		try {
			// PreprocessorExpressionParser.g:36:17: ( ( logical_and_expr -> logical_and_expr ) ( OR arg= logical_and_expr -> ^( OR $logical_or_expr $arg) )* )
			// PreprocessorExpressionParser.g:36:19: ( logical_and_expr -> logical_and_expr ) ( OR arg= logical_and_expr -> ^( OR $logical_or_expr $arg) )*
			{
			// PreprocessorExpressionParser.g:36:19: ( logical_and_expr -> logical_and_expr )
			// PreprocessorExpressionParser.g:36:20: logical_and_expr
			{
			pushFollow(FOLLOW_logical_and_expr_in_logical_or_expr89);
			logical_and_expr4=logical_and_expr();
			state._fsp--;

			stream_logical_and_expr.add(logical_and_expr4.getTree());
			// AST REWRITE
			// elements: logical_and_expr
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 36:37: -> logical_and_expr
			{
				adaptor.addChild(root_0, stream_logical_and_expr.nextTree());
			}


			retval.tree = root_0;

			}

			// PreprocessorExpressionParser.g:37:4: ( OR arg= logical_and_expr -> ^( OR $logical_or_expr $arg) )*
			loop1:
			while (true) {
				int alt1=2;
				int LA1_0 = input.LA(1);
				if ( (LA1_0==OR) ) {
					alt1=1;
				}

				switch (alt1) {
				case 1 :
					// PreprocessorExpressionParser.g:37:5: OR arg= logical_and_expr
					{
					OR5=(Token)match(input,OR,FOLLOW_OR_in_logical_or_expr100);  
					stream_OR.add(OR5);

					pushFollow(FOLLOW_logical_and_expr_in_logical_or_expr104);
					arg=logical_and_expr();
					state._fsp--;

					stream_logical_and_expr.add(arg.getTree());
					// AST REWRITE
					// elements: logical_or_expr, arg, OR
					// token labels: 
					// rule labels: arg, retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_arg=new RewriteRuleSubtreeStream(adaptor,"rule arg",arg!=null?arg.getTree():null);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 37:29: -> ^( OR $logical_or_expr $arg)
					{
						// PreprocessorExpressionParser.g:37:32: ^( OR $logical_or_expr $arg)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_OR.nextNode(), root_1);
						adaptor.addChild(root_1, stream_retval.nextTree());
						adaptor.addChild(root_1, stream_arg.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

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
	// $ANTLR end "logical_or_expr"


	public static class logical_and_expr_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "logical_and_expr"
	// PreprocessorExpressionParser.g:46:1: logical_and_expr : ( equality_expr -> equality_expr ) ( AND arg= equality_expr -> ^( AND $logical_and_expr $arg) )* ;
	public final PreprocessorExpressionParser.logical_and_expr_return logical_and_expr() throws RecognitionException {
		PreprocessorExpressionParser.logical_and_expr_return retval = new PreprocessorExpressionParser.logical_and_expr_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token AND7=null;
		ParserRuleReturnScope arg =null;
		ParserRuleReturnScope equality_expr6 =null;

		Object AND7_tree=null;
		RewriteRuleTokenStream stream_AND=new RewriteRuleTokenStream(adaptor,"token AND");
		RewriteRuleSubtreeStream stream_equality_expr=new RewriteRuleSubtreeStream(adaptor,"rule equality_expr");

		try {
			// PreprocessorExpressionParser.g:46:17: ( ( equality_expr -> equality_expr ) ( AND arg= equality_expr -> ^( AND $logical_and_expr $arg) )* )
			// PreprocessorExpressionParser.g:46:19: ( equality_expr -> equality_expr ) ( AND arg= equality_expr -> ^( AND $logical_and_expr $arg) )*
			{
			// PreprocessorExpressionParser.g:46:19: ( equality_expr -> equality_expr )
			// PreprocessorExpressionParser.g:46:20: equality_expr
			{
			pushFollow(FOLLOW_equality_expr_in_logical_and_expr131);
			equality_expr6=equality_expr();
			state._fsp--;

			stream_equality_expr.add(equality_expr6.getTree());
			// AST REWRITE
			// elements: equality_expr
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 46:34: -> equality_expr
			{
				adaptor.addChild(root_0, stream_equality_expr.nextTree());
			}


			retval.tree = root_0;

			}

			// PreprocessorExpressionParser.g:47:4: ( AND arg= equality_expr -> ^( AND $logical_and_expr $arg) )*
			loop2:
			while (true) {
				int alt2=2;
				int LA2_0 = input.LA(1);
				if ( (LA2_0==AND) ) {
					alt2=1;
				}

				switch (alt2) {
				case 1 :
					// PreprocessorExpressionParser.g:47:5: AND arg= equality_expr
					{
					AND7=(Token)match(input,AND,FOLLOW_AND_in_logical_and_expr142);  
					stream_AND.add(AND7);

					pushFollow(FOLLOW_equality_expr_in_logical_and_expr146);
					arg=equality_expr();
					state._fsp--;

					stream_equality_expr.add(arg.getTree());
					// AST REWRITE
					// elements: AND, logical_and_expr, arg
					// token labels: 
					// rule labels: arg, retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_arg=new RewriteRuleSubtreeStream(adaptor,"rule arg",arg!=null?arg.getTree():null);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 47:27: -> ^( AND $logical_and_expr $arg)
					{
						// PreprocessorExpressionParser.g:47:30: ^( AND $logical_and_expr $arg)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_AND.nextNode(), root_1);
						adaptor.addChild(root_1, stream_retval.nextTree());
						adaptor.addChild(root_1, stream_arg.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

				default :
					break loop2;
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
	// $ANTLR end "logical_and_expr"


	public static class equality_expr_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "equality_expr"
	// PreprocessorExpressionParser.g:56:1: equality_expr : ( relational_expr -> relational_expr ) (op= equality_operator arg= relational_expr -> ^( $op $equality_expr $arg) )* ;
	public final PreprocessorExpressionParser.equality_expr_return equality_expr() throws RecognitionException {
		PreprocessorExpressionParser.equality_expr_return retval = new PreprocessorExpressionParser.equality_expr_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope op =null;
		ParserRuleReturnScope arg =null;
		ParserRuleReturnScope relational_expr8 =null;

		RewriteRuleSubtreeStream stream_relational_expr=new RewriteRuleSubtreeStream(adaptor,"rule relational_expr");
		RewriteRuleSubtreeStream stream_equality_operator=new RewriteRuleSubtreeStream(adaptor,"rule equality_operator");

		try {
			// PreprocessorExpressionParser.g:56:15: ( ( relational_expr -> relational_expr ) (op= equality_operator arg= relational_expr -> ^( $op $equality_expr $arg) )* )
			// PreprocessorExpressionParser.g:56:17: ( relational_expr -> relational_expr ) (op= equality_operator arg= relational_expr -> ^( $op $equality_expr $arg) )*
			{
			// PreprocessorExpressionParser.g:56:17: ( relational_expr -> relational_expr )
			// PreprocessorExpressionParser.g:56:18: relational_expr
			{
			pushFollow(FOLLOW_relational_expr_in_equality_expr174);
			relational_expr8=relational_expr();
			state._fsp--;

			stream_relational_expr.add(relational_expr8.getTree());
			// AST REWRITE
			// elements: relational_expr
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 56:34: -> relational_expr
			{
				adaptor.addChild(root_0, stream_relational_expr.nextTree());
			}


			retval.tree = root_0;

			}

			// PreprocessorExpressionParser.g:57:4: (op= equality_operator arg= relational_expr -> ^( $op $equality_expr $arg) )*
			loop3:
			while (true) {
				int alt3=2;
				int LA3_0 = input.LA(1);
				if ( (LA3_0==EQUALS||LA3_0==NEQ) ) {
					alt3=1;
				}

				switch (alt3) {
				case 1 :
					// PreprocessorExpressionParser.g:57:5: op= equality_operator arg= relational_expr
					{
					pushFollow(FOLLOW_equality_operator_in_equality_expr187);
					op=equality_operator();
					state._fsp--;

					stream_equality_operator.add(op.getTree());
					pushFollow(FOLLOW_relational_expr_in_equality_expr191);
					arg=relational_expr();
					state._fsp--;

					stream_relational_expr.add(arg.getTree());
					// AST REWRITE
					// elements: equality_expr, op, arg
					// token labels: 
					// rule labels: arg, retval, op
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_arg=new RewriteRuleSubtreeStream(adaptor,"rule arg",arg!=null?arg.getTree():null);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_op=new RewriteRuleSubtreeStream(adaptor,"rule op",op!=null?op.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 58:7: -> ^( $op $equality_expr $arg)
					{
						// PreprocessorExpressionParser.g:58:10: ^( $op $equality_expr $arg)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_op.nextNode(), root_1);
						adaptor.addChild(root_1, stream_retval.nextTree());
						adaptor.addChild(root_1, stream_arg.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

				default :
					break loop3;
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
	// $ANTLR end "equality_expr"


	public static class equality_operator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "equality_operator"
	// PreprocessorExpressionParser.g:61:1: equality_operator : ( EQUALS | NEQ );
	public final PreprocessorExpressionParser.equality_operator_return equality_operator() throws RecognitionException {
		PreprocessorExpressionParser.equality_operator_return retval = new PreprocessorExpressionParser.equality_operator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set9=null;

		Object set9_tree=null;

		try {
			// PreprocessorExpressionParser.g:62:3: ( EQUALS | NEQ )
			// PreprocessorExpressionParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set9=input.LT(1);
			if ( input.LA(1)==EQUALS||input.LA(1)==NEQ ) {
				input.consume();
				adaptor.addChild(root_0, (Object)adaptor.create(set9));
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
	// $ANTLR end "equality_operator"


	public static class relational_expr_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "relational_expr"
	// PreprocessorExpressionParser.g:72:1: relational_expr : ( additive_expr -> additive_expr ) (op= relational_operator arg= additive_expr -> ^( $op $relational_expr $arg) )* ;
	public final PreprocessorExpressionParser.relational_expr_return relational_expr() throws RecognitionException {
		PreprocessorExpressionParser.relational_expr_return retval = new PreprocessorExpressionParser.relational_expr_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope op =null;
		ParserRuleReturnScope arg =null;
		ParserRuleReturnScope additive_expr10 =null;

		RewriteRuleSubtreeStream stream_additive_expr=new RewriteRuleSubtreeStream(adaptor,"rule additive_expr");
		RewriteRuleSubtreeStream stream_relational_operator=new RewriteRuleSubtreeStream(adaptor,"rule relational_operator");

		try {
			// PreprocessorExpressionParser.g:72:17: ( ( additive_expr -> additive_expr ) (op= relational_operator arg= additive_expr -> ^( $op $relational_expr $arg) )* )
			// PreprocessorExpressionParser.g:72:19: ( additive_expr -> additive_expr ) (op= relational_operator arg= additive_expr -> ^( $op $relational_expr $arg) )*
			{
			// PreprocessorExpressionParser.g:72:19: ( additive_expr -> additive_expr )
			// PreprocessorExpressionParser.g:72:20: additive_expr
			{
			pushFollow(FOLLOW_additive_expr_in_relational_expr245);
			additive_expr10=additive_expr();
			state._fsp--;

			stream_additive_expr.add(additive_expr10.getTree());
			// AST REWRITE
			// elements: additive_expr
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 72:34: -> additive_expr
			{
				adaptor.addChild(root_0, stream_additive_expr.nextTree());
			}


			retval.tree = root_0;

			}

			// PreprocessorExpressionParser.g:73:4: (op= relational_operator arg= additive_expr -> ^( $op $relational_expr $arg) )*
			loop4:
			while (true) {
				int alt4=2;
				int LA4_0 = input.LA(1);
				if ( ((LA4_0 >= GT && LA4_0 <= GTE)||(LA4_0 >= LT && LA4_0 <= LTE)) ) {
					alt4=1;
				}

				switch (alt4) {
				case 1 :
					// PreprocessorExpressionParser.g:73:5: op= relational_operator arg= additive_expr
					{
					pushFollow(FOLLOW_relational_operator_in_relational_expr258);
					op=relational_operator();
					state._fsp--;

					stream_relational_operator.add(op.getTree());
					pushFollow(FOLLOW_additive_expr_in_relational_expr262);
					arg=additive_expr();
					state._fsp--;

					stream_additive_expr.add(arg.getTree());
					// AST REWRITE
					// elements: relational_expr, arg, op
					// token labels: 
					// rule labels: arg, retval, op
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_arg=new RewriteRuleSubtreeStream(adaptor,"rule arg",arg!=null?arg.getTree():null);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_op=new RewriteRuleSubtreeStream(adaptor,"rule op",op!=null?op.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 74:7: -> ^( $op $relational_expr $arg)
					{
						// PreprocessorExpressionParser.g:74:10: ^( $op $relational_expr $arg)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_op.nextNode(), root_1);
						adaptor.addChild(root_1, stream_retval.nextTree());
						adaptor.addChild(root_1, stream_arg.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

				default :
					break loop4;
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
	// $ANTLR end "relational_expr"


	public static class relational_operator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "relational_operator"
	// PreprocessorExpressionParser.g:77:1: relational_operator : ( LT | GT | LTE | GTE );
	public final PreprocessorExpressionParser.relational_operator_return relational_operator() throws RecognitionException {
		PreprocessorExpressionParser.relational_operator_return retval = new PreprocessorExpressionParser.relational_operator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set11=null;

		Object set11_tree=null;

		try {
			// PreprocessorExpressionParser.g:78:3: ( LT | GT | LTE | GTE )
			// PreprocessorExpressionParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set11=input.LT(1);
			if ( (input.LA(1) >= GT && input.LA(1) <= GTE)||(input.LA(1) >= LT && input.LA(1) <= LTE) ) {
				input.consume();
				adaptor.addChild(root_0, (Object)adaptor.create(set11));
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
	// $ANTLR end "relational_operator"


	public static class additive_expr_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "additive_expr"
	// PreprocessorExpressionParser.g:89:1: additive_expr : ( multi_expr -> multi_expr ) ( additive_operator arg= multi_expr -> ^( additive_operator $additive_expr $arg) )* ;
	public final PreprocessorExpressionParser.additive_expr_return additive_expr() throws RecognitionException {
		PreprocessorExpressionParser.additive_expr_return retval = new PreprocessorExpressionParser.additive_expr_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope arg =null;
		ParserRuleReturnScope multi_expr12 =null;
		ParserRuleReturnScope additive_operator13 =null;

		RewriteRuleSubtreeStream stream_additive_operator=new RewriteRuleSubtreeStream(adaptor,"rule additive_operator");
		RewriteRuleSubtreeStream stream_multi_expr=new RewriteRuleSubtreeStream(adaptor,"rule multi_expr");

		try {
			// PreprocessorExpressionParser.g:89:15: ( ( multi_expr -> multi_expr ) ( additive_operator arg= multi_expr -> ^( additive_operator $additive_expr $arg) )* )
			// PreprocessorExpressionParser.g:89:17: ( multi_expr -> multi_expr ) ( additive_operator arg= multi_expr -> ^( additive_operator $additive_expr $arg) )*
			{
			// PreprocessorExpressionParser.g:89:17: ( multi_expr -> multi_expr )
			// PreprocessorExpressionParser.g:89:18: multi_expr
			{
			pushFollow(FOLLOW_multi_expr_in_additive_expr328);
			multi_expr12=multi_expr();
			state._fsp--;

			stream_multi_expr.add(multi_expr12.getTree());
			// AST REWRITE
			// elements: multi_expr
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 89:29: -> multi_expr
			{
				adaptor.addChild(root_0, stream_multi_expr.nextTree());
			}


			retval.tree = root_0;

			}

			// PreprocessorExpressionParser.g:90:4: ( additive_operator arg= multi_expr -> ^( additive_operator $additive_expr $arg) )*
			loop5:
			while (true) {
				int alt5=2;
				int LA5_0 = input.LA(1);
				if ( (LA5_0==PLUS||LA5_0==SUB) ) {
					alt5=1;
				}

				switch (alt5) {
				case 1 :
					// PreprocessorExpressionParser.g:90:5: additive_operator arg= multi_expr
					{
					pushFollow(FOLLOW_additive_operator_in_additive_expr339);
					additive_operator13=additive_operator();
					state._fsp--;

					stream_additive_operator.add(additive_operator13.getTree());
					pushFollow(FOLLOW_multi_expr_in_additive_expr343);
					arg=multi_expr();
					state._fsp--;

					stream_multi_expr.add(arg.getTree());
					// AST REWRITE
					// elements: additive_expr, additive_operator, arg
					// token labels: 
					// rule labels: arg, retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_arg=new RewriteRuleSubtreeStream(adaptor,"rule arg",arg!=null?arg.getTree():null);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 91:7: -> ^( additive_operator $additive_expr $arg)
					{
						// PreprocessorExpressionParser.g:91:10: ^( additive_operator $additive_expr $arg)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_additive_operator.nextNode(), root_1);
						adaptor.addChild(root_1, stream_retval.nextTree());
						adaptor.addChild(root_1, stream_arg.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

				default :
					break loop5;
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
	// $ANTLR end "additive_expr"


	public static class additive_operator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "additive_operator"
	// PreprocessorExpressionParser.g:93:1: additive_operator : ( PLUS | SUB );
	public final PreprocessorExpressionParser.additive_operator_return additive_operator() throws RecognitionException {
		PreprocessorExpressionParser.additive_operator_return retval = new PreprocessorExpressionParser.additive_operator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set14=null;

		Object set14_tree=null;

		try {
			// PreprocessorExpressionParser.g:94:3: ( PLUS | SUB )
			// PreprocessorExpressionParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set14=input.LT(1);
			if ( input.LA(1)==PLUS||input.LA(1)==SUB ) {
				input.consume();
				adaptor.addChild(root_0, (Object)adaptor.create(set14));
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
	// $ANTLR end "additive_operator"


	public static class multi_expr_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "multi_expr"
	// PreprocessorExpressionParser.g:103:1: multi_expr : ( unary_expr -> unary_expr ) ( multi_operator unary_expr -> ^( multi_operator $multi_expr unary_expr ) )* ;
	public final PreprocessorExpressionParser.multi_expr_return multi_expr() throws RecognitionException {
		PreprocessorExpressionParser.multi_expr_return retval = new PreprocessorExpressionParser.multi_expr_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope unary_expr15 =null;
		ParserRuleReturnScope multi_operator16 =null;
		ParserRuleReturnScope unary_expr17 =null;

		RewriteRuleSubtreeStream stream_unary_expr=new RewriteRuleSubtreeStream(adaptor,"rule unary_expr");
		RewriteRuleSubtreeStream stream_multi_operator=new RewriteRuleSubtreeStream(adaptor,"rule multi_operator");

		try {
			// PreprocessorExpressionParser.g:103:12: ( ( unary_expr -> unary_expr ) ( multi_operator unary_expr -> ^( multi_operator $multi_expr unary_expr ) )* )
			// PreprocessorExpressionParser.g:103:14: ( unary_expr -> unary_expr ) ( multi_operator unary_expr -> ^( multi_operator $multi_expr unary_expr ) )*
			{
			// PreprocessorExpressionParser.g:103:14: ( unary_expr -> unary_expr )
			// PreprocessorExpressionParser.g:103:15: unary_expr
			{
			pushFollow(FOLLOW_unary_expr_in_multi_expr396);
			unary_expr15=unary_expr();
			state._fsp--;

			stream_unary_expr.add(unary_expr15.getTree());
			// AST REWRITE
			// elements: unary_expr
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 103:26: -> unary_expr
			{
				adaptor.addChild(root_0, stream_unary_expr.nextTree());
			}


			retval.tree = root_0;

			}

			// PreprocessorExpressionParser.g:104:4: ( multi_operator unary_expr -> ^( multi_operator $multi_expr unary_expr ) )*
			loop6:
			while (true) {
				int alt6=2;
				int LA6_0 = input.LA(1);
				if ( (LA6_0==DIV||LA6_0==MOD||LA6_0==STAR) ) {
					alt6=1;
				}

				switch (alt6) {
				case 1 :
					// PreprocessorExpressionParser.g:104:5: multi_operator unary_expr
					{
					pushFollow(FOLLOW_multi_operator_in_multi_expr407);
					multi_operator16=multi_operator();
					state._fsp--;

					stream_multi_operator.add(multi_operator16.getTree());
					pushFollow(FOLLOW_unary_expr_in_multi_expr409);
					unary_expr17=unary_expr();
					state._fsp--;

					stream_unary_expr.add(unary_expr17.getTree());
					// AST REWRITE
					// elements: unary_expr, multi_operator, multi_expr
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 105:7: -> ^( multi_operator $multi_expr unary_expr )
					{
						// PreprocessorExpressionParser.g:105:10: ^( multi_operator $multi_expr unary_expr )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_multi_operator.nextNode(), root_1);
						adaptor.addChild(root_1, stream_retval.nextTree());
						adaptor.addChild(root_1, stream_unary_expr.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;

				default :
					break loop6;
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
	// $ANTLR end "multi_expr"


	public static class multi_operator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "multi_operator"
	// PreprocessorExpressionParser.g:108:1: multi_operator : ( STAR | DIV | MOD );
	public final PreprocessorExpressionParser.multi_operator_return multi_operator() throws RecognitionException {
		PreprocessorExpressionParser.multi_operator_return retval = new PreprocessorExpressionParser.multi_operator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set18=null;

		Object set18_tree=null;

		try {
			// PreprocessorExpressionParser.g:108:16: ( STAR | DIV | MOD )
			// PreprocessorExpressionParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set18=input.LT(1);
			if ( input.LA(1)==DIV||input.LA(1)==MOD||input.LA(1)==STAR ) {
				input.consume();
				adaptor.addChild(root_0, (Object)adaptor.create(set18));
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
	// $ANTLR end "multi_operator"


	public static class unary_expr_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "unary_expr"
	// PreprocessorExpressionParser.g:117:1: unary_expr : ( primary_expr | unary_operator unary_expr -> ^( unary_operator unary_expr ) );
	public final PreprocessorExpressionParser.unary_expr_return unary_expr() throws RecognitionException {
		PreprocessorExpressionParser.unary_expr_return retval = new PreprocessorExpressionParser.unary_expr_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope primary_expr19 =null;
		ParserRuleReturnScope unary_operator20 =null;
		ParserRuleReturnScope unary_expr21 =null;

		RewriteRuleSubtreeStream stream_unary_expr=new RewriteRuleSubtreeStream(adaptor,"rule unary_expr");
		RewriteRuleSubtreeStream stream_unary_operator=new RewriteRuleSubtreeStream(adaptor,"rule unary_operator");

		try {
			// PreprocessorExpressionParser.g:117:12: ( primary_expr | unary_operator unary_expr -> ^( unary_operator unary_expr ) )
			int alt7=2;
			int LA7_0 = input.LA(1);
			if ( ((LA7_0 >= ALIGNAS && LA7_0 <= ALIGNOF)||LA7_0==ASSIGNS||(LA7_0 >= ATOMIC && LA7_0 <= AUTO)||(LA7_0 >= BOOL && LA7_0 <= BREAK)||(LA7_0 >= CALLS && LA7_0 <= CASE)||LA7_0==CHAR||LA7_0==CHOOSE||LA7_0==COLLECTIVE||(LA7_0 >= COMPLEX && LA7_0 <= CONST)||(LA7_0 >= CONTINUE && LA7_0 <= DEPENDS)||LA7_0==DEVICE||LA7_0==DO||LA7_0==DOUBLE||(LA7_0 >= ELSE && LA7_0 <= ENUM)||LA7_0==EXTERN||(LA7_0 >= FALSE && LA7_0 <= FOR)||(LA7_0 >= GENERIC && LA7_0 <= GOTO)||LA7_0==GUARD||LA7_0==HERE||(LA7_0 >= IDENTIFIER && LA7_0 <= IMAGINARY)||(LA7_0 >= INLINE && LA7_0 <= INVARIANT)||(LA7_0 >= LONG && LA7_0 <= LPAREN)||LA7_0==NORETURN||LA7_0==OUTPUT||LA7_0==PP_NUMBER||LA7_0==PROCNULL||LA7_0==READS||(LA7_0 >= REGISTER && LA7_0 <= RETURN)||LA7_0==SCOPEOF||LA7_0==SELF||LA7_0==SHARED||(LA7_0 >= SHORT && LA7_0 <= SPAWN)||(LA7_0 >= STATIC && LA7_0 <= STATICASSERT)||LA7_0==STRUCT||LA7_0==SWITCH||LA7_0==THREADLOCAL||(LA7_0 >= TRUE && LA7_0 <= TYPEOF)||(LA7_0 >= UNION && LA7_0 <= UNSIGNED)||(LA7_0 >= VOID && LA7_0 <= WHILE)||(LA7_0 >= PROC && LA7_0 <= WAIT)) ) {
				alt7=1;
			}
			else if ( (LA7_0==NOT||LA7_0==PLUS||LA7_0==STAR||LA7_0==SUB) ) {
				alt7=2;
			}

			else {
				NoViableAltException nvae =
					new NoViableAltException("", 7, 0, input);
				throw nvae;
			}

			switch (alt7) {
				case 1 :
					// PreprocessorExpressionParser.g:117:14: primary_expr
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_primary_expr_in_unary_expr464);
					primary_expr19=primary_expr();
					state._fsp--;

					adaptor.addChild(root_0, primary_expr19.getTree());

					}
					break;
				case 2 :
					// PreprocessorExpressionParser.g:118:5: unary_operator unary_expr
					{
					pushFollow(FOLLOW_unary_operator_in_unary_expr470);
					unary_operator20=unary_operator();
					state._fsp--;

					stream_unary_operator.add(unary_operator20.getTree());
					pushFollow(FOLLOW_unary_expr_in_unary_expr472);
					unary_expr21=unary_expr();
					state._fsp--;

					stream_unary_expr.add(unary_expr21.getTree());
					// AST REWRITE
					// elements: unary_expr, unary_operator
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 118:31: -> ^( unary_operator unary_expr )
					{
						// PreprocessorExpressionParser.g:118:34: ^( unary_operator unary_expr )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_unary_operator.nextNode(), root_1);
						adaptor.addChild(root_1, stream_unary_expr.nextTree());
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
	// $ANTLR end "unary_expr"


	public static class unary_operator_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "unary_operator"
	// PreprocessorExpressionParser.g:121:1: unary_operator : ( PLUS | SUB | NOT | STAR );
	public final PreprocessorExpressionParser.unary_operator_return unary_operator() throws RecognitionException {
		PreprocessorExpressionParser.unary_operator_return retval = new PreprocessorExpressionParser.unary_operator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set22=null;

		Object set22_tree=null;

		try {
			// PreprocessorExpressionParser.g:121:16: ( PLUS | SUB | NOT | STAR )
			// PreprocessorExpressionParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set22=input.LT(1);
			if ( input.LA(1)==NOT||input.LA(1)==PLUS||input.LA(1)==STAR||input.LA(1)==SUB ) {
				input.consume();
				adaptor.addChild(root_0, (Object)adaptor.create(set22));
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
	// $ANTLR end "unary_operator"


	public static class primary_expr_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "primary_expr"
	// PreprocessorExpressionParser.g:127:1: primary_expr : ( pp_number | LPAREN expr RPAREN -> expr | DEFINED ( identifier | LPAREN identifier RPAREN ) -> ^( DEFINED identifier ) | identifier );
	public final PreprocessorExpressionParser.primary_expr_return primary_expr() throws RecognitionException {
		PreprocessorExpressionParser.primary_expr_return retval = new PreprocessorExpressionParser.primary_expr_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LPAREN24=null;
		Token RPAREN26=null;
		Token DEFINED27=null;
		Token LPAREN29=null;
		Token RPAREN31=null;
		ParserRuleReturnScope pp_number23 =null;
		ParserRuleReturnScope expr25 =null;
		ParserRuleReturnScope identifier28 =null;
		ParserRuleReturnScope identifier30 =null;
		ParserRuleReturnScope identifier32 =null;

		Object LPAREN24_tree=null;
		Object RPAREN26_tree=null;
		Object DEFINED27_tree=null;
		Object LPAREN29_tree=null;
		Object RPAREN31_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_DEFINED=new RewriteRuleTokenStream(adaptor,"token DEFINED");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_expr=new RewriteRuleSubtreeStream(adaptor,"rule expr");
		RewriteRuleSubtreeStream stream_identifier=new RewriteRuleSubtreeStream(adaptor,"rule identifier");

		try {
			// PreprocessorExpressionParser.g:127:14: ( pp_number | LPAREN expr RPAREN -> expr | DEFINED ( identifier | LPAREN identifier RPAREN ) -> ^( DEFINED identifier ) | identifier )
			int alt9=4;
			switch ( input.LA(1) ) {
			case FLOATING_CONSTANT:
			case INTEGER_CONSTANT:
			case PP_NUMBER:
				{
				alt9=1;
				}
				break;
			case LPAREN:
				{
				alt9=2;
				}
				break;
			case DEFINED:
				{
				alt9=3;
				}
				break;
			case ALIGNAS:
			case ALIGNOF:
			case ASSIGNS:
			case ATOMIC:
			case AUTO:
			case BOOL:
			case BREAK:
			case CALLS:
			case CASE:
			case CHAR:
			case CHOOSE:
			case COLLECTIVE:
			case COMPLEX:
			case CONST:
			case CONTINUE:
			case DEFAULT:
			case DEPENDS:
			case DEVICE:
			case DO:
			case DOUBLE:
			case ELSE:
			case ENSURES:
			case ENUM:
			case EXTERN:
			case FALSE:
			case FATOMIC:
			case FLOAT:
			case FOR:
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
			case PROCNULL:
			case READS:
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
			case THREADLOCAL:
			case TRUE:
			case TYPEDEF:
			case TYPEOF:
			case UNION:
			case UNSIGNED:
			case VOID:
			case VOLATILE:
			case WHEN:
			case WHILE:
			case PROC:
			case ROOT:
			case WAIT:
				{
				alt9=4;
				}
				break;
			default:
				NoViableAltException nvae =
					new NoViableAltException("", 9, 0, input);
				throw nvae;
			}
			switch (alt9) {
				case 1 :
					// PreprocessorExpressionParser.g:127:16: pp_number
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_pp_number_in_primary_expr523);
					pp_number23=pp_number();
					state._fsp--;

					adaptor.addChild(root_0, pp_number23.getTree());

					}
					break;
				case 2 :
					// PreprocessorExpressionParser.g:128:5: LPAREN expr RPAREN
					{
					LPAREN24=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_primary_expr529);  
					stream_LPAREN.add(LPAREN24);

					pushFollow(FOLLOW_expr_in_primary_expr531);
					expr25=expr();
					state._fsp--;

					stream_expr.add(expr25.getTree());
					RPAREN26=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_primary_expr533);  
					stream_RPAREN.add(RPAREN26);

					// AST REWRITE
					// elements: expr
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 128:24: -> expr
					{
						adaptor.addChild(root_0, stream_expr.nextTree());
					}


					retval.tree = root_0;

					}
					break;
				case 3 :
					// PreprocessorExpressionParser.g:129:5: DEFINED ( identifier | LPAREN identifier RPAREN )
					{
					DEFINED27=(Token)match(input,DEFINED,FOLLOW_DEFINED_in_primary_expr543);  
					stream_DEFINED.add(DEFINED27);

					// PreprocessorExpressionParser.g:129:13: ( identifier | LPAREN identifier RPAREN )
					int alt8=2;
					int LA8_0 = input.LA(1);
					if ( ((LA8_0 >= ALIGNAS && LA8_0 <= ALIGNOF)||LA8_0==ASSIGNS||(LA8_0 >= ATOMIC && LA8_0 <= AUTO)||(LA8_0 >= BOOL && LA8_0 <= BREAK)||(LA8_0 >= CALLS && LA8_0 <= CASE)||LA8_0==CHAR||LA8_0==CHOOSE||LA8_0==COLLECTIVE||(LA8_0 >= COMPLEX && LA8_0 <= CONST)||(LA8_0 >= CONTINUE && LA8_0 <= DEFAULT)||LA8_0==DEPENDS||LA8_0==DEVICE||LA8_0==DO||LA8_0==DOUBLE||(LA8_0 >= ELSE && LA8_0 <= ENUM)||LA8_0==EXTERN||(LA8_0 >= FALSE && LA8_0 <= FLOAT)||LA8_0==FOR||(LA8_0 >= GENERIC && LA8_0 <= GOTO)||LA8_0==GUARD||LA8_0==HERE||(LA8_0 >= IDENTIFIER && LA8_0 <= IMAGINARY)||(LA8_0 >= INLINE && LA8_0 <= INT)||LA8_0==INVARIANT||LA8_0==LONG||LA8_0==NORETURN||LA8_0==OUTPUT||LA8_0==PROCNULL||LA8_0==READS||(LA8_0 >= REGISTER && LA8_0 <= RETURN)||LA8_0==SCOPEOF||LA8_0==SELF||LA8_0==SHARED||(LA8_0 >= SHORT && LA8_0 <= SPAWN)||(LA8_0 >= STATIC && LA8_0 <= STATICASSERT)||LA8_0==STRUCT||LA8_0==SWITCH||LA8_0==THREADLOCAL||(LA8_0 >= TRUE && LA8_0 <= TYPEOF)||(LA8_0 >= UNION && LA8_0 <= UNSIGNED)||(LA8_0 >= VOID && LA8_0 <= WHILE)||(LA8_0 >= PROC && LA8_0 <= WAIT)) ) {
						alt8=1;
					}
					else if ( (LA8_0==LPAREN) ) {
						alt8=2;
					}

					else {
						NoViableAltException nvae =
							new NoViableAltException("", 8, 0, input);
						throw nvae;
					}

					switch (alt8) {
						case 1 :
							// PreprocessorExpressionParser.g:129:15: identifier
							{
							pushFollow(FOLLOW_identifier_in_primary_expr547);
							identifier28=identifier();
							state._fsp--;

							stream_identifier.add(identifier28.getTree());
							}
							break;
						case 2 :
							// PreprocessorExpressionParser.g:129:28: LPAREN identifier RPAREN
							{
							LPAREN29=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_primary_expr551);  
							stream_LPAREN.add(LPAREN29);

							pushFollow(FOLLOW_identifier_in_primary_expr553);
							identifier30=identifier();
							state._fsp--;

							stream_identifier.add(identifier30.getTree());
							RPAREN31=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_primary_expr555);  
							stream_RPAREN.add(RPAREN31);

							}
							break;

					}

					// AST REWRITE
					// elements: identifier, DEFINED
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 130:4: -> ^( DEFINED identifier )
					{
						// PreprocessorExpressionParser.g:130:7: ^( DEFINED identifier )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_DEFINED.nextNode(), root_1);
						adaptor.addChild(root_1, stream_identifier.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;

					}
					break;
				case 4 :
					// PreprocessorExpressionParser.g:131:5: identifier
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_identifier_in_primary_expr574);
					identifier32=identifier();
					state._fsp--;

					adaptor.addChild(root_0, identifier32.getTree());

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
	// $ANTLR end "primary_expr"


	public static class white_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "white"
	// PreprocessorExpressionParser.g:135:1: white : ( WS | NEWLINE );
	public final PreprocessorExpressionParser.white_return white() throws RecognitionException {
		PreprocessorExpressionParser.white_return retval = new PreprocessorExpressionParser.white_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set33=null;

		Object set33_tree=null;

		try {
			// PreprocessorExpressionParser.g:135:8: ( WS | NEWLINE )
			// PreprocessorExpressionParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set33=input.LT(1);
			if ( input.LA(1)==NEWLINE||input.LA(1)==WS ) {
				input.consume();
				adaptor.addChild(root_0, (Object)adaptor.create(set33));
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


	public static class identifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "identifier"
	// PreprocessorExpressionParser.g:140:1: identifier : ( IDENTIFIER | c_keyword | civl_keyword | cuda_keyword | gnuc_keyword );
	public final PreprocessorExpressionParser.identifier_return identifier() throws RecognitionException {
		PreprocessorExpressionParser.identifier_return retval = new PreprocessorExpressionParser.identifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token IDENTIFIER34=null;
		ParserRuleReturnScope c_keyword35 =null;
		ParserRuleReturnScope civl_keyword36 =null;
		ParserRuleReturnScope cuda_keyword37 =null;
		ParserRuleReturnScope gnuc_keyword38 =null;

		Object IDENTIFIER34_tree=null;

		try {
			// PreprocessorExpressionParser.g:140:12: ( IDENTIFIER | c_keyword | civl_keyword | cuda_keyword | gnuc_keyword )
			int alt10=5;
			switch ( input.LA(1) ) {
			case IDENTIFIER:
				{
				alt10=1;
				}
				break;
			case ALIGNAS:
			case ALIGNOF:
			case ATOMIC:
			case AUTO:
			case BOOL:
			case BREAK:
			case CASE:
			case CHAR:
			case COMPLEX:
			case CONST:
			case CONTINUE:
			case DEFAULT:
			case DO:
			case DOUBLE:
			case ELSE:
			case ENUM:
			case EXTERN:
			case FLOAT:
			case FOR:
			case GENERIC:
			case GOTO:
			case IF:
			case IMAGINARY:
			case INLINE:
			case INT:
			case LONG:
			case NORETURN:
			case REGISTER:
			case RESTRICT:
			case RETURN:
			case SCOPEOF:
			case SHORT:
			case SIGNED:
			case SIZEOF:
			case STATIC:
			case STATICASSERT:
			case STRUCT:
			case SWITCH:
			case THREADLOCAL:
			case TYPEDEF:
			case UNION:
			case UNSIGNED:
			case VOID:
			case VOLATILE:
			case WHILE:
				{
				alt10=2;
				}
				break;
			case ASSIGNS:
			case CALLS:
			case CHOOSE:
			case COLLECTIVE:
			case DEPENDS:
			case ENSURES:
			case FALSE:
			case FATOMIC:
			case GUARD:
			case HERE:
			case INPUT:
			case INVARIANT:
			case OUTPUT:
			case PROCNULL:
			case READS:
			case REQUIRES:
			case RESULT:
			case SELF:
			case SPAWN:
			case TRUE:
			case WHEN:
			case PROC:
			case ROOT:
			case WAIT:
				{
				alt10=3;
				}
				break;
			case DEVICE:
			case GLOBAL:
			case SHARED:
				{
				alt10=4;
				}
				break;
			case TYPEOF:
				{
				alt10=5;
				}
				break;
			default:
				NoViableAltException nvae =
					new NoViableAltException("", 10, 0, input);
				throw nvae;
			}
			switch (alt10) {
				case 1 :
					// PreprocessorExpressionParser.g:140:14: IDENTIFIER
					{
					root_0 = (Object)adaptor.nil();


					IDENTIFIER34=(Token)match(input,IDENTIFIER,FOLLOW_IDENTIFIER_in_identifier605); 
					IDENTIFIER34_tree = (Object)adaptor.create(IDENTIFIER34);
					adaptor.addChild(root_0, IDENTIFIER34_tree);

					}
					break;
				case 2 :
					// PreprocessorExpressionParser.g:140:27: c_keyword
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_c_keyword_in_identifier609);
					c_keyword35=c_keyword();
					state._fsp--;

					adaptor.addChild(root_0, c_keyword35.getTree());

					}
					break;
				case 3 :
					// PreprocessorExpressionParser.g:140:39: civl_keyword
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_civl_keyword_in_identifier613);
					civl_keyword36=civl_keyword();
					state._fsp--;

					adaptor.addChild(root_0, civl_keyword36.getTree());

					}
					break;
				case 4 :
					// PreprocessorExpressionParser.g:140:54: cuda_keyword
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_cuda_keyword_in_identifier617);
					cuda_keyword37=cuda_keyword();
					state._fsp--;

					adaptor.addChild(root_0, cuda_keyword37.getTree());

					}
					break;
				case 5 :
					// PreprocessorExpressionParser.g:140:69: gnuc_keyword
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_gnuc_keyword_in_identifier621);
					gnuc_keyword38=gnuc_keyword();
					state._fsp--;

					adaptor.addChild(root_0, gnuc_keyword38.getTree());

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
	// PreprocessorExpressionParser.g:142:1: c_keyword : ( AUTO | BREAK | CASE | CHAR | CONST | CONTINUE | DEFAULT | DO | DOUBLE | ELSE | ENUM | EXTERN | FLOAT | FOR | GOTO | IF | INLINE | INT | LONG | REGISTER | RESTRICT | RETURN | SHORT | SIGNED | SIZEOF | SCOPEOF | STATIC | STRUCT | SWITCH | TYPEDEF | UNION | UNSIGNED | VOID | VOLATILE | WHILE | ALIGNAS | ALIGNOF | ATOMIC | BOOL | COMPLEX | GENERIC | IMAGINARY | NORETURN | STATICASSERT | THREADLOCAL );
	public final PreprocessorExpressionParser.c_keyword_return c_keyword() throws RecognitionException {
		PreprocessorExpressionParser.c_keyword_return retval = new PreprocessorExpressionParser.c_keyword_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set39=null;

		Object set39_tree=null;

		try {
			// PreprocessorExpressionParser.g:142:11: ( AUTO | BREAK | CASE | CHAR | CONST | CONTINUE | DEFAULT | DO | DOUBLE | ELSE | ENUM | EXTERN | FLOAT | FOR | GOTO | IF | INLINE | INT | LONG | REGISTER | RESTRICT | RETURN | SHORT | SIGNED | SIZEOF | SCOPEOF | STATIC | STRUCT | SWITCH | TYPEDEF | UNION | UNSIGNED | VOID | VOLATILE | WHILE | ALIGNAS | ALIGNOF | ATOMIC | BOOL | COMPLEX | GENERIC | IMAGINARY | NORETURN | STATICASSERT | THREADLOCAL )
			// PreprocessorExpressionParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set39=input.LT(1);
			if ( (input.LA(1) >= ALIGNAS && input.LA(1) <= ALIGNOF)||(input.LA(1) >= ATOMIC && input.LA(1) <= AUTO)||(input.LA(1) >= BOOL && input.LA(1) <= BREAK)||input.LA(1)==CASE||input.LA(1)==CHAR||(input.LA(1) >= COMPLEX && input.LA(1) <= CONST)||(input.LA(1) >= CONTINUE && input.LA(1) <= DEFAULT)||input.LA(1)==DO||input.LA(1)==DOUBLE||input.LA(1)==ELSE||input.LA(1)==ENUM||input.LA(1)==EXTERN||input.LA(1)==FLOAT||input.LA(1)==FOR||input.LA(1)==GENERIC||input.LA(1)==GOTO||(input.LA(1) >= IF && input.LA(1) <= IMAGINARY)||input.LA(1)==INLINE||input.LA(1)==INT||input.LA(1)==LONG||input.LA(1)==NORETURN||input.LA(1)==REGISTER||input.LA(1)==RESTRICT||input.LA(1)==RETURN||input.LA(1)==SCOPEOF||(input.LA(1) >= SHORT && input.LA(1) <= SIZEOF)||(input.LA(1) >= STATIC && input.LA(1) <= STATICASSERT)||input.LA(1)==STRUCT||input.LA(1)==SWITCH||input.LA(1)==THREADLOCAL||input.LA(1)==TYPEDEF||(input.LA(1) >= UNION && input.LA(1) <= UNSIGNED)||(input.LA(1) >= VOID && input.LA(1) <= VOLATILE)||input.LA(1)==WHILE ) {
				input.consume();
				adaptor.addChild(root_0, (Object)adaptor.create(set39));
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


	public static class civl_keyword_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "civl_keyword"
	// PreprocessorExpressionParser.g:151:1: civl_keyword : ( ASSIGNS | CHOOSE | COLLECTIVE | DEPENDS | ENSURES | FALSE | GUARD | INPUT | INVARIANT | OUTPUT | PROC | READS | REQUIRES | RESULT | SELF | PROCNULL | SPAWN | TRUE | HERE | ROOT | WAIT | WHEN | FATOMIC | CALLS );
	public final PreprocessorExpressionParser.civl_keyword_return civl_keyword() throws RecognitionException {
		PreprocessorExpressionParser.civl_keyword_return retval = new PreprocessorExpressionParser.civl_keyword_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set40=null;

		Object set40_tree=null;

		try {
			// PreprocessorExpressionParser.g:151:14: ( ASSIGNS | CHOOSE | COLLECTIVE | DEPENDS | ENSURES | FALSE | GUARD | INPUT | INVARIANT | OUTPUT | PROC | READS | REQUIRES | RESULT | SELF | PROCNULL | SPAWN | TRUE | HERE | ROOT | WAIT | WHEN | FATOMIC | CALLS )
			// PreprocessorExpressionParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set40=input.LT(1);
			if ( input.LA(1)==ASSIGNS||input.LA(1)==CALLS||input.LA(1)==CHOOSE||input.LA(1)==COLLECTIVE||input.LA(1)==DEPENDS||input.LA(1)==ENSURES||(input.LA(1) >= FALSE && input.LA(1) <= FATOMIC)||input.LA(1)==GUARD||input.LA(1)==HERE||input.LA(1)==INPUT||input.LA(1)==INVARIANT||input.LA(1)==OUTPUT||input.LA(1)==PROCNULL||input.LA(1)==READS||input.LA(1)==REQUIRES||input.LA(1)==RESULT||input.LA(1)==SELF||input.LA(1)==SPAWN||input.LA(1)==TRUE||input.LA(1)==WHEN||(input.LA(1) >= PROC && input.LA(1) <= WAIT) ) {
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
	// $ANTLR end "civl_keyword"


	public static class gnuc_keyword_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "gnuc_keyword"
	// PreprocessorExpressionParser.g:158:1: gnuc_keyword : TYPEOF ;
	public final PreprocessorExpressionParser.gnuc_keyword_return gnuc_keyword() throws RecognitionException {
		PreprocessorExpressionParser.gnuc_keyword_return retval = new PreprocessorExpressionParser.gnuc_keyword_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token TYPEOF41=null;

		Object TYPEOF41_tree=null;

		try {
			// PreprocessorExpressionParser.g:158:15: ( TYPEOF )
			// PreprocessorExpressionParser.g:158:18: TYPEOF
			{
			root_0 = (Object)adaptor.nil();


			TYPEOF41=(Token)match(input,TYPEOF,FOLLOW_TYPEOF_in_gnuc_keyword945); 
			TYPEOF41_tree = (Object)adaptor.create(TYPEOF41);
			adaptor.addChild(root_0, TYPEOF41_tree);

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


	public static class cuda_keyword_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "cuda_keyword"
	// PreprocessorExpressionParser.g:160:1: cuda_keyword : ( DEVICE | GLOBAL | SHARED );
	public final PreprocessorExpressionParser.cuda_keyword_return cuda_keyword() throws RecognitionException {
		PreprocessorExpressionParser.cuda_keyword_return retval = new PreprocessorExpressionParser.cuda_keyword_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set42=null;

		Object set42_tree=null;

		try {
			// PreprocessorExpressionParser.g:160:14: ( DEVICE | GLOBAL | SHARED )
			// PreprocessorExpressionParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set42=input.LT(1);
			if ( input.LA(1)==DEVICE||input.LA(1)==GLOBAL||input.LA(1)==SHARED ) {
				input.consume();
				adaptor.addChild(root_0, (Object)adaptor.create(set42));
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
	// $ANTLR end "cuda_keyword"


	public static class pp_number_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "pp_number"
	// PreprocessorExpressionParser.g:165:1: pp_number : ( INTEGER_CONSTANT | FLOATING_CONSTANT | PP_NUMBER );
	public final PreprocessorExpressionParser.pp_number_return pp_number() throws RecognitionException {
		PreprocessorExpressionParser.pp_number_return retval = new PreprocessorExpressionParser.pp_number_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set43=null;

		Object set43_tree=null;

		try {
			// PreprocessorExpressionParser.g:165:11: ( INTEGER_CONSTANT | FLOATING_CONSTANT | PP_NUMBER )
			// PreprocessorExpressionParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set43=input.LT(1);
			if ( input.LA(1)==FLOATING_CONSTANT||input.LA(1)==INTEGER_CONSTANT||input.LA(1)==PP_NUMBER ) {
				input.consume();
				adaptor.addChild(root_0, (Object)adaptor.create(set43));
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

	// Delegated rules



	public static final BitSet FOLLOW_expr_in_start56 = new BitSet(new long[]{0x0000000000000000L});
	public static final BitSet FOLLOW_EOF_in_start58 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_logical_or_expr_in_expr75 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_logical_and_expr_in_logical_or_expr89 = new BitSet(new long[]{0x0000000000000002L,0x0400000000000000L});
	public static final BitSet FOLLOW_OR_in_logical_or_expr100 = new BitSet(new long[]{0x4E112F622B606860L,0x10300187DC044E3EL,0xDD5B7C2A1F414800L,0x0000000000000E3CL});
	public static final BitSet FOLLOW_logical_and_expr_in_logical_or_expr104 = new BitSet(new long[]{0x0000000000000002L,0x0400000000000000L});
	public static final BitSet FOLLOW_equality_expr_in_logical_and_expr131 = new BitSet(new long[]{0x0000000000000102L});
	public static final BitSet FOLLOW_AND_in_logical_and_expr142 = new BitSet(new long[]{0x4E112F622B606860L,0x10300187DC044E3EL,0xDD5B7C2A1F414800L,0x0000000000000E3CL});
	public static final BitSet FOLLOW_equality_expr_in_logical_and_expr146 = new BitSet(new long[]{0x0000000000000102L});
	public static final BitSet FOLLOW_relational_expr_in_equality_expr174 = new BitSet(new long[]{0x1000000000000002L,0x0004000000000000L});
	public static final BitSet FOLLOW_equality_operator_in_equality_expr187 = new BitSet(new long[]{0x4E112F622B606860L,0x10300187DC044E3EL,0xDD5B7C2A1F414800L,0x0000000000000E3CL});
	public static final BitSet FOLLOW_relational_expr_in_equality_expr191 = new BitSet(new long[]{0x1000000000000002L,0x0004000000000000L});
	public static final BitSet FOLLOW_additive_expr_in_relational_expr245 = new BitSet(new long[]{0x0000000000000002L,0x0000180000003000L});
	public static final BitSet FOLLOW_relational_operator_in_relational_expr258 = new BitSet(new long[]{0x4E112F622B606860L,0x10300187DC044E3EL,0xDD5B7C2A1F414800L,0x0000000000000E3CL});
	public static final BitSet FOLLOW_additive_expr_in_relational_expr262 = new BitSet(new long[]{0x0000000000000002L,0x0000180000003000L});
	public static final BitSet FOLLOW_multi_expr_in_additive_expr328 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0010000000000800L});
	public static final BitSet FOLLOW_additive_operator_in_additive_expr339 = new BitSet(new long[]{0x4E112F622B606860L,0x10300187DC044E3EL,0xDD5B7C2A1F414800L,0x0000000000000E3CL});
	public static final BitSet FOLLOW_multi_expr_in_additive_expr343 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0010000000000800L});
	public static final BitSet FOLLOW_unary_expr_in_multi_expr396 = new BitSet(new long[]{0x0000400000000002L,0x0001000000000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_multi_operator_in_multi_expr407 = new BitSet(new long[]{0x4E112F622B606860L,0x10300187DC044E3EL,0xDD5B7C2A1F414800L,0x0000000000000E3CL});
	public static final BitSet FOLLOW_unary_expr_in_multi_expr409 = new BitSet(new long[]{0x0000400000000002L,0x0001000000000000L,0x0000400000000000L});
	public static final BitSet FOLLOW_primary_expr_in_unary_expr464 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unary_operator_in_unary_expr470 = new BitSet(new long[]{0x4E112F622B606860L,0x10300187DC044E3EL,0xDD5B7C2A1F414800L,0x0000000000000E3CL});
	public static final BitSet FOLLOW_unary_expr_in_unary_expr472 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_pp_number_in_primary_expr523 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_primary_expr529 = new BitSet(new long[]{0x4E112F622B606860L,0x10300187DC044E3EL,0xDD5B7C2A1F414800L,0x0000000000000E3CL});
	public static final BitSet FOLLOW_expr_in_primary_expr531 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_primary_expr533 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DEFINED_in_primary_expr543 = new BitSet(new long[]{0x4E112B622B606860L,0x10100185DC044E2EL,0xDD4B3C2A1F410000L,0x0000000000000E3CL});
	public static final BitSet FOLLOW_identifier_in_primary_expr547 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_primary_expr551 = new BitSet(new long[]{0x4E112B622B606860L,0x10100085DC044E2EL,0xDD4B3C2A1F410000L,0x0000000000000E3CL});
	public static final BitSet FOLLOW_identifier_in_primary_expr553 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000040000000L});
	public static final BitSet FOLLOW_RPAREN_in_primary_expr555 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_identifier_in_primary_expr574 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_IDENTIFIER_in_identifier605 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_c_keyword_in_identifier609 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_civl_keyword_in_identifier613 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cuda_keyword_in_identifier617 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_gnuc_keyword_in_identifier621 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_TYPEOF_in_gnuc_keyword945 = new BitSet(new long[]{0x0000000000000002L});
}
