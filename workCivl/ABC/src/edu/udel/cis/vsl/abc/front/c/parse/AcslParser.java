// $ANTLR 3.5.2 AcslParser.g 2016-04-11 02:06:43

package edu.udel.cis.vsl.abc.front.c.parse;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;

import org.antlr.runtime.tree.*;


@SuppressWarnings("all")
public class AcslParser extends Parser {
	public static final String[] tokenNames = new String[] {
		"<invalid>", "<EOR>", "<DOWN>", "<UP>", "ALLOC", "AMPERSAND", "ANYACT", 
		"ARROW", "ASSIGN", "ASSIGNS", "ASSUMES", "AT", "BAR", "BEHAVIOR", "BEHAVIORS", 
		"BITXOR", "BOOLEAN", "BOTH", "BinaryExponentPart", "CALL", "CHAR", "COL", 
		"COLON", "COMMA", "COMP", "COMPLETE", "DECREASES", "DEPENDS", "DISJOINT", 
		"DIVIDE", "DOT", "DOTDOT", "DOUBLE", "DecimalConstant", "DecimalFloatingConstant", 
		"Digit", "ELLIPSIS", "EMPTY", "ENSURES", "EQ", "EQUIV", "EXISTS", "EscapeSequence", 
		"ExponentPart", "FALSE", "FLOAT", "FLOATING_CONSTANT", "FOR", "FORALL", 
		"FREES", "FloatingSuffix", "FractionalConstant", "GT", "GTE", "GUARDS", 
		"HASH", "HexFractionalConstant", "HexPrefix", "HexQuad", "HexadecimalConstant", 
		"HexadecimalDigit", "HexadecimalFloatingConstant", "ID", "IMPLY", "INT", 
		"INTEGER", "INTEGER_CONSTANT", "INTER", "INVARIANT", "IdentifierNonDigit", 
		"IntegerSuffix", "LAND", "LCOMMENT", "LCURLY", "LET", "LONG", "LOOP", 
		"LOR", "LPAREN", "LSQUARE", "LT", "LTE", "LongLongSuffix", "LongSuffix", 
		"MOD", "MPI_AGREE", "MPI_COLLECTIVE", "MPI_COMM_RANK", "MPI_COMM_SIZE", 
		"MPI_EMPTY_IN", "MPI_EMPTY_OUT", "MPI_EQUALS", "MPI_REGION", "NEQ", "NEWLINE", 
		"NOACT", "NOT", "NOTHING", "NULL", "NewLine", "NonDigit", "NonZeroDigit", 
		"OLD", "OctalConstant", "OctalDigit", "OctalEscape", "P2P", "PLUS", "PP_NUMBER", 
		"PURE", "QUESTION", "RCOMMENT", "RCURLY", "REACH", "READ", "READS", "REAL", 
		"REMOTE_ACCESS", "REQUIRES", "RESULT", "RPAREN", "RSQUARE", "SChar", "SELF", 
		"SEMICOL", "SHIFTLEFT", "SHIFTRIGHT", "SHORT", "SIZEOF", "STAR", "STRING_LITERAL", 
		"SUB", "TERMINATES", "TRUE", "UNION", "UniversalCharacterName", "UnsignedSuffix", 
		"VALID", "VARIANT", "VOID", "WITH", "WRITE", "WS", "XOR", "Zero", "ARGUMENT_LIST", 
		"BEHAVIOR_BODY", "BEHAVIOR_COMPLETE", "BEHAVIOR_DISJOINT", "BINDER", "BINDER_LIST", 
		"CAST", "CHARACTER_CONSTANT", "CLAUSE_BEHAVIOR", "CLAUSE_COMPLETE", "CLAUSE_NORMAL", 
		"CONTRACT", "C_TYPE", "EVENT_BASE", "EVENT_INTS", "EVENT_LIST", "EVENT_PARENTHESIZED", 
		"EVENT_PLUS", "EVENT_SUB", "FUNC_CALL", "FUNC_CONTRACT", "FUNC_CONTRACT_BLOCK", 
		"ID_LIST", "INDEX", "LOGIC_TYPE", "LOOP_ALLOC", "LOOP_ASSIGNS", "LOOP_BEHAVIOR", 
		"LOOP_CLAUSE", "LOOP_CONTRACT", "LOOP_CONTRACT_BLOCK", "LOOP_FREE", "LOOP_INVARIANT", 
		"LOOP_VARIANT", "LSHIFT", "MINUS", "MPI_CONSTANT", "MPI_EXPRESSION", "OPERATOR", 
		"RSHIFT", "SET_BINDERS", "SET_SIMPLE", "SIZEOF_EXPR", "SIZEOF_TYPE", "TEMINATES", 
		"TERM_PARENTHESIZED", "TYPE_BUILTIN", "TYPE_ID", "VAR_ID", "VAR_ID_BASE", 
		"VAR_ID_SQUARE", "VAR_ID_STAR"
	};
	public static final int EOF=-1;
	public static final int ALLOC=4;
	public static final int AMPERSAND=5;
	public static final int ANYACT=6;
	public static final int ARROW=7;
	public static final int ASSIGN=8;
	public static final int ASSIGNS=9;
	public static final int ASSUMES=10;
	public static final int AT=11;
	public static final int BAR=12;
	public static final int BEHAVIOR=13;
	public static final int BEHAVIORS=14;
	public static final int BITXOR=15;
	public static final int BOOLEAN=16;
	public static final int BOTH=17;
	public static final int BinaryExponentPart=18;
	public static final int CALL=19;
	public static final int CHAR=20;
	public static final int COL=21;
	public static final int COLON=22;
	public static final int COMMA=23;
	public static final int COMP=24;
	public static final int COMPLETE=25;
	public static final int DECREASES=26;
	public static final int DEPENDS=27;
	public static final int DISJOINT=28;
	public static final int DIVIDE=29;
	public static final int DOT=30;
	public static final int DOTDOT=31;
	public static final int DOUBLE=32;
	public static final int DecimalConstant=33;
	public static final int DecimalFloatingConstant=34;
	public static final int Digit=35;
	public static final int ELLIPSIS=36;
	public static final int EMPTY=37;
	public static final int ENSURES=38;
	public static final int EQ=39;
	public static final int EQUIV=40;
	public static final int EXISTS=41;
	public static final int EscapeSequence=42;
	public static final int ExponentPart=43;
	public static final int FALSE=44;
	public static final int FLOAT=45;
	public static final int FLOATING_CONSTANT=46;
	public static final int FOR=47;
	public static final int FORALL=48;
	public static final int FREES=49;
	public static final int FloatingSuffix=50;
	public static final int FractionalConstant=51;
	public static final int GT=52;
	public static final int GTE=53;
	public static final int GUARDS=54;
	public static final int HASH=55;
	public static final int HexFractionalConstant=56;
	public static final int HexPrefix=57;
	public static final int HexQuad=58;
	public static final int HexadecimalConstant=59;
	public static final int HexadecimalDigit=60;
	public static final int HexadecimalFloatingConstant=61;
	public static final int ID=62;
	public static final int IMPLY=63;
	public static final int INT=64;
	public static final int INTEGER=65;
	public static final int INTEGER_CONSTANT=66;
	public static final int INTER=67;
	public static final int INVARIANT=68;
	public static final int IdentifierNonDigit=69;
	public static final int IntegerSuffix=70;
	public static final int LAND=71;
	public static final int LCOMMENT=72;
	public static final int LCURLY=73;
	public static final int LET=74;
	public static final int LONG=75;
	public static final int LOOP=76;
	public static final int LOR=77;
	public static final int LPAREN=78;
	public static final int LSQUARE=79;
	public static final int LT=80;
	public static final int LTE=81;
	public static final int LongLongSuffix=82;
	public static final int LongSuffix=83;
	public static final int MOD=84;
	public static final int MPI_AGREE=85;
	public static final int MPI_COLLECTIVE=86;
	public static final int MPI_COMM_RANK=87;
	public static final int MPI_COMM_SIZE=88;
	public static final int MPI_EMPTY_IN=89;
	public static final int MPI_EMPTY_OUT=90;
	public static final int MPI_EQUALS=91;
	public static final int MPI_REGION=92;
	public static final int NEQ=93;
	public static final int NEWLINE=94;
	public static final int NOACT=95;
	public static final int NOT=96;
	public static final int NOTHING=97;
	public static final int NULL=98;
	public static final int NewLine=99;
	public static final int NonDigit=100;
	public static final int NonZeroDigit=101;
	public static final int OLD=102;
	public static final int OctalConstant=103;
	public static final int OctalDigit=104;
	public static final int OctalEscape=105;
	public static final int P2P=106;
	public static final int PLUS=107;
	public static final int PP_NUMBER=108;
	public static final int PURE=109;
	public static final int QUESTION=110;
	public static final int RCOMMENT=111;
	public static final int RCURLY=112;
	public static final int REACH=113;
	public static final int READ=114;
	public static final int READS=115;
	public static final int REAL=116;
	public static final int REMOTE_ACCESS=117;
	public static final int REQUIRES=118;
	public static final int RESULT=119;
	public static final int RPAREN=120;
	public static final int RSQUARE=121;
	public static final int SChar=122;
	public static final int SELF=123;
	public static final int SEMICOL=124;
	public static final int SHIFTLEFT=125;
	public static final int SHIFTRIGHT=126;
	public static final int SHORT=127;
	public static final int SIZEOF=128;
	public static final int STAR=129;
	public static final int STRING_LITERAL=130;
	public static final int SUB=131;
	public static final int TERMINATES=132;
	public static final int TRUE=133;
	public static final int UNION=134;
	public static final int UniversalCharacterName=135;
	public static final int UnsignedSuffix=136;
	public static final int VALID=137;
	public static final int VARIANT=138;
	public static final int VOID=139;
	public static final int WITH=140;
	public static final int WRITE=141;
	public static final int WS=142;
	public static final int XOR=143;
	public static final int Zero=144;
	public static final int ARGUMENT_LIST=145;
	public static final int BEHAVIOR_BODY=146;
	public static final int BEHAVIOR_COMPLETE=147;
	public static final int BEHAVIOR_DISJOINT=148;
	public static final int BINDER=149;
	public static final int BINDER_LIST=150;
	public static final int CAST=151;
	public static final int CHARACTER_CONSTANT=152;
	public static final int CLAUSE_BEHAVIOR=153;
	public static final int CLAUSE_COMPLETE=154;
	public static final int CLAUSE_NORMAL=155;
	public static final int CONTRACT=156;
	public static final int C_TYPE=157;
	public static final int EVENT_BASE=158;
	public static final int EVENT_INTS=159;
	public static final int EVENT_LIST=160;
	public static final int EVENT_PARENTHESIZED=161;
	public static final int EVENT_PLUS=162;
	public static final int EVENT_SUB=163;
	public static final int FUNC_CALL=164;
	public static final int FUNC_CONTRACT=165;
	public static final int FUNC_CONTRACT_BLOCK=166;
	public static final int ID_LIST=167;
	public static final int INDEX=168;
	public static final int LOGIC_TYPE=169;
	public static final int LOOP_ALLOC=170;
	public static final int LOOP_ASSIGNS=171;
	public static final int LOOP_BEHAVIOR=172;
	public static final int LOOP_CLAUSE=173;
	public static final int LOOP_CONTRACT=174;
	public static final int LOOP_CONTRACT_BLOCK=175;
	public static final int LOOP_FREE=176;
	public static final int LOOP_INVARIANT=177;
	public static final int LOOP_VARIANT=178;
	public static final int LSHIFT=179;
	public static final int MINUS=180;
	public static final int MPI_CONSTANT=181;
	public static final int MPI_EXPRESSION=182;
	public static final int OPERATOR=183;
	public static final int RSHIFT=184;
	public static final int SET_BINDERS=185;
	public static final int SET_SIMPLE=186;
	public static final int SIZEOF_EXPR=187;
	public static final int SIZEOF_TYPE=188;
	public static final int TEMINATES=189;
	public static final int TERM_PARENTHESIZED=190;
	public static final int TYPE_BUILTIN=191;
	public static final int TYPE_ID=192;
	public static final int VAR_ID=193;
	public static final int VAR_ID_BASE=194;
	public static final int VAR_ID_SQUARE=195;
	public static final int VAR_ID_STAR=196;

	// delegates
	public Parser[] getDelegates() {
		return new Parser[] {};
	}

	// delegators


	public AcslParser(TokenStream input) {
		this(input, new RecognizerSharedState());
	}
	public AcslParser(TokenStream input, RecognizerSharedState state) {
		super(input, state);
	}

	protected TreeAdaptor adaptor = new CommonTreeAdaptor();

	public void setTreeAdaptor(TreeAdaptor adaptor) {
		this.adaptor = adaptor;
	}
	public TreeAdaptor getTreeAdaptor() {
		return adaptor;
	}
	@Override public String[] getTokenNames() { return AcslParser.tokenNames; }
	@Override public String getGrammarFileName() { return "AcslParser.g"; }


	public static class contract_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "contract"
	// AcslParser.g:75:1: contract : ( function_contract -> ^( CONTRACT function_contract ) | loop_contract -> ^( CONTRACT loop_contract ) );
	public final AcslParser.contract_return contract() throws RecognitionException {
		AcslParser.contract_return retval = new AcslParser.contract_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope function_contract1 =null;
		ParserRuleReturnScope loop_contract2 =null;

		RewriteRuleSubtreeStream stream_function_contract=new RewriteRuleSubtreeStream(adaptor,"rule function_contract");
		RewriteRuleSubtreeStream stream_loop_contract=new RewriteRuleSubtreeStream(adaptor,"rule loop_contract");

		try {
			// AcslParser.g:76:5: ( function_contract -> ^( CONTRACT function_contract ) | loop_contract -> ^( CONTRACT loop_contract ) )
			int alt1=2;
			int LA1_0 = input.LA(1);
			if ( (LA1_0==LCOMMENT) ) {
				switch ( input.LA(2) ) {
				case ALLOC:
				case ASSIGNS:
				case BEHAVIOR:
				case COMPLETE:
				case DEPENDS:
				case DISJOINT:
				case ENSURES:
				case FREES:
				case GUARDS:
				case MPI_COLLECTIVE:
				case PURE:
				case READS:
				case REQUIRES:
				case TEMINATES:
					{
					alt1=1;
					}
					break;
				case RCOMMENT:
					{
					int LA1_3 = input.LA(3);
					if ( (synpred1_AcslParser()) ) {
						alt1=1;
					}
					else if ( (true) ) {
						alt1=2;
					}

					}
					break;
				case FOR:
				case LOOP:
					{
					alt1=2;
					}
					break;
				default:
					if (state.backtracking>0) {state.failed=true; return retval;}
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

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 1, 0, input);
				throw nvae;
			}

			switch (alt1) {
				case 1 :
					// AcslParser.g:76:7: function_contract
					{
					pushFollow(FOLLOW_function_contract_in_contract391);
					function_contract1=function_contract();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_function_contract.add(function_contract1.getTree());
					// AST REWRITE
					// elements: function_contract
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 77:9: -> ^( CONTRACT function_contract )
					{
						// AcslParser.g:77:12: ^( CONTRACT function_contract )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CONTRACT, "CONTRACT"), root_1);
						adaptor.addChild(root_1, stream_function_contract.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:78:7: loop_contract
					{
					pushFollow(FOLLOW_loop_contract_in_contract415);
					loop_contract2=loop_contract();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_loop_contract.add(loop_contract2.getTree());
					// AST REWRITE
					// elements: loop_contract
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 79:9: -> ^( CONTRACT loop_contract )
					{
						// AcslParser.g:79:12: ^( CONTRACT loop_contract )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CONTRACT, "CONTRACT"), root_1);
						adaptor.addChild(root_1, stream_loop_contract.nextTree());
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
	// $ANTLR end "contract"


	public static class loop_contract_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "loop_contract"
	// AcslParser.g:82:1: loop_contract : LCOMMENT loop_contract_block RCOMMENT -> ^( LOOP_CONTRACT loop_contract_block ) ;
	public final AcslParser.loop_contract_return loop_contract() throws RecognitionException {
		AcslParser.loop_contract_return retval = new AcslParser.loop_contract_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LCOMMENT3=null;
		Token RCOMMENT5=null;
		ParserRuleReturnScope loop_contract_block4 =null;

		Object LCOMMENT3_tree=null;
		Object RCOMMENT5_tree=null;
		RewriteRuleTokenStream stream_LCOMMENT=new RewriteRuleTokenStream(adaptor,"token LCOMMENT");
		RewriteRuleTokenStream stream_RCOMMENT=new RewriteRuleTokenStream(adaptor,"token RCOMMENT");
		RewriteRuleSubtreeStream stream_loop_contract_block=new RewriteRuleSubtreeStream(adaptor,"rule loop_contract_block");

		try {
			// AcslParser.g:83:5: ( LCOMMENT loop_contract_block RCOMMENT -> ^( LOOP_CONTRACT loop_contract_block ) )
			// AcslParser.g:83:7: LCOMMENT loop_contract_block RCOMMENT
			{
			LCOMMENT3=(Token)match(input,LCOMMENT,FOLLOW_LCOMMENT_in_loop_contract448); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LCOMMENT.add(LCOMMENT3);

			pushFollow(FOLLOW_loop_contract_block_in_loop_contract450);
			loop_contract_block4=loop_contract_block();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_loop_contract_block.add(loop_contract_block4.getTree());
			RCOMMENT5=(Token)match(input,RCOMMENT,FOLLOW_RCOMMENT_in_loop_contract452); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_RCOMMENT.add(RCOMMENT5);

			// AST REWRITE
			// elements: loop_contract_block
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 84:9: -> ^( LOOP_CONTRACT loop_contract_block )
			{
				// AcslParser.g:84:11: ^( LOOP_CONTRACT loop_contract_block )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(LOOP_CONTRACT, "LOOP_CONTRACT"), root_1);
				adaptor.addChild(root_1, stream_loop_contract_block.nextTree());
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
	// $ANTLR end "loop_contract"


	public static class loop_contract_block_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "loop_contract_block"
	// AcslParser.g:87:1: loop_contract_block : (lc+= loop_clause )* (lb+= loop_behavior )* (lv= loop_variant )? -> ^( LOOP_CONTRACT_BLOCK ( $lc)* ( $lb)* ( $lv)? ) ;
	public final AcslParser.loop_contract_block_return loop_contract_block() throws RecognitionException {
		AcslParser.loop_contract_block_return retval = new AcslParser.loop_contract_block_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		List<Object> list_lc=null;
		List<Object> list_lb=null;
		ParserRuleReturnScope lv =null;
		RuleReturnScope lc = null;
		RuleReturnScope lb = null;
		RewriteRuleSubtreeStream stream_loop_variant=new RewriteRuleSubtreeStream(adaptor,"rule loop_variant");
		RewriteRuleSubtreeStream stream_loop_clause=new RewriteRuleSubtreeStream(adaptor,"rule loop_clause");
		RewriteRuleSubtreeStream stream_loop_behavior=new RewriteRuleSubtreeStream(adaptor,"rule loop_behavior");

		try {
			// AcslParser.g:88:5: ( (lc+= loop_clause )* (lb+= loop_behavior )* (lv= loop_variant )? -> ^( LOOP_CONTRACT_BLOCK ( $lc)* ( $lb)* ( $lv)? ) )
			// AcslParser.g:88:7: (lc+= loop_clause )* (lb+= loop_behavior )* (lv= loop_variant )?
			{
			// AcslParser.g:88:9: (lc+= loop_clause )*
			loop2:
			while (true) {
				int alt2=2;
				int LA2_0 = input.LA(1);
				if ( (LA2_0==LOOP) ) {
					int LA2_2 = input.LA(2);
					if ( (LA2_2==ALLOC||LA2_2==ASSIGNS||LA2_2==FREES||LA2_2==INVARIANT) ) {
						alt2=1;
					}

				}

				switch (alt2) {
				case 1 :
					// AcslParser.g:88:9: lc+= loop_clause
					{
					pushFollow(FOLLOW_loop_clause_in_loop_contract_block486);
					lc=loop_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_loop_clause.add(lc.getTree());
					if (list_lc==null) list_lc=new ArrayList<Object>();
					list_lc.add(lc.getTree());
					}
					break;

				default :
					break loop2;
				}
			}

			// AcslParser.g:88:26: (lb+= loop_behavior )*
			loop3:
			while (true) {
				int alt3=2;
				int LA3_0 = input.LA(1);
				if ( (LA3_0==FOR) ) {
					alt3=1;
				}

				switch (alt3) {
				case 1 :
					// AcslParser.g:88:26: lb+= loop_behavior
					{
					pushFollow(FOLLOW_loop_behavior_in_loop_contract_block491);
					lb=loop_behavior();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_loop_behavior.add(lb.getTree());
					if (list_lb==null) list_lb=new ArrayList<Object>();
					list_lb.add(lb.getTree());
					}
					break;

				default :
					break loop3;
				}
			}

			// AcslParser.g:88:45: (lv= loop_variant )?
			int alt4=2;
			int LA4_0 = input.LA(1);
			if ( (LA4_0==LOOP) ) {
				alt4=1;
			}
			switch (alt4) {
				case 1 :
					// AcslParser.g:88:45: lv= loop_variant
					{
					pushFollow(FOLLOW_loop_variant_in_loop_contract_block496);
					lv=loop_variant();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_loop_variant.add(lv.getTree());
					}
					break;

			}

			// AST REWRITE
			// elements: lb, lv, lc
			// token labels: 
			// rule labels: retval, lv
			// token list labels: 
			// rule list labels: lc, lb
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_lv=new RewriteRuleSubtreeStream(adaptor,"rule lv",lv!=null?lv.getTree():null);
			RewriteRuleSubtreeStream stream_lc=new RewriteRuleSubtreeStream(adaptor,"token lc",list_lc);
			RewriteRuleSubtreeStream stream_lb=new RewriteRuleSubtreeStream(adaptor,"token lb",list_lb);
			root_0 = (Object)adaptor.nil();
			// 89:9: -> ^( LOOP_CONTRACT_BLOCK ( $lc)* ( $lb)* ( $lv)? )
			{
				// AcslParser.g:89:11: ^( LOOP_CONTRACT_BLOCK ( $lc)* ( $lb)* ( $lv)? )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(LOOP_CONTRACT_BLOCK, "LOOP_CONTRACT_BLOCK"), root_1);
				// AcslParser.g:89:34: ( $lc)*
				while ( stream_lc.hasNext() ) {
					adaptor.addChild(root_1, stream_lc.nextTree());
				}
				stream_lc.reset();

				// AcslParser.g:89:39: ( $lb)*
				while ( stream_lb.hasNext() ) {
					adaptor.addChild(root_1, stream_lb.nextTree());
				}
				stream_lb.reset();

				// AcslParser.g:89:44: ( $lv)?
				if ( stream_lv.hasNext() ) {
					adaptor.addChild(root_1, stream_lv.nextTree());
				}
				stream_lv.reset();

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
	// $ANTLR end "loop_contract_block"


	public static class loop_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "loop_clause"
	// AcslParser.g:92:1: loop_clause : ( loop_invariant SEMICOL -> ^( LOOP_CLAUSE loop_invariant ) | loop_assigns SEMICOL -> ^( LOOP_CLAUSE loop_assigns ) | loop_allocation SEMICOL -> ^( LOOP_CLAUSE loop_allocation ) );
	public final AcslParser.loop_clause_return loop_clause() throws RecognitionException {
		AcslParser.loop_clause_return retval = new AcslParser.loop_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SEMICOL7=null;
		Token SEMICOL9=null;
		Token SEMICOL11=null;
		ParserRuleReturnScope loop_invariant6 =null;
		ParserRuleReturnScope loop_assigns8 =null;
		ParserRuleReturnScope loop_allocation10 =null;

		Object SEMICOL7_tree=null;
		Object SEMICOL9_tree=null;
		Object SEMICOL11_tree=null;
		RewriteRuleTokenStream stream_SEMICOL=new RewriteRuleTokenStream(adaptor,"token SEMICOL");
		RewriteRuleSubtreeStream stream_loop_invariant=new RewriteRuleSubtreeStream(adaptor,"rule loop_invariant");
		RewriteRuleSubtreeStream stream_loop_assigns=new RewriteRuleSubtreeStream(adaptor,"rule loop_assigns");
		RewriteRuleSubtreeStream stream_loop_allocation=new RewriteRuleSubtreeStream(adaptor,"rule loop_allocation");

		try {
			// AcslParser.g:93:5: ( loop_invariant SEMICOL -> ^( LOOP_CLAUSE loop_invariant ) | loop_assigns SEMICOL -> ^( LOOP_CLAUSE loop_assigns ) | loop_allocation SEMICOL -> ^( LOOP_CLAUSE loop_allocation ) )
			int alt5=3;
			int LA5_0 = input.LA(1);
			if ( (LA5_0==LOOP) ) {
				switch ( input.LA(2) ) {
				case INVARIANT:
					{
					alt5=1;
					}
					break;
				case ASSIGNS:
					{
					alt5=2;
					}
					break;
				case ALLOC:
				case FREES:
					{
					alt5=3;
					}
					break;
				default:
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 5, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 5, 0, input);
				throw nvae;
			}

			switch (alt5) {
				case 1 :
					// AcslParser.g:93:7: loop_invariant SEMICOL
					{
					pushFollow(FOLLOW_loop_invariant_in_loop_clause539);
					loop_invariant6=loop_invariant();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_loop_invariant.add(loop_invariant6.getTree());
					SEMICOL7=(Token)match(input,SEMICOL,FOLLOW_SEMICOL_in_loop_clause541); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMICOL.add(SEMICOL7);

					// AST REWRITE
					// elements: loop_invariant
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 94:9: -> ^( LOOP_CLAUSE loop_invariant )
					{
						// AcslParser.g:94:11: ^( LOOP_CLAUSE loop_invariant )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(LOOP_CLAUSE, "LOOP_CLAUSE"), root_1);
						adaptor.addChild(root_1, stream_loop_invariant.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:95:7: loop_assigns SEMICOL
					{
					pushFollow(FOLLOW_loop_assigns_in_loop_clause564);
					loop_assigns8=loop_assigns();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_loop_assigns.add(loop_assigns8.getTree());
					SEMICOL9=(Token)match(input,SEMICOL,FOLLOW_SEMICOL_in_loop_clause566); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMICOL.add(SEMICOL9);

					// AST REWRITE
					// elements: loop_assigns
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 96:9: -> ^( LOOP_CLAUSE loop_assigns )
					{
						// AcslParser.g:96:11: ^( LOOP_CLAUSE loop_assigns )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(LOOP_CLAUSE, "LOOP_CLAUSE"), root_1);
						adaptor.addChild(root_1, stream_loop_assigns.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// AcslParser.g:97:7: loop_allocation SEMICOL
					{
					pushFollow(FOLLOW_loop_allocation_in_loop_clause589);
					loop_allocation10=loop_allocation();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_loop_allocation.add(loop_allocation10.getTree());
					SEMICOL11=(Token)match(input,SEMICOL,FOLLOW_SEMICOL_in_loop_clause591); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMICOL.add(SEMICOL11);

					// AST REWRITE
					// elements: loop_allocation
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 98:9: -> ^( LOOP_CLAUSE loop_allocation )
					{
						// AcslParser.g:98:11: ^( LOOP_CLAUSE loop_allocation )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(LOOP_CLAUSE, "LOOP_CLAUSE"), root_1);
						adaptor.addChild(root_1, stream_loop_allocation.nextTree());
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
	// $ANTLR end "loop_clause"


	public static class loop_invariant_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "loop_invariant"
	// AcslParser.g:101:1: loop_invariant : LOOP INVARIANT term -> ^( LOOP_INVARIANT term ) ;
	public final AcslParser.loop_invariant_return loop_invariant() throws RecognitionException {
		AcslParser.loop_invariant_return retval = new AcslParser.loop_invariant_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LOOP12=null;
		Token INVARIANT13=null;
		ParserRuleReturnScope term14 =null;

		Object LOOP12_tree=null;
		Object INVARIANT13_tree=null;
		RewriteRuleTokenStream stream_LOOP=new RewriteRuleTokenStream(adaptor,"token LOOP");
		RewriteRuleTokenStream stream_INVARIANT=new RewriteRuleTokenStream(adaptor,"token INVARIANT");
		RewriteRuleSubtreeStream stream_term=new RewriteRuleSubtreeStream(adaptor,"rule term");

		try {
			// AcslParser.g:102:5: ( LOOP INVARIANT term -> ^( LOOP_INVARIANT term ) )
			// AcslParser.g:102:7: LOOP INVARIANT term
			{
			LOOP12=(Token)match(input,LOOP,FOLLOW_LOOP_in_loop_invariant623); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LOOP.add(LOOP12);

			INVARIANT13=(Token)match(input,INVARIANT,FOLLOW_INVARIANT_in_loop_invariant625); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_INVARIANT.add(INVARIANT13);

			pushFollow(FOLLOW_term_in_loop_invariant627);
			term14=term();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_term.add(term14.getTree());
			// AST REWRITE
			// elements: term
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 103:9: -> ^( LOOP_INVARIANT term )
			{
				// AcslParser.g:103:11: ^( LOOP_INVARIANT term )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(LOOP_INVARIANT, "LOOP_INVARIANT"), root_1);
				adaptor.addChild(root_1, stream_term.nextTree());
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
	// $ANTLR end "loop_invariant"


	public static class loop_assigns_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "loop_assigns"
	// AcslParser.g:106:1: loop_assigns : LOOP ASSIGNS argumentExpressionList -> ^( LOOP_ASSIGNS argumentExpressionList ) ;
	public final AcslParser.loop_assigns_return loop_assigns() throws RecognitionException {
		AcslParser.loop_assigns_return retval = new AcslParser.loop_assigns_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LOOP15=null;
		Token ASSIGNS16=null;
		ParserRuleReturnScope argumentExpressionList17 =null;

		Object LOOP15_tree=null;
		Object ASSIGNS16_tree=null;
		RewriteRuleTokenStream stream_LOOP=new RewriteRuleTokenStream(adaptor,"token LOOP");
		RewriteRuleTokenStream stream_ASSIGNS=new RewriteRuleTokenStream(adaptor,"token ASSIGNS");
		RewriteRuleSubtreeStream stream_argumentExpressionList=new RewriteRuleSubtreeStream(adaptor,"rule argumentExpressionList");

		try {
			// AcslParser.g:107:5: ( LOOP ASSIGNS argumentExpressionList -> ^( LOOP_ASSIGNS argumentExpressionList ) )
			// AcslParser.g:107:7: LOOP ASSIGNS argumentExpressionList
			{
			LOOP15=(Token)match(input,LOOP,FOLLOW_LOOP_in_loop_assigns659); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LOOP.add(LOOP15);

			ASSIGNS16=(Token)match(input,ASSIGNS,FOLLOW_ASSIGNS_in_loop_assigns661); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ASSIGNS.add(ASSIGNS16);

			pushFollow(FOLLOW_argumentExpressionList_in_loop_assigns663);
			argumentExpressionList17=argumentExpressionList();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList17.getTree());
			// AST REWRITE
			// elements: argumentExpressionList
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 108:9: -> ^( LOOP_ASSIGNS argumentExpressionList )
			{
				// AcslParser.g:108:11: ^( LOOP_ASSIGNS argumentExpressionList )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(LOOP_ASSIGNS, "LOOP_ASSIGNS"), root_1);
				adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
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
	// $ANTLR end "loop_assigns"


	public static class loop_allocation_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "loop_allocation"
	// AcslParser.g:111:1: loop_allocation : ( LOOP ALLOC argumentExpressionList ( COMMA term )? -> ^( LOOP_ALLOC argumentExpressionList ( term )? ) | LOOP FREES argumentExpressionList -> ^( LOOP_FREE argumentExpressionList ) );
	public final AcslParser.loop_allocation_return loop_allocation() throws RecognitionException {
		AcslParser.loop_allocation_return retval = new AcslParser.loop_allocation_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LOOP18=null;
		Token ALLOC19=null;
		Token COMMA21=null;
		Token LOOP23=null;
		Token FREES24=null;
		ParserRuleReturnScope argumentExpressionList20 =null;
		ParserRuleReturnScope term22 =null;
		ParserRuleReturnScope argumentExpressionList25 =null;

		Object LOOP18_tree=null;
		Object ALLOC19_tree=null;
		Object COMMA21_tree=null;
		Object LOOP23_tree=null;
		Object FREES24_tree=null;
		RewriteRuleTokenStream stream_FREES=new RewriteRuleTokenStream(adaptor,"token FREES");
		RewriteRuleTokenStream stream_ALLOC=new RewriteRuleTokenStream(adaptor,"token ALLOC");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_LOOP=new RewriteRuleTokenStream(adaptor,"token LOOP");
		RewriteRuleSubtreeStream stream_term=new RewriteRuleSubtreeStream(adaptor,"rule term");
		RewriteRuleSubtreeStream stream_argumentExpressionList=new RewriteRuleSubtreeStream(adaptor,"rule argumentExpressionList");

		try {
			// AcslParser.g:112:5: ( LOOP ALLOC argumentExpressionList ( COMMA term )? -> ^( LOOP_ALLOC argumentExpressionList ( term )? ) | LOOP FREES argumentExpressionList -> ^( LOOP_FREE argumentExpressionList ) )
			int alt7=2;
			int LA7_0 = input.LA(1);
			if ( (LA7_0==LOOP) ) {
				int LA7_1 = input.LA(2);
				if ( (LA7_1==ALLOC) ) {
					alt7=1;
				}
				else if ( (LA7_1==FREES) ) {
					alt7=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 7, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 7, 0, input);
				throw nvae;
			}

			switch (alt7) {
				case 1 :
					// AcslParser.g:112:7: LOOP ALLOC argumentExpressionList ( COMMA term )?
					{
					LOOP18=(Token)match(input,LOOP,FOLLOW_LOOP_in_loop_allocation695); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LOOP.add(LOOP18);

					ALLOC19=(Token)match(input,ALLOC,FOLLOW_ALLOC_in_loop_allocation697); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ALLOC.add(ALLOC19);

					pushFollow(FOLLOW_argumentExpressionList_in_loop_allocation699);
					argumentExpressionList20=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList20.getTree());
					// AcslParser.g:112:41: ( COMMA term )?
					int alt6=2;
					int LA6_0 = input.LA(1);
					if ( (LA6_0==COMMA) ) {
						alt6=1;
					}
					switch (alt6) {
						case 1 :
							// AcslParser.g:112:42: COMMA term
							{
							COMMA21=(Token)match(input,COMMA,FOLLOW_COMMA_in_loop_allocation702); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_COMMA.add(COMMA21);

							pushFollow(FOLLOW_term_in_loop_allocation704);
							term22=term();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_term.add(term22.getTree());
							}
							break;

					}

					// AST REWRITE
					// elements: argumentExpressionList, term
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 113:9: -> ^( LOOP_ALLOC argumentExpressionList ( term )? )
					{
						// AcslParser.g:113:11: ^( LOOP_ALLOC argumentExpressionList ( term )? )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(LOOP_ALLOC, "LOOP_ALLOC"), root_1);
						adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
						// AcslParser.g:113:47: ( term )?
						if ( stream_term.hasNext() ) {
							adaptor.addChild(root_1, stream_term.nextTree());
						}
						stream_term.reset();

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:114:7: LOOP FREES argumentExpressionList
					{
					LOOP23=(Token)match(input,LOOP,FOLLOW_LOOP_in_loop_allocation732); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LOOP.add(LOOP23);

					FREES24=(Token)match(input,FREES,FOLLOW_FREES_in_loop_allocation734); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_FREES.add(FREES24);

					pushFollow(FOLLOW_argumentExpressionList_in_loop_allocation736);
					argumentExpressionList25=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList25.getTree());
					// AST REWRITE
					// elements: argumentExpressionList
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 115:9: -> ^( LOOP_FREE argumentExpressionList )
					{
						// AcslParser.g:115:11: ^( LOOP_FREE argumentExpressionList )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(LOOP_FREE, "LOOP_FREE"), root_1);
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
	// $ANTLR end "loop_allocation"


	public static class loop_behavior_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "loop_behavior"
	// AcslParser.g:118:1: loop_behavior : FOR ilist= id_list COLON (lc+= loop_clause )* -> ^( LOOP_BEHAVIOR $ilist ( $lc)* ) ;
	public final AcslParser.loop_behavior_return loop_behavior() throws RecognitionException {
		AcslParser.loop_behavior_return retval = new AcslParser.loop_behavior_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token FOR26=null;
		Token COLON27=null;
		List<Object> list_lc=null;
		ParserRuleReturnScope ilist =null;
		RuleReturnScope lc = null;
		Object FOR26_tree=null;
		Object COLON27_tree=null;
		RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
		RewriteRuleTokenStream stream_FOR=new RewriteRuleTokenStream(adaptor,"token FOR");
		RewriteRuleSubtreeStream stream_loop_clause=new RewriteRuleSubtreeStream(adaptor,"rule loop_clause");
		RewriteRuleSubtreeStream stream_id_list=new RewriteRuleSubtreeStream(adaptor,"rule id_list");

		try {
			// AcslParser.g:119:5: ( FOR ilist= id_list COLON (lc+= loop_clause )* -> ^( LOOP_BEHAVIOR $ilist ( $lc)* ) )
			// AcslParser.g:119:7: FOR ilist= id_list COLON (lc+= loop_clause )*
			{
			FOR26=(Token)match(input,FOR,FOLLOW_FOR_in_loop_behavior768); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_FOR.add(FOR26);

			pushFollow(FOLLOW_id_list_in_loop_behavior772);
			ilist=id_list();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_id_list.add(ilist.getTree());
			COLON27=(Token)match(input,COLON,FOLLOW_COLON_in_loop_behavior774); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_COLON.add(COLON27);

			// AcslParser.g:119:33: (lc+= loop_clause )*
			loop8:
			while (true) {
				int alt8=2;
				int LA8_0 = input.LA(1);
				if ( (LA8_0==LOOP) ) {
					int LA8_1 = input.LA(2);
					if ( (LA8_1==ALLOC||LA8_1==ASSIGNS||LA8_1==FREES||LA8_1==INVARIANT) ) {
						alt8=1;
					}

				}

				switch (alt8) {
				case 1 :
					// AcslParser.g:119:33: lc+= loop_clause
					{
					pushFollow(FOLLOW_loop_clause_in_loop_behavior778);
					lc=loop_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_loop_clause.add(lc.getTree());
					if (list_lc==null) list_lc=new ArrayList<Object>();
					list_lc.add(lc.getTree());
					}
					break;

				default :
					break loop8;
				}
			}

			// AST REWRITE
			// elements: lc, ilist
			// token labels: 
			// rule labels: retval, ilist
			// token list labels: 
			// rule list labels: lc
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_ilist=new RewriteRuleSubtreeStream(adaptor,"rule ilist",ilist!=null?ilist.getTree():null);
			RewriteRuleSubtreeStream stream_lc=new RewriteRuleSubtreeStream(adaptor,"token lc",list_lc);
			root_0 = (Object)adaptor.nil();
			// 120:9: -> ^( LOOP_BEHAVIOR $ilist ( $lc)* )
			{
				// AcslParser.g:120:11: ^( LOOP_BEHAVIOR $ilist ( $lc)* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(LOOP_BEHAVIOR, "LOOP_BEHAVIOR"), root_1);
				adaptor.addChild(root_1, stream_ilist.nextTree());
				// AcslParser.g:120:35: ( $lc)*
				while ( stream_lc.hasNext() ) {
					adaptor.addChild(root_1, stream_lc.nextTree());
				}
				stream_lc.reset();

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
	// $ANTLR end "loop_behavior"


	public static class loop_variant_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "loop_variant"
	// AcslParser.g:123:1: loop_variant : ( LOOP VARIANT term -> ^( LOOP_VARIANT term ) | LOOP VARIANT term FOR ID -> ^( LOOP_VARIANT term ID ) );
	public final AcslParser.loop_variant_return loop_variant() throws RecognitionException {
		AcslParser.loop_variant_return retval = new AcslParser.loop_variant_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LOOP28=null;
		Token VARIANT29=null;
		Token LOOP31=null;
		Token VARIANT32=null;
		Token FOR34=null;
		Token ID35=null;
		ParserRuleReturnScope term30 =null;
		ParserRuleReturnScope term33 =null;

		Object LOOP28_tree=null;
		Object VARIANT29_tree=null;
		Object LOOP31_tree=null;
		Object VARIANT32_tree=null;
		Object FOR34_tree=null;
		Object ID35_tree=null;
		RewriteRuleTokenStream stream_FOR=new RewriteRuleTokenStream(adaptor,"token FOR");
		RewriteRuleTokenStream stream_VARIANT=new RewriteRuleTokenStream(adaptor,"token VARIANT");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_LOOP=new RewriteRuleTokenStream(adaptor,"token LOOP");
		RewriteRuleSubtreeStream stream_term=new RewriteRuleSubtreeStream(adaptor,"rule term");

		try {
			// AcslParser.g:124:5: ( LOOP VARIANT term -> ^( LOOP_VARIANT term ) | LOOP VARIANT term FOR ID -> ^( LOOP_VARIANT term ID ) )
			int alt9=2;
			int LA9_0 = input.LA(1);
			if ( (LA9_0==LOOP) ) {
				int LA9_1 = input.LA(2);
				if ( (synpred10_AcslParser()) ) {
					alt9=1;
				}
				else if ( (true) ) {
					alt9=2;
				}

			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 9, 0, input);
				throw nvae;
			}

			switch (alt9) {
				case 1 :
					// AcslParser.g:124:7: LOOP VARIANT term
					{
					LOOP28=(Token)match(input,LOOP,FOLLOW_LOOP_in_loop_variant816); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LOOP.add(LOOP28);

					VARIANT29=(Token)match(input,VARIANT,FOLLOW_VARIANT_in_loop_variant818); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_VARIANT.add(VARIANT29);

					pushFollow(FOLLOW_term_in_loop_variant820);
					term30=term();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_term.add(term30.getTree());
					// AST REWRITE
					// elements: term
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 125:9: -> ^( LOOP_VARIANT term )
					{
						// AcslParser.g:125:11: ^( LOOP_VARIANT term )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(LOOP_VARIANT, "LOOP_VARIANT"), root_1);
						adaptor.addChild(root_1, stream_term.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:126:7: LOOP VARIANT term FOR ID
					{
					LOOP31=(Token)match(input,LOOP,FOLLOW_LOOP_in_loop_variant843); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LOOP.add(LOOP31);

					VARIANT32=(Token)match(input,VARIANT,FOLLOW_VARIANT_in_loop_variant845); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_VARIANT.add(VARIANT32);

					pushFollow(FOLLOW_term_in_loop_variant847);
					term33=term();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_term.add(term33.getTree());
					FOR34=(Token)match(input,FOR,FOLLOW_FOR_in_loop_variant849); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_FOR.add(FOR34);

					ID35=(Token)match(input,ID,FOLLOW_ID_in_loop_variant851); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID35);

					// AST REWRITE
					// elements: term, ID
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 127:9: -> ^( LOOP_VARIANT term ID )
					{
						// AcslParser.g:127:11: ^( LOOP_VARIANT term ID )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(LOOP_VARIANT, "LOOP_VARIANT"), root_1);
						adaptor.addChild(root_1, stream_term.nextTree());
						adaptor.addChild(root_1, stream_ID.nextNode());
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
	// $ANTLR end "loop_variant"


	public static class function_contract_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "function_contract"
	// AcslParser.g:131:1: function_contract : LCOMMENT ( pure_function )? full_contract_block RCOMMENT -> ^( FUNC_CONTRACT full_contract_block ( pure_function )? ) ;
	public final AcslParser.function_contract_return function_contract() throws RecognitionException {
		AcslParser.function_contract_return retval = new AcslParser.function_contract_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LCOMMENT36=null;
		Token RCOMMENT39=null;
		ParserRuleReturnScope pure_function37 =null;
		ParserRuleReturnScope full_contract_block38 =null;

		Object LCOMMENT36_tree=null;
		Object RCOMMENT39_tree=null;
		RewriteRuleTokenStream stream_LCOMMENT=new RewriteRuleTokenStream(adaptor,"token LCOMMENT");
		RewriteRuleTokenStream stream_RCOMMENT=new RewriteRuleTokenStream(adaptor,"token RCOMMENT");
		RewriteRuleSubtreeStream stream_pure_function=new RewriteRuleSubtreeStream(adaptor,"rule pure_function");
		RewriteRuleSubtreeStream stream_full_contract_block=new RewriteRuleSubtreeStream(adaptor,"rule full_contract_block");

		try {
			// AcslParser.g:132:5: ( LCOMMENT ( pure_function )? full_contract_block RCOMMENT -> ^( FUNC_CONTRACT full_contract_block ( pure_function )? ) )
			// AcslParser.g:132:7: LCOMMENT ( pure_function )? full_contract_block RCOMMENT
			{
			LCOMMENT36=(Token)match(input,LCOMMENT,FOLLOW_LCOMMENT_in_function_contract887); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LCOMMENT.add(LCOMMENT36);

			// AcslParser.g:132:16: ( pure_function )?
			int alt10=2;
			int LA10_0 = input.LA(1);
			if ( (LA10_0==PURE) ) {
				alt10=1;
			}
			switch (alt10) {
				case 1 :
					// AcslParser.g:132:16: pure_function
					{
					pushFollow(FOLLOW_pure_function_in_function_contract889);
					pure_function37=pure_function();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_pure_function.add(pure_function37.getTree());
					}
					break;

			}

			pushFollow(FOLLOW_full_contract_block_in_function_contract892);
			full_contract_block38=full_contract_block();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_full_contract_block.add(full_contract_block38.getTree());
			RCOMMENT39=(Token)match(input,RCOMMENT,FOLLOW_RCOMMENT_in_function_contract894); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_RCOMMENT.add(RCOMMENT39);

			// AST REWRITE
			// elements: pure_function, full_contract_block
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 133:7: -> ^( FUNC_CONTRACT full_contract_block ( pure_function )? )
			{
				// AcslParser.g:133:10: ^( FUNC_CONTRACT full_contract_block ( pure_function )? )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FUNC_CONTRACT, "FUNC_CONTRACT"), root_1);
				adaptor.addChild(root_1, stream_full_contract_block.nextTree());
				// AcslParser.g:133:46: ( pure_function )?
				if ( stream_pure_function.hasNext() ) {
					adaptor.addChild(root_1, stream_pure_function.nextTree());
				}
				stream_pure_function.reset();

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
	// $ANTLR end "function_contract"


	public static class pure_function_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "pure_function"
	// AcslParser.g:136:1: pure_function : PURE SEMICOL -> ^( PURE ) ;
	public final AcslParser.pure_function_return pure_function() throws RecognitionException {
		AcslParser.pure_function_return retval = new AcslParser.pure_function_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PURE40=null;
		Token SEMICOL41=null;

		Object PURE40_tree=null;
		Object SEMICOL41_tree=null;
		RewriteRuleTokenStream stream_SEMICOL=new RewriteRuleTokenStream(adaptor,"token SEMICOL");
		RewriteRuleTokenStream stream_PURE=new RewriteRuleTokenStream(adaptor,"token PURE");

		try {
			// AcslParser.g:137:5: ( PURE SEMICOL -> ^( PURE ) )
			// AcslParser.g:137:7: PURE SEMICOL
			{
			PURE40=(Token)match(input,PURE,FOLLOW_PURE_in_pure_function928); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_PURE.add(PURE40);

			SEMICOL41=(Token)match(input,SEMICOL,FOLLOW_SEMICOL_in_pure_function930); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_SEMICOL.add(SEMICOL41);

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
			// 138:7: -> ^( PURE )
			{
				// AcslParser.g:138:9: ^( PURE )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_PURE.nextNode(), root_1);
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
	// $ANTLR end "pure_function"


	public static class full_contract_block_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "full_contract_block"
	// AcslParser.g:143:1: full_contract_block : (f+= function_clause )* (m+= contract_block )* (c+= completeness_clause_block )* -> ^( FUNC_CONTRACT_BLOCK ( $f)* ( $m)* ( $c)* ) ;
	public final AcslParser.full_contract_block_return full_contract_block() throws RecognitionException {
		AcslParser.full_contract_block_return retval = new AcslParser.full_contract_block_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		List<Object> list_f=null;
		List<Object> list_m=null;
		List<Object> list_c=null;
		RuleReturnScope f = null;
		RuleReturnScope m = null;
		RuleReturnScope c = null;
		RewriteRuleSubtreeStream stream_completeness_clause_block=new RewriteRuleSubtreeStream(adaptor,"rule completeness_clause_block");
		RewriteRuleSubtreeStream stream_function_clause=new RewriteRuleSubtreeStream(adaptor,"rule function_clause");
		RewriteRuleSubtreeStream stream_contract_block=new RewriteRuleSubtreeStream(adaptor,"rule contract_block");

		try {
			// AcslParser.g:144:5: ( (f+= function_clause )* (m+= contract_block )* (c+= completeness_clause_block )* -> ^( FUNC_CONTRACT_BLOCK ( $f)* ( $m)* ( $c)* ) )
			// AcslParser.g:144:7: (f+= function_clause )* (m+= contract_block )* (c+= completeness_clause_block )*
			{
			// AcslParser.g:144:7: (f+= function_clause )*
			loop11:
			while (true) {
				int alt11=2;
				int LA11_0 = input.LA(1);
				if ( (LA11_0==ALLOC||LA11_0==ASSIGNS||LA11_0==DEPENDS||LA11_0==ENSURES||LA11_0==FREES||LA11_0==GUARDS||LA11_0==READS||LA11_0==REQUIRES||LA11_0==TEMINATES) ) {
					alt11=1;
				}

				switch (alt11) {
				case 1 :
					// AcslParser.g:144:8: f+= function_clause
					{
					pushFollow(FOLLOW_function_clause_in_full_contract_block963);
					f=function_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_function_clause.add(f.getTree());
					if (list_f==null) list_f=new ArrayList<Object>();
					list_f.add(f.getTree());
					}
					break;

				default :
					break loop11;
				}
			}

			// AcslParser.g:144:29: (m+= contract_block )*
			loop12:
			while (true) {
				int alt12=2;
				int LA12_0 = input.LA(1);
				if ( (LA12_0==BEHAVIOR||LA12_0==MPI_COLLECTIVE) ) {
					alt12=1;
				}

				switch (alt12) {
				case 1 :
					// AcslParser.g:144:30: m+= contract_block
					{
					pushFollow(FOLLOW_contract_block_in_full_contract_block970);
					m=contract_block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_contract_block.add(m.getTree());
					if (list_m==null) list_m=new ArrayList<Object>();
					list_m.add(m.getTree());
					}
					break;

				default :
					break loop12;
				}
			}

			// AcslParser.g:145:9: (c+= completeness_clause_block )*
			loop13:
			while (true) {
				int alt13=2;
				int LA13_0 = input.LA(1);
				if ( (LA13_0==COMPLETE||LA13_0==DISJOINT) ) {
					alt13=1;
				}

				switch (alt13) {
				case 1 :
					// AcslParser.g:145:10: c+= completeness_clause_block
					{
					pushFollow(FOLLOW_completeness_clause_block_in_full_contract_block985);
					c=completeness_clause_block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_completeness_clause_block.add(c.getTree());
					if (list_c==null) list_c=new ArrayList<Object>();
					list_c.add(c.getTree());
					}
					break;

				default :
					break loop13;
				}
			}

			// AST REWRITE
			// elements: m, c, f
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: f, c, m
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_f=new RewriteRuleSubtreeStream(adaptor,"token f",list_f);
			RewriteRuleSubtreeStream stream_c=new RewriteRuleSubtreeStream(adaptor,"token c",list_c);
			RewriteRuleSubtreeStream stream_m=new RewriteRuleSubtreeStream(adaptor,"token m",list_m);
			root_0 = (Object)adaptor.nil();
			// 146:9: -> ^( FUNC_CONTRACT_BLOCK ( $f)* ( $m)* ( $c)* )
			{
				// AcslParser.g:146:12: ^( FUNC_CONTRACT_BLOCK ( $f)* ( $m)* ( $c)* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FUNC_CONTRACT_BLOCK, "FUNC_CONTRACT_BLOCK"), root_1);
				// AcslParser.g:146:35: ( $f)*
				while ( stream_f.hasNext() ) {
					adaptor.addChild(root_1, stream_f.nextTree());
				}
				stream_f.reset();

				// AcslParser.g:146:39: ( $m)*
				while ( stream_m.hasNext() ) {
					adaptor.addChild(root_1, stream_m.nextTree());
				}
				stream_m.reset();

				// AcslParser.g:146:43: ( $c)*
				while ( stream_c.hasNext() ) {
					adaptor.addChild(root_1, stream_c.nextTree());
				}
				stream_c.reset();

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
	// $ANTLR end "full_contract_block"


	public static class partial_contract_block_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "partial_contract_block"
	// AcslParser.g:152:1: partial_contract_block : (f+= function_clause )* (b+= named_behavior_block )* (c+= completeness_clause_block )* -> ^( FUNC_CONTRACT_BLOCK ( $f)* ( $b)* ( $c)* ) ;
	public final AcslParser.partial_contract_block_return partial_contract_block() throws RecognitionException {
		AcslParser.partial_contract_block_return retval = new AcslParser.partial_contract_block_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		List<Object> list_f=null;
		List<Object> list_b=null;
		List<Object> list_c=null;
		RuleReturnScope f = null;
		RuleReturnScope b = null;
		RuleReturnScope c = null;
		RewriteRuleSubtreeStream stream_completeness_clause_block=new RewriteRuleSubtreeStream(adaptor,"rule completeness_clause_block");
		RewriteRuleSubtreeStream stream_function_clause=new RewriteRuleSubtreeStream(adaptor,"rule function_clause");
		RewriteRuleSubtreeStream stream_named_behavior_block=new RewriteRuleSubtreeStream(adaptor,"rule named_behavior_block");

		try {
			// AcslParser.g:153:5: ( (f+= function_clause )* (b+= named_behavior_block )* (c+= completeness_clause_block )* -> ^( FUNC_CONTRACT_BLOCK ( $f)* ( $b)* ( $c)* ) )
			// AcslParser.g:153:7: (f+= function_clause )* (b+= named_behavior_block )* (c+= completeness_clause_block )*
			{
			// AcslParser.g:153:7: (f+= function_clause )*
			loop14:
			while (true) {
				int alt14=2;
				int LA14_0 = input.LA(1);
				if ( (LA14_0==ALLOC||LA14_0==ASSIGNS||LA14_0==DEPENDS||LA14_0==ENSURES||LA14_0==FREES||LA14_0==GUARDS||LA14_0==READS||LA14_0==REQUIRES||LA14_0==TEMINATES) ) {
					alt14=1;
				}

				switch (alt14) {
				case 1 :
					// AcslParser.g:153:8: f+= function_clause
					{
					pushFollow(FOLLOW_function_clause_in_partial_contract_block1037);
					f=function_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_function_clause.add(f.getTree());
					if (list_f==null) list_f=new ArrayList<Object>();
					list_f.add(f.getTree());
					}
					break;

				default :
					break loop14;
				}
			}

			// AcslParser.g:153:29: (b+= named_behavior_block )*
			loop15:
			while (true) {
				int alt15=2;
				int LA15_0 = input.LA(1);
				if ( (LA15_0==BEHAVIOR) ) {
					int LA15_5 = input.LA(2);
					if ( (synpred16_AcslParser()) ) {
						alt15=1;
					}

				}

				switch (alt15) {
				case 1 :
					// AcslParser.g:153:30: b+= named_behavior_block
					{
					pushFollow(FOLLOW_named_behavior_block_in_partial_contract_block1044);
					b=named_behavior_block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_named_behavior_block.add(b.getTree());
					if (list_b==null) list_b=new ArrayList<Object>();
					list_b.add(b.getTree());
					}
					break;

				default :
					break loop15;
				}
			}

			// AcslParser.g:154:9: (c+= completeness_clause_block )*
			loop16:
			while (true) {
				int alt16=2;
				alt16 = dfa16.predict(input);
				switch (alt16) {
				case 1 :
					// AcslParser.g:154:10: c+= completeness_clause_block
					{
					pushFollow(FOLLOW_completeness_clause_block_in_partial_contract_block1060);
					c=completeness_clause_block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_completeness_clause_block.add(c.getTree());
					if (list_c==null) list_c=new ArrayList<Object>();
					list_c.add(c.getTree());
					}
					break;

				default :
					break loop16;
				}
			}

			// AST REWRITE
			// elements: f, c, b
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: f, b, c
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_f=new RewriteRuleSubtreeStream(adaptor,"token f",list_f);
			RewriteRuleSubtreeStream stream_b=new RewriteRuleSubtreeStream(adaptor,"token b",list_b);
			RewriteRuleSubtreeStream stream_c=new RewriteRuleSubtreeStream(adaptor,"token c",list_c);
			root_0 = (Object)adaptor.nil();
			// 155:9: -> ^( FUNC_CONTRACT_BLOCK ( $f)* ( $b)* ( $c)* )
			{
				// AcslParser.g:155:12: ^( FUNC_CONTRACT_BLOCK ( $f)* ( $b)* ( $c)* )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FUNC_CONTRACT_BLOCK, "FUNC_CONTRACT_BLOCK"), root_1);
				// AcslParser.g:155:35: ( $f)*
				while ( stream_f.hasNext() ) {
					adaptor.addChild(root_1, stream_f.nextTree());
				}
				stream_f.reset();

				// AcslParser.g:155:39: ( $b)*
				while ( stream_b.hasNext() ) {
					adaptor.addChild(root_1, stream_b.nextTree());
				}
				stream_b.reset();

				// AcslParser.g:155:43: ( $c)*
				while ( stream_c.hasNext() ) {
					adaptor.addChild(root_1, stream_c.nextTree());
				}
				stream_c.reset();

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
	// $ANTLR end "partial_contract_block"


	public static class contract_block_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "contract_block"
	// AcslParser.g:163:1: contract_block : ( mpi_collective_block | named_behavior_block ( completeness_clause_block )? );
	public final AcslParser.contract_block_return contract_block() throws RecognitionException {
		AcslParser.contract_block_return retval = new AcslParser.contract_block_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope mpi_collective_block42 =null;
		ParserRuleReturnScope named_behavior_block43 =null;
		ParserRuleReturnScope completeness_clause_block44 =null;


		try {
			// AcslParser.g:164:5: ( mpi_collective_block | named_behavior_block ( completeness_clause_block )? )
			int alt18=2;
			int LA18_0 = input.LA(1);
			if ( (LA18_0==MPI_COLLECTIVE) ) {
				alt18=1;
			}
			else if ( (LA18_0==BEHAVIOR) ) {
				alt18=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 18, 0, input);
				throw nvae;
			}

			switch (alt18) {
				case 1 :
					// AcslParser.g:164:7: mpi_collective_block
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_mpi_collective_block_in_contract_block1109);
					mpi_collective_block42=mpi_collective_block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, mpi_collective_block42.getTree());

					}
					break;
				case 2 :
					// AcslParser.g:165:7: named_behavior_block ( completeness_clause_block )?
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_named_behavior_block_in_contract_block1117);
					named_behavior_block43=named_behavior_block();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, named_behavior_block43.getTree());

					// AcslParser.g:165:28: ( completeness_clause_block )?
					int alt17=2;
					alt17 = dfa17.predict(input);
					switch (alt17) {
						case 1 :
							// AcslParser.g:165:28: completeness_clause_block
							{
							pushFollow(FOLLOW_completeness_clause_block_in_contract_block1119);
							completeness_clause_block44=completeness_clause_block();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) adaptor.addChild(root_0, completeness_clause_block44.getTree());

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
	// $ANTLR end "contract_block"


	public static class function_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "function_clause"
	// AcslParser.g:168:1: function_clause : ( requires_clause SEMICOL -> ^( CLAUSE_NORMAL requires_clause ) | terminates_clause SEMICOL -> ^( CLAUSE_NORMAL terminates_clause ) | simple_clause SEMICOL -> ^( CLAUSE_NORMAL simple_clause ) );
	public final AcslParser.function_clause_return function_clause() throws RecognitionException {
		AcslParser.function_clause_return retval = new AcslParser.function_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SEMICOL46=null;
		Token SEMICOL48=null;
		Token SEMICOL50=null;
		ParserRuleReturnScope requires_clause45 =null;
		ParserRuleReturnScope terminates_clause47 =null;
		ParserRuleReturnScope simple_clause49 =null;

		Object SEMICOL46_tree=null;
		Object SEMICOL48_tree=null;
		Object SEMICOL50_tree=null;
		RewriteRuleTokenStream stream_SEMICOL=new RewriteRuleTokenStream(adaptor,"token SEMICOL");
		RewriteRuleSubtreeStream stream_terminates_clause=new RewriteRuleSubtreeStream(adaptor,"rule terminates_clause");
		RewriteRuleSubtreeStream stream_simple_clause=new RewriteRuleSubtreeStream(adaptor,"rule simple_clause");
		RewriteRuleSubtreeStream stream_requires_clause=new RewriteRuleSubtreeStream(adaptor,"rule requires_clause");

		try {
			// AcslParser.g:169:5: ( requires_clause SEMICOL -> ^( CLAUSE_NORMAL requires_clause ) | terminates_clause SEMICOL -> ^( CLAUSE_NORMAL terminates_clause ) | simple_clause SEMICOL -> ^( CLAUSE_NORMAL simple_clause ) )
			int alt19=3;
			switch ( input.LA(1) ) {
			case REQUIRES:
				{
				alt19=1;
				}
				break;
			case TEMINATES:
				{
				alt19=2;
				}
				break;
			case ALLOC:
			case ASSIGNS:
			case DEPENDS:
			case ENSURES:
			case FREES:
			case GUARDS:
			case READS:
				{
				alt19=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 19, 0, input);
				throw nvae;
			}
			switch (alt19) {
				case 1 :
					// AcslParser.g:169:7: requires_clause SEMICOL
					{
					pushFollow(FOLLOW_requires_clause_in_function_clause1137);
					requires_clause45=requires_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_requires_clause.add(requires_clause45.getTree());
					SEMICOL46=(Token)match(input,SEMICOL,FOLLOW_SEMICOL_in_function_clause1139); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMICOL.add(SEMICOL46);

					// AST REWRITE
					// elements: requires_clause
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 169:30: -> ^( CLAUSE_NORMAL requires_clause )
					{
						// AcslParser.g:169:33: ^( CLAUSE_NORMAL requires_clause )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CLAUSE_NORMAL, "CLAUSE_NORMAL"), root_1);
						adaptor.addChild(root_1, stream_requires_clause.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:170:7: terminates_clause SEMICOL
					{
					pushFollow(FOLLOW_terminates_clause_in_function_clause1154);
					terminates_clause47=terminates_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_terminates_clause.add(terminates_clause47.getTree());
					SEMICOL48=(Token)match(input,SEMICOL,FOLLOW_SEMICOL_in_function_clause1156); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMICOL.add(SEMICOL48);

					// AST REWRITE
					// elements: terminates_clause
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 170:32: -> ^( CLAUSE_NORMAL terminates_clause )
					{
						// AcslParser.g:170:35: ^( CLAUSE_NORMAL terminates_clause )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CLAUSE_NORMAL, "CLAUSE_NORMAL"), root_1);
						adaptor.addChild(root_1, stream_terminates_clause.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// AcslParser.g:171:7: simple_clause SEMICOL
					{
					pushFollow(FOLLOW_simple_clause_in_function_clause1171);
					simple_clause49=simple_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_simple_clause.add(simple_clause49.getTree());
					SEMICOL50=(Token)match(input,SEMICOL,FOLLOW_SEMICOL_in_function_clause1173); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMICOL.add(SEMICOL50);

					// AST REWRITE
					// elements: simple_clause
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 171:29: -> ^( CLAUSE_NORMAL simple_clause )
					{
						// AcslParser.g:171:32: ^( CLAUSE_NORMAL simple_clause )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CLAUSE_NORMAL, "CLAUSE_NORMAL"), root_1);
						adaptor.addChild(root_1, stream_simple_clause.nextTree());
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
	// $ANTLR end "function_clause"


	public static class named_behavior_block_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "named_behavior_block"
	// AcslParser.g:174:1: named_behavior_block : named_behavior -> ^( CLAUSE_BEHAVIOR named_behavior ) ;
	public final AcslParser.named_behavior_block_return named_behavior_block() throws RecognitionException {
		AcslParser.named_behavior_block_return retval = new AcslParser.named_behavior_block_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope named_behavior51 =null;

		RewriteRuleSubtreeStream stream_named_behavior=new RewriteRuleSubtreeStream(adaptor,"rule named_behavior");

		try {
			// AcslParser.g:175:5: ( named_behavior -> ^( CLAUSE_BEHAVIOR named_behavior ) )
			// AcslParser.g:175:7: named_behavior
			{
			pushFollow(FOLLOW_named_behavior_in_named_behavior_block1198);
			named_behavior51=named_behavior();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_named_behavior.add(named_behavior51.getTree());
			// AST REWRITE
			// elements: named_behavior
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 175:22: -> ^( CLAUSE_BEHAVIOR named_behavior )
			{
				// AcslParser.g:175:25: ^( CLAUSE_BEHAVIOR named_behavior )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CLAUSE_BEHAVIOR, "CLAUSE_BEHAVIOR"), root_1);
				adaptor.addChild(root_1, stream_named_behavior.nextTree());
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
	// $ANTLR end "named_behavior_block"


	public static class completeness_clause_block_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "completeness_clause_block"
	// AcslParser.g:178:1: completeness_clause_block : completeness_clause SEMICOL -> ^( CLAUSE_COMPLETE completeness_clause ) ;
	public final AcslParser.completeness_clause_block_return completeness_clause_block() throws RecognitionException {
		AcslParser.completeness_clause_block_return retval = new AcslParser.completeness_clause_block_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SEMICOL53=null;
		ParserRuleReturnScope completeness_clause52 =null;

		Object SEMICOL53_tree=null;
		RewriteRuleTokenStream stream_SEMICOL=new RewriteRuleTokenStream(adaptor,"token SEMICOL");
		RewriteRuleSubtreeStream stream_completeness_clause=new RewriteRuleSubtreeStream(adaptor,"rule completeness_clause");

		try {
			// AcslParser.g:179:5: ( completeness_clause SEMICOL -> ^( CLAUSE_COMPLETE completeness_clause ) )
			// AcslParser.g:179:7: completeness_clause SEMICOL
			{
			pushFollow(FOLLOW_completeness_clause_in_completeness_clause_block1223);
			completeness_clause52=completeness_clause();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_completeness_clause.add(completeness_clause52.getTree());
			SEMICOL53=(Token)match(input,SEMICOL,FOLLOW_SEMICOL_in_completeness_clause_block1225); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_SEMICOL.add(SEMICOL53);

			// AST REWRITE
			// elements: completeness_clause
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 179:35: -> ^( CLAUSE_COMPLETE completeness_clause )
			{
				// AcslParser.g:179:38: ^( CLAUSE_COMPLETE completeness_clause )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CLAUSE_COMPLETE, "CLAUSE_COMPLETE"), root_1);
				adaptor.addChild(root_1, stream_completeness_clause.nextTree());
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
	// $ANTLR end "completeness_clause_block"


	public static class requires_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "requires_clause"
	// AcslParser.g:182:1: requires_clause : REQUIRES term -> ^( REQUIRES term ) ;
	public final AcslParser.requires_clause_return requires_clause() throws RecognitionException {
		AcslParser.requires_clause_return retval = new AcslParser.requires_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token REQUIRES54=null;
		ParserRuleReturnScope term55 =null;

		Object REQUIRES54_tree=null;
		RewriteRuleTokenStream stream_REQUIRES=new RewriteRuleTokenStream(adaptor,"token REQUIRES");
		RewriteRuleSubtreeStream stream_term=new RewriteRuleSubtreeStream(adaptor,"rule term");

		try {
			// AcslParser.g:183:5: ( REQUIRES term -> ^( REQUIRES term ) )
			// AcslParser.g:183:7: REQUIRES term
			{
			REQUIRES54=(Token)match(input,REQUIRES,FOLLOW_REQUIRES_in_requires_clause1250); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_REQUIRES.add(REQUIRES54);

			pushFollow(FOLLOW_term_in_requires_clause1252);
			term55=term();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_term.add(term55.getTree());
			// AST REWRITE
			// elements: term, REQUIRES
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 183:21: -> ^( REQUIRES term )
			{
				// AcslParser.g:183:24: ^( REQUIRES term )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_REQUIRES.nextNode(), root_1);
				adaptor.addChild(root_1, stream_term.nextTree());
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
	// $ANTLR end "requires_clause"


	public static class terminates_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "terminates_clause"
	// AcslParser.g:186:1: terminates_clause : TEMINATES term -> ^( TERMINATES term ) ;
	public final AcslParser.terminates_clause_return terminates_clause() throws RecognitionException {
		AcslParser.terminates_clause_return retval = new AcslParser.terminates_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token TEMINATES56=null;
		ParserRuleReturnScope term57 =null;

		Object TEMINATES56_tree=null;
		RewriteRuleTokenStream stream_TEMINATES=new RewriteRuleTokenStream(adaptor,"token TEMINATES");
		RewriteRuleSubtreeStream stream_term=new RewriteRuleSubtreeStream(adaptor,"rule term");

		try {
			// AcslParser.g:187:5: ( TEMINATES term -> ^( TERMINATES term ) )
			// AcslParser.g:187:7: TEMINATES term
			{
			TEMINATES56=(Token)match(input,TEMINATES,FOLLOW_TEMINATES_in_terminates_clause1277); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_TEMINATES.add(TEMINATES56);

			pushFollow(FOLLOW_term_in_terminates_clause1279);
			term57=term();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_term.add(term57.getTree());
			// AST REWRITE
			// elements: term
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 187:22: -> ^( TERMINATES term )
			{
				// AcslParser.g:187:25: ^( TERMINATES term )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TERMINATES, "TERMINATES"), root_1);
				adaptor.addChild(root_1, stream_term.nextTree());
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
	// $ANTLR end "terminates_clause"


	public static class rel_op_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "rel_op"
	// AcslParser.g:190:1: rel_op : ( EQ | NEQ | LTE | GTE | LT | GT );
	public final AcslParser.rel_op_return rel_op() throws RecognitionException {
		AcslParser.rel_op_return retval = new AcslParser.rel_op_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set58=null;

		Object set58_tree=null;

		try {
			// AcslParser.g:191:5: ( EQ | NEQ | LTE | GTE | LT | GT )
			// AcslParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set58=input.LT(1);
			if ( input.LA(1)==EQ||(input.LA(1) >= GT && input.LA(1) <= GTE)||(input.LA(1) >= LT && input.LA(1) <= LTE)||input.LA(1)==NEQ ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set58));
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
	// $ANTLR end "rel_op"


	public static class binders_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "binders"
	// AcslParser.g:194:1: binders : binder ( COMMA binder )* -> ^( BINDER_LIST ( binder )+ ) ;
	public final AcslParser.binders_return binders() throws RecognitionException {
		AcslParser.binders_return retval = new AcslParser.binders_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMMA60=null;
		ParserRuleReturnScope binder59 =null;
		ParserRuleReturnScope binder61 =null;

		Object COMMA60_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_binder=new RewriteRuleSubtreeStream(adaptor,"rule binder");

		try {
			// AcslParser.g:195:5: ( binder ( COMMA binder )* -> ^( BINDER_LIST ( binder )+ ) )
			// AcslParser.g:195:7: binder ( COMMA binder )*
			{
			pushFollow(FOLLOW_binder_in_binders1341);
			binder59=binder();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_binder.add(binder59.getTree());
			// AcslParser.g:195:14: ( COMMA binder )*
			loop20:
			while (true) {
				int alt20=2;
				int LA20_0 = input.LA(1);
				if ( (LA20_0==COMMA) ) {
					alt20=1;
				}

				switch (alt20) {
				case 1 :
					// AcslParser.g:195:15: COMMA binder
					{
					COMMA60=(Token)match(input,COMMA,FOLLOW_COMMA_in_binders1344); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA60);

					pushFollow(FOLLOW_binder_in_binders1346);
					binder61=binder();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_binder.add(binder61.getTree());
					}
					break;

				default :
					break loop20;
				}
			}

			// AST REWRITE
			// elements: binder
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 196:9: -> ^( BINDER_LIST ( binder )+ )
			{
				// AcslParser.g:196:11: ^( BINDER_LIST ( binder )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(BINDER_LIST, "BINDER_LIST"), root_1);
				if ( !(stream_binder.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_binder.hasNext() ) {
					adaptor.addChild(root_1, stream_binder.nextTree());
				}
				stream_binder.reset();

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
	// $ANTLR end "binders"


	public static class binder_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "binder"
	// AcslParser.g:199:1: binder : type_expr variable_ident ( COMMA variable_ident )* -> ^( BINDER type_expr ( variable_ident )+ ) ;
	public final AcslParser.binder_return binder() throws RecognitionException {
		AcslParser.binder_return retval = new AcslParser.binder_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMMA64=null;
		ParserRuleReturnScope type_expr62 =null;
		ParserRuleReturnScope variable_ident63 =null;
		ParserRuleReturnScope variable_ident65 =null;

		Object COMMA64_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_variable_ident=new RewriteRuleSubtreeStream(adaptor,"rule variable_ident");
		RewriteRuleSubtreeStream stream_type_expr=new RewriteRuleSubtreeStream(adaptor,"rule type_expr");

		try {
			// AcslParser.g:200:5: ( type_expr variable_ident ( COMMA variable_ident )* -> ^( BINDER type_expr ( variable_ident )+ ) )
			// AcslParser.g:200:7: type_expr variable_ident ( COMMA variable_ident )*
			{
			pushFollow(FOLLOW_type_expr_in_binder1381);
			type_expr62=type_expr();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_type_expr.add(type_expr62.getTree());
			pushFollow(FOLLOW_variable_ident_in_binder1383);
			variable_ident63=variable_ident();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_variable_ident.add(variable_ident63.getTree());
			// AcslParser.g:200:32: ( COMMA variable_ident )*
			loop21:
			while (true) {
				int alt21=2;
				int LA21_0 = input.LA(1);
				if ( (LA21_0==COMMA) ) {
					int LA21_1 = input.LA(2);
					if ( (LA21_1==ID) ) {
						int LA21_3 = input.LA(3);
						if ( (LA21_3==EOF||LA21_3==COMMA||LA21_3==LSQUARE||LA21_3==RCURLY||LA21_3==SEMICOL) ) {
							alt21=1;
						}

					}
					else if ( (LA21_1==LPAREN||LA21_1==STAR) ) {
						alt21=1;
					}

				}

				switch (alt21) {
				case 1 :
					// AcslParser.g:200:33: COMMA variable_ident
					{
					COMMA64=(Token)match(input,COMMA,FOLLOW_COMMA_in_binder1386); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA64);

					pushFollow(FOLLOW_variable_ident_in_binder1388);
					variable_ident65=variable_ident();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_variable_ident.add(variable_ident65.getTree());
					}
					break;

				default :
					break loop21;
				}
			}

			// AST REWRITE
			// elements: variable_ident, type_expr
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 201:9: -> ^( BINDER type_expr ( variable_ident )+ )
			{
				// AcslParser.g:201:11: ^( BINDER type_expr ( variable_ident )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(BINDER, "BINDER"), root_1);
				adaptor.addChild(root_1, stream_type_expr.nextTree());
				if ( !(stream_variable_ident.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_variable_ident.hasNext() ) {
					adaptor.addChild(root_1, stream_variable_ident.nextTree());
				}
				stream_variable_ident.reset();

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
	// $ANTLR end "binder"


	public static class type_expr_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "type_expr"
	// AcslParser.g:204:1: type_expr : ( logic_type_expr -> ^( LOGIC_TYPE logic_type_expr ) | c_type -> ^( C_TYPE c_type ) );
	public final AcslParser.type_expr_return type_expr() throws RecognitionException {
		AcslParser.type_expr_return retval = new AcslParser.type_expr_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope logic_type_expr66 =null;
		ParserRuleReturnScope c_type67 =null;

		RewriteRuleSubtreeStream stream_c_type=new RewriteRuleSubtreeStream(adaptor,"rule c_type");
		RewriteRuleSubtreeStream stream_logic_type_expr=new RewriteRuleSubtreeStream(adaptor,"rule logic_type_expr");

		try {
			// AcslParser.g:205:5: ( logic_type_expr -> ^( LOGIC_TYPE logic_type_expr ) | c_type -> ^( C_TYPE c_type ) )
			int alt22=2;
			int LA22_0 = input.LA(1);
			if ( (LA22_0==BOOLEAN||LA22_0==ID||LA22_0==INTEGER||LA22_0==REAL) ) {
				alt22=1;
			}
			else if ( (LA22_0==CHAR||LA22_0==DOUBLE||LA22_0==FLOAT||LA22_0==INT||LA22_0==LONG||LA22_0==SHORT||LA22_0==VOID) ) {
				alt22=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 22, 0, input);
				throw nvae;
			}

			switch (alt22) {
				case 1 :
					// AcslParser.g:205:7: logic_type_expr
					{
					pushFollow(FOLLOW_logic_type_expr_in_type_expr1425);
					logic_type_expr66=logic_type_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_logic_type_expr.add(logic_type_expr66.getTree());
					// AST REWRITE
					// elements: logic_type_expr
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 205:23: -> ^( LOGIC_TYPE logic_type_expr )
					{
						// AcslParser.g:205:25: ^( LOGIC_TYPE logic_type_expr )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(LOGIC_TYPE, "LOGIC_TYPE"), root_1);
						adaptor.addChild(root_1, stream_logic_type_expr.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:206:7: c_type
					{
					pushFollow(FOLLOW_c_type_in_type_expr1440);
					c_type67=c_type();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_c_type.add(c_type67.getTree());
					// AST REWRITE
					// elements: c_type
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 206:14: -> ^( C_TYPE c_type )
					{
						// AcslParser.g:206:16: ^( C_TYPE c_type )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(C_TYPE, "C_TYPE"), root_1);
						adaptor.addChild(root_1, stream_c_type.nextTree());
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
	// $ANTLR end "type_expr"


	public static class logic_type_expr_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "logic_type_expr"
	// AcslParser.g:209:1: logic_type_expr : ( built_in_logic_type -> ^( TYPE_BUILTIN built_in_logic_type ) | ID -> ^( TYPE_ID ID ) );
	public final AcslParser.logic_type_expr_return logic_type_expr() throws RecognitionException {
		AcslParser.logic_type_expr_return retval = new AcslParser.logic_type_expr_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ID69=null;
		ParserRuleReturnScope built_in_logic_type68 =null;

		Object ID69_tree=null;
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleSubtreeStream stream_built_in_logic_type=new RewriteRuleSubtreeStream(adaptor,"rule built_in_logic_type");

		try {
			// AcslParser.g:210:5: ( built_in_logic_type -> ^( TYPE_BUILTIN built_in_logic_type ) | ID -> ^( TYPE_ID ID ) )
			int alt23=2;
			int LA23_0 = input.LA(1);
			if ( (LA23_0==BOOLEAN||LA23_0==INTEGER||LA23_0==REAL) ) {
				alt23=1;
			}
			else if ( (LA23_0==ID) ) {
				alt23=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 23, 0, input);
				throw nvae;
			}

			switch (alt23) {
				case 1 :
					// AcslParser.g:210:7: built_in_logic_type
					{
					pushFollow(FOLLOW_built_in_logic_type_in_logic_type_expr1464);
					built_in_logic_type68=built_in_logic_type();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_built_in_logic_type.add(built_in_logic_type68.getTree());
					// AST REWRITE
					// elements: built_in_logic_type
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 210:27: -> ^( TYPE_BUILTIN built_in_logic_type )
					{
						// AcslParser.g:210:29: ^( TYPE_BUILTIN built_in_logic_type )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TYPE_BUILTIN, "TYPE_BUILTIN"), root_1);
						adaptor.addChild(root_1, stream_built_in_logic_type.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:211:7: ID
					{
					ID69=(Token)match(input,ID,FOLLOW_ID_in_logic_type_expr1479); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID69);

					// AST REWRITE
					// elements: ID
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 211:10: -> ^( TYPE_ID ID )
					{
						// AcslParser.g:211:12: ^( TYPE_ID ID )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TYPE_ID, "TYPE_ID"), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
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
	// $ANTLR end "logic_type_expr"


	public static class c_type_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "c_type"
	// AcslParser.g:214:1: c_type : ( CHAR | DOUBLE | FLOAT | INT | LONG | SHORT | VOID );
	public final AcslParser.c_type_return c_type() throws RecognitionException {
		AcslParser.c_type_return retval = new AcslParser.c_type_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set70=null;

		Object set70_tree=null;

		try {
			// AcslParser.g:215:5: ( CHAR | DOUBLE | FLOAT | INT | LONG | SHORT | VOID )
			// AcslParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set70=input.LT(1);
			if ( input.LA(1)==CHAR||input.LA(1)==DOUBLE||input.LA(1)==FLOAT||input.LA(1)==INT||input.LA(1)==LONG||input.LA(1)==SHORT||input.LA(1)==VOID ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set70));
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
	// $ANTLR end "c_type"


	public static class built_in_logic_type_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "built_in_logic_type"
	// AcslParser.g:218:1: built_in_logic_type : ( BOOLEAN | INTEGER | REAL );
	public final AcslParser.built_in_logic_type_return built_in_logic_type() throws RecognitionException {
		AcslParser.built_in_logic_type_return retval = new AcslParser.built_in_logic_type_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set71=null;

		Object set71_tree=null;

		try {
			// AcslParser.g:219:5: ( BOOLEAN | INTEGER | REAL )
			// AcslParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set71=input.LT(1);
			if ( input.LA(1)==BOOLEAN||input.LA(1)==INTEGER||input.LA(1)==REAL ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set71));
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
	// $ANTLR end "built_in_logic_type"


	public static class variable_ident_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "variable_ident"
	// AcslParser.g:222:1: variable_ident : ( STAR variable_ident_base -> ^( VAR_ID_STAR variable_ident_base ) | variable_ident_base LSQUARE RSQUARE -> ^( VAR_ID_SQUARE variable_ident_base ) | variable_ident_base -> ^( VAR_ID variable_ident_base ) );
	public final AcslParser.variable_ident_return variable_ident() throws RecognitionException {
		AcslParser.variable_ident_return retval = new AcslParser.variable_ident_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token STAR72=null;
		Token LSQUARE75=null;
		Token RSQUARE76=null;
		ParserRuleReturnScope variable_ident_base73 =null;
		ParserRuleReturnScope variable_ident_base74 =null;
		ParserRuleReturnScope variable_ident_base77 =null;

		Object STAR72_tree=null;
		Object LSQUARE75_tree=null;
		Object RSQUARE76_tree=null;
		RewriteRuleTokenStream stream_STAR=new RewriteRuleTokenStream(adaptor,"token STAR");
		RewriteRuleTokenStream stream_LSQUARE=new RewriteRuleTokenStream(adaptor,"token LSQUARE");
		RewriteRuleTokenStream stream_RSQUARE=new RewriteRuleTokenStream(adaptor,"token RSQUARE");
		RewriteRuleSubtreeStream stream_variable_ident_base=new RewriteRuleSubtreeStream(adaptor,"rule variable_ident_base");

		try {
			// AcslParser.g:223:5: ( STAR variable_ident_base -> ^( VAR_ID_STAR variable_ident_base ) | variable_ident_base LSQUARE RSQUARE -> ^( VAR_ID_SQUARE variable_ident_base ) | variable_ident_base -> ^( VAR_ID variable_ident_base ) )
			int alt24=3;
			switch ( input.LA(1) ) {
			case STAR:
				{
				alt24=1;
				}
				break;
			case ID:
				{
				int LA24_2 = input.LA(2);
				if ( (synpred40_AcslParser()) ) {
					alt24=2;
				}
				else if ( (true) ) {
					alt24=3;
				}

				}
				break;
			case LPAREN:
				{
				int LA24_3 = input.LA(2);
				if ( (synpred40_AcslParser()) ) {
					alt24=2;
				}
				else if ( (true) ) {
					alt24=3;
				}

				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 24, 0, input);
				throw nvae;
			}
			switch (alt24) {
				case 1 :
					// AcslParser.g:223:7: STAR variable_ident_base
					{
					STAR72=(Token)match(input,STAR,FOLLOW_STAR_in_variable_ident1569); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_STAR.add(STAR72);

					pushFollow(FOLLOW_variable_ident_base_in_variable_ident1571);
					variable_ident_base73=variable_ident_base();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_variable_ident_base.add(variable_ident_base73.getTree());
					// AST REWRITE
					// elements: variable_ident_base
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 224:9: -> ^( VAR_ID_STAR variable_ident_base )
					{
						// AcslParser.g:224:11: ^( VAR_ID_STAR variable_ident_base )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(VAR_ID_STAR, "VAR_ID_STAR"), root_1);
						adaptor.addChild(root_1, stream_variable_ident_base.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:225:7: variable_ident_base LSQUARE RSQUARE
					{
					pushFollow(FOLLOW_variable_ident_base_in_variable_ident1594);
					variable_ident_base74=variable_ident_base();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_variable_ident_base.add(variable_ident_base74.getTree());
					LSQUARE75=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_variable_ident1596); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LSQUARE.add(LSQUARE75);

					RSQUARE76=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_variable_ident1598); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE76);

					// AST REWRITE
					// elements: variable_ident_base
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 226:9: -> ^( VAR_ID_SQUARE variable_ident_base )
					{
						// AcslParser.g:226:11: ^( VAR_ID_SQUARE variable_ident_base )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(VAR_ID_SQUARE, "VAR_ID_SQUARE"), root_1);
						adaptor.addChild(root_1, stream_variable_ident_base.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// AcslParser.g:227:7: variable_ident_base
					{
					pushFollow(FOLLOW_variable_ident_base_in_variable_ident1621);
					variable_ident_base77=variable_ident_base();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_variable_ident_base.add(variable_ident_base77.getTree());
					// AST REWRITE
					// elements: variable_ident_base
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 228:9: -> ^( VAR_ID variable_ident_base )
					{
						// AcslParser.g:228:11: ^( VAR_ID variable_ident_base )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(VAR_ID, "VAR_ID"), root_1);
						adaptor.addChild(root_1, stream_variable_ident_base.nextTree());
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
	// $ANTLR end "variable_ident"


	public static class variable_ident_base_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "variable_ident_base"
	// AcslParser.g:231:1: variable_ident_base : ( ID -> ^( ID ) | LPAREN variable_ident RPAREN -> ^( VAR_ID_BASE variable_ident ) );
	public final AcslParser.variable_ident_base_return variable_ident_base() throws RecognitionException {
		AcslParser.variable_ident_base_return retval = new AcslParser.variable_ident_base_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ID78=null;
		Token LPAREN79=null;
		Token RPAREN81=null;
		ParserRuleReturnScope variable_ident80 =null;

		Object ID78_tree=null;
		Object LPAREN79_tree=null;
		Object RPAREN81_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_variable_ident=new RewriteRuleSubtreeStream(adaptor,"rule variable_ident");

		try {
			// AcslParser.g:232:5: ( ID -> ^( ID ) | LPAREN variable_ident RPAREN -> ^( VAR_ID_BASE variable_ident ) )
			int alt25=2;
			int LA25_0 = input.LA(1);
			if ( (LA25_0==ID) ) {
				alt25=1;
			}
			else if ( (LA25_0==LPAREN) ) {
				alt25=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 25, 0, input);
				throw nvae;
			}

			switch (alt25) {
				case 1 :
					// AcslParser.g:232:7: ID
					{
					ID78=(Token)match(input,ID,FOLLOW_ID_in_variable_ident_base1653); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID78);

					// AST REWRITE
					// elements: ID
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 233:7: -> ^( ID )
					{
						// AcslParser.g:233:9: ^( ID )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ID.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:234:7: LPAREN variable_ident RPAREN
					{
					LPAREN79=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_variable_ident_base1672); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN79);

					pushFollow(FOLLOW_variable_ident_in_variable_ident_base1674);
					variable_ident80=variable_ident();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_variable_ident.add(variable_ident80.getTree());
					RPAREN81=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_variable_ident_base1676); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN81);

					// AST REWRITE
					// elements: variable_ident
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 235:7: -> ^( VAR_ID_BASE variable_ident )
					{
						// AcslParser.g:235:9: ^( VAR_ID_BASE variable_ident )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(VAR_ID_BASE, "VAR_ID_BASE"), root_1);
						adaptor.addChild(root_1, stream_variable_ident.nextTree());
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
	// $ANTLR end "variable_ident_base"


	public static class guards_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "guards_clause"
	// AcslParser.g:238:1: guards_clause : GUARDS term -> ^( GUARDS term ) ;
	public final AcslParser.guards_clause_return guards_clause() throws RecognitionException {
		AcslParser.guards_clause_return retval = new AcslParser.guards_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token GUARDS82=null;
		ParserRuleReturnScope term83 =null;

		Object GUARDS82_tree=null;
		RewriteRuleTokenStream stream_GUARDS=new RewriteRuleTokenStream(adaptor,"token GUARDS");
		RewriteRuleSubtreeStream stream_term=new RewriteRuleSubtreeStream(adaptor,"rule term");

		try {
			// AcslParser.g:239:5: ( GUARDS term -> ^( GUARDS term ) )
			// AcslParser.g:239:7: GUARDS term
			{
			GUARDS82=(Token)match(input,GUARDS,FOLLOW_GUARDS_in_guards_clause1706); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_GUARDS.add(GUARDS82);

			pushFollow(FOLLOW_term_in_guards_clause1708);
			term83=term();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_term.add(term83.getTree());
			// AST REWRITE
			// elements: term, GUARDS
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 239:19: -> ^( GUARDS term )
			{
				// AcslParser.g:239:21: ^( GUARDS term )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_GUARDS.nextNode(), root_1);
				adaptor.addChild(root_1, stream_term.nextTree());
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
	// $ANTLR end "guards_clause"


	public static class simple_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "simple_clause"
	// AcslParser.g:242:1: simple_clause : ( assigns_clause | ensures_clause | allocation_clause | reads_clause | depends_clause | guards_clause );
	public final AcslParser.simple_clause_return simple_clause() throws RecognitionException {
		AcslParser.simple_clause_return retval = new AcslParser.simple_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope assigns_clause84 =null;
		ParserRuleReturnScope ensures_clause85 =null;
		ParserRuleReturnScope allocation_clause86 =null;
		ParserRuleReturnScope reads_clause87 =null;
		ParserRuleReturnScope depends_clause88 =null;
		ParserRuleReturnScope guards_clause89 =null;


		try {
			// AcslParser.g:243:5: ( assigns_clause | ensures_clause | allocation_clause | reads_clause | depends_clause | guards_clause )
			int alt26=6;
			switch ( input.LA(1) ) {
			case ASSIGNS:
				{
				alt26=1;
				}
				break;
			case ENSURES:
				{
				alt26=2;
				}
				break;
			case ALLOC:
			case FREES:
				{
				alt26=3;
				}
				break;
			case READS:
				{
				alt26=4;
				}
				break;
			case DEPENDS:
				{
				alt26=5;
				}
				break;
			case GUARDS:
				{
				alt26=6;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 26, 0, input);
				throw nvae;
			}
			switch (alt26) {
				case 1 :
					// AcslParser.g:243:7: assigns_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_assigns_clause_in_simple_clause1732);
					assigns_clause84=assigns_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, assigns_clause84.getTree());

					}
					break;
				case 2 :
					// AcslParser.g:244:7: ensures_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_ensures_clause_in_simple_clause1740);
					ensures_clause85=ensures_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, ensures_clause85.getTree());

					}
					break;
				case 3 :
					// AcslParser.g:245:7: allocation_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_allocation_clause_in_simple_clause1749);
					allocation_clause86=allocation_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, allocation_clause86.getTree());

					}
					break;
				case 4 :
					// AcslParser.g:246:7: reads_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_reads_clause_in_simple_clause1757);
					reads_clause87=reads_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, reads_clause87.getTree());

					}
					break;
				case 5 :
					// AcslParser.g:247:7: depends_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_depends_clause_in_simple_clause1765);
					depends_clause88=depends_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, depends_clause88.getTree());

					}
					break;
				case 6 :
					// AcslParser.g:248:7: guards_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_guards_clause_in_simple_clause1773);
					guards_clause89=guards_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, guards_clause89.getTree());

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
	// $ANTLR end "simple_clause"


	public static class assigns_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "assigns_clause"
	// AcslParser.g:251:1: assigns_clause : ASSIGNS argumentExpressionList -> ^( ASSIGNS argumentExpressionList ) ;
	public final AcslParser.assigns_clause_return assigns_clause() throws RecognitionException {
		AcslParser.assigns_clause_return retval = new AcslParser.assigns_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ASSIGNS90=null;
		ParserRuleReturnScope argumentExpressionList91 =null;

		Object ASSIGNS90_tree=null;
		RewriteRuleTokenStream stream_ASSIGNS=new RewriteRuleTokenStream(adaptor,"token ASSIGNS");
		RewriteRuleSubtreeStream stream_argumentExpressionList=new RewriteRuleSubtreeStream(adaptor,"rule argumentExpressionList");

		try {
			// AcslParser.g:252:5: ( ASSIGNS argumentExpressionList -> ^( ASSIGNS argumentExpressionList ) )
			// AcslParser.g:252:7: ASSIGNS argumentExpressionList
			{
			ASSIGNS90=(Token)match(input,ASSIGNS,FOLLOW_ASSIGNS_in_assigns_clause1790); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ASSIGNS.add(ASSIGNS90);

			pushFollow(FOLLOW_argumentExpressionList_in_assigns_clause1792);
			argumentExpressionList91=argumentExpressionList();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList91.getTree());
			// AST REWRITE
			// elements: argumentExpressionList, ASSIGNS
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 252:38: -> ^( ASSIGNS argumentExpressionList )
			{
				// AcslParser.g:252:40: ^( ASSIGNS argumentExpressionList )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_ASSIGNS.nextNode(), root_1);
				adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
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
	// $ANTLR end "assigns_clause"


	public static class ensures_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "ensures_clause"
	// AcslParser.g:255:1: ensures_clause : ENSURES term -> ^( ENSURES term ) ;
	public final AcslParser.ensures_clause_return ensures_clause() throws RecognitionException {
		AcslParser.ensures_clause_return retval = new AcslParser.ensures_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ENSURES92=null;
		ParserRuleReturnScope term93 =null;

		Object ENSURES92_tree=null;
		RewriteRuleTokenStream stream_ENSURES=new RewriteRuleTokenStream(adaptor,"token ENSURES");
		RewriteRuleSubtreeStream stream_term=new RewriteRuleSubtreeStream(adaptor,"rule term");

		try {
			// AcslParser.g:256:5: ( ENSURES term -> ^( ENSURES term ) )
			// AcslParser.g:256:7: ENSURES term
			{
			ENSURES92=(Token)match(input,ENSURES,FOLLOW_ENSURES_in_ensures_clause1816); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ENSURES.add(ENSURES92);

			pushFollow(FOLLOW_term_in_ensures_clause1818);
			term93=term();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_term.add(term93.getTree());
			// AST REWRITE
			// elements: ENSURES, term
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 256:20: -> ^( ENSURES term )
			{
				// AcslParser.g:256:22: ^( ENSURES term )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_ENSURES.nextNode(), root_1);
				adaptor.addChild(root_1, stream_term.nextTree());
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
	// $ANTLR end "ensures_clause"


	public static class allocation_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "allocation_clause"
	// AcslParser.g:259:1: allocation_clause : ( ALLOC argumentExpressionList ( COMMA term )? -> ^( ALLOC argumentExpressionList ( term )? ) | FREES argumentExpressionList -> ^( FREES argumentExpressionList ) );
	public final AcslParser.allocation_clause_return allocation_clause() throws RecognitionException {
		AcslParser.allocation_clause_return retval = new AcslParser.allocation_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ALLOC94=null;
		Token COMMA96=null;
		Token FREES98=null;
		ParserRuleReturnScope argumentExpressionList95 =null;
		ParserRuleReturnScope term97 =null;
		ParserRuleReturnScope argumentExpressionList99 =null;

		Object ALLOC94_tree=null;
		Object COMMA96_tree=null;
		Object FREES98_tree=null;
		RewriteRuleTokenStream stream_FREES=new RewriteRuleTokenStream(adaptor,"token FREES");
		RewriteRuleTokenStream stream_ALLOC=new RewriteRuleTokenStream(adaptor,"token ALLOC");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_term=new RewriteRuleSubtreeStream(adaptor,"rule term");
		RewriteRuleSubtreeStream stream_argumentExpressionList=new RewriteRuleSubtreeStream(adaptor,"rule argumentExpressionList");

		try {
			// AcslParser.g:260:5: ( ALLOC argumentExpressionList ( COMMA term )? -> ^( ALLOC argumentExpressionList ( term )? ) | FREES argumentExpressionList -> ^( FREES argumentExpressionList ) )
			int alt28=2;
			int LA28_0 = input.LA(1);
			if ( (LA28_0==ALLOC) ) {
				alt28=1;
			}
			else if ( (LA28_0==FREES) ) {
				alt28=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 28, 0, input);
				throw nvae;
			}

			switch (alt28) {
				case 1 :
					// AcslParser.g:260:7: ALLOC argumentExpressionList ( COMMA term )?
					{
					ALLOC94=(Token)match(input,ALLOC,FOLLOW_ALLOC_in_allocation_clause1842); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ALLOC.add(ALLOC94);

					pushFollow(FOLLOW_argumentExpressionList_in_allocation_clause1844);
					argumentExpressionList95=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList95.getTree());
					// AcslParser.g:260:36: ( COMMA term )?
					int alt27=2;
					int LA27_0 = input.LA(1);
					if ( (LA27_0==COMMA) ) {
						alt27=1;
					}
					switch (alt27) {
						case 1 :
							// AcslParser.g:260:37: COMMA term
							{
							COMMA96=(Token)match(input,COMMA,FOLLOW_COMMA_in_allocation_clause1847); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_COMMA.add(COMMA96);

							pushFollow(FOLLOW_term_in_allocation_clause1849);
							term97=term();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_term.add(term97.getTree());
							}
							break;

					}

					// AST REWRITE
					// elements: argumentExpressionList, term, ALLOC
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 260:50: -> ^( ALLOC argumentExpressionList ( term )? )
					{
						// AcslParser.g:260:52: ^( ALLOC argumentExpressionList ( term )? )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ALLOC.nextNode(), root_1);
						adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
						// AcslParser.g:260:83: ( term )?
						if ( stream_term.hasNext() ) {
							adaptor.addChild(root_1, stream_term.nextTree());
						}
						stream_term.reset();

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:261:7: FREES argumentExpressionList
					{
					FREES98=(Token)match(input,FREES,FOLLOW_FREES_in_allocation_clause1869); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_FREES.add(FREES98);

					pushFollow(FOLLOW_argumentExpressionList_in_allocation_clause1871);
					argumentExpressionList99=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList99.getTree());
					// AST REWRITE
					// elements: argumentExpressionList, FREES
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 261:36: -> ^( FREES argumentExpressionList )
					{
						// AcslParser.g:261:38: ^( FREES argumentExpressionList )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_FREES.nextNode(), root_1);
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
	// $ANTLR end "allocation_clause"


	public static class reads_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "reads_clause"
	// AcslParser.g:264:1: reads_clause : READS argumentExpressionList -> ^( READS argumentExpressionList ) ;
	public final AcslParser.reads_clause_return reads_clause() throws RecognitionException {
		AcslParser.reads_clause_return retval = new AcslParser.reads_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token READS100=null;
		ParserRuleReturnScope argumentExpressionList101 =null;

		Object READS100_tree=null;
		RewriteRuleTokenStream stream_READS=new RewriteRuleTokenStream(adaptor,"token READS");
		RewriteRuleSubtreeStream stream_argumentExpressionList=new RewriteRuleSubtreeStream(adaptor,"rule argumentExpressionList");

		try {
			// AcslParser.g:265:5: ( READS argumentExpressionList -> ^( READS argumentExpressionList ) )
			// AcslParser.g:265:7: READS argumentExpressionList
			{
			READS100=(Token)match(input,READS,FOLLOW_READS_in_reads_clause1895); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_READS.add(READS100);

			pushFollow(FOLLOW_argumentExpressionList_in_reads_clause1897);
			argumentExpressionList101=argumentExpressionList();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList101.getTree());
			// AST REWRITE
			// elements: argumentExpressionList, READS
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 265:36: -> ^( READS argumentExpressionList )
			{
				// AcslParser.g:265:38: ^( READS argumentExpressionList )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_READS.nextNode(), root_1);
				adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
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
	// $ANTLR end "reads_clause"


	public static class depends_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "depends_clause"
	// AcslParser.g:272:1: depends_clause : DEPENDS event_list -> ^( DEPENDS event_list ) ;
	public final AcslParser.depends_clause_return depends_clause() throws RecognitionException {
		AcslParser.depends_clause_return retval = new AcslParser.depends_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token DEPENDS102=null;
		ParserRuleReturnScope event_list103 =null;

		Object DEPENDS102_tree=null;
		RewriteRuleTokenStream stream_DEPENDS=new RewriteRuleTokenStream(adaptor,"token DEPENDS");
		RewriteRuleSubtreeStream stream_event_list=new RewriteRuleSubtreeStream(adaptor,"rule event_list");

		try {
			// AcslParser.g:273:5: ( DEPENDS event_list -> ^( DEPENDS event_list ) )
			// AcslParser.g:273:7: DEPENDS event_list
			{
			DEPENDS102=(Token)match(input,DEPENDS,FOLLOW_DEPENDS_in_depends_clause1922); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_DEPENDS.add(DEPENDS102);

			pushFollow(FOLLOW_event_list_in_depends_clause1924);
			event_list103=event_list();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_event_list.add(event_list103.getTree());
			// AST REWRITE
			// elements: event_list, DEPENDS
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 273:26: -> ^( DEPENDS event_list )
			{
				// AcslParser.g:273:28: ^( DEPENDS event_list )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_DEPENDS.nextNode(), root_1);
				adaptor.addChild(root_1, stream_event_list.nextTree());
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
	// $ANTLR end "depends_clause"


	public static class event_list_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "event_list"
	// AcslParser.g:276:1: event_list : event ( COMMA event )* -> ^( EVENT_LIST ( event )+ ) ;
	public final AcslParser.event_list_return event_list() throws RecognitionException {
		AcslParser.event_list_return retval = new AcslParser.event_list_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMMA105=null;
		ParserRuleReturnScope event104 =null;
		ParserRuleReturnScope event106 =null;

		Object COMMA105_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_event=new RewriteRuleSubtreeStream(adaptor,"rule event");

		try {
			// AcslParser.g:277:5: ( event ( COMMA event )* -> ^( EVENT_LIST ( event )+ ) )
			// AcslParser.g:277:7: event ( COMMA event )*
			{
			pushFollow(FOLLOW_event_in_event_list1948);
			event104=event();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_event.add(event104.getTree());
			// AcslParser.g:277:13: ( COMMA event )*
			loop29:
			while (true) {
				int alt29=2;
				int LA29_0 = input.LA(1);
				if ( (LA29_0==COMMA) ) {
					alt29=1;
				}

				switch (alt29) {
				case 1 :
					// AcslParser.g:277:14: COMMA event
					{
					COMMA105=(Token)match(input,COMMA,FOLLOW_COMMA_in_event_list1951); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA105);

					pushFollow(FOLLOW_event_in_event_list1953);
					event106=event();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_event.add(event106.getTree());
					}
					break;

				default :
					break loop29;
				}
			}

			// AST REWRITE
			// elements: event
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 277:28: -> ^( EVENT_LIST ( event )+ )
			{
				// AcslParser.g:277:31: ^( EVENT_LIST ( event )+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(EVENT_LIST, "EVENT_LIST"), root_1);
				if ( !(stream_event.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_event.hasNext() ) {
					adaptor.addChild(root_1, stream_event.nextTree());
				}
				stream_event.reset();

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
	// $ANTLR end "event_list"


	public static class event_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "event"
	// AcslParser.g:280:1: event : ( event_base PLUS event_base -> ^( EVENT_PLUS event_base event_base ) | event_base SUB event_base -> ^( EVENT_SUB event_base event_base ) | event_base AMPERSAND event_base -> ^( EVENT_INTS event_base event_base ) | event_base -> ^( EVENT_BASE event_base ) );
	public final AcslParser.event_return event() throws RecognitionException {
		AcslParser.event_return retval = new AcslParser.event_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PLUS108=null;
		Token SUB111=null;
		Token AMPERSAND114=null;
		ParserRuleReturnScope event_base107 =null;
		ParserRuleReturnScope event_base109 =null;
		ParserRuleReturnScope event_base110 =null;
		ParserRuleReturnScope event_base112 =null;
		ParserRuleReturnScope event_base113 =null;
		ParserRuleReturnScope event_base115 =null;
		ParserRuleReturnScope event_base116 =null;

		Object PLUS108_tree=null;
		Object SUB111_tree=null;
		Object AMPERSAND114_tree=null;
		RewriteRuleTokenStream stream_AMPERSAND=new RewriteRuleTokenStream(adaptor,"token AMPERSAND");
		RewriteRuleTokenStream stream_SUB=new RewriteRuleTokenStream(adaptor,"token SUB");
		RewriteRuleTokenStream stream_PLUS=new RewriteRuleTokenStream(adaptor,"token PLUS");
		RewriteRuleSubtreeStream stream_event_base=new RewriteRuleSubtreeStream(adaptor,"rule event_base");

		try {
			// AcslParser.g:281:5: ( event_base PLUS event_base -> ^( EVENT_PLUS event_base event_base ) | event_base SUB event_base -> ^( EVENT_SUB event_base event_base ) | event_base AMPERSAND event_base -> ^( EVENT_INTS event_base event_base ) | event_base -> ^( EVENT_BASE event_base ) )
			int alt30=4;
			switch ( input.LA(1) ) {
			case READ:
				{
				int LA30_1 = input.LA(2);
				if ( (synpred50_AcslParser()) ) {
					alt30=1;
				}
				else if ( (synpred51_AcslParser()) ) {
					alt30=2;
				}
				else if ( (synpred52_AcslParser()) ) {
					alt30=3;
				}
				else if ( (true) ) {
					alt30=4;
				}

				}
				break;
			case WRITE:
				{
				int LA30_2 = input.LA(2);
				if ( (synpred50_AcslParser()) ) {
					alt30=1;
				}
				else if ( (synpred51_AcslParser()) ) {
					alt30=2;
				}
				else if ( (synpred52_AcslParser()) ) {
					alt30=3;
				}
				else if ( (true) ) {
					alt30=4;
				}

				}
				break;
			case REACH:
				{
				int LA30_3 = input.LA(2);
				if ( (synpred50_AcslParser()) ) {
					alt30=1;
				}
				else if ( (synpred51_AcslParser()) ) {
					alt30=2;
				}
				else if ( (synpred52_AcslParser()) ) {
					alt30=3;
				}
				else if ( (true) ) {
					alt30=4;
				}

				}
				break;
			case CALL:
				{
				int LA30_4 = input.LA(2);
				if ( (synpred50_AcslParser()) ) {
					alt30=1;
				}
				else if ( (synpred51_AcslParser()) ) {
					alt30=2;
				}
				else if ( (synpred52_AcslParser()) ) {
					alt30=3;
				}
				else if ( (true) ) {
					alt30=4;
				}

				}
				break;
			case NOACT:
				{
				int LA30_5 = input.LA(2);
				if ( (synpred50_AcslParser()) ) {
					alt30=1;
				}
				else if ( (synpred51_AcslParser()) ) {
					alt30=2;
				}
				else if ( (synpred52_AcslParser()) ) {
					alt30=3;
				}
				else if ( (true) ) {
					alt30=4;
				}

				}
				break;
			case ANYACT:
				{
				int LA30_6 = input.LA(2);
				if ( (synpred50_AcslParser()) ) {
					alt30=1;
				}
				else if ( (synpred51_AcslParser()) ) {
					alt30=2;
				}
				else if ( (synpred52_AcslParser()) ) {
					alt30=3;
				}
				else if ( (true) ) {
					alt30=4;
				}

				}
				break;
			case LPAREN:
				{
				int LA30_7 = input.LA(2);
				if ( (synpred50_AcslParser()) ) {
					alt30=1;
				}
				else if ( (synpred51_AcslParser()) ) {
					alt30=2;
				}
				else if ( (synpred52_AcslParser()) ) {
					alt30=3;
				}
				else if ( (true) ) {
					alt30=4;
				}

				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 30, 0, input);
				throw nvae;
			}
			switch (alt30) {
				case 1 :
					// AcslParser.g:281:7: event_base PLUS event_base
					{
					pushFollow(FOLLOW_event_base_in_event1981);
					event_base107=event_base();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_event_base.add(event_base107.getTree());
					PLUS108=(Token)match(input,PLUS,FOLLOW_PLUS_in_event1983); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_PLUS.add(PLUS108);

					pushFollow(FOLLOW_event_base_in_event1985);
					event_base109=event_base();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_event_base.add(event_base109.getTree());
					// AST REWRITE
					// elements: event_base, event_base
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 282:9: -> ^( EVENT_PLUS event_base event_base )
					{
						// AcslParser.g:282:12: ^( EVENT_PLUS event_base event_base )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(EVENT_PLUS, "EVENT_PLUS"), root_1);
						adaptor.addChild(root_1, stream_event_base.nextTree());
						adaptor.addChild(root_1, stream_event_base.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:283:7: event_base SUB event_base
					{
					pushFollow(FOLLOW_event_base_in_event2011);
					event_base110=event_base();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_event_base.add(event_base110.getTree());
					SUB111=(Token)match(input,SUB,FOLLOW_SUB_in_event2013); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SUB.add(SUB111);

					pushFollow(FOLLOW_event_base_in_event2015);
					event_base112=event_base();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_event_base.add(event_base112.getTree());
					// AST REWRITE
					// elements: event_base, event_base
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 284:9: -> ^( EVENT_SUB event_base event_base )
					{
						// AcslParser.g:284:12: ^( EVENT_SUB event_base event_base )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(EVENT_SUB, "EVENT_SUB"), root_1);
						adaptor.addChild(root_1, stream_event_base.nextTree());
						adaptor.addChild(root_1, stream_event_base.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// AcslParser.g:285:7: event_base AMPERSAND event_base
					{
					pushFollow(FOLLOW_event_base_in_event2041);
					event_base113=event_base();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_event_base.add(event_base113.getTree());
					AMPERSAND114=(Token)match(input,AMPERSAND,FOLLOW_AMPERSAND_in_event2043); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_AMPERSAND.add(AMPERSAND114);

					pushFollow(FOLLOW_event_base_in_event2045);
					event_base115=event_base();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_event_base.add(event_base115.getTree());
					// AST REWRITE
					// elements: event_base, event_base
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 286:9: -> ^( EVENT_INTS event_base event_base )
					{
						// AcslParser.g:286:12: ^( EVENT_INTS event_base event_base )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(EVENT_INTS, "EVENT_INTS"), root_1);
						adaptor.addChild(root_1, stream_event_base.nextTree());
						adaptor.addChild(root_1, stream_event_base.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// AcslParser.g:287:7: event_base
					{
					pushFollow(FOLLOW_event_base_in_event2071);
					event_base116=event_base();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_event_base.add(event_base116.getTree());
					// AST REWRITE
					// elements: event_base
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 288:9: -> ^( EVENT_BASE event_base )
					{
						// AcslParser.g:288:12: ^( EVENT_BASE event_base )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(EVENT_BASE, "EVENT_BASE"), root_1);
						adaptor.addChild(root_1, stream_event_base.nextTree());
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
	// $ANTLR end "event"


	public static class event_base_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "event_base"
	// AcslParser.g:291:1: event_base : ( READ LPAREN argumentExpressionList RPAREN -> ^( READ argumentExpressionList ) | WRITE LPAREN argumentExpressionList RPAREN -> ^( WRITE argumentExpressionList ) | REACH LPAREN argumentExpressionList RPAREN -> ^( REACH argumentExpressionList ) | CALL LPAREN ID ( COMMA argumentExpressionList )? RPAREN -> ^( CALL ID ( argumentExpressionList )? ) | NOACT -> ^( NOACT ) | ANYACT -> ^( ANYACT ) | LPAREN event RPAREN -> ^( EVENT_PARENTHESIZED event ) );
	public final AcslParser.event_base_return event_base() throws RecognitionException {
		AcslParser.event_base_return retval = new AcslParser.event_base_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token READ117=null;
		Token LPAREN118=null;
		Token RPAREN120=null;
		Token WRITE121=null;
		Token LPAREN122=null;
		Token RPAREN124=null;
		Token REACH125=null;
		Token LPAREN126=null;
		Token RPAREN128=null;
		Token CALL129=null;
		Token LPAREN130=null;
		Token ID131=null;
		Token COMMA132=null;
		Token RPAREN134=null;
		Token NOACT135=null;
		Token ANYACT136=null;
		Token LPAREN137=null;
		Token RPAREN139=null;
		ParserRuleReturnScope argumentExpressionList119 =null;
		ParserRuleReturnScope argumentExpressionList123 =null;
		ParserRuleReturnScope argumentExpressionList127 =null;
		ParserRuleReturnScope argumentExpressionList133 =null;
		ParserRuleReturnScope event138 =null;

		Object READ117_tree=null;
		Object LPAREN118_tree=null;
		Object RPAREN120_tree=null;
		Object WRITE121_tree=null;
		Object LPAREN122_tree=null;
		Object RPAREN124_tree=null;
		Object REACH125_tree=null;
		Object LPAREN126_tree=null;
		Object RPAREN128_tree=null;
		Object CALL129_tree=null;
		Object LPAREN130_tree=null;
		Object ID131_tree=null;
		Object COMMA132_tree=null;
		Object RPAREN134_tree=null;
		Object NOACT135_tree=null;
		Object ANYACT136_tree=null;
		Object LPAREN137_tree=null;
		Object RPAREN139_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_NOACT=new RewriteRuleTokenStream(adaptor,"token NOACT");
		RewriteRuleTokenStream stream_REACH=new RewriteRuleTokenStream(adaptor,"token REACH");
		RewriteRuleTokenStream stream_CALL=new RewriteRuleTokenStream(adaptor,"token CALL");
		RewriteRuleTokenStream stream_ANYACT=new RewriteRuleTokenStream(adaptor,"token ANYACT");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_READ=new RewriteRuleTokenStream(adaptor,"token READ");
		RewriteRuleTokenStream stream_WRITE=new RewriteRuleTokenStream(adaptor,"token WRITE");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_event=new RewriteRuleSubtreeStream(adaptor,"rule event");
		RewriteRuleSubtreeStream stream_argumentExpressionList=new RewriteRuleSubtreeStream(adaptor,"rule argumentExpressionList");

		try {
			// AcslParser.g:292:5: ( READ LPAREN argumentExpressionList RPAREN -> ^( READ argumentExpressionList ) | WRITE LPAREN argumentExpressionList RPAREN -> ^( WRITE argumentExpressionList ) | REACH LPAREN argumentExpressionList RPAREN -> ^( REACH argumentExpressionList ) | CALL LPAREN ID ( COMMA argumentExpressionList )? RPAREN -> ^( CALL ID ( argumentExpressionList )? ) | NOACT -> ^( NOACT ) | ANYACT -> ^( ANYACT ) | LPAREN event RPAREN -> ^( EVENT_PARENTHESIZED event ) )
			int alt32=7;
			switch ( input.LA(1) ) {
			case READ:
				{
				alt32=1;
				}
				break;
			case WRITE:
				{
				alt32=2;
				}
				break;
			case REACH:
				{
				alt32=3;
				}
				break;
			case CALL:
				{
				alt32=4;
				}
				break;
			case NOACT:
				{
				alt32=5;
				}
				break;
			case ANYACT:
				{
				alt32=6;
				}
				break;
			case LPAREN:
				{
				alt32=7;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 32, 0, input);
				throw nvae;
			}
			switch (alt32) {
				case 1 :
					// AcslParser.g:292:7: READ LPAREN argumentExpressionList RPAREN
					{
					READ117=(Token)match(input,READ,FOLLOW_READ_in_event_base2104); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_READ.add(READ117);

					LPAREN118=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_event_base2106); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN118);

					pushFollow(FOLLOW_argumentExpressionList_in_event_base2108);
					argumentExpressionList119=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList119.getTree());
					RPAREN120=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_event_base2110); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN120);

					// AST REWRITE
					// elements: READ, argumentExpressionList
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 293:9: -> ^( READ argumentExpressionList )
					{
						// AcslParser.g:293:12: ^( READ argumentExpressionList )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_READ.nextNode(), root_1);
						adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:294:7: WRITE LPAREN argumentExpressionList RPAREN
					{
					WRITE121=(Token)match(input,WRITE,FOLLOW_WRITE_in_event_base2134); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_WRITE.add(WRITE121);

					LPAREN122=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_event_base2136); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN122);

					pushFollow(FOLLOW_argumentExpressionList_in_event_base2138);
					argumentExpressionList123=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList123.getTree());
					RPAREN124=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_event_base2140); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN124);

					// AST REWRITE
					// elements: argumentExpressionList, WRITE
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 295:9: -> ^( WRITE argumentExpressionList )
					{
						// AcslParser.g:295:12: ^( WRITE argumentExpressionList )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_WRITE.nextNode(), root_1);
						adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// AcslParser.g:296:7: REACH LPAREN argumentExpressionList RPAREN
					{
					REACH125=(Token)match(input,REACH,FOLLOW_REACH_in_event_base2164); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_REACH.add(REACH125);

					LPAREN126=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_event_base2166); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN126);

					pushFollow(FOLLOW_argumentExpressionList_in_event_base2168);
					argumentExpressionList127=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList127.getTree());
					RPAREN128=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_event_base2170); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN128);

					// AST REWRITE
					// elements: argumentExpressionList, REACH
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 297:9: -> ^( REACH argumentExpressionList )
					{
						// AcslParser.g:297:12: ^( REACH argumentExpressionList )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_REACH.nextNode(), root_1);
						adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// AcslParser.g:298:7: CALL LPAREN ID ( COMMA argumentExpressionList )? RPAREN
					{
					CALL129=(Token)match(input,CALL,FOLLOW_CALL_in_event_base2194); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_CALL.add(CALL129);

					LPAREN130=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_event_base2196); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN130);

					ID131=(Token)match(input,ID,FOLLOW_ID_in_event_base2198); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID131);

					// AcslParser.g:298:22: ( COMMA argumentExpressionList )?
					int alt31=2;
					int LA31_0 = input.LA(1);
					if ( (LA31_0==COMMA) ) {
						alt31=1;
					}
					switch (alt31) {
						case 1 :
							// AcslParser.g:298:23: COMMA argumentExpressionList
							{
							COMMA132=(Token)match(input,COMMA,FOLLOW_COMMA_in_event_base2201); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_COMMA.add(COMMA132);

							pushFollow(FOLLOW_argumentExpressionList_in_event_base2203);
							argumentExpressionList133=argumentExpressionList();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList133.getTree());
							}
							break;

					}

					RPAREN134=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_event_base2207); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN134);

					// AST REWRITE
					// elements: CALL, ID, argumentExpressionList
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 299:9: -> ^( CALL ID ( argumentExpressionList )? )
					{
						// AcslParser.g:299:12: ^( CALL ID ( argumentExpressionList )? )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_CALL.nextNode(), root_1);
						adaptor.addChild(root_1, stream_ID.nextNode());
						// AcslParser.g:299:22: ( argumentExpressionList )?
						if ( stream_argumentExpressionList.hasNext() ) {
							adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
						}
						stream_argumentExpressionList.reset();

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 5 :
					// AcslParser.g:300:7: NOACT
					{
					NOACT135=(Token)match(input,NOACT,FOLLOW_NOACT_in_event_base2234); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_NOACT.add(NOACT135);

					// AST REWRITE
					// elements: NOACT
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 301:9: -> ^( NOACT )
					{
						// AcslParser.g:301:12: ^( NOACT )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_NOACT.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 6 :
					// AcslParser.g:302:7: ANYACT
					{
					ANYACT136=(Token)match(input,ANYACT,FOLLOW_ANYACT_in_event_base2256); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ANYACT.add(ANYACT136);

					// AST REWRITE
					// elements: ANYACT
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 303:9: -> ^( ANYACT )
					{
						// AcslParser.g:303:12: ^( ANYACT )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ANYACT.nextNode(), root_1);
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 7 :
					// AcslParser.g:304:7: LPAREN event RPAREN
					{
					LPAREN137=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_event_base2278); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN137);

					pushFollow(FOLLOW_event_in_event_base2280);
					event138=event();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_event.add(event138.getTree());
					RPAREN139=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_event_base2282); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN139);

					// AST REWRITE
					// elements: event
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 305:9: -> ^( EVENT_PARENTHESIZED event )
					{
						// AcslParser.g:305:12: ^( EVENT_PARENTHESIZED event )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(EVENT_PARENTHESIZED, "EVENT_PARENTHESIZED"), root_1);
						adaptor.addChild(root_1, stream_event.nextTree());
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
	// $ANTLR end "event_base"


	public static class mpi_collective_block_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "mpi_collective_block"
	// AcslParser.g:309:1: mpi_collective_block : MPI_COLLECTIVE LPAREN ID COMMA kind= mpi_collective_kind RPAREN COLON c= partial_contract_block -> ^( MPI_COLLECTIVE ID $kind $c) ;
	public final AcslParser.mpi_collective_block_return mpi_collective_block() throws RecognitionException {
		AcslParser.mpi_collective_block_return retval = new AcslParser.mpi_collective_block_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token MPI_COLLECTIVE140=null;
		Token LPAREN141=null;
		Token ID142=null;
		Token COMMA143=null;
		Token RPAREN144=null;
		Token COLON145=null;
		ParserRuleReturnScope kind =null;
		ParserRuleReturnScope c =null;

		Object MPI_COLLECTIVE140_tree=null;
		Object LPAREN141_tree=null;
		Object ID142_tree=null;
		Object COMMA143_tree=null;
		Object RPAREN144_tree=null;
		Object COLON145_tree=null;
		RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_MPI_COLLECTIVE=new RewriteRuleTokenStream(adaptor,"token MPI_COLLECTIVE");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_partial_contract_block=new RewriteRuleSubtreeStream(adaptor,"rule partial_contract_block");
		RewriteRuleSubtreeStream stream_mpi_collective_kind=new RewriteRuleSubtreeStream(adaptor,"rule mpi_collective_kind");

		try {
			// AcslParser.g:310:5: ( MPI_COLLECTIVE LPAREN ID COMMA kind= mpi_collective_kind RPAREN COLON c= partial_contract_block -> ^( MPI_COLLECTIVE ID $kind $c) )
			// AcslParser.g:310:7: MPI_COLLECTIVE LPAREN ID COMMA kind= mpi_collective_kind RPAREN COLON c= partial_contract_block
			{
			MPI_COLLECTIVE140=(Token)match(input,MPI_COLLECTIVE,FOLLOW_MPI_COLLECTIVE_in_mpi_collective_block2317); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_MPI_COLLECTIVE.add(MPI_COLLECTIVE140);

			LPAREN141=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_mpi_collective_block2319); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN141);

			ID142=(Token)match(input,ID,FOLLOW_ID_in_mpi_collective_block2321); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID142);

			COMMA143=(Token)match(input,COMMA,FOLLOW_COMMA_in_mpi_collective_block2323); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_COMMA.add(COMMA143);

			pushFollow(FOLLOW_mpi_collective_kind_in_mpi_collective_block2327);
			kind=mpi_collective_kind();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_mpi_collective_kind.add(kind.getTree());
			RPAREN144=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_mpi_collective_block2330); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN144);

			COLON145=(Token)match(input,COLON,FOLLOW_COLON_in_mpi_collective_block2332); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_COLON.add(COLON145);

			pushFollow(FOLLOW_partial_contract_block_in_mpi_collective_block2342);
			c=partial_contract_block();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_partial_contract_block.add(c.getTree());
			// AST REWRITE
			// elements: c, ID, MPI_COLLECTIVE, kind
			// token labels: 
			// rule labels: retval, c, kind
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_c=new RewriteRuleSubtreeStream(adaptor,"rule c",c!=null?c.getTree():null);
			RewriteRuleSubtreeStream stream_kind=new RewriteRuleSubtreeStream(adaptor,"rule kind",kind!=null?kind.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 311:32: -> ^( MPI_COLLECTIVE ID $kind $c)
			{
				// AcslParser.g:311:35: ^( MPI_COLLECTIVE ID $kind $c)
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_MPI_COLLECTIVE.nextNode(), root_1);
				adaptor.addChild(root_1, stream_ID.nextNode());
				adaptor.addChild(root_1, stream_kind.nextTree());
				adaptor.addChild(root_1, stream_c.nextTree());
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
	// $ANTLR end "mpi_collective_block"


	public static class named_behavior_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "named_behavior"
	// AcslParser.g:317:1: named_behavior : BEHAVIOR ID COLON behavior_body -> ^( BEHAVIOR ID behavior_body ) ;
	public final AcslParser.named_behavior_return named_behavior() throws RecognitionException {
		AcslParser.named_behavior_return retval = new AcslParser.named_behavior_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token BEHAVIOR146=null;
		Token ID147=null;
		Token COLON148=null;
		ParserRuleReturnScope behavior_body149 =null;

		Object BEHAVIOR146_tree=null;
		Object ID147_tree=null;
		Object COLON148_tree=null;
		RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_BEHAVIOR=new RewriteRuleTokenStream(adaptor,"token BEHAVIOR");
		RewriteRuleSubtreeStream stream_behavior_body=new RewriteRuleSubtreeStream(adaptor,"rule behavior_body");

		try {
			// AcslParser.g:318:5: ( BEHAVIOR ID COLON behavior_body -> ^( BEHAVIOR ID behavior_body ) )
			// AcslParser.g:318:7: BEHAVIOR ID COLON behavior_body
			{
			BEHAVIOR146=(Token)match(input,BEHAVIOR,FOLLOW_BEHAVIOR_in_named_behavior2377); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_BEHAVIOR.add(BEHAVIOR146);

			ID147=(Token)match(input,ID,FOLLOW_ID_in_named_behavior2379); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ID.add(ID147);

			COLON148=(Token)match(input,COLON,FOLLOW_COLON_in_named_behavior2381); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_COLON.add(COLON148);

			pushFollow(FOLLOW_behavior_body_in_named_behavior2383);
			behavior_body149=behavior_body();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_behavior_body.add(behavior_body149.getTree());
			// AST REWRITE
			// elements: ID, behavior_body, BEHAVIOR
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 318:39: -> ^( BEHAVIOR ID behavior_body )
			{
				// AcslParser.g:318:41: ^( BEHAVIOR ID behavior_body )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_BEHAVIOR.nextNode(), root_1);
				adaptor.addChild(root_1, stream_ID.nextNode());
				adaptor.addChild(root_1, stream_behavior_body.nextTree());
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
	// $ANTLR end "named_behavior"


	public static class behavior_body_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "behavior_body"
	// AcslParser.g:321:1: behavior_body : (b+= behavior_clause SEMICOL )+ -> ^( BEHAVIOR_BODY ( $b)+ ) ;
	public final AcslParser.behavior_body_return behavior_body() throws RecognitionException {
		AcslParser.behavior_body_return retval = new AcslParser.behavior_body_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SEMICOL150=null;
		List<Object> list_b=null;
		RuleReturnScope b = null;
		Object SEMICOL150_tree=null;
		RewriteRuleTokenStream stream_SEMICOL=new RewriteRuleTokenStream(adaptor,"token SEMICOL");
		RewriteRuleSubtreeStream stream_behavior_clause=new RewriteRuleSubtreeStream(adaptor,"rule behavior_clause");

		try {
			// AcslParser.g:322:5: ( (b+= behavior_clause SEMICOL )+ -> ^( BEHAVIOR_BODY ( $b)+ ) )
			// AcslParser.g:322:7: (b+= behavior_clause SEMICOL )+
			{
			// AcslParser.g:322:7: (b+= behavior_clause SEMICOL )+
			int cnt33=0;
			loop33:
			while (true) {
				int alt33=2;
				int LA33_0 = input.LA(1);
				if ( (LA33_0==ALLOC||(LA33_0 >= ASSIGNS && LA33_0 <= ASSUMES)||LA33_0==DEPENDS||LA33_0==ENSURES||LA33_0==FREES||LA33_0==GUARDS||LA33_0==READS||LA33_0==REQUIRES) ) {
					alt33=1;
				}

				switch (alt33) {
				case 1 :
					// AcslParser.g:322:8: b+= behavior_clause SEMICOL
					{
					pushFollow(FOLLOW_behavior_clause_in_behavior_body2412);
					b=behavior_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_behavior_clause.add(b.getTree());
					if (list_b==null) list_b=new ArrayList<Object>();
					list_b.add(b.getTree());
					SEMICOL150=(Token)match(input,SEMICOL,FOLLOW_SEMICOL_in_behavior_body2414); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SEMICOL.add(SEMICOL150);

					}
					break;

				default :
					if ( cnt33 >= 1 ) break loop33;
					if (state.backtracking>0) {state.failed=true; return retval;}
					EarlyExitException eee = new EarlyExitException(33, input);
					throw eee;
				}
				cnt33++;
			}

			// AST REWRITE
			// elements: b
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: b
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
			RewriteRuleSubtreeStream stream_b=new RewriteRuleSubtreeStream(adaptor,"token b",list_b);
			root_0 = (Object)adaptor.nil();
			// 322:37: -> ^( BEHAVIOR_BODY ( $b)+ )
			{
				// AcslParser.g:322:40: ^( BEHAVIOR_BODY ( $b)+ )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(BEHAVIOR_BODY, "BEHAVIOR_BODY"), root_1);
				if ( !(stream_b.hasNext()) ) {
					throw new RewriteEarlyExitException();
				}
				while ( stream_b.hasNext() ) {
					adaptor.addChild(root_1, stream_b.nextTree());
				}
				stream_b.reset();

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
	// $ANTLR end "behavior_body"


	public static class behavior_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "behavior_clause"
	// AcslParser.g:325:1: behavior_clause : ( assumes_clause | requires_clause | simple_clause );
	public final AcslParser.behavior_clause_return behavior_clause() throws RecognitionException {
		AcslParser.behavior_clause_return retval = new AcslParser.behavior_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope assumes_clause151 =null;
		ParserRuleReturnScope requires_clause152 =null;
		ParserRuleReturnScope simple_clause153 =null;


		try {
			// AcslParser.g:326:5: ( assumes_clause | requires_clause | simple_clause )
			int alt34=3;
			switch ( input.LA(1) ) {
			case ASSUMES:
				{
				alt34=1;
				}
				break;
			case REQUIRES:
				{
				alt34=2;
				}
				break;
			case ALLOC:
			case ASSIGNS:
			case DEPENDS:
			case ENSURES:
			case FREES:
			case GUARDS:
			case READS:
				{
				alt34=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 34, 0, input);
				throw nvae;
			}
			switch (alt34) {
				case 1 :
					// AcslParser.g:326:7: assumes_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_assumes_clause_in_behavior_clause2443);
					assumes_clause151=assumes_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, assumes_clause151.getTree());

					}
					break;
				case 2 :
					// AcslParser.g:327:7: requires_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_requires_clause_in_behavior_clause2452);
					requires_clause152=requires_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, requires_clause152.getTree());

					}
					break;
				case 3 :
					// AcslParser.g:328:7: simple_clause
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_simple_clause_in_behavior_clause2460);
					simple_clause153=simple_clause();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, simple_clause153.getTree());

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
	// $ANTLR end "behavior_clause"


	public static class assumes_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "assumes_clause"
	// AcslParser.g:331:1: assumes_clause : ASSUMES term -> ^( ASSUMES term ) ;
	public final AcslParser.assumes_clause_return assumes_clause() throws RecognitionException {
		AcslParser.assumes_clause_return retval = new AcslParser.assumes_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ASSUMES154=null;
		ParserRuleReturnScope term155 =null;

		Object ASSUMES154_tree=null;
		RewriteRuleTokenStream stream_ASSUMES=new RewriteRuleTokenStream(adaptor,"token ASSUMES");
		RewriteRuleSubtreeStream stream_term=new RewriteRuleSubtreeStream(adaptor,"rule term");

		try {
			// AcslParser.g:332:5: ( ASSUMES term -> ^( ASSUMES term ) )
			// AcslParser.g:332:7: ASSUMES term
			{
			ASSUMES154=(Token)match(input,ASSUMES,FOLLOW_ASSUMES_in_assumes_clause2477); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_ASSUMES.add(ASSUMES154);

			pushFollow(FOLLOW_term_in_assumes_clause2479);
			term155=term();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_term.add(term155.getTree());
			// AST REWRITE
			// elements: ASSUMES, term
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 332:20: -> ^( ASSUMES term )
			{
				// AcslParser.g:332:22: ^( ASSUMES term )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_ASSUMES.nextNode(), root_1);
				adaptor.addChild(root_1, stream_term.nextTree());
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
	// $ANTLR end "assumes_clause"


	public static class completeness_clause_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "completeness_clause"
	// AcslParser.g:335:1: completeness_clause : ( COMPLETE BEHAVIORS id_list -> ^( BEHAVIOR_COMPLETE id_list ) | DISJOINT BEHAVIORS id_list -> ^( BEHAVIOR_DISJOINT id_list ) );
	public final AcslParser.completeness_clause_return completeness_clause() throws RecognitionException {
		AcslParser.completeness_clause_return retval = new AcslParser.completeness_clause_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMPLETE156=null;
		Token BEHAVIORS157=null;
		Token DISJOINT159=null;
		Token BEHAVIORS160=null;
		ParserRuleReturnScope id_list158 =null;
		ParserRuleReturnScope id_list161 =null;

		Object COMPLETE156_tree=null;
		Object BEHAVIORS157_tree=null;
		Object DISJOINT159_tree=null;
		Object BEHAVIORS160_tree=null;
		RewriteRuleTokenStream stream_DISJOINT=new RewriteRuleTokenStream(adaptor,"token DISJOINT");
		RewriteRuleTokenStream stream_COMPLETE=new RewriteRuleTokenStream(adaptor,"token COMPLETE");
		RewriteRuleTokenStream stream_BEHAVIORS=new RewriteRuleTokenStream(adaptor,"token BEHAVIORS");
		RewriteRuleSubtreeStream stream_id_list=new RewriteRuleSubtreeStream(adaptor,"rule id_list");

		try {
			// AcslParser.g:336:5: ( COMPLETE BEHAVIORS id_list -> ^( BEHAVIOR_COMPLETE id_list ) | DISJOINT BEHAVIORS id_list -> ^( BEHAVIOR_DISJOINT id_list ) )
			int alt35=2;
			int LA35_0 = input.LA(1);
			if ( (LA35_0==COMPLETE) ) {
				alt35=1;
			}
			else if ( (LA35_0==DISJOINT) ) {
				alt35=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 35, 0, input);
				throw nvae;
			}

			switch (alt35) {
				case 1 :
					// AcslParser.g:336:7: COMPLETE BEHAVIORS id_list
					{
					COMPLETE156=(Token)match(input,COMPLETE,FOLLOW_COMPLETE_in_completeness_clause2503); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMPLETE.add(COMPLETE156);

					BEHAVIORS157=(Token)match(input,BEHAVIORS,FOLLOW_BEHAVIORS_in_completeness_clause2505); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BEHAVIORS.add(BEHAVIORS157);

					pushFollow(FOLLOW_id_list_in_completeness_clause2507);
					id_list158=id_list();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_id_list.add(id_list158.getTree());
					// AST REWRITE
					// elements: id_list
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 336:34: -> ^( BEHAVIOR_COMPLETE id_list )
					{
						// AcslParser.g:336:36: ^( BEHAVIOR_COMPLETE id_list )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(BEHAVIOR_COMPLETE, "BEHAVIOR_COMPLETE"), root_1);
						adaptor.addChild(root_1, stream_id_list.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:337:7: DISJOINT BEHAVIORS id_list
					{
					DISJOINT159=(Token)match(input,DISJOINT,FOLLOW_DISJOINT_in_completeness_clause2522); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DISJOINT.add(DISJOINT159);

					BEHAVIORS160=(Token)match(input,BEHAVIORS,FOLLOW_BEHAVIORS_in_completeness_clause2524); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BEHAVIORS.add(BEHAVIORS160);

					pushFollow(FOLLOW_id_list_in_completeness_clause2526);
					id_list161=id_list();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_id_list.add(id_list161.getTree());
					// AST REWRITE
					// elements: id_list
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 337:34: -> ^( BEHAVIOR_DISJOINT id_list )
					{
						// AcslParser.g:337:36: ^( BEHAVIOR_DISJOINT id_list )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(BEHAVIOR_DISJOINT, "BEHAVIOR_DISJOINT"), root_1);
						adaptor.addChild(root_1, stream_id_list.nextTree());
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
	// $ANTLR end "completeness_clause"


	public static class id_list_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "id_list"
	// AcslParser.g:340:1: id_list : (| ID ( COMMA ID )* -> ^( ID_LIST ( ID )+ ) );
	public final AcslParser.id_list_return id_list() throws RecognitionException {
		AcslParser.id_list_return retval = new AcslParser.id_list_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ID162=null;
		Token COMMA163=null;
		Token ID164=null;

		Object ID162_tree=null;
		Object COMMA163_tree=null;
		Object ID164_tree=null;
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");

		try {
			// AcslParser.g:341:5: (| ID ( COMMA ID )* -> ^( ID_LIST ( ID )+ ) )
			int alt37=2;
			int LA37_0 = input.LA(1);
			if ( (LA37_0==EOF||LA37_0==COLON||LA37_0==SEMICOL) ) {
				alt37=1;
			}
			else if ( (LA37_0==ID) ) {
				alt37=2;
			}

			else {
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 37, 0, input);
				throw nvae;
			}

			switch (alt37) {
				case 1 :
					// AcslParser.g:342:5: 
					{
					root_0 = (Object)adaptor.nil();


					}
					break;
				case 2 :
					// AcslParser.g:342:7: ID ( COMMA ID )*
					{
					ID162=(Token)match(input,ID,FOLLOW_ID_in_id_list2556); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID162);

					// AcslParser.g:342:10: ( COMMA ID )*
					loop36:
					while (true) {
						int alt36=2;
						int LA36_0 = input.LA(1);
						if ( (LA36_0==COMMA) ) {
							alt36=1;
						}

						switch (alt36) {
						case 1 :
							// AcslParser.g:342:11: COMMA ID
							{
							COMMA163=(Token)match(input,COMMA,FOLLOW_COMMA_in_id_list2559); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_COMMA.add(COMMA163);

							ID164=(Token)match(input,ID,FOLLOW_ID_in_id_list2561); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_ID.add(ID164);

							}
							break;

						default :
							break loop36;
						}
					}

					// AST REWRITE
					// elements: ID
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 342:22: -> ^( ID_LIST ( ID )+ )
					{
						// AcslParser.g:342:24: ^( ID_LIST ( ID )+ )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(ID_LIST, "ID_LIST"), root_1);
						if ( !(stream_ID.hasNext()) ) {
							throw new RewriteEarlyExitException();
						}
						while ( stream_ID.hasNext() ) {
							adaptor.addChild(root_1, stream_ID.nextNode());
						}
						stream_ID.reset();

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
	// $ANTLR end "id_list"


	public static class primaryExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "primaryExpression"
	// AcslParser.g:346:1: primaryExpression : ( constant | ID | STRING_LITERAL | LCURLY term BAR binders ( SEMICOL term )? RCURLY -> ^( SET_BINDERS term binders ( term )? ) | LCURLY term RCURLY -> ^( SET_SIMPLE term ) | LPAREN term RPAREN -> ^( TERM_PARENTHESIZED term ) | mpi_expression -> ^( MPI_EXPRESSION mpi_expression ) | REMOTE_ACCESS LPAREN a= ID COMMA b= primaryExpression RPAREN -> ^( REMOTE_ACCESS $a $b) );
	public final AcslParser.primaryExpression_return primaryExpression() throws RecognitionException {
		AcslParser.primaryExpression_return retval = new AcslParser.primaryExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token a=null;
		Token ID166=null;
		Token STRING_LITERAL167=null;
		Token LCURLY168=null;
		Token BAR170=null;
		Token SEMICOL172=null;
		Token RCURLY174=null;
		Token LCURLY175=null;
		Token RCURLY177=null;
		Token LPAREN178=null;
		Token RPAREN180=null;
		Token REMOTE_ACCESS182=null;
		Token LPAREN183=null;
		Token COMMA184=null;
		Token RPAREN185=null;
		ParserRuleReturnScope b =null;
		ParserRuleReturnScope constant165 =null;
		ParserRuleReturnScope term169 =null;
		ParserRuleReturnScope binders171 =null;
		ParserRuleReturnScope term173 =null;
		ParserRuleReturnScope term176 =null;
		ParserRuleReturnScope term179 =null;
		ParserRuleReturnScope mpi_expression181 =null;

		Object a_tree=null;
		Object ID166_tree=null;
		Object STRING_LITERAL167_tree=null;
		Object LCURLY168_tree=null;
		Object BAR170_tree=null;
		Object SEMICOL172_tree=null;
		Object RCURLY174_tree=null;
		Object LCURLY175_tree=null;
		Object RCURLY177_tree=null;
		Object LPAREN178_tree=null;
		Object RPAREN180_tree=null;
		Object REMOTE_ACCESS182_tree=null;
		Object LPAREN183_tree=null;
		Object COMMA184_tree=null;
		Object RPAREN185_tree=null;
		RewriteRuleTokenStream stream_SEMICOL=new RewriteRuleTokenStream(adaptor,"token SEMICOL");
		RewriteRuleTokenStream stream_REMOTE_ACCESS=new RewriteRuleTokenStream(adaptor,"token REMOTE_ACCESS");
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_LCURLY=new RewriteRuleTokenStream(adaptor,"token LCURLY");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_BAR=new RewriteRuleTokenStream(adaptor,"token BAR");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleTokenStream stream_RCURLY=new RewriteRuleTokenStream(adaptor,"token RCURLY");
		RewriteRuleSubtreeStream stream_binders=new RewriteRuleSubtreeStream(adaptor,"rule binders");
		RewriteRuleSubtreeStream stream_term=new RewriteRuleSubtreeStream(adaptor,"rule term");
		RewriteRuleSubtreeStream stream_mpi_expression=new RewriteRuleSubtreeStream(adaptor,"rule mpi_expression");
		RewriteRuleSubtreeStream stream_primaryExpression=new RewriteRuleSubtreeStream(adaptor,"rule primaryExpression");

		try {
			// AcslParser.g:347:2: ( constant | ID | STRING_LITERAL | LCURLY term BAR binders ( SEMICOL term )? RCURLY -> ^( SET_BINDERS term binders ( term )? ) | LCURLY term RCURLY -> ^( SET_SIMPLE term ) | LPAREN term RPAREN -> ^( TERM_PARENTHESIZED term ) | mpi_expression -> ^( MPI_EXPRESSION mpi_expression ) | REMOTE_ACCESS LPAREN a= ID COMMA b= primaryExpression RPAREN -> ^( REMOTE_ACCESS $a $b) )
			int alt39=8;
			switch ( input.LA(1) ) {
			case ELLIPSIS:
			case FALSE:
			case FLOATING_CONSTANT:
			case INTEGER_CONSTANT:
			case MPI_COMM_RANK:
			case MPI_COMM_SIZE:
			case NOTHING:
			case NULL:
			case RESULT:
			case SELF:
			case TRUE:
			case CHARACTER_CONSTANT:
				{
				alt39=1;
				}
				break;
			case ID:
				{
				alt39=2;
				}
				break;
			case STRING_LITERAL:
				{
				alt39=3;
				}
				break;
			case LCURLY:
				{
				int LA39_14 = input.LA(2);
				if ( (synpred70_AcslParser()) ) {
					alt39=4;
				}
				else if ( (synpred71_AcslParser()) ) {
					alt39=5;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 39, 14, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case LPAREN:
				{
				alt39=6;
				}
				break;
			case MPI_AGREE:
			case MPI_EMPTY_IN:
			case MPI_EMPTY_OUT:
			case MPI_EQUALS:
			case MPI_REGION:
				{
				alt39=7;
				}
				break;
			case REMOTE_ACCESS:
				{
				alt39=8;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 39, 0, input);
				throw nvae;
			}
			switch (alt39) {
				case 1 :
					// AcslParser.g:347:4: constant
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_constant_in_primaryExpression2587);
					constant165=constant();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, constant165.getTree());

					}
					break;
				case 2 :
					// AcslParser.g:348:7: ID
					{
					root_0 = (Object)adaptor.nil();


					ID166=(Token)match(input,ID,FOLLOW_ID_in_primaryExpression2595); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ID166_tree = (Object)adaptor.create(ID166);
					adaptor.addChild(root_0, ID166_tree);
					}

					}
					break;
				case 3 :
					// AcslParser.g:349:4: STRING_LITERAL
					{
					root_0 = (Object)adaptor.nil();


					STRING_LITERAL167=(Token)match(input,STRING_LITERAL,FOLLOW_STRING_LITERAL_in_primaryExpression2600); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					STRING_LITERAL167_tree = (Object)adaptor.create(STRING_LITERAL167);
					adaptor.addChild(root_0, STRING_LITERAL167_tree);
					}

					}
					break;
				case 4 :
					// AcslParser.g:350:7: LCURLY term BAR binders ( SEMICOL term )? RCURLY
					{
					LCURLY168=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_primaryExpression2608); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY168);

					pushFollow(FOLLOW_term_in_primaryExpression2610);
					term169=term();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_term.add(term169.getTree());
					BAR170=(Token)match(input,BAR,FOLLOW_BAR_in_primaryExpression2612); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BAR.add(BAR170);

					pushFollow(FOLLOW_binders_in_primaryExpression2614);
					binders171=binders();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_binders.add(binders171.getTree());
					// AcslParser.g:350:31: ( SEMICOL term )?
					int alt38=2;
					int LA38_0 = input.LA(1);
					if ( (LA38_0==SEMICOL) ) {
						alt38=1;
					}
					switch (alt38) {
						case 1 :
							// AcslParser.g:350:32: SEMICOL term
							{
							SEMICOL172=(Token)match(input,SEMICOL,FOLLOW_SEMICOL_in_primaryExpression2617); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_SEMICOL.add(SEMICOL172);

							pushFollow(FOLLOW_term_in_primaryExpression2619);
							term173=term();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_term.add(term173.getTree());
							}
							break;

					}

					RCURLY174=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_primaryExpression2623); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY174);

					// AST REWRITE
					// elements: term, term, binders
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 351:9: -> ^( SET_BINDERS term binders ( term )? )
					{
						// AcslParser.g:351:11: ^( SET_BINDERS term binders ( term )? )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(SET_BINDERS, "SET_BINDERS"), root_1);
						adaptor.addChild(root_1, stream_term.nextTree());
						adaptor.addChild(root_1, stream_binders.nextTree());
						// AcslParser.g:351:38: ( term )?
						if ( stream_term.hasNext() ) {
							adaptor.addChild(root_1, stream_term.nextTree());
						}
						stream_term.reset();

						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 5 :
					// AcslParser.g:352:7: LCURLY term RCURLY
					{
					LCURLY175=(Token)match(input,LCURLY,FOLLOW_LCURLY_in_primaryExpression2651); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LCURLY.add(LCURLY175);

					pushFollow(FOLLOW_term_in_primaryExpression2653);
					term176=term();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_term.add(term176.getTree());
					RCURLY177=(Token)match(input,RCURLY,FOLLOW_RCURLY_in_primaryExpression2655); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RCURLY.add(RCURLY177);

					// AST REWRITE
					// elements: term
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 353:9: -> ^( SET_SIMPLE term )
					{
						// AcslParser.g:353:11: ^( SET_SIMPLE term )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(SET_SIMPLE, "SET_SIMPLE"), root_1);
						adaptor.addChild(root_1, stream_term.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 6 :
					// AcslParser.g:354:4: LPAREN term RPAREN
					{
					LPAREN178=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_primaryExpression2675); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN178);

					pushFollow(FOLLOW_term_in_primaryExpression2677);
					term179=term();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_term.add(term179.getTree());
					RPAREN180=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_primaryExpression2679); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN180);

					// AST REWRITE
					// elements: term
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 355:4: -> ^( TERM_PARENTHESIZED term )
					{
						// AcslParser.g:355:7: ^( TERM_PARENTHESIZED term )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(TERM_PARENTHESIZED, "TERM_PARENTHESIZED"), root_1);
						adaptor.addChild(root_1, stream_term.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 7 :
					// AcslParser.g:356:7: mpi_expression
					{
					pushFollow(FOLLOW_mpi_expression_in_primaryExpression2699);
					mpi_expression181=mpi_expression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_mpi_expression.add(mpi_expression181.getTree());
					// AST REWRITE
					// elements: mpi_expression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 356:22: -> ^( MPI_EXPRESSION mpi_expression )
					{
						// AcslParser.g:356:25: ^( MPI_EXPRESSION mpi_expression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(MPI_EXPRESSION, "MPI_EXPRESSION"), root_1);
						adaptor.addChild(root_1, stream_mpi_expression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 8 :
					// AcslParser.g:357:7: REMOTE_ACCESS LPAREN a= ID COMMA b= primaryExpression RPAREN
					{
					REMOTE_ACCESS182=(Token)match(input,REMOTE_ACCESS,FOLLOW_REMOTE_ACCESS_in_primaryExpression2715); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_REMOTE_ACCESS.add(REMOTE_ACCESS182);

					LPAREN183=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_primaryExpression2717); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN183);

					a=(Token)match(input,ID,FOLLOW_ID_in_primaryExpression2721); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(a);

					COMMA184=(Token)match(input,COMMA,FOLLOW_COMMA_in_primaryExpression2723); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA184);

					pushFollow(FOLLOW_primaryExpression_in_primaryExpression2727);
					b=primaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_primaryExpression.add(b.getTree());
					RPAREN185=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_primaryExpression2729); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN185);

					// AST REWRITE
					// elements: a, b, REMOTE_ACCESS
					// token labels: a
					// rule labels: retval, b
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleTokenStream stream_a=new RewriteRuleTokenStream(adaptor,"token a",a);
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_b=new RewriteRuleSubtreeStream(adaptor,"rule b",b!=null?b.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 358:7: -> ^( REMOTE_ACCESS $a $b)
					{
						// AcslParser.g:358:10: ^( REMOTE_ACCESS $a $b)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_REMOTE_ACCESS.nextNode(), root_1);
						adaptor.addChild(root_1, stream_a.nextNode());
						adaptor.addChild(root_1, stream_b.nextTree());
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
	// $ANTLR end "primaryExpression"


	public static class postfixExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "postfixExpression"
	// AcslParser.g:362:1: postfixExpression : ( primaryExpression -> primaryExpression ) (l= LSQUARE term RSQUARE -> ^( OPERATOR INDEX[$l] ^( ARGUMENT_LIST $postfixExpression term ) RSQUARE ) | LPAREN argumentExpressionList RPAREN -> ^( FUNC_CALL $postfixExpression argumentExpressionList ) | DOT ID -> ^( DOT $postfixExpression ID ) | ARROW ID -> ^( ARROW $postfixExpression ID ) )* ;
	public final AcslParser.postfixExpression_return postfixExpression() throws RecognitionException {
		AcslParser.postfixExpression_return retval = new AcslParser.postfixExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token l=null;
		Token RSQUARE188=null;
		Token LPAREN189=null;
		Token RPAREN191=null;
		Token DOT192=null;
		Token ID193=null;
		Token ARROW194=null;
		Token ID195=null;
		ParserRuleReturnScope primaryExpression186 =null;
		ParserRuleReturnScope term187 =null;
		ParserRuleReturnScope argumentExpressionList190 =null;

		Object l_tree=null;
		Object RSQUARE188_tree=null;
		Object LPAREN189_tree=null;
		Object RPAREN191_tree=null;
		Object DOT192_tree=null;
		Object ID193_tree=null;
		Object ARROW194_tree=null;
		Object ID195_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_ARROW=new RewriteRuleTokenStream(adaptor,"token ARROW");
		RewriteRuleTokenStream stream_LSQUARE=new RewriteRuleTokenStream(adaptor,"token LSQUARE");
		RewriteRuleTokenStream stream_RSQUARE=new RewriteRuleTokenStream(adaptor,"token RSQUARE");
		RewriteRuleTokenStream stream_DOT=new RewriteRuleTokenStream(adaptor,"token DOT");
		RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_term=new RewriteRuleSubtreeStream(adaptor,"rule term");
		RewriteRuleSubtreeStream stream_argumentExpressionList=new RewriteRuleSubtreeStream(adaptor,"rule argumentExpressionList");
		RewriteRuleSubtreeStream stream_primaryExpression=new RewriteRuleSubtreeStream(adaptor,"rule primaryExpression");

		try {
			// AcslParser.g:363:2: ( ( primaryExpression -> primaryExpression ) (l= LSQUARE term RSQUARE -> ^( OPERATOR INDEX[$l] ^( ARGUMENT_LIST $postfixExpression term ) RSQUARE ) | LPAREN argumentExpressionList RPAREN -> ^( FUNC_CALL $postfixExpression argumentExpressionList ) | DOT ID -> ^( DOT $postfixExpression ID ) | ARROW ID -> ^( ARROW $postfixExpression ID ) )* )
			// AcslParser.g:363:4: ( primaryExpression -> primaryExpression ) (l= LSQUARE term RSQUARE -> ^( OPERATOR INDEX[$l] ^( ARGUMENT_LIST $postfixExpression term ) RSQUARE ) | LPAREN argumentExpressionList RPAREN -> ^( FUNC_CALL $postfixExpression argumentExpressionList ) | DOT ID -> ^( DOT $postfixExpression ID ) | ARROW ID -> ^( ARROW $postfixExpression ID ) )*
			{
			// AcslParser.g:363:4: ( primaryExpression -> primaryExpression )
			// AcslParser.g:363:5: primaryExpression
			{
			pushFollow(FOLLOW_primaryExpression_in_postfixExpression2761);
			primaryExpression186=primaryExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_primaryExpression.add(primaryExpression186.getTree());
			// AST REWRITE
			// elements: primaryExpression
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 363:23: -> primaryExpression
			{
				adaptor.addChild(root_0, stream_primaryExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// AcslParser.g:365:4: (l= LSQUARE term RSQUARE -> ^( OPERATOR INDEX[$l] ^( ARGUMENT_LIST $postfixExpression term ) RSQUARE ) | LPAREN argumentExpressionList RPAREN -> ^( FUNC_CALL $postfixExpression argumentExpressionList ) | DOT ID -> ^( DOT $postfixExpression ID ) | ARROW ID -> ^( ARROW $postfixExpression ID ) )*
			loop40:
			while (true) {
				int alt40=5;
				switch ( input.LA(1) ) {
				case LSQUARE:
					{
					alt40=1;
					}
					break;
				case LPAREN:
					{
					alt40=2;
					}
					break;
				case DOT:
					{
					alt40=3;
					}
					break;
				case ARROW:
					{
					alt40=4;
					}
					break;
				}
				switch (alt40) {
				case 1 :
					// AcslParser.g:365:6: l= LSQUARE term RSQUARE
					{
					l=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_postfixExpression2778); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LSQUARE.add(l);

					pushFollow(FOLLOW_term_in_postfixExpression2780);
					term187=term();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_term.add(term187.getTree());
					RSQUARE188=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_postfixExpression2782); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RSQUARE.add(RSQUARE188);

					// AST REWRITE
					// elements: term, RSQUARE, postfixExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 366:6: -> ^( OPERATOR INDEX[$l] ^( ARGUMENT_LIST $postfixExpression term ) RSQUARE )
					{
						// AcslParser.g:366:9: ^( OPERATOR INDEX[$l] ^( ARGUMENT_LIST $postfixExpression term ) RSQUARE )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, (Object)adaptor.create(INDEX, l));
						// AcslParser.g:368:13: ^( ARGUMENT_LIST $postfixExpression term )
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_retval.nextTree());
						adaptor.addChild(root_2, stream_term.nextTree());
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
					// AcslParser.g:371:6: LPAREN argumentExpressionList RPAREN
					{
					LPAREN189=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_postfixExpression2856); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN189);

					pushFollow(FOLLOW_argumentExpressionList_in_postfixExpression2858);
					argumentExpressionList190=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList190.getTree());
					RPAREN191=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_postfixExpression2860); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN191);

					// AST REWRITE
					// elements: argumentExpressionList, postfixExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 372:6: -> ^( FUNC_CALL $postfixExpression argumentExpressionList )
					{
						// AcslParser.g:372:9: ^( FUNC_CALL $postfixExpression argumentExpressionList )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(FUNC_CALL, "FUNC_CALL"), root_1);
						adaptor.addChild(root_1, stream_retval.nextTree());
						adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// AcslParser.g:374:6: DOT ID
					{
					DOT192=(Token)match(input,DOT,FOLLOW_DOT_in_postfixExpression2891); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOT.add(DOT192);

					ID193=(Token)match(input,ID,FOLLOW_ID_in_postfixExpression2893); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID193);

					// AST REWRITE
					// elements: postfixExpression, ID, DOT
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 375:6: -> ^( DOT $postfixExpression ID )
					{
						// AcslParser.g:375:9: ^( DOT $postfixExpression ID )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_DOT.nextNode(), root_1);
						adaptor.addChild(root_1, stream_retval.nextTree());
						adaptor.addChild(root_1, stream_ID.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// AcslParser.g:376:6: ARROW ID
					{
					ARROW194=(Token)match(input,ARROW,FOLLOW_ARROW_in_postfixExpression2916); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ARROW.add(ARROW194);

					ID195=(Token)match(input,ID,FOLLOW_ID_in_postfixExpression2918); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ID.add(ID195);

					// AST REWRITE
					// elements: ID, ARROW, postfixExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 377:6: -> ^( ARROW $postfixExpression ID )
					{
						// AcslParser.g:377:9: ^( ARROW $postfixExpression ID )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_ARROW.nextNode(), root_1);
						adaptor.addChild(root_1, stream_retval.nextTree());
						adaptor.addChild(root_1, stream_ID.nextNode());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;

				default :
					break loop40;
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


	public static class argumentExpressionList_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "argumentExpressionList"
	// AcslParser.g:382:1: argumentExpressionList : ( -> ^( ARGUMENT_LIST ) | assignmentExpression ( COMMA assignmentExpression )* -> ^( ARGUMENT_LIST ( assignmentExpression )+ ) );
	public final AcslParser.argumentExpressionList_return argumentExpressionList() throws RecognitionException {
		AcslParser.argumentExpressionList_return retval = new AcslParser.argumentExpressionList_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token COMMA197=null;
		ParserRuleReturnScope assignmentExpression196 =null;
		ParserRuleReturnScope assignmentExpression198 =null;

		Object COMMA197_tree=null;
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleSubtreeStream stream_assignmentExpression=new RewriteRuleSubtreeStream(adaptor,"rule assignmentExpression");

		try {
			// AcslParser.g:383:2: ( -> ^( ARGUMENT_LIST ) | assignmentExpression ( COMMA assignmentExpression )* -> ^( ARGUMENT_LIST ( assignmentExpression )+ ) )
			int alt42=2;
			int LA42_0 = input.LA(1);
			if ( (LA42_0==EOF||LA42_0==COMMA||LA42_0==RPAREN||LA42_0==SEMICOL) ) {
				alt42=1;
			}
			else if ( (LA42_0==AMPERSAND||LA42_0==COMP||LA42_0==ELLIPSIS||LA42_0==EXISTS||LA42_0==FALSE||LA42_0==FLOATING_CONSTANT||LA42_0==FORALL||LA42_0==ID||(LA42_0 >= INTEGER_CONSTANT && LA42_0 <= INTER)||LA42_0==LCURLY||LA42_0==LPAREN||LA42_0==MPI_AGREE||(LA42_0 >= MPI_COMM_RANK && LA42_0 <= MPI_REGION)||(LA42_0 >= NOT && LA42_0 <= NULL)||LA42_0==PLUS||LA42_0==REMOTE_ACCESS||LA42_0==RESULT||LA42_0==SELF||(LA42_0 >= SIZEOF && LA42_0 <= STRING_LITERAL)||(LA42_0 >= TRUE && LA42_0 <= UNION)||LA42_0==VALID||LA42_0==CHARACTER_CONSTANT||LA42_0==MINUS) ) {
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
					// AcslParser.g:383:4: 
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
					// 383:4: -> ^( ARGUMENT_LIST )
					{
						// AcslParser.g:383:7: ^( ARGUMENT_LIST )
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
					// AcslParser.g:384:4: assignmentExpression ( COMMA assignmentExpression )*
					{
					pushFollow(FOLLOW_assignmentExpression_in_argumentExpressionList2962);
					assignmentExpression196=assignmentExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression196.getTree());
					// AcslParser.g:384:25: ( COMMA assignmentExpression )*
					loop41:
					while (true) {
						int alt41=2;
						int LA41_0 = input.LA(1);
						if ( (LA41_0==COMMA) ) {
							int LA41_2 = input.LA(2);
							if ( (synpred79_AcslParser()) ) {
								alt41=1;
							}

						}

						switch (alt41) {
						case 1 :
							// AcslParser.g:384:26: COMMA assignmentExpression
							{
							COMMA197=(Token)match(input,COMMA,FOLLOW_COMMA_in_argumentExpressionList2965); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_COMMA.add(COMMA197);

							pushFollow(FOLLOW_assignmentExpression_in_argumentExpressionList2967);
							assignmentExpression198=assignmentExpression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression198.getTree());
							}
							break;

						default :
							break loop41;
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
					// 385:4: -> ^( ARGUMENT_LIST ( assignmentExpression )+ )
					{
						// AcslParser.g:385:7: ^( ARGUMENT_LIST ( assignmentExpression )+ )
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
	// AcslParser.g:389:1: unaryExpression : ( postfixExpression | unary_op castExpression -> ^( OPERATOR unary_op ^( ARGUMENT_LIST castExpression ) ) | ( SIZEOF LPAREN type_expr )=> SIZEOF LPAREN type_expr RPAREN -> ^( SIZEOF_TYPE type_expr ) | SIZEOF unaryExpression -> ^( SIZEOF_EXPR unaryExpression ) | UNION LPAREN argumentExpressionList RPAREN -> ^( UNION argumentExpressionList ) | INTER LPAREN argumentExpressionList RPAREN -> ^( INTER argumentExpressionList ) | VALID LPAREN term RPAREN -> ^( VALID term ) );
	public final AcslParser.unaryExpression_return unaryExpression() throws RecognitionException {
		AcslParser.unaryExpression_return retval = new AcslParser.unaryExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SIZEOF202=null;
		Token LPAREN203=null;
		Token RPAREN205=null;
		Token SIZEOF206=null;
		Token UNION208=null;
		Token LPAREN209=null;
		Token RPAREN211=null;
		Token INTER212=null;
		Token LPAREN213=null;
		Token RPAREN215=null;
		Token VALID216=null;
		Token LPAREN217=null;
		Token RPAREN219=null;
		ParserRuleReturnScope postfixExpression199 =null;
		ParserRuleReturnScope unary_op200 =null;
		ParserRuleReturnScope castExpression201 =null;
		ParserRuleReturnScope type_expr204 =null;
		ParserRuleReturnScope unaryExpression207 =null;
		ParserRuleReturnScope argumentExpressionList210 =null;
		ParserRuleReturnScope argumentExpressionList214 =null;
		ParserRuleReturnScope term218 =null;

		Object SIZEOF202_tree=null;
		Object LPAREN203_tree=null;
		Object RPAREN205_tree=null;
		Object SIZEOF206_tree=null;
		Object UNION208_tree=null;
		Object LPAREN209_tree=null;
		Object RPAREN211_tree=null;
		Object INTER212_tree=null;
		Object LPAREN213_tree=null;
		Object RPAREN215_tree=null;
		Object VALID216_tree=null;
		Object LPAREN217_tree=null;
		Object RPAREN219_tree=null;
		RewriteRuleTokenStream stream_SIZEOF=new RewriteRuleTokenStream(adaptor,"token SIZEOF");
		RewriteRuleTokenStream stream_INTER=new RewriteRuleTokenStream(adaptor,"token INTER");
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_UNION=new RewriteRuleTokenStream(adaptor,"token UNION");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleTokenStream stream_VALID=new RewriteRuleTokenStream(adaptor,"token VALID");
		RewriteRuleSubtreeStream stream_term=new RewriteRuleSubtreeStream(adaptor,"rule term");
		RewriteRuleSubtreeStream stream_unaryExpression=new RewriteRuleSubtreeStream(adaptor,"rule unaryExpression");
		RewriteRuleSubtreeStream stream_castExpression=new RewriteRuleSubtreeStream(adaptor,"rule castExpression");
		RewriteRuleSubtreeStream stream_argumentExpressionList=new RewriteRuleSubtreeStream(adaptor,"rule argumentExpressionList");
		RewriteRuleSubtreeStream stream_type_expr=new RewriteRuleSubtreeStream(adaptor,"rule type_expr");
		RewriteRuleSubtreeStream stream_unary_op=new RewriteRuleSubtreeStream(adaptor,"rule unary_op");

		try {
			// AcslParser.g:390:2: ( postfixExpression | unary_op castExpression -> ^( OPERATOR unary_op ^( ARGUMENT_LIST castExpression ) ) | ( SIZEOF LPAREN type_expr )=> SIZEOF LPAREN type_expr RPAREN -> ^( SIZEOF_TYPE type_expr ) | SIZEOF unaryExpression -> ^( SIZEOF_EXPR unaryExpression ) | UNION LPAREN argumentExpressionList RPAREN -> ^( UNION argumentExpressionList ) | INTER LPAREN argumentExpressionList RPAREN -> ^( INTER argumentExpressionList ) | VALID LPAREN term RPAREN -> ^( VALID term ) )
			int alt43=7;
			switch ( input.LA(1) ) {
			case ELLIPSIS:
			case FALSE:
			case FLOATING_CONSTANT:
			case ID:
			case INTEGER_CONSTANT:
			case LCURLY:
			case LPAREN:
			case MPI_AGREE:
			case MPI_COMM_RANK:
			case MPI_COMM_SIZE:
			case MPI_EMPTY_IN:
			case MPI_EMPTY_OUT:
			case MPI_EQUALS:
			case MPI_REGION:
			case NOTHING:
			case NULL:
			case REMOTE_ACCESS:
			case RESULT:
			case SELF:
			case STRING_LITERAL:
			case TRUE:
			case CHARACTER_CONSTANT:
				{
				alt43=1;
				}
				break;
			case AMPERSAND:
			case COMP:
			case NOT:
			case PLUS:
			case STAR:
			case MINUS:
				{
				alt43=2;
				}
				break;
			case SIZEOF:
				{
				int LA43_3 = input.LA(2);
				if ( (LA43_3==LPAREN) ) {
					int LA43_7 = input.LA(3);
					if ( (LA43_7==BOOLEAN||LA43_7==INTEGER||LA43_7==REAL) && (synpred82_AcslParser())) {
						alt43=3;
					}
					else if ( (LA43_7==ID) ) {
						int LA43_10 = input.LA(4);
						if ( (LA43_10==RPAREN) ) {
							int LA43_12 = input.LA(5);
							if ( (synpred82_AcslParser()) ) {
								alt43=3;
							}
							else if ( (synpred83_AcslParser()) ) {
								alt43=4;
							}

							else {
								if (state.backtracking>0) {state.failed=true; return retval;}
								int nvaeMark = input.mark();
								try {
									for (int nvaeConsume = 0; nvaeConsume < 5 - 1; nvaeConsume++) {
										input.consume();
									}
									NoViableAltException nvae =
										new NoViableAltException("", 43, 12, input);
									throw nvae;
								} finally {
									input.rewind(nvaeMark);
								}
							}

						}
						else if ( (LA43_10==AMPERSAND||(LA43_10 >= ARROW && LA43_10 <= ASSIGN)||LA43_10==BAR||LA43_10==BITXOR||(LA43_10 >= DIVIDE && LA43_10 <= DOTDOT)||LA43_10==EQ||(LA43_10 >= GT && LA43_10 <= GTE)||LA43_10==HASH||LA43_10==IMPLY||LA43_10==LAND||(LA43_10 >= LOR && LA43_10 <= LTE)||LA43_10==MOD||LA43_10==NEQ||LA43_10==PLUS||LA43_10==QUESTION||(LA43_10 >= SHIFTLEFT && LA43_10 <= SHIFTRIGHT)||LA43_10==STAR||LA43_10==SUB) ) {
							alt43=4;
						}

						else {
							if (state.backtracking>0) {state.failed=true; return retval;}
							int nvaeMark = input.mark();
							try {
								for (int nvaeConsume = 0; nvaeConsume < 4 - 1; nvaeConsume++) {
									input.consume();
								}
								NoViableAltException nvae =
									new NoViableAltException("", 43, 10, input);
								throw nvae;
							} finally {
								input.rewind(nvaeMark);
							}
						}

					}
					else if ( (LA43_7==CHAR||LA43_7==DOUBLE||LA43_7==FLOAT||LA43_7==INT||LA43_7==LONG||LA43_7==SHORT||LA43_7==VOID) && (synpred82_AcslParser())) {
						alt43=3;
					}
					else if ( (LA43_7==AMPERSAND||LA43_7==COMP||LA43_7==ELLIPSIS||LA43_7==EXISTS||LA43_7==FALSE||LA43_7==FLOATING_CONSTANT||LA43_7==FORALL||(LA43_7 >= INTEGER_CONSTANT && LA43_7 <= INTER)||LA43_7==LCURLY||LA43_7==LPAREN||LA43_7==MPI_AGREE||(LA43_7 >= MPI_COMM_RANK && LA43_7 <= MPI_REGION)||(LA43_7 >= NOT && LA43_7 <= NULL)||LA43_7==PLUS||LA43_7==REMOTE_ACCESS||LA43_7==RESULT||LA43_7==SELF||(LA43_7 >= SIZEOF && LA43_7 <= STRING_LITERAL)||(LA43_7 >= TRUE && LA43_7 <= UNION)||LA43_7==VALID||LA43_7==CHARACTER_CONSTANT||LA43_7==MINUS) ) {
						alt43=4;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return retval;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 43, 7, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

				}
				else if ( (LA43_3==AMPERSAND||LA43_3==COMP||LA43_3==ELLIPSIS||LA43_3==FALSE||LA43_3==FLOATING_CONSTANT||LA43_3==ID||(LA43_3 >= INTEGER_CONSTANT && LA43_3 <= INTER)||LA43_3==LCURLY||LA43_3==MPI_AGREE||(LA43_3 >= MPI_COMM_RANK && LA43_3 <= MPI_REGION)||(LA43_3 >= NOT && LA43_3 <= NULL)||LA43_3==PLUS||LA43_3==REMOTE_ACCESS||LA43_3==RESULT||LA43_3==SELF||(LA43_3 >= SIZEOF && LA43_3 <= STRING_LITERAL)||(LA43_3 >= TRUE && LA43_3 <= UNION)||LA43_3==VALID||LA43_3==CHARACTER_CONSTANT||LA43_3==MINUS) ) {
					alt43=4;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 43, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case UNION:
				{
				alt43=5;
				}
				break;
			case INTER:
				{
				alt43=6;
				}
				break;
			case VALID:
				{
				alt43=7;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 43, 0, input);
				throw nvae;
			}
			switch (alt43) {
				case 1 :
					// AcslParser.g:390:4: postfixExpression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_postfixExpression_in_unaryExpression2994);
					postfixExpression199=postfixExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, postfixExpression199.getTree());

					}
					break;
				case 2 :
					// AcslParser.g:391:4: unary_op castExpression
					{
					pushFollow(FOLLOW_unary_op_in_unaryExpression2999);
					unary_op200=unary_op();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_unary_op.add(unary_op200.getTree());
					pushFollow(FOLLOW_castExpression_in_unaryExpression3001);
					castExpression201=castExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_castExpression.add(castExpression201.getTree());
					// AST REWRITE
					// elements: unary_op, castExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 392:4: -> ^( OPERATOR unary_op ^( ARGUMENT_LIST castExpression ) )
					{
						// AcslParser.g:392:7: ^( OPERATOR unary_op ^( ARGUMENT_LIST castExpression ) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_unary_op.nextTree());
						// AcslParser.g:392:27: ^( ARGUMENT_LIST castExpression )
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
				case 3 :
					// AcslParser.g:393:4: ( SIZEOF LPAREN type_expr )=> SIZEOF LPAREN type_expr RPAREN
					{
					SIZEOF202=(Token)match(input,SIZEOF,FOLLOW_SIZEOF_in_unaryExpression3032); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SIZEOF.add(SIZEOF202);

					LPAREN203=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_unaryExpression3034); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN203);

					pushFollow(FOLLOW_type_expr_in_unaryExpression3036);
					type_expr204=type_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_type_expr.add(type_expr204.getTree());
					RPAREN205=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_unaryExpression3038); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN205);

					// AST REWRITE
					// elements: type_expr
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 394:4: -> ^( SIZEOF_TYPE type_expr )
					{
						// AcslParser.g:394:7: ^( SIZEOF_TYPE type_expr )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(SIZEOF_TYPE, "SIZEOF_TYPE"), root_1);
						adaptor.addChild(root_1, stream_type_expr.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// AcslParser.g:395:4: SIZEOF unaryExpression
					{
					SIZEOF206=(Token)match(input,SIZEOF,FOLLOW_SIZEOF_in_unaryExpression3054); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SIZEOF.add(SIZEOF206);

					pushFollow(FOLLOW_unaryExpression_in_unaryExpression3056);
					unaryExpression207=unaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_unaryExpression.add(unaryExpression207.getTree());
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
					// 396:4: -> ^( SIZEOF_EXPR unaryExpression )
					{
						// AcslParser.g:396:7: ^( SIZEOF_EXPR unaryExpression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(SIZEOF_EXPR, "SIZEOF_EXPR"), root_1);
						adaptor.addChild(root_1, stream_unaryExpression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 5 :
					// AcslParser.g:398:7: UNION LPAREN argumentExpressionList RPAREN
					{
					UNION208=(Token)match(input,UNION,FOLLOW_UNION_in_unaryExpression3077); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_UNION.add(UNION208);

					LPAREN209=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_unaryExpression3079); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN209);

					pushFollow(FOLLOW_argumentExpressionList_in_unaryExpression3081);
					argumentExpressionList210=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList210.getTree());
					RPAREN211=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_unaryExpression3083); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN211);

					// AST REWRITE
					// elements: argumentExpressionList, UNION
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 399:9: -> ^( UNION argumentExpressionList )
					{
						// AcslParser.g:399:12: ^( UNION argumentExpressionList )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_UNION.nextNode(), root_1);
						adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 6 :
					// AcslParser.g:400:7: INTER LPAREN argumentExpressionList RPAREN
					{
					INTER212=(Token)match(input,INTER,FOLLOW_INTER_in_unaryExpression3107); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_INTER.add(INTER212);

					LPAREN213=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_unaryExpression3109); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN213);

					pushFollow(FOLLOW_argumentExpressionList_in_unaryExpression3111);
					argumentExpressionList214=argumentExpressionList();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_argumentExpressionList.add(argumentExpressionList214.getTree());
					RPAREN215=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_unaryExpression3113); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN215);

					// AST REWRITE
					// elements: argumentExpressionList, INTER
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 401:9: -> ^( INTER argumentExpressionList )
					{
						// AcslParser.g:401:12: ^( INTER argumentExpressionList )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_INTER.nextNode(), root_1);
						adaptor.addChild(root_1, stream_argumentExpressionList.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 7 :
					// AcslParser.g:402:7: VALID LPAREN term RPAREN
					{
					VALID216=(Token)match(input,VALID,FOLLOW_VALID_in_unaryExpression3137); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_VALID.add(VALID216);

					LPAREN217=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_unaryExpression3139); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN217);

					pushFollow(FOLLOW_term_in_unaryExpression3141);
					term218=term();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_term.add(term218.getTree());
					RPAREN219=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_unaryExpression3143); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN219);

					// AST REWRITE
					// elements: term, VALID
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 403:9: -> ^( VALID term )
					{
						// AcslParser.g:403:12: ^( VALID term )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_VALID.nextNode(), root_1);
						adaptor.addChild(root_1, stream_term.nextTree());
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
	// $ANTLR end "unaryExpression"


	public static class castExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "castExpression"
	// AcslParser.g:419:1: castExpression : ( ( LPAREN type_expr RPAREN )=>l= LPAREN type_expr RPAREN castExpression -> ^( CAST type_expr castExpression ) | unaryExpression );
	public final AcslParser.castExpression_return castExpression() throws RecognitionException {
		AcslParser.castExpression_return retval = new AcslParser.castExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token l=null;
		Token RPAREN221=null;
		ParserRuleReturnScope type_expr220 =null;
		ParserRuleReturnScope castExpression222 =null;
		ParserRuleReturnScope unaryExpression223 =null;

		Object l_tree=null;
		Object RPAREN221_tree=null;
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_castExpression=new RewriteRuleSubtreeStream(adaptor,"rule castExpression");
		RewriteRuleSubtreeStream stream_type_expr=new RewriteRuleSubtreeStream(adaptor,"rule type_expr");

		try {
			// AcslParser.g:420:2: ( ( LPAREN type_expr RPAREN )=>l= LPAREN type_expr RPAREN castExpression -> ^( CAST type_expr castExpression ) | unaryExpression )
			int alt44=2;
			int LA44_0 = input.LA(1);
			if ( (LA44_0==LPAREN) ) {
				int LA44_1 = input.LA(2);
				if ( (synpred86_AcslParser()) ) {
					alt44=1;
				}
				else if ( (true) ) {
					alt44=2;
				}

			}
			else if ( (LA44_0==AMPERSAND||LA44_0==COMP||LA44_0==ELLIPSIS||LA44_0==FALSE||LA44_0==FLOATING_CONSTANT||LA44_0==ID||(LA44_0 >= INTEGER_CONSTANT && LA44_0 <= INTER)||LA44_0==LCURLY||LA44_0==MPI_AGREE||(LA44_0 >= MPI_COMM_RANK && LA44_0 <= MPI_REGION)||(LA44_0 >= NOT && LA44_0 <= NULL)||LA44_0==PLUS||LA44_0==REMOTE_ACCESS||LA44_0==RESULT||LA44_0==SELF||(LA44_0 >= SIZEOF && LA44_0 <= STRING_LITERAL)||(LA44_0 >= TRUE && LA44_0 <= UNION)||LA44_0==VALID||LA44_0==CHARACTER_CONSTANT||LA44_0==MINUS) ) {
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
					// AcslParser.g:420:4: ( LPAREN type_expr RPAREN )=>l= LPAREN type_expr RPAREN castExpression
					{
					l=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_castExpression3213); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(l);

					pushFollow(FOLLOW_type_expr_in_castExpression3215);
					type_expr220=type_expr();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_type_expr.add(type_expr220.getTree());
					RPAREN221=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_castExpression3217); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN221);

					pushFollow(FOLLOW_castExpression_in_castExpression3219);
					castExpression222=castExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_castExpression.add(castExpression222.getTree());
					// AST REWRITE
					// elements: type_expr, castExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 421:4: -> ^( CAST type_expr castExpression )
					{
						// AcslParser.g:421:7: ^( CAST type_expr castExpression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(CAST, "CAST"), root_1);
						adaptor.addChild(root_1, stream_type_expr.nextTree());
						adaptor.addChild(root_1, stream_castExpression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:422:4: unaryExpression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_unaryExpression_in_castExpression3237);
					unaryExpression223=unaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, unaryExpression223.getTree());

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
	// $ANTLR end "castExpression"


	public static class remoteExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "remoteExpression"
	// AcslParser.g:425:1: remoteExpression : ( castExpression -> castExpression ) ( HASH y= castExpression -> ^( OPERATOR HASH ^( ARGUMENT_LIST $remoteExpression $y) ) )* ;
	public final AcslParser.remoteExpression_return remoteExpression() throws RecognitionException {
		AcslParser.remoteExpression_return retval = new AcslParser.remoteExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token HASH225=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope castExpression224 =null;

		Object HASH225_tree=null;
		RewriteRuleTokenStream stream_HASH=new RewriteRuleTokenStream(adaptor,"token HASH");
		RewriteRuleSubtreeStream stream_castExpression=new RewriteRuleSubtreeStream(adaptor,"rule castExpression");

		try {
			// AcslParser.g:426:2: ( ( castExpression -> castExpression ) ( HASH y= castExpression -> ^( OPERATOR HASH ^( ARGUMENT_LIST $remoteExpression $y) ) )* )
			// AcslParser.g:426:3: ( castExpression -> castExpression ) ( HASH y= castExpression -> ^( OPERATOR HASH ^( ARGUMENT_LIST $remoteExpression $y) ) )*
			{
			// AcslParser.g:426:3: ( castExpression -> castExpression )
			// AcslParser.g:426:4: castExpression
			{
			pushFollow(FOLLOW_castExpression_in_remoteExpression3248);
			castExpression224=castExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_castExpression.add(castExpression224.getTree());
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
			// 426:19: -> castExpression
			{
				adaptor.addChild(root_0, stream_castExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// AcslParser.g:427:2: ( HASH y= castExpression -> ^( OPERATOR HASH ^( ARGUMENT_LIST $remoteExpression $y) ) )*
			loop45:
			while (true) {
				int alt45=2;
				int LA45_0 = input.LA(1);
				if ( (LA45_0==HASH) ) {
					int LA45_27 = input.LA(2);
					if ( (synpred87_AcslParser()) ) {
						alt45=1;
					}

				}

				switch (alt45) {
				case 1 :
					// AcslParser.g:427:4: HASH y= castExpression
					{
					HASH225=(Token)match(input,HASH,FOLLOW_HASH_in_remoteExpression3258); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_HASH.add(HASH225);

					pushFollow(FOLLOW_castExpression_in_remoteExpression3262);
					y=castExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_castExpression.add(y.getTree());
					// AST REWRITE
					// elements: HASH, remoteExpression, y
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
					// 428:4: -> ^( OPERATOR HASH ^( ARGUMENT_LIST $remoteExpression $y) )
					{
						// AcslParser.g:428:7: ^( OPERATOR HASH ^( ARGUMENT_LIST $remoteExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_HASH.nextNode());
						// AcslParser.g:428:23: ^( ARGUMENT_LIST $remoteExpression $y)
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
					break loop45;
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
	// AcslParser.g:433:1: multiplicativeExpression : ( remoteExpression -> remoteExpression ) ( STAR y= remoteExpression -> ^( OPERATOR STAR ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | DIVIDE y= remoteExpression -> ^( OPERATOR DIVIDE ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | MOD y= remoteExpression -> ^( OPERATOR MOD ^( ARGUMENT_LIST $multiplicativeExpression $y) ) )* ;
	public final AcslParser.multiplicativeExpression_return multiplicativeExpression() throws RecognitionException {
		AcslParser.multiplicativeExpression_return retval = new AcslParser.multiplicativeExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token STAR227=null;
		Token DIVIDE228=null;
		Token MOD229=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope remoteExpression226 =null;

		Object STAR227_tree=null;
		Object DIVIDE228_tree=null;
		Object MOD229_tree=null;
		RewriteRuleTokenStream stream_STAR=new RewriteRuleTokenStream(adaptor,"token STAR");
		RewriteRuleTokenStream stream_MOD=new RewriteRuleTokenStream(adaptor,"token MOD");
		RewriteRuleTokenStream stream_DIVIDE=new RewriteRuleTokenStream(adaptor,"token DIVIDE");
		RewriteRuleSubtreeStream stream_remoteExpression=new RewriteRuleSubtreeStream(adaptor,"rule remoteExpression");

		try {
			// AcslParser.g:434:2: ( ( remoteExpression -> remoteExpression ) ( STAR y= remoteExpression -> ^( OPERATOR STAR ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | DIVIDE y= remoteExpression -> ^( OPERATOR DIVIDE ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | MOD y= remoteExpression -> ^( OPERATOR MOD ^( ARGUMENT_LIST $multiplicativeExpression $y) ) )* )
			// AcslParser.g:434:4: ( remoteExpression -> remoteExpression ) ( STAR y= remoteExpression -> ^( OPERATOR STAR ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | DIVIDE y= remoteExpression -> ^( OPERATOR DIVIDE ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | MOD y= remoteExpression -> ^( OPERATOR MOD ^( ARGUMENT_LIST $multiplicativeExpression $y) ) )*
			{
			// AcslParser.g:434:4: ( remoteExpression -> remoteExpression )
			// AcslParser.g:434:5: remoteExpression
			{
			pushFollow(FOLLOW_remoteExpression_in_multiplicativeExpression3304);
			remoteExpression226=remoteExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_remoteExpression.add(remoteExpression226.getTree());
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
			// 434:22: -> remoteExpression
			{
				adaptor.addChild(root_0, stream_remoteExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// AcslParser.g:435:2: ( STAR y= remoteExpression -> ^( OPERATOR STAR ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | DIVIDE y= remoteExpression -> ^( OPERATOR DIVIDE ^( ARGUMENT_LIST $multiplicativeExpression $y) ) | MOD y= remoteExpression -> ^( OPERATOR MOD ^( ARGUMENT_LIST $multiplicativeExpression $y) ) )*
			loop46:
			while (true) {
				int alt46=4;
				switch ( input.LA(1) ) {
				case STAR:
					{
					alt46=1;
					}
					break;
				case DIVIDE:
					{
					alt46=2;
					}
					break;
				case MOD:
					{
					alt46=3;
					}
					break;
				}
				switch (alt46) {
				case 1 :
					// AcslParser.g:435:4: STAR y= remoteExpression
					{
					STAR227=(Token)match(input,STAR,FOLLOW_STAR_in_multiplicativeExpression3314); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_STAR.add(STAR227);

					pushFollow(FOLLOW_remoteExpression_in_multiplicativeExpression3318);
					y=remoteExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_remoteExpression.add(y.getTree());
					// AST REWRITE
					// elements: y, multiplicativeExpression, STAR
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
					// 436:4: -> ^( OPERATOR STAR ^( ARGUMENT_LIST $multiplicativeExpression $y) )
					{
						// AcslParser.g:436:7: ^( OPERATOR STAR ^( ARGUMENT_LIST $multiplicativeExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_STAR.nextNode());
						// AcslParser.g:436:23: ^( ARGUMENT_LIST $multiplicativeExpression $y)
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
					// AcslParser.g:437:4: DIVIDE y= remoteExpression
					{
					DIVIDE228=(Token)match(input,DIVIDE,FOLLOW_DIVIDE_in_multiplicativeExpression3344); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DIVIDE.add(DIVIDE228);

					pushFollow(FOLLOW_remoteExpression_in_multiplicativeExpression3348);
					y=remoteExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_remoteExpression.add(y.getTree());
					// AST REWRITE
					// elements: y, multiplicativeExpression, DIVIDE
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
					// 438:4: -> ^( OPERATOR DIVIDE ^( ARGUMENT_LIST $multiplicativeExpression $y) )
					{
						// AcslParser.g:438:7: ^( OPERATOR DIVIDE ^( ARGUMENT_LIST $multiplicativeExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_DIVIDE.nextNode());
						// AcslParser.g:438:25: ^( ARGUMENT_LIST $multiplicativeExpression $y)
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
					// AcslParser.g:439:7: MOD y= remoteExpression
					{
					MOD229=(Token)match(input,MOD,FOLLOW_MOD_in_multiplicativeExpression3377); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_MOD.add(MOD229);

					pushFollow(FOLLOW_remoteExpression_in_multiplicativeExpression3381);
					y=remoteExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_remoteExpression.add(y.getTree());
					// AST REWRITE
					// elements: MOD, multiplicativeExpression, y
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
					// 440:4: -> ^( OPERATOR MOD ^( ARGUMENT_LIST $multiplicativeExpression $y) )
					{
						// AcslParser.g:440:7: ^( OPERATOR MOD ^( ARGUMENT_LIST $multiplicativeExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_MOD.nextNode());
						// AcslParser.g:440:22: ^( ARGUMENT_LIST $multiplicativeExpression $y)
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
					break loop46;
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
	// AcslParser.g:445:1: additiveExpression : ( multiplicativeExpression -> multiplicativeExpression ) ( PLUS y= multiplicativeExpression -> ^( OPERATOR PLUS ^( ARGUMENT_LIST $additiveExpression $y) ) | SUB y= multiplicativeExpression -> ^( OPERATOR SUB ^( ARGUMENT_LIST $additiveExpression $y) ) )* ;
	public final AcslParser.additiveExpression_return additiveExpression() throws RecognitionException {
		AcslParser.additiveExpression_return retval = new AcslParser.additiveExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token PLUS231=null;
		Token SUB232=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope multiplicativeExpression230 =null;

		Object PLUS231_tree=null;
		Object SUB232_tree=null;
		RewriteRuleTokenStream stream_PLUS=new RewriteRuleTokenStream(adaptor,"token PLUS");
		RewriteRuleTokenStream stream_SUB=new RewriteRuleTokenStream(adaptor,"token SUB");
		RewriteRuleSubtreeStream stream_multiplicativeExpression=new RewriteRuleSubtreeStream(adaptor,"rule multiplicativeExpression");

		try {
			// AcslParser.g:446:2: ( ( multiplicativeExpression -> multiplicativeExpression ) ( PLUS y= multiplicativeExpression -> ^( OPERATOR PLUS ^( ARGUMENT_LIST $additiveExpression $y) ) | SUB y= multiplicativeExpression -> ^( OPERATOR SUB ^( ARGUMENT_LIST $additiveExpression $y) ) )* )
			// AcslParser.g:446:4: ( multiplicativeExpression -> multiplicativeExpression ) ( PLUS y= multiplicativeExpression -> ^( OPERATOR PLUS ^( ARGUMENT_LIST $additiveExpression $y) ) | SUB y= multiplicativeExpression -> ^( OPERATOR SUB ^( ARGUMENT_LIST $additiveExpression $y) ) )*
			{
			// AcslParser.g:446:4: ( multiplicativeExpression -> multiplicativeExpression )
			// AcslParser.g:446:5: multiplicativeExpression
			{
			pushFollow(FOLLOW_multiplicativeExpression_in_additiveExpression3423);
			multiplicativeExpression230=multiplicativeExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_multiplicativeExpression.add(multiplicativeExpression230.getTree());
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
			// 446:30: -> multiplicativeExpression
			{
				adaptor.addChild(root_0, stream_multiplicativeExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// AcslParser.g:447:9: ( PLUS y= multiplicativeExpression -> ^( OPERATOR PLUS ^( ARGUMENT_LIST $additiveExpression $y) ) | SUB y= multiplicativeExpression -> ^( OPERATOR SUB ^( ARGUMENT_LIST $additiveExpression $y) ) )*
			loop47:
			while (true) {
				int alt47=3;
				int LA47_0 = input.LA(1);
				if ( (LA47_0==PLUS) ) {
					alt47=1;
				}
				else if ( (LA47_0==SUB) ) {
					alt47=2;
				}

				switch (alt47) {
				case 1 :
					// AcslParser.g:447:11: PLUS y= multiplicativeExpression
					{
					PLUS231=(Token)match(input,PLUS,FOLLOW_PLUS_in_additiveExpression3440); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_PLUS.add(PLUS231);

					pushFollow(FOLLOW_multiplicativeExpression_in_additiveExpression3444);
					y=multiplicativeExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_multiplicativeExpression.add(y.getTree());
					// AST REWRITE
					// elements: PLUS, y, additiveExpression
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
					// 448:11: -> ^( OPERATOR PLUS ^( ARGUMENT_LIST $additiveExpression $y) )
					{
						// AcslParser.g:448:14: ^( OPERATOR PLUS ^( ARGUMENT_LIST $additiveExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_PLUS.nextNode());
						// AcslParser.g:448:30: ^( ARGUMENT_LIST $additiveExpression $y)
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
					// AcslParser.g:449:11: SUB y= multiplicativeExpression
					{
					SUB232=(Token)match(input,SUB,FOLLOW_SUB_in_additiveExpression3484); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SUB.add(SUB232);

					pushFollow(FOLLOW_multiplicativeExpression_in_additiveExpression3488);
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
					// 450:11: -> ^( OPERATOR SUB ^( ARGUMENT_LIST $additiveExpression $y) )
					{
						// AcslParser.g:450:14: ^( OPERATOR SUB ^( ARGUMENT_LIST $additiveExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_SUB.nextNode());
						// AcslParser.g:450:29: ^( ARGUMENT_LIST $additiveExpression $y)
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
					break loop47;
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
	// AcslParser.g:456:1: rangeExpression : ( additiveExpression -> additiveExpression ) ( DOTDOT y= additiveExpression ( -> ^( DOTDOT $rangeExpression $y) | HASH z= additiveExpression -> ^( DOTDOT $rangeExpression $y $z) ) )? ;
	public final AcslParser.rangeExpression_return rangeExpression() throws RecognitionException {
		AcslParser.rangeExpression_return retval = new AcslParser.rangeExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token DOTDOT234=null;
		Token HASH235=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope z =null;
		ParserRuleReturnScope additiveExpression233 =null;

		Object DOTDOT234_tree=null;
		Object HASH235_tree=null;
		RewriteRuleTokenStream stream_HASH=new RewriteRuleTokenStream(adaptor,"token HASH");
		RewriteRuleTokenStream stream_DOTDOT=new RewriteRuleTokenStream(adaptor,"token DOTDOT");
		RewriteRuleSubtreeStream stream_additiveExpression=new RewriteRuleSubtreeStream(adaptor,"rule additiveExpression");

		try {
			// AcslParser.g:457:2: ( ( additiveExpression -> additiveExpression ) ( DOTDOT y= additiveExpression ( -> ^( DOTDOT $rangeExpression $y) | HASH z= additiveExpression -> ^( DOTDOT $rangeExpression $y $z) ) )? )
			// AcslParser.g:457:4: ( additiveExpression -> additiveExpression ) ( DOTDOT y= additiveExpression ( -> ^( DOTDOT $rangeExpression $y) | HASH z= additiveExpression -> ^( DOTDOT $rangeExpression $y $z) ) )?
			{
			// AcslParser.g:457:4: ( additiveExpression -> additiveExpression )
			// AcslParser.g:457:5: additiveExpression
			{
			pushFollow(FOLLOW_additiveExpression_in_rangeExpression3542);
			additiveExpression233=additiveExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_additiveExpression.add(additiveExpression233.getTree());
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
			// 457:24: -> additiveExpression
			{
				adaptor.addChild(root_0, stream_additiveExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// AcslParser.g:458:7: ( DOTDOT y= additiveExpression ( -> ^( DOTDOT $rangeExpression $y) | HASH z= additiveExpression -> ^( DOTDOT $rangeExpression $y $z) ) )?
			int alt49=2;
			int LA49_0 = input.LA(1);
			if ( (LA49_0==DOTDOT) ) {
				alt49=1;
			}
			switch (alt49) {
				case 1 :
					// AcslParser.g:458:9: DOTDOT y= additiveExpression ( -> ^( DOTDOT $rangeExpression $y) | HASH z= additiveExpression -> ^( DOTDOT $rangeExpression $y $z) )
					{
					DOTDOT234=(Token)match(input,DOTDOT,FOLLOW_DOTDOT_in_rangeExpression3557); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_DOTDOT.add(DOTDOT234);

					pushFollow(FOLLOW_additiveExpression_in_rangeExpression3561);
					y=additiveExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_additiveExpression.add(y.getTree());
					// AcslParser.g:459:9: ( -> ^( DOTDOT $rangeExpression $y) | HASH z= additiveExpression -> ^( DOTDOT $rangeExpression $y $z) )
					int alt48=2;
					int LA48_0 = input.LA(1);
					if ( (LA48_0==EOF||LA48_0==AMPERSAND||LA48_0==BAR||LA48_0==BITXOR||(LA48_0 >= COLON && LA48_0 <= COMMA)||LA48_0==EQ||LA48_0==FOR||(LA48_0 >= GT && LA48_0 <= GTE)||LA48_0==IMPLY||LA48_0==LAND||LA48_0==LOR||(LA48_0 >= LT && LA48_0 <= LTE)||LA48_0==NEQ||(LA48_0 >= QUESTION && LA48_0 <= RCURLY)||(LA48_0 >= RPAREN && LA48_0 <= RSQUARE)||(LA48_0 >= SEMICOL && LA48_0 <= SHIFTRIGHT)) ) {
						alt48=1;
					}
					else if ( (LA48_0==HASH) ) {
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
							// AcslParser.g:459:11: 
							{
							// AST REWRITE
							// elements: rangeExpression, DOTDOT, y
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
							// 459:11: -> ^( DOTDOT $rangeExpression $y)
							{
								// AcslParser.g:459:14: ^( DOTDOT $rangeExpression $y)
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
							// AcslParser.g:460:11: HASH z= additiveExpression
							{
							HASH235=(Token)match(input,HASH,FOLLOW_HASH_in_rangeExpression3595); if (state.failed) return retval; 
							if ( state.backtracking==0 ) stream_HASH.add(HASH235);

							pushFollow(FOLLOW_additiveExpression_in_rangeExpression3599);
							z=additiveExpression();
							state._fsp--;
							if (state.failed) return retval;
							if ( state.backtracking==0 ) stream_additiveExpression.add(z.getTree());
							// AST REWRITE
							// elements: y, rangeExpression, z, DOTDOT
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
							// 461:11: -> ^( DOTDOT $rangeExpression $y $z)
							{
								// AcslParser.g:461:14: ^( DOTDOT $rangeExpression $y $z)
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
	// AcslParser.g:467:1: shiftExpression : ( rangeExpression -> rangeExpression ) ( SHIFTLEFT y= rangeExpression -> ^( OPERATOR SHIFTLEFT ^( ARGUMENT_LIST $shiftExpression $y) ) | SHIFTRIGHT y= rangeExpression -> ^( OPERATOR SHIFTRIGHT ^( ARGUMENT_LIST $shiftExpression $y) ) )* ;
	public final AcslParser.shiftExpression_return shiftExpression() throws RecognitionException {
		AcslParser.shiftExpression_return retval = new AcslParser.shiftExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SHIFTLEFT237=null;
		Token SHIFTRIGHT238=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope rangeExpression236 =null;

		Object SHIFTLEFT237_tree=null;
		Object SHIFTRIGHT238_tree=null;
		RewriteRuleTokenStream stream_SHIFTLEFT=new RewriteRuleTokenStream(adaptor,"token SHIFTLEFT");
		RewriteRuleTokenStream stream_SHIFTRIGHT=new RewriteRuleTokenStream(adaptor,"token SHIFTRIGHT");
		RewriteRuleSubtreeStream stream_rangeExpression=new RewriteRuleSubtreeStream(adaptor,"rule rangeExpression");

		try {
			// AcslParser.g:468:2: ( ( rangeExpression -> rangeExpression ) ( SHIFTLEFT y= rangeExpression -> ^( OPERATOR SHIFTLEFT ^( ARGUMENT_LIST $shiftExpression $y) ) | SHIFTRIGHT y= rangeExpression -> ^( OPERATOR SHIFTRIGHT ^( ARGUMENT_LIST $shiftExpression $y) ) )* )
			// AcslParser.g:468:4: ( rangeExpression -> rangeExpression ) ( SHIFTLEFT y= rangeExpression -> ^( OPERATOR SHIFTLEFT ^( ARGUMENT_LIST $shiftExpression $y) ) | SHIFTRIGHT y= rangeExpression -> ^( OPERATOR SHIFTRIGHT ^( ARGUMENT_LIST $shiftExpression $y) ) )*
			{
			// AcslParser.g:468:4: ( rangeExpression -> rangeExpression )
			// AcslParser.g:468:5: rangeExpression
			{
			pushFollow(FOLLOW_rangeExpression_in_shiftExpression3660);
			rangeExpression236=rangeExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_rangeExpression.add(rangeExpression236.getTree());
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
			// 468:21: -> rangeExpression
			{
				adaptor.addChild(root_0, stream_rangeExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// AcslParser.g:469:9: ( SHIFTLEFT y= rangeExpression -> ^( OPERATOR SHIFTLEFT ^( ARGUMENT_LIST $shiftExpression $y) ) | SHIFTRIGHT y= rangeExpression -> ^( OPERATOR SHIFTRIGHT ^( ARGUMENT_LIST $shiftExpression $y) ) )*
			loop50:
			while (true) {
				int alt50=3;
				int LA50_0 = input.LA(1);
				if ( (LA50_0==SHIFTLEFT) ) {
					alt50=1;
				}
				else if ( (LA50_0==SHIFTRIGHT) ) {
					alt50=2;
				}

				switch (alt50) {
				case 1 :
					// AcslParser.g:469:11: SHIFTLEFT y= rangeExpression
					{
					SHIFTLEFT237=(Token)match(input,SHIFTLEFT,FOLLOW_SHIFTLEFT_in_shiftExpression3677); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SHIFTLEFT.add(SHIFTLEFT237);

					pushFollow(FOLLOW_rangeExpression_in_shiftExpression3681);
					y=rangeExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_rangeExpression.add(y.getTree());
					// AST REWRITE
					// elements: SHIFTLEFT, y, shiftExpression
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
					// 470:11: -> ^( OPERATOR SHIFTLEFT ^( ARGUMENT_LIST $shiftExpression $y) )
					{
						// AcslParser.g:470:14: ^( OPERATOR SHIFTLEFT ^( ARGUMENT_LIST $shiftExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_SHIFTLEFT.nextNode());
						// AcslParser.g:470:35: ^( ARGUMENT_LIST $shiftExpression $y)
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
					// AcslParser.g:471:11: SHIFTRIGHT y= rangeExpression
					{
					SHIFTRIGHT238=(Token)match(input,SHIFTRIGHT,FOLLOW_SHIFTRIGHT_in_shiftExpression3721); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_SHIFTRIGHT.add(SHIFTRIGHT238);

					pushFollow(FOLLOW_rangeExpression_in_shiftExpression3725);
					y=rangeExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_rangeExpression.add(y.getTree());
					// AST REWRITE
					// elements: SHIFTRIGHT, y, shiftExpression
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
					// 472:11: -> ^( OPERATOR SHIFTRIGHT ^( ARGUMENT_LIST $shiftExpression $y) )
					{
						// AcslParser.g:472:14: ^( OPERATOR SHIFTRIGHT ^( ARGUMENT_LIST $shiftExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_SHIFTRIGHT.nextNode());
						// AcslParser.g:472:36: ^( ARGUMENT_LIST $shiftExpression $y)
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
					break loop50;
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
	// AcslParser.g:477:1: relationalExpression : ( shiftExpression -> shiftExpression ) ( relationalOperator y= shiftExpression -> ^( OPERATOR relationalOperator ^( ARGUMENT_LIST $relationalExpression $y) ) )* ;
	public final AcslParser.relationalExpression_return relationalExpression() throws RecognitionException {
		AcslParser.relationalExpression_return retval = new AcslParser.relationalExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope y =null;
		ParserRuleReturnScope shiftExpression239 =null;
		ParserRuleReturnScope relationalOperator240 =null;

		RewriteRuleSubtreeStream stream_relationalOperator=new RewriteRuleSubtreeStream(adaptor,"rule relationalOperator");
		RewriteRuleSubtreeStream stream_shiftExpression=new RewriteRuleSubtreeStream(adaptor,"rule shiftExpression");

		try {
			// AcslParser.g:478:2: ( ( shiftExpression -> shiftExpression ) ( relationalOperator y= shiftExpression -> ^( OPERATOR relationalOperator ^( ARGUMENT_LIST $relationalExpression $y) ) )* )
			// AcslParser.g:478:4: ( shiftExpression -> shiftExpression ) ( relationalOperator y= shiftExpression -> ^( OPERATOR relationalOperator ^( ARGUMENT_LIST $relationalExpression $y) ) )*
			{
			// AcslParser.g:478:4: ( shiftExpression -> shiftExpression )
			// AcslParser.g:478:6: shiftExpression
			{
			pushFollow(FOLLOW_shiftExpression_in_relationalExpression3779);
			shiftExpression239=shiftExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_shiftExpression.add(shiftExpression239.getTree());
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
			// 478:22: -> shiftExpression
			{
				adaptor.addChild(root_0, stream_shiftExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// AcslParser.g:479:4: ( relationalOperator y= shiftExpression -> ^( OPERATOR relationalOperator ^( ARGUMENT_LIST $relationalExpression $y) ) )*
			loop51:
			while (true) {
				int alt51=2;
				int LA51_0 = input.LA(1);
				if ( ((LA51_0 >= GT && LA51_0 <= GTE)||(LA51_0 >= LT && LA51_0 <= LTE)) ) {
					alt51=1;
				}

				switch (alt51) {
				case 1 :
					// AcslParser.g:479:6: relationalOperator y= shiftExpression
					{
					pushFollow(FOLLOW_relationalOperator_in_relationalExpression3792);
					relationalOperator240=relationalOperator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_relationalOperator.add(relationalOperator240.getTree());
					pushFollow(FOLLOW_shiftExpression_in_relationalExpression3796);
					y=shiftExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_shiftExpression.add(y.getTree());
					// AST REWRITE
					// elements: y, relationalExpression, relationalOperator
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
					// 480:6: -> ^( OPERATOR relationalOperator ^( ARGUMENT_LIST $relationalExpression $y) )
					{
						// AcslParser.g:480:9: ^( OPERATOR relationalOperator ^( ARGUMENT_LIST $relationalExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_relationalOperator.nextTree());
						// AcslParser.g:480:39: ^( ARGUMENT_LIST $relationalExpression $y)
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
					break loop51;
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
	// AcslParser.g:484:1: relationalOperator : ( LT | GT | LTE | GTE );
	public final AcslParser.relationalOperator_return relationalOperator() throws RecognitionException {
		AcslParser.relationalOperator_return retval = new AcslParser.relationalOperator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set241=null;

		Object set241_tree=null;

		try {
			// AcslParser.g:485:2: ( LT | GT | LTE | GTE )
			// AcslParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set241=input.LT(1);
			if ( (input.LA(1) >= GT && input.LA(1) <= GTE)||(input.LA(1) >= LT && input.LA(1) <= LTE) ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set241));
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
	// AcslParser.g:489:1: equalityExpression : ( relationalExpression -> relationalExpression ) ( equalityOperator y= relationalExpression -> ^( OPERATOR equalityOperator ^( ARGUMENT_LIST $equalityExpression $y) ) )* ;
	public final AcslParser.equalityExpression_return equalityExpression() throws RecognitionException {
		AcslParser.equalityExpression_return retval = new AcslParser.equalityExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope y =null;
		ParserRuleReturnScope relationalExpression242 =null;
		ParserRuleReturnScope equalityOperator243 =null;

		RewriteRuleSubtreeStream stream_relationalExpression=new RewriteRuleSubtreeStream(adaptor,"rule relationalExpression");
		RewriteRuleSubtreeStream stream_equalityOperator=new RewriteRuleSubtreeStream(adaptor,"rule equalityOperator");

		try {
			// AcslParser.g:490:2: ( ( relationalExpression -> relationalExpression ) ( equalityOperator y= relationalExpression -> ^( OPERATOR equalityOperator ^( ARGUMENT_LIST $equalityExpression $y) ) )* )
			// AcslParser.g:490:4: ( relationalExpression -> relationalExpression ) ( equalityOperator y= relationalExpression -> ^( OPERATOR equalityOperator ^( ARGUMENT_LIST $equalityExpression $y) ) )*
			{
			// AcslParser.g:490:4: ( relationalExpression -> relationalExpression )
			// AcslParser.g:490:6: relationalExpression
			{
			pushFollow(FOLLOW_relationalExpression_in_equalityExpression3864);
			relationalExpression242=relationalExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_relationalExpression.add(relationalExpression242.getTree());
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
			// 490:27: -> relationalExpression
			{
				adaptor.addChild(root_0, stream_relationalExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// AcslParser.g:491:4: ( equalityOperator y= relationalExpression -> ^( OPERATOR equalityOperator ^( ARGUMENT_LIST $equalityExpression $y) ) )*
			loop52:
			while (true) {
				int alt52=2;
				int LA52_0 = input.LA(1);
				if ( (LA52_0==EQ||LA52_0==NEQ) ) {
					alt52=1;
				}

				switch (alt52) {
				case 1 :
					// AcslParser.g:491:6: equalityOperator y= relationalExpression
					{
					pushFollow(FOLLOW_equalityOperator_in_equalityExpression3877);
					equalityOperator243=equalityOperator();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_equalityOperator.add(equalityOperator243.getTree());
					pushFollow(FOLLOW_relationalExpression_in_equalityExpression3881);
					y=relationalExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_relationalExpression.add(y.getTree());
					// AST REWRITE
					// elements: equalityExpression, y, equalityOperator
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
					// 492:6: -> ^( OPERATOR equalityOperator ^( ARGUMENT_LIST $equalityExpression $y) )
					{
						// AcslParser.g:492:9: ^( OPERATOR equalityOperator ^( ARGUMENT_LIST $equalityExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_equalityOperator.nextTree());
						// AcslParser.g:492:37: ^( ARGUMENT_LIST $equalityExpression $y)
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
					break loop52;
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
	// AcslParser.g:496:1: equalityOperator : ( EQ | NEQ );
	public final AcslParser.equalityOperator_return equalityOperator() throws RecognitionException {
		AcslParser.equalityOperator_return retval = new AcslParser.equalityOperator_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set244=null;

		Object set244_tree=null;

		try {
			// AcslParser.g:497:2: ( EQ | NEQ )
			// AcslParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set244=input.LT(1);
			if ( input.LA(1)==EQ||input.LA(1)==NEQ ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set244));
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
	// AcslParser.g:501:1: andExpression : ( equalityExpression -> equalityExpression ) ( AMPERSAND y= equalityExpression -> ^( OPERATOR AMPERSAND ^( ARGUMENT_LIST $andExpression $y) ) )* ;
	public final AcslParser.andExpression_return andExpression() throws RecognitionException {
		AcslParser.andExpression_return retval = new AcslParser.andExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token AMPERSAND246=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope equalityExpression245 =null;

		Object AMPERSAND246_tree=null;
		RewriteRuleTokenStream stream_AMPERSAND=new RewriteRuleTokenStream(adaptor,"token AMPERSAND");
		RewriteRuleSubtreeStream stream_equalityExpression=new RewriteRuleSubtreeStream(adaptor,"rule equalityExpression");

		try {
			// AcslParser.g:502:2: ( ( equalityExpression -> equalityExpression ) ( AMPERSAND y= equalityExpression -> ^( OPERATOR AMPERSAND ^( ARGUMENT_LIST $andExpression $y) ) )* )
			// AcslParser.g:502:4: ( equalityExpression -> equalityExpression ) ( AMPERSAND y= equalityExpression -> ^( OPERATOR AMPERSAND ^( ARGUMENT_LIST $andExpression $y) ) )*
			{
			// AcslParser.g:502:4: ( equalityExpression -> equalityExpression )
			// AcslParser.g:502:6: equalityExpression
			{
			pushFollow(FOLLOW_equalityExpression_in_andExpression3940);
			equalityExpression245=equalityExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_equalityExpression.add(equalityExpression245.getTree());
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
			// 502:25: -> equalityExpression
			{
				adaptor.addChild(root_0, stream_equalityExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// AcslParser.g:503:4: ( AMPERSAND y= equalityExpression -> ^( OPERATOR AMPERSAND ^( ARGUMENT_LIST $andExpression $y) ) )*
			loop53:
			while (true) {
				int alt53=2;
				int LA53_0 = input.LA(1);
				if ( (LA53_0==AMPERSAND) ) {
					alt53=1;
				}

				switch (alt53) {
				case 1 :
					// AcslParser.g:503:6: AMPERSAND y= equalityExpression
					{
					AMPERSAND246=(Token)match(input,AMPERSAND,FOLLOW_AMPERSAND_in_andExpression3953); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_AMPERSAND.add(AMPERSAND246);

					pushFollow(FOLLOW_equalityExpression_in_andExpression3957);
					y=equalityExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_equalityExpression.add(y.getTree());
					// AST REWRITE
					// elements: AMPERSAND, y, andExpression
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
					// 504:6: -> ^( OPERATOR AMPERSAND ^( ARGUMENT_LIST $andExpression $y) )
					{
						// AcslParser.g:504:9: ^( OPERATOR AMPERSAND ^( ARGUMENT_LIST $andExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_AMPERSAND.nextNode());
						// AcslParser.g:504:30: ^( ARGUMENT_LIST $andExpression $y)
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
					break loop53;
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
	// AcslParser.g:509:1: exclusiveOrExpression : ( andExpression -> andExpression ) ( BITXOR y= andExpression -> ^( OPERATOR BITXOR ^( ARGUMENT_LIST $exclusiveOrExpression $y) ) )* ;
	public final AcslParser.exclusiveOrExpression_return exclusiveOrExpression() throws RecognitionException {
		AcslParser.exclusiveOrExpression_return retval = new AcslParser.exclusiveOrExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token BITXOR248=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope andExpression247 =null;

		Object BITXOR248_tree=null;
		RewriteRuleTokenStream stream_BITXOR=new RewriteRuleTokenStream(adaptor,"token BITXOR");
		RewriteRuleSubtreeStream stream_andExpression=new RewriteRuleSubtreeStream(adaptor,"rule andExpression");

		try {
			// AcslParser.g:510:3: ( ( andExpression -> andExpression ) ( BITXOR y= andExpression -> ^( OPERATOR BITXOR ^( ARGUMENT_LIST $exclusiveOrExpression $y) ) )* )
			// AcslParser.g:510:3: ( andExpression -> andExpression ) ( BITXOR y= andExpression -> ^( OPERATOR BITXOR ^( ARGUMENT_LIST $exclusiveOrExpression $y) ) )*
			{
			// AcslParser.g:510:3: ( andExpression -> andExpression )
			// AcslParser.g:510:5: andExpression
			{
			pushFollow(FOLLOW_andExpression_in_exclusiveOrExpression4000);
			andExpression247=andExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_andExpression.add(andExpression247.getTree());
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
			// 510:19: -> andExpression
			{
				adaptor.addChild(root_0, stream_andExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// AcslParser.g:511:4: ( BITXOR y= andExpression -> ^( OPERATOR BITXOR ^( ARGUMENT_LIST $exclusiveOrExpression $y) ) )*
			loop54:
			while (true) {
				int alt54=2;
				int LA54_0 = input.LA(1);
				if ( (LA54_0==BITXOR) ) {
					alt54=1;
				}

				switch (alt54) {
				case 1 :
					// AcslParser.g:511:6: BITXOR y= andExpression
					{
					BITXOR248=(Token)match(input,BITXOR,FOLLOW_BITXOR_in_exclusiveOrExpression4013); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BITXOR.add(BITXOR248);

					pushFollow(FOLLOW_andExpression_in_exclusiveOrExpression4017);
					y=andExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_andExpression.add(y.getTree());
					// AST REWRITE
					// elements: y, exclusiveOrExpression, BITXOR
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
					// 512:6: -> ^( OPERATOR BITXOR ^( ARGUMENT_LIST $exclusiveOrExpression $y) )
					{
						// AcslParser.g:512:9: ^( OPERATOR BITXOR ^( ARGUMENT_LIST $exclusiveOrExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_BITXOR.nextNode());
						// AcslParser.g:512:27: ^( ARGUMENT_LIST $exclusiveOrExpression $y)
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
					break loop54;
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
	// AcslParser.g:517:1: inclusiveOrExpression : ( exclusiveOrExpression -> exclusiveOrExpression ) ( BAR y= exclusiveOrExpression -> ^( OPERATOR BAR ^( ARGUMENT_LIST $inclusiveOrExpression $y) ) )* ;
	public final AcslParser.inclusiveOrExpression_return inclusiveOrExpression() throws RecognitionException {
		AcslParser.inclusiveOrExpression_return retval = new AcslParser.inclusiveOrExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token BAR250=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope exclusiveOrExpression249 =null;

		Object BAR250_tree=null;
		RewriteRuleTokenStream stream_BAR=new RewriteRuleTokenStream(adaptor,"token BAR");
		RewriteRuleSubtreeStream stream_exclusiveOrExpression=new RewriteRuleSubtreeStream(adaptor,"rule exclusiveOrExpression");

		try {
			// AcslParser.g:518:2: ( ( exclusiveOrExpression -> exclusiveOrExpression ) ( BAR y= exclusiveOrExpression -> ^( OPERATOR BAR ^( ARGUMENT_LIST $inclusiveOrExpression $y) ) )* )
			// AcslParser.g:518:4: ( exclusiveOrExpression -> exclusiveOrExpression ) ( BAR y= exclusiveOrExpression -> ^( OPERATOR BAR ^( ARGUMENT_LIST $inclusiveOrExpression $y) ) )*
			{
			// AcslParser.g:518:4: ( exclusiveOrExpression -> exclusiveOrExpression )
			// AcslParser.g:518:6: exclusiveOrExpression
			{
			pushFollow(FOLLOW_exclusiveOrExpression_in_inclusiveOrExpression4061);
			exclusiveOrExpression249=exclusiveOrExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_exclusiveOrExpression.add(exclusiveOrExpression249.getTree());
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
			// 518:28: -> exclusiveOrExpression
			{
				adaptor.addChild(root_0, stream_exclusiveOrExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// AcslParser.g:519:4: ( BAR y= exclusiveOrExpression -> ^( OPERATOR BAR ^( ARGUMENT_LIST $inclusiveOrExpression $y) ) )*
			loop55:
			while (true) {
				int alt55=2;
				int LA55_0 = input.LA(1);
				if ( (LA55_0==BAR) ) {
					int LA55_10 = input.LA(2);
					if ( (synpred105_AcslParser()) ) {
						alt55=1;
					}

				}

				switch (alt55) {
				case 1 :
					// AcslParser.g:519:6: BAR y= exclusiveOrExpression
					{
					BAR250=(Token)match(input,BAR,FOLLOW_BAR_in_inclusiveOrExpression4074); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_BAR.add(BAR250);

					pushFollow(FOLLOW_exclusiveOrExpression_in_inclusiveOrExpression4078);
					y=exclusiveOrExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_exclusiveOrExpression.add(y.getTree());
					// AST REWRITE
					// elements: BAR, y, inclusiveOrExpression
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
					// 520:6: -> ^( OPERATOR BAR ^( ARGUMENT_LIST $inclusiveOrExpression $y) )
					{
						// AcslParser.g:520:9: ^( OPERATOR BAR ^( ARGUMENT_LIST $inclusiveOrExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_BAR.nextNode());
						// AcslParser.g:520:24: ^( ARGUMENT_LIST $inclusiveOrExpression $y)
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
					break loop55;
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
	// AcslParser.g:525:1: logicalAndExpression : ( inclusiveOrExpression -> inclusiveOrExpression ) ( LAND y= inclusiveOrExpression -> ^( OPERATOR LAND ^( ARGUMENT_LIST $logicalAndExpression $y) ) )* ;
	public final AcslParser.logicalAndExpression_return logicalAndExpression() throws RecognitionException {
		AcslParser.logicalAndExpression_return retval = new AcslParser.logicalAndExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LAND252=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope inclusiveOrExpression251 =null;

		Object LAND252_tree=null;
		RewriteRuleTokenStream stream_LAND=new RewriteRuleTokenStream(adaptor,"token LAND");
		RewriteRuleSubtreeStream stream_inclusiveOrExpression=new RewriteRuleSubtreeStream(adaptor,"rule inclusiveOrExpression");

		try {
			// AcslParser.g:526:2: ( ( inclusiveOrExpression -> inclusiveOrExpression ) ( LAND y= inclusiveOrExpression -> ^( OPERATOR LAND ^( ARGUMENT_LIST $logicalAndExpression $y) ) )* )
			// AcslParser.g:526:4: ( inclusiveOrExpression -> inclusiveOrExpression ) ( LAND y= inclusiveOrExpression -> ^( OPERATOR LAND ^( ARGUMENT_LIST $logicalAndExpression $y) ) )*
			{
			// AcslParser.g:526:4: ( inclusiveOrExpression -> inclusiveOrExpression )
			// AcslParser.g:526:6: inclusiveOrExpression
			{
			pushFollow(FOLLOW_inclusiveOrExpression_in_logicalAndExpression4122);
			inclusiveOrExpression251=inclusiveOrExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_inclusiveOrExpression.add(inclusiveOrExpression251.getTree());
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
			// 526:28: -> inclusiveOrExpression
			{
				adaptor.addChild(root_0, stream_inclusiveOrExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// AcslParser.g:527:4: ( LAND y= inclusiveOrExpression -> ^( OPERATOR LAND ^( ARGUMENT_LIST $logicalAndExpression $y) ) )*
			loop56:
			while (true) {
				int alt56=2;
				int LA56_0 = input.LA(1);
				if ( (LA56_0==LAND) ) {
					alt56=1;
				}

				switch (alt56) {
				case 1 :
					// AcslParser.g:527:6: LAND y= inclusiveOrExpression
					{
					LAND252=(Token)match(input,LAND,FOLLOW_LAND_in_logicalAndExpression4135); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LAND.add(LAND252);

					pushFollow(FOLLOW_inclusiveOrExpression_in_logicalAndExpression4139);
					y=inclusiveOrExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_inclusiveOrExpression.add(y.getTree());
					// AST REWRITE
					// elements: LAND, y, logicalAndExpression
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
					// 528:6: -> ^( OPERATOR LAND ^( ARGUMENT_LIST $logicalAndExpression $y) )
					{
						// AcslParser.g:528:9: ^( OPERATOR LAND ^( ARGUMENT_LIST $logicalAndExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_LAND.nextNode());
						// AcslParser.g:528:25: ^( ARGUMENT_LIST $logicalAndExpression $y)
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
					break loop56;
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
	// AcslParser.g:533:1: logicalOrExpression : ( logicalAndExpression -> logicalAndExpression ) ( LOR y= logicalAndExpression -> ^( OPERATOR LOR ^( ARGUMENT_LIST $logicalOrExpression $y) ) )* ;
	public final AcslParser.logicalOrExpression_return logicalOrExpression() throws RecognitionException {
		AcslParser.logicalOrExpression_return retval = new AcslParser.logicalOrExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token LOR254=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope logicalAndExpression253 =null;

		Object LOR254_tree=null;
		RewriteRuleTokenStream stream_LOR=new RewriteRuleTokenStream(adaptor,"token LOR");
		RewriteRuleSubtreeStream stream_logicalAndExpression=new RewriteRuleSubtreeStream(adaptor,"rule logicalAndExpression");

		try {
			// AcslParser.g:534:2: ( ( logicalAndExpression -> logicalAndExpression ) ( LOR y= logicalAndExpression -> ^( OPERATOR LOR ^( ARGUMENT_LIST $logicalOrExpression $y) ) )* )
			// AcslParser.g:534:4: ( logicalAndExpression -> logicalAndExpression ) ( LOR y= logicalAndExpression -> ^( OPERATOR LOR ^( ARGUMENT_LIST $logicalOrExpression $y) ) )*
			{
			// AcslParser.g:534:4: ( logicalAndExpression -> logicalAndExpression )
			// AcslParser.g:534:6: logicalAndExpression
			{
			pushFollow(FOLLOW_logicalAndExpression_in_logicalOrExpression4183);
			logicalAndExpression253=logicalAndExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_logicalAndExpression.add(logicalAndExpression253.getTree());
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
			// 534:27: -> logicalAndExpression
			{
				adaptor.addChild(root_0, stream_logicalAndExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// AcslParser.g:535:4: ( LOR y= logicalAndExpression -> ^( OPERATOR LOR ^( ARGUMENT_LIST $logicalOrExpression $y) ) )*
			loop57:
			while (true) {
				int alt57=2;
				int LA57_0 = input.LA(1);
				if ( (LA57_0==LOR) ) {
					alt57=1;
				}

				switch (alt57) {
				case 1 :
					// AcslParser.g:535:6: LOR y= logicalAndExpression
					{
					LOR254=(Token)match(input,LOR,FOLLOW_LOR_in_logicalOrExpression4196); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LOR.add(LOR254);

					pushFollow(FOLLOW_logicalAndExpression_in_logicalOrExpression4200);
					y=logicalAndExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_logicalAndExpression.add(y.getTree());
					// AST REWRITE
					// elements: logicalOrExpression, y, LOR
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
					// 536:6: -> ^( OPERATOR LOR ^( ARGUMENT_LIST $logicalOrExpression $y) )
					{
						// AcslParser.g:536:9: ^( OPERATOR LOR ^( ARGUMENT_LIST $logicalOrExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_LOR.nextNode());
						// AcslParser.g:536:24: ^( ARGUMENT_LIST $logicalOrExpression $y)
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
					break loop57;
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
	// AcslParser.g:541:1: logicalImpliesExpression : ( logicalOrExpression -> logicalOrExpression ) ( IMPLY y= logicalOrExpression -> ^( OPERATOR IMPLY ^( ARGUMENT_LIST $logicalImpliesExpression $y) ) )* ;
	public final AcslParser.logicalImpliesExpression_return logicalImpliesExpression() throws RecognitionException {
		AcslParser.logicalImpliesExpression_return retval = new AcslParser.logicalImpliesExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token IMPLY256=null;
		ParserRuleReturnScope y =null;
		ParserRuleReturnScope logicalOrExpression255 =null;

		Object IMPLY256_tree=null;
		RewriteRuleTokenStream stream_IMPLY=new RewriteRuleTokenStream(adaptor,"token IMPLY");
		RewriteRuleSubtreeStream stream_logicalOrExpression=new RewriteRuleSubtreeStream(adaptor,"rule logicalOrExpression");

		try {
			// AcslParser.g:542:2: ( ( logicalOrExpression -> logicalOrExpression ) ( IMPLY y= logicalOrExpression -> ^( OPERATOR IMPLY ^( ARGUMENT_LIST $logicalImpliesExpression $y) ) )* )
			// AcslParser.g:542:4: ( logicalOrExpression -> logicalOrExpression ) ( IMPLY y= logicalOrExpression -> ^( OPERATOR IMPLY ^( ARGUMENT_LIST $logicalImpliesExpression $y) ) )*
			{
			// AcslParser.g:542:4: ( logicalOrExpression -> logicalOrExpression )
			// AcslParser.g:542:6: logicalOrExpression
			{
			pushFollow(FOLLOW_logicalOrExpression_in_logicalImpliesExpression4245);
			logicalOrExpression255=logicalOrExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_logicalOrExpression.add(logicalOrExpression255.getTree());
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
			// 542:26: -> logicalOrExpression
			{
				adaptor.addChild(root_0, stream_logicalOrExpression.nextTree());
			}


			retval.tree = root_0;
			}

			}

			// AcslParser.g:543:4: ( IMPLY y= logicalOrExpression -> ^( OPERATOR IMPLY ^( ARGUMENT_LIST $logicalImpliesExpression $y) ) )*
			loop58:
			while (true) {
				int alt58=2;
				int LA58_0 = input.LA(1);
				if ( (LA58_0==IMPLY) ) {
					alt58=1;
				}

				switch (alt58) {
				case 1 :
					// AcslParser.g:543:6: IMPLY y= logicalOrExpression
					{
					IMPLY256=(Token)match(input,IMPLY,FOLLOW_IMPLY_in_logicalImpliesExpression4258); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_IMPLY.add(IMPLY256);

					pushFollow(FOLLOW_logicalOrExpression_in_logicalImpliesExpression4262);
					y=logicalOrExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_logicalOrExpression.add(y.getTree());
					// AST REWRITE
					// elements: y, logicalImpliesExpression, IMPLY
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
					// 544:6: -> ^( OPERATOR IMPLY ^( ARGUMENT_LIST $logicalImpliesExpression $y) )
					{
						// AcslParser.g:544:9: ^( OPERATOR IMPLY ^( ARGUMENT_LIST $logicalImpliesExpression $y) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_IMPLY.nextNode());
						// AcslParser.g:544:26: ^( ARGUMENT_LIST $logicalImpliesExpression $y)
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
					break loop58;
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
	// AcslParser.g:549:1: conditionalExpression : logicalImpliesExpression ( -> logicalImpliesExpression | QUESTION term COLON conditionalExpression -> ^( OPERATOR QUESTION ^( ARGUMENT_LIST logicalImpliesExpression term conditionalExpression ) ) ) ;
	public final AcslParser.conditionalExpression_return conditionalExpression() throws RecognitionException {
		AcslParser.conditionalExpression_return retval = new AcslParser.conditionalExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token QUESTION258=null;
		Token COLON260=null;
		ParserRuleReturnScope logicalImpliesExpression257 =null;
		ParserRuleReturnScope term259 =null;
		ParserRuleReturnScope conditionalExpression261 =null;

		Object QUESTION258_tree=null;
		Object COLON260_tree=null;
		RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
		RewriteRuleTokenStream stream_QUESTION=new RewriteRuleTokenStream(adaptor,"token QUESTION");
		RewriteRuleSubtreeStream stream_logicalImpliesExpression=new RewriteRuleSubtreeStream(adaptor,"rule logicalImpliesExpression");
		RewriteRuleSubtreeStream stream_term=new RewriteRuleSubtreeStream(adaptor,"rule term");
		RewriteRuleSubtreeStream stream_conditionalExpression=new RewriteRuleSubtreeStream(adaptor,"rule conditionalExpression");

		try {
			// AcslParser.g:550:2: ( logicalImpliesExpression ( -> logicalImpliesExpression | QUESTION term COLON conditionalExpression -> ^( OPERATOR QUESTION ^( ARGUMENT_LIST logicalImpliesExpression term conditionalExpression ) ) ) )
			// AcslParser.g:550:4: logicalImpliesExpression ( -> logicalImpliesExpression | QUESTION term COLON conditionalExpression -> ^( OPERATOR QUESTION ^( ARGUMENT_LIST logicalImpliesExpression term conditionalExpression ) ) )
			{
			pushFollow(FOLLOW_logicalImpliesExpression_in_conditionalExpression4308);
			logicalImpliesExpression257=logicalImpliesExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_logicalImpliesExpression.add(logicalImpliesExpression257.getTree());
			// AcslParser.g:551:2: ( -> logicalImpliesExpression | QUESTION term COLON conditionalExpression -> ^( OPERATOR QUESTION ^( ARGUMENT_LIST logicalImpliesExpression term conditionalExpression ) ) )
			int alt59=2;
			int LA59_0 = input.LA(1);
			if ( (LA59_0==EOF||LA59_0==BAR||(LA59_0 >= COLON && LA59_0 <= COMMA)||LA59_0==FOR||(LA59_0 >= RCOMMENT && LA59_0 <= RCURLY)||(LA59_0 >= RPAREN && LA59_0 <= RSQUARE)||LA59_0==SEMICOL) ) {
				alt59=1;
			}
			else if ( (LA59_0==QUESTION) ) {
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
					// AcslParser.g:551:4: 
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
					// 551:4: -> logicalImpliesExpression
					{
						adaptor.addChild(root_0, stream_logicalImpliesExpression.nextTree());
					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:552:8: QUESTION term COLON conditionalExpression
					{
					QUESTION258=(Token)match(input,QUESTION,FOLLOW_QUESTION_in_conditionalExpression4324); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_QUESTION.add(QUESTION258);

					pushFollow(FOLLOW_term_in_conditionalExpression4326);
					term259=term();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_term.add(term259.getTree());
					COLON260=(Token)match(input,COLON,FOLLOW_COLON_in_conditionalExpression4328); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COLON.add(COLON260);

					pushFollow(FOLLOW_conditionalExpression_in_conditionalExpression4330);
					conditionalExpression261=conditionalExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_conditionalExpression.add(conditionalExpression261.getTree());
					// AST REWRITE
					// elements: QUESTION, term, conditionalExpression, logicalImpliesExpression
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 553:8: -> ^( OPERATOR QUESTION ^( ARGUMENT_LIST logicalImpliesExpression term conditionalExpression ) )
					{
						// AcslParser.g:553:11: ^( OPERATOR QUESTION ^( ARGUMENT_LIST logicalImpliesExpression term conditionalExpression ) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_QUESTION.nextNode());
						// AcslParser.g:554:13: ^( ARGUMENT_LIST logicalImpliesExpression term conditionalExpression )
						{
						Object root_2 = (Object)adaptor.nil();
						root_2 = (Object)adaptor.becomeRoot((Object)adaptor.create(ARGUMENT_LIST, "ARGUMENT_LIST"), root_2);
						adaptor.addChild(root_2, stream_logicalImpliesExpression.nextTree());
						adaptor.addChild(root_2, stream_term.nextTree());
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
	// AcslParser.g:563:1: quantifierExpression : quantifier binders SEMICOL assignmentExpression -> ^( quantifier binders assignmentExpression ) ;
	public final AcslParser.quantifierExpression_return quantifierExpression() throws RecognitionException {
		AcslParser.quantifierExpression_return retval = new AcslParser.quantifierExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token SEMICOL264=null;
		ParserRuleReturnScope quantifier262 =null;
		ParserRuleReturnScope binders263 =null;
		ParserRuleReturnScope assignmentExpression265 =null;

		Object SEMICOL264_tree=null;
		RewriteRuleTokenStream stream_SEMICOL=new RewriteRuleTokenStream(adaptor,"token SEMICOL");
		RewriteRuleSubtreeStream stream_quantifier=new RewriteRuleSubtreeStream(adaptor,"rule quantifier");
		RewriteRuleSubtreeStream stream_binders=new RewriteRuleSubtreeStream(adaptor,"rule binders");
		RewriteRuleSubtreeStream stream_assignmentExpression=new RewriteRuleSubtreeStream(adaptor,"rule assignmentExpression");

		try {
			// AcslParser.g:564:2: ( quantifier binders SEMICOL assignmentExpression -> ^( quantifier binders assignmentExpression ) )
			// AcslParser.g:564:4: quantifier binders SEMICOL assignmentExpression
			{
			pushFollow(FOLLOW_quantifier_in_quantifierExpression4429);
			quantifier262=quantifier();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_quantifier.add(quantifier262.getTree());
			pushFollow(FOLLOW_binders_in_quantifierExpression4431);
			binders263=binders();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_binders.add(binders263.getTree());
			SEMICOL264=(Token)match(input,SEMICOL,FOLLOW_SEMICOL_in_quantifierExpression4433); if (state.failed) return retval; 
			if ( state.backtracking==0 ) stream_SEMICOL.add(SEMICOL264);

			pushFollow(FOLLOW_assignmentExpression_in_quantifierExpression4435);
			assignmentExpression265=assignmentExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression265.getTree());
			// AST REWRITE
			// elements: quantifier, assignmentExpression, binders
			// token labels: 
			// rule labels: retval
			// token list labels: 
			// rule list labels: 
			// wildcard labels: 
			if ( state.backtracking==0 ) {
			retval.tree = root_0;
			RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

			root_0 = (Object)adaptor.nil();
			// 565:4: -> ^( quantifier binders assignmentExpression )
			{
				// AcslParser.g:565:7: ^( quantifier binders assignmentExpression )
				{
				Object root_1 = (Object)adaptor.nil();
				root_1 = (Object)adaptor.becomeRoot(stream_quantifier.nextNode(), root_1);
				adaptor.addChild(root_1, stream_binders.nextTree());
				adaptor.addChild(root_1, stream_assignmentExpression.nextTree());
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
	// $ANTLR end "quantifierExpression"


	public static class quantifier_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "quantifier"
	// AcslParser.g:579:1: quantifier : ( FORALL | EXISTS );
	public final AcslParser.quantifier_return quantifier() throws RecognitionException {
		AcslParser.quantifier_return retval = new AcslParser.quantifier_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set266=null;

		Object set266_tree=null;

		try {
			// AcslParser.g:580:2: ( FORALL | EXISTS )
			// AcslParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set266=input.LT(1);
			if ( input.LA(1)==EXISTS||input.LA(1)==FORALL ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set266));
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
	// AcslParser.g:591:1: assignmentExpression : ( ( unaryExpression ASSIGN )=> unaryExpression ASSIGN assignmentExpression -> ^( OPERATOR ASSIGN ^( ARGUMENT_LIST unaryExpression assignmentExpression ) ) | conditionalExpression | quantifierExpression );
	public final AcslParser.assignmentExpression_return assignmentExpression() throws RecognitionException {
		AcslParser.assignmentExpression_return retval = new AcslParser.assignmentExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token ASSIGN268=null;
		ParserRuleReturnScope unaryExpression267 =null;
		ParserRuleReturnScope assignmentExpression269 =null;
		ParserRuleReturnScope conditionalExpression270 =null;
		ParserRuleReturnScope quantifierExpression271 =null;

		Object ASSIGN268_tree=null;
		RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
		RewriteRuleSubtreeStream stream_assignmentExpression=new RewriteRuleSubtreeStream(adaptor,"rule assignmentExpression");
		RewriteRuleSubtreeStream stream_unaryExpression=new RewriteRuleSubtreeStream(adaptor,"rule unaryExpression");

		try {
			// AcslParser.g:592:2: ( ( unaryExpression ASSIGN )=> unaryExpression ASSIGN assignmentExpression -> ^( OPERATOR ASSIGN ^( ARGUMENT_LIST unaryExpression assignmentExpression ) ) | conditionalExpression | quantifierExpression )
			int alt60=3;
			switch ( input.LA(1) ) {
			case INTEGER_CONSTANT:
				{
				int LA60_1 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case FLOATING_CONSTANT:
				{
				int LA60_2 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 2, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case CHARACTER_CONSTANT:
				{
				int LA60_3 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case TRUE:
				{
				int LA60_4 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 4, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case FALSE:
				{
				int LA60_5 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 5, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case RESULT:
				{
				int LA60_6 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 6, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case NOTHING:
				{
				int LA60_7 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 7, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case ELLIPSIS:
				{
				int LA60_8 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 8, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case SELF:
				{
				int LA60_9 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 9, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case NULL:
				{
				int LA60_10 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 10, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case MPI_COMM_RANK:
			case MPI_COMM_SIZE:
				{
				int LA60_11 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 11, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case ID:
				{
				int LA60_12 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 12, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case STRING_LITERAL:
				{
				int LA60_13 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 13, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case LCURLY:
				{
				int LA60_14 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 14, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case LPAREN:
				{
				int LA60_15 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 15, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case MPI_EMPTY_IN:
				{
				int LA60_16 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 16, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case MPI_EMPTY_OUT:
				{
				int LA60_17 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 17, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case MPI_AGREE:
				{
				int LA60_18 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 18, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case MPI_REGION:
				{
				int LA60_19 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 19, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case MPI_EQUALS:
				{
				int LA60_20 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 20, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case REMOTE_ACCESS:
				{
				int LA60_21 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 21, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case AMPERSAND:
			case COMP:
			case NOT:
			case PLUS:
			case STAR:
			case MINUS:
				{
				int LA60_22 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 22, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case SIZEOF:
				{
				int LA60_23 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 23, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case UNION:
				{
				int LA60_24 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 24, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case INTER:
				{
				int LA60_25 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 25, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case VALID:
				{
				int LA60_26 = input.LA(2);
				if ( (synpred111_AcslParser()) ) {
					alt60=1;
				}
				else if ( (synpred112_AcslParser()) ) {
					alt60=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return retval;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 60, 26, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case EXISTS:
			case FORALL:
				{
				alt60=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 60, 0, input);
				throw nvae;
			}
			switch (alt60) {
				case 1 :
					// AcslParser.g:592:4: ( unaryExpression ASSIGN )=> unaryExpression ASSIGN assignmentExpression
					{
					pushFollow(FOLLOW_unaryExpression_in_assignmentExpression4507);
					unaryExpression267=unaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_unaryExpression.add(unaryExpression267.getTree());
					ASSIGN268=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_assignmentExpression4509); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_ASSIGN.add(ASSIGN268);

					pushFollow(FOLLOW_assignmentExpression_in_assignmentExpression4511);
					assignmentExpression269=assignmentExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_assignmentExpression.add(assignmentExpression269.getTree());
					// AST REWRITE
					// elements: unaryExpression, assignmentExpression, ASSIGN
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 594:4: -> ^( OPERATOR ASSIGN ^( ARGUMENT_LIST unaryExpression assignmentExpression ) )
					{
						// AcslParser.g:594:7: ^( OPERATOR ASSIGN ^( ARGUMENT_LIST unaryExpression assignmentExpression ) )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(OPERATOR, "OPERATOR"), root_1);
						adaptor.addChild(root_1, stream_ASSIGN.nextNode());
						// AcslParser.g:595:9: ^( ARGUMENT_LIST unaryExpression assignmentExpression )
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
					// AcslParser.g:596:4: conditionalExpression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_conditionalExpression_in_assignmentExpression4543);
					conditionalExpression270=conditionalExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, conditionalExpression270.getTree());

					}
					break;
				case 3 :
					// AcslParser.g:597:4: quantifierExpression
					{
					root_0 = (Object)adaptor.nil();


					pushFollow(FOLLOW_quantifierExpression_in_assignmentExpression4548);
					quantifierExpression271=quantifierExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) adaptor.addChild(root_0, quantifierExpression271.getTree());

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


	public static class term_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "term"
	// AcslParser.g:608:1: term : assignmentExpression ;
	public final AcslParser.term_return term() throws RecognitionException {
		AcslParser.term_return retval = new AcslParser.term_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope assignmentExpression272 =null;


		try {
			// AcslParser.g:609:2: ( assignmentExpression )
			// AcslParser.g:609:4: assignmentExpression
			{
			root_0 = (Object)adaptor.nil();


			pushFollow(FOLLOW_assignmentExpression_in_term4561);
			assignmentExpression272=assignmentExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, assignmentExpression272.getTree());

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
	// $ANTLR end "term"


	public static class constantExpression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "constantExpression"
	// AcslParser.g:613:1: constantExpression : conditionalExpression ;
	public final AcslParser.constantExpression_return constantExpression() throws RecognitionException {
		AcslParser.constantExpression_return retval = new AcslParser.constantExpression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		ParserRuleReturnScope conditionalExpression273 =null;


		try {
			// AcslParser.g:614:2: ( conditionalExpression )
			// AcslParser.g:614:4: conditionalExpression
			{
			root_0 = (Object)adaptor.nil();


			pushFollow(FOLLOW_conditionalExpression_in_constantExpression4580);
			conditionalExpression273=conditionalExpression();
			state._fsp--;
			if (state.failed) return retval;
			if ( state.backtracking==0 ) adaptor.addChild(root_0, conditionalExpression273.getTree());

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


	public static class constant_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "constant"
	// AcslParser.g:617:1: constant : ( INTEGER_CONSTANT | FLOATING_CONSTANT | CHARACTER_CONSTANT | TRUE | FALSE | RESULT | NOTHING | ELLIPSIS | SELF | NULL | mpi_constant -> ^( MPI_CONSTANT mpi_constant ) );
	public final AcslParser.constant_return constant() throws RecognitionException {
		AcslParser.constant_return retval = new AcslParser.constant_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token INTEGER_CONSTANT274=null;
		Token FLOATING_CONSTANT275=null;
		Token CHARACTER_CONSTANT276=null;
		Token TRUE277=null;
		Token FALSE278=null;
		Token RESULT279=null;
		Token NOTHING280=null;
		Token ELLIPSIS281=null;
		Token SELF282=null;
		Token NULL283=null;
		ParserRuleReturnScope mpi_constant284 =null;

		Object INTEGER_CONSTANT274_tree=null;
		Object FLOATING_CONSTANT275_tree=null;
		Object CHARACTER_CONSTANT276_tree=null;
		Object TRUE277_tree=null;
		Object FALSE278_tree=null;
		Object RESULT279_tree=null;
		Object NOTHING280_tree=null;
		Object ELLIPSIS281_tree=null;
		Object SELF282_tree=null;
		Object NULL283_tree=null;
		RewriteRuleSubtreeStream stream_mpi_constant=new RewriteRuleSubtreeStream(adaptor,"rule mpi_constant");

		try {
			// AcslParser.g:618:2: ( INTEGER_CONSTANT | FLOATING_CONSTANT | CHARACTER_CONSTANT | TRUE | FALSE | RESULT | NOTHING | ELLIPSIS | SELF | NULL | mpi_constant -> ^( MPI_CONSTANT mpi_constant ) )
			int alt61=11;
			switch ( input.LA(1) ) {
			case INTEGER_CONSTANT:
				{
				alt61=1;
				}
				break;
			case FLOATING_CONSTANT:
				{
				alt61=2;
				}
				break;
			case CHARACTER_CONSTANT:
				{
				alt61=3;
				}
				break;
			case TRUE:
				{
				alt61=4;
				}
				break;
			case FALSE:
				{
				alt61=5;
				}
				break;
			case RESULT:
				{
				alt61=6;
				}
				break;
			case NOTHING:
				{
				alt61=7;
				}
				break;
			case ELLIPSIS:
				{
				alt61=8;
				}
				break;
			case SELF:
				{
				alt61=9;
				}
				break;
			case NULL:
				{
				alt61=10;
				}
				break;
			case MPI_COMM_RANK:
			case MPI_COMM_SIZE:
				{
				alt61=11;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 61, 0, input);
				throw nvae;
			}
			switch (alt61) {
				case 1 :
					// AcslParser.g:618:4: INTEGER_CONSTANT
					{
					root_0 = (Object)adaptor.nil();


					INTEGER_CONSTANT274=(Token)match(input,INTEGER_CONSTANT,FOLLOW_INTEGER_CONSTANT_in_constant4592); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					INTEGER_CONSTANT274_tree = (Object)adaptor.create(INTEGER_CONSTANT274);
					adaptor.addChild(root_0, INTEGER_CONSTANT274_tree);
					}

					}
					break;
				case 2 :
					// AcslParser.g:619:4: FLOATING_CONSTANT
					{
					root_0 = (Object)adaptor.nil();


					FLOATING_CONSTANT275=(Token)match(input,FLOATING_CONSTANT,FOLLOW_FLOATING_CONSTANT_in_constant4597); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					FLOATING_CONSTANT275_tree = (Object)adaptor.create(FLOATING_CONSTANT275);
					adaptor.addChild(root_0, FLOATING_CONSTANT275_tree);
					}

					}
					break;
				case 3 :
					// AcslParser.g:620:4: CHARACTER_CONSTANT
					{
					root_0 = (Object)adaptor.nil();


					CHARACTER_CONSTANT276=(Token)match(input,CHARACTER_CONSTANT,FOLLOW_CHARACTER_CONSTANT_in_constant4602); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					CHARACTER_CONSTANT276_tree = (Object)adaptor.create(CHARACTER_CONSTANT276);
					adaptor.addChild(root_0, CHARACTER_CONSTANT276_tree);
					}

					}
					break;
				case 4 :
					// AcslParser.g:621:4: TRUE
					{
					root_0 = (Object)adaptor.nil();


					TRUE277=(Token)match(input,TRUE,FOLLOW_TRUE_in_constant4607); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					TRUE277_tree = (Object)adaptor.create(TRUE277);
					adaptor.addChild(root_0, TRUE277_tree);
					}

					}
					break;
				case 5 :
					// AcslParser.g:621:11: FALSE
					{
					root_0 = (Object)adaptor.nil();


					FALSE278=(Token)match(input,FALSE,FOLLOW_FALSE_in_constant4611); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					FALSE278_tree = (Object)adaptor.create(FALSE278);
					adaptor.addChild(root_0, FALSE278_tree);
					}

					}
					break;
				case 6 :
					// AcslParser.g:621:19: RESULT
					{
					root_0 = (Object)adaptor.nil();


					RESULT279=(Token)match(input,RESULT,FOLLOW_RESULT_in_constant4615); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					RESULT279_tree = (Object)adaptor.create(RESULT279);
					adaptor.addChild(root_0, RESULT279_tree);
					}

					}
					break;
				case 7 :
					// AcslParser.g:621:28: NOTHING
					{
					root_0 = (Object)adaptor.nil();


					NOTHING280=(Token)match(input,NOTHING,FOLLOW_NOTHING_in_constant4619); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					NOTHING280_tree = (Object)adaptor.create(NOTHING280);
					adaptor.addChild(root_0, NOTHING280_tree);
					}

					}
					break;
				case 8 :
					// AcslParser.g:621:38: ELLIPSIS
					{
					root_0 = (Object)adaptor.nil();


					ELLIPSIS281=(Token)match(input,ELLIPSIS,FOLLOW_ELLIPSIS_in_constant4623); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					ELLIPSIS281_tree = (Object)adaptor.create(ELLIPSIS281);
					adaptor.addChild(root_0, ELLIPSIS281_tree);
					}

					}
					break;
				case 9 :
					// AcslParser.g:622:7: SELF
					{
					root_0 = (Object)adaptor.nil();


					SELF282=(Token)match(input,SELF,FOLLOW_SELF_in_constant4631); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					SELF282_tree = (Object)adaptor.create(SELF282);
					adaptor.addChild(root_0, SELF282_tree);
					}

					}
					break;
				case 10 :
					// AcslParser.g:622:14: NULL
					{
					root_0 = (Object)adaptor.nil();


					NULL283=(Token)match(input,NULL,FOLLOW_NULL_in_constant4635); if (state.failed) return retval;
					if ( state.backtracking==0 ) {
					NULL283_tree = (Object)adaptor.create(NULL283);
					adaptor.addChild(root_0, NULL283_tree);
					}

					}
					break;
				case 11 :
					// AcslParser.g:623:7: mpi_constant
					{
					pushFollow(FOLLOW_mpi_constant_in_constant4643);
					mpi_constant284=mpi_constant();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_mpi_constant.add(mpi_constant284.getTree());
					// AST REWRITE
					// elements: mpi_constant
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 623:20: -> ^( MPI_CONSTANT mpi_constant )
					{
						// AcslParser.g:623:23: ^( MPI_CONSTANT mpi_constant )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot((Object)adaptor.create(MPI_CONSTANT, "MPI_CONSTANT"), root_1);
						adaptor.addChild(root_1, stream_mpi_constant.nextTree());
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
	// $ANTLR end "constant"


	public static class mpi_expression_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "mpi_expression"
	// AcslParser.g:627:1: mpi_expression : ( MPI_EMPTY_IN LPAREN primaryExpression RPAREN -> ^( MPI_EMPTY_IN primaryExpression ) | MPI_EMPTY_OUT LPAREN primaryExpression RPAREN -> ^( MPI_EMPTY_OUT primaryExpression ) | MPI_AGREE LPAREN a= variable_ident_base RPAREN -> ^( MPI_AGREE $a) | MPI_REGION LPAREN a= primaryExpression COMMA b= primaryExpression COMMA c= primaryExpression RPAREN -> ^( MPI_REGION $a $b $c) | MPI_EQUALS LPAREN a= primaryExpression COMMA b= primaryExpression COMMA c= primaryExpression COMMA d= primaryExpression RPAREN -> ^( MPI_EQUALS $a $b $c $d) );
	public final AcslParser.mpi_expression_return mpi_expression() throws RecognitionException {
		AcslParser.mpi_expression_return retval = new AcslParser.mpi_expression_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token MPI_EMPTY_IN285=null;
		Token LPAREN286=null;
		Token RPAREN288=null;
		Token MPI_EMPTY_OUT289=null;
		Token LPAREN290=null;
		Token RPAREN292=null;
		Token MPI_AGREE293=null;
		Token LPAREN294=null;
		Token RPAREN295=null;
		Token MPI_REGION296=null;
		Token LPAREN297=null;
		Token COMMA298=null;
		Token COMMA299=null;
		Token RPAREN300=null;
		Token MPI_EQUALS301=null;
		Token LPAREN302=null;
		Token COMMA303=null;
		Token COMMA304=null;
		Token COMMA305=null;
		Token RPAREN306=null;
		ParserRuleReturnScope a =null;
		ParserRuleReturnScope b =null;
		ParserRuleReturnScope c =null;
		ParserRuleReturnScope d =null;
		ParserRuleReturnScope primaryExpression287 =null;
		ParserRuleReturnScope primaryExpression291 =null;

		Object MPI_EMPTY_IN285_tree=null;
		Object LPAREN286_tree=null;
		Object RPAREN288_tree=null;
		Object MPI_EMPTY_OUT289_tree=null;
		Object LPAREN290_tree=null;
		Object RPAREN292_tree=null;
		Object MPI_AGREE293_tree=null;
		Object LPAREN294_tree=null;
		Object RPAREN295_tree=null;
		Object MPI_REGION296_tree=null;
		Object LPAREN297_tree=null;
		Object COMMA298_tree=null;
		Object COMMA299_tree=null;
		Object RPAREN300_tree=null;
		Object MPI_EQUALS301_tree=null;
		Object LPAREN302_tree=null;
		Object COMMA303_tree=null;
		Object COMMA304_tree=null;
		Object COMMA305_tree=null;
		Object RPAREN306_tree=null;
		RewriteRuleTokenStream stream_MPI_REGION=new RewriteRuleTokenStream(adaptor,"token MPI_REGION");
		RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
		RewriteRuleTokenStream stream_MPI_EMPTY_OUT=new RewriteRuleTokenStream(adaptor,"token MPI_EMPTY_OUT");
		RewriteRuleTokenStream stream_MPI_EMPTY_IN=new RewriteRuleTokenStream(adaptor,"token MPI_EMPTY_IN");
		RewriteRuleTokenStream stream_MPI_EQUALS=new RewriteRuleTokenStream(adaptor,"token MPI_EQUALS");
		RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
		RewriteRuleTokenStream stream_MPI_AGREE=new RewriteRuleTokenStream(adaptor,"token MPI_AGREE");
		RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
		RewriteRuleSubtreeStream stream_primaryExpression=new RewriteRuleSubtreeStream(adaptor,"rule primaryExpression");
		RewriteRuleSubtreeStream stream_variable_ident_base=new RewriteRuleSubtreeStream(adaptor,"rule variable_ident_base");

		try {
			// AcslParser.g:628:5: ( MPI_EMPTY_IN LPAREN primaryExpression RPAREN -> ^( MPI_EMPTY_IN primaryExpression ) | MPI_EMPTY_OUT LPAREN primaryExpression RPAREN -> ^( MPI_EMPTY_OUT primaryExpression ) | MPI_AGREE LPAREN a= variable_ident_base RPAREN -> ^( MPI_AGREE $a) | MPI_REGION LPAREN a= primaryExpression COMMA b= primaryExpression COMMA c= primaryExpression RPAREN -> ^( MPI_REGION $a $b $c) | MPI_EQUALS LPAREN a= primaryExpression COMMA b= primaryExpression COMMA c= primaryExpression COMMA d= primaryExpression RPAREN -> ^( MPI_EQUALS $a $b $c $d) )
			int alt62=5;
			switch ( input.LA(1) ) {
			case MPI_EMPTY_IN:
				{
				alt62=1;
				}
				break;
			case MPI_EMPTY_OUT:
				{
				alt62=2;
				}
				break;
			case MPI_AGREE:
				{
				alt62=3;
				}
				break;
			case MPI_REGION:
				{
				alt62=4;
				}
				break;
			case MPI_EQUALS:
				{
				alt62=5;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return retval;}
				NoViableAltException nvae =
					new NoViableAltException("", 62, 0, input);
				throw nvae;
			}
			switch (alt62) {
				case 1 :
					// AcslParser.g:628:7: MPI_EMPTY_IN LPAREN primaryExpression RPAREN
					{
					MPI_EMPTY_IN285=(Token)match(input,MPI_EMPTY_IN,FOLLOW_MPI_EMPTY_IN_in_mpi_expression4667); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_MPI_EMPTY_IN.add(MPI_EMPTY_IN285);

					LPAREN286=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_mpi_expression4669); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN286);

					pushFollow(FOLLOW_primaryExpression_in_mpi_expression4671);
					primaryExpression287=primaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_primaryExpression.add(primaryExpression287.getTree());
					RPAREN288=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_mpi_expression4673); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN288);

					// AST REWRITE
					// elements: primaryExpression, MPI_EMPTY_IN
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 629:7: -> ^( MPI_EMPTY_IN primaryExpression )
					{
						// AcslParser.g:629:10: ^( MPI_EMPTY_IN primaryExpression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_MPI_EMPTY_IN.nextNode(), root_1);
						adaptor.addChild(root_1, stream_primaryExpression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 2 :
					// AcslParser.g:630:7: MPI_EMPTY_OUT LPAREN primaryExpression RPAREN
					{
					MPI_EMPTY_OUT289=(Token)match(input,MPI_EMPTY_OUT,FOLLOW_MPI_EMPTY_OUT_in_mpi_expression4695); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_MPI_EMPTY_OUT.add(MPI_EMPTY_OUT289);

					LPAREN290=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_mpi_expression4697); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN290);

					pushFollow(FOLLOW_primaryExpression_in_mpi_expression4699);
					primaryExpression291=primaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_primaryExpression.add(primaryExpression291.getTree());
					RPAREN292=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_mpi_expression4701); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN292);

					// AST REWRITE
					// elements: primaryExpression, MPI_EMPTY_OUT
					// token labels: 
					// rule labels: retval
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 631:7: -> ^( MPI_EMPTY_OUT primaryExpression )
					{
						// AcslParser.g:631:10: ^( MPI_EMPTY_OUT primaryExpression )
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_MPI_EMPTY_OUT.nextNode(), root_1);
						adaptor.addChild(root_1, stream_primaryExpression.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 3 :
					// AcslParser.g:632:7: MPI_AGREE LPAREN a= variable_ident_base RPAREN
					{
					MPI_AGREE293=(Token)match(input,MPI_AGREE,FOLLOW_MPI_AGREE_in_mpi_expression4723); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_MPI_AGREE.add(MPI_AGREE293);

					LPAREN294=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_mpi_expression4725); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN294);

					pushFollow(FOLLOW_variable_ident_base_in_mpi_expression4729);
					a=variable_ident_base();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_variable_ident_base.add(a.getTree());
					RPAREN295=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_mpi_expression4731); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN295);

					// AST REWRITE
					// elements: MPI_AGREE, a
					// token labels: 
					// rule labels: retval, a
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_a=new RewriteRuleSubtreeStream(adaptor,"rule a",a!=null?a.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 633:7: -> ^( MPI_AGREE $a)
					{
						// AcslParser.g:633:10: ^( MPI_AGREE $a)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_MPI_AGREE.nextNode(), root_1);
						adaptor.addChild(root_1, stream_a.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 4 :
					// AcslParser.g:634:7: MPI_REGION LPAREN a= primaryExpression COMMA b= primaryExpression COMMA c= primaryExpression RPAREN
					{
					MPI_REGION296=(Token)match(input,MPI_REGION,FOLLOW_MPI_REGION_in_mpi_expression4757); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_MPI_REGION.add(MPI_REGION296);

					LPAREN297=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_mpi_expression4759); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN297);

					pushFollow(FOLLOW_primaryExpression_in_mpi_expression4763);
					a=primaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_primaryExpression.add(a.getTree());
					COMMA298=(Token)match(input,COMMA,FOLLOW_COMMA_in_mpi_expression4765); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA298);

					pushFollow(FOLLOW_primaryExpression_in_mpi_expression4769);
					b=primaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_primaryExpression.add(b.getTree());
					COMMA299=(Token)match(input,COMMA,FOLLOW_COMMA_in_mpi_expression4771); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA299);

					pushFollow(FOLLOW_primaryExpression_in_mpi_expression4775);
					c=primaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_primaryExpression.add(c.getTree());
					RPAREN300=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_mpi_expression4777); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN300);

					// AST REWRITE
					// elements: a, c, b, MPI_REGION
					// token labels: 
					// rule labels: retval, b, c, a
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_b=new RewriteRuleSubtreeStream(adaptor,"rule b",b!=null?b.getTree():null);
					RewriteRuleSubtreeStream stream_c=new RewriteRuleSubtreeStream(adaptor,"rule c",c!=null?c.getTree():null);
					RewriteRuleSubtreeStream stream_a=new RewriteRuleSubtreeStream(adaptor,"rule a",a!=null?a.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 635:7: -> ^( MPI_REGION $a $b $c)
					{
						// AcslParser.g:635:10: ^( MPI_REGION $a $b $c)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_MPI_REGION.nextNode(), root_1);
						adaptor.addChild(root_1, stream_a.nextTree());
						adaptor.addChild(root_1, stream_b.nextTree());
						adaptor.addChild(root_1, stream_c.nextTree());
						adaptor.addChild(root_0, root_1);
						}

					}


					retval.tree = root_0;
					}

					}
					break;
				case 5 :
					// AcslParser.g:636:7: MPI_EQUALS LPAREN a= primaryExpression COMMA b= primaryExpression COMMA c= primaryExpression COMMA d= primaryExpression RPAREN
					{
					MPI_EQUALS301=(Token)match(input,MPI_EQUALS,FOLLOW_MPI_EQUALS_in_mpi_expression4806); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_MPI_EQUALS.add(MPI_EQUALS301);

					LPAREN302=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_mpi_expression4808); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_LPAREN.add(LPAREN302);

					pushFollow(FOLLOW_primaryExpression_in_mpi_expression4812);
					a=primaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_primaryExpression.add(a.getTree());
					COMMA303=(Token)match(input,COMMA,FOLLOW_COMMA_in_mpi_expression4814); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA303);

					pushFollow(FOLLOW_primaryExpression_in_mpi_expression4818);
					b=primaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_primaryExpression.add(b.getTree());
					COMMA304=(Token)match(input,COMMA,FOLLOW_COMMA_in_mpi_expression4820); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA304);

					pushFollow(FOLLOW_primaryExpression_in_mpi_expression4824);
					c=primaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_primaryExpression.add(c.getTree());
					COMMA305=(Token)match(input,COMMA,FOLLOW_COMMA_in_mpi_expression4826); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_COMMA.add(COMMA305);

					pushFollow(FOLLOW_primaryExpression_in_mpi_expression4830);
					d=primaryExpression();
					state._fsp--;
					if (state.failed) return retval;
					if ( state.backtracking==0 ) stream_primaryExpression.add(d.getTree());
					RPAREN306=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_mpi_expression4832); if (state.failed) return retval; 
					if ( state.backtracking==0 ) stream_RPAREN.add(RPAREN306);

					// AST REWRITE
					// elements: d, c, a, b, MPI_EQUALS
					// token labels: 
					// rule labels: retval, d, b, c, a
					// token list labels: 
					// rule list labels: 
					// wildcard labels: 
					if ( state.backtracking==0 ) {
					retval.tree = root_0;
					RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"rule retval",retval!=null?retval.getTree():null);
					RewriteRuleSubtreeStream stream_d=new RewriteRuleSubtreeStream(adaptor,"rule d",d!=null?d.getTree():null);
					RewriteRuleSubtreeStream stream_b=new RewriteRuleSubtreeStream(adaptor,"rule b",b!=null?b.getTree():null);
					RewriteRuleSubtreeStream stream_c=new RewriteRuleSubtreeStream(adaptor,"rule c",c!=null?c.getTree():null);
					RewriteRuleSubtreeStream stream_a=new RewriteRuleSubtreeStream(adaptor,"rule a",a!=null?a.getTree():null);

					root_0 = (Object)adaptor.nil();
					// 637:7: -> ^( MPI_EQUALS $a $b $c $d)
					{
						// AcslParser.g:637:10: ^( MPI_EQUALS $a $b $c $d)
						{
						Object root_1 = (Object)adaptor.nil();
						root_1 = (Object)adaptor.becomeRoot(stream_MPI_EQUALS.nextNode(), root_1);
						adaptor.addChild(root_1, stream_a.nextTree());
						adaptor.addChild(root_1, stream_b.nextTree());
						adaptor.addChild(root_1, stream_c.nextTree());
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
	// $ANTLR end "mpi_expression"


	public static class mpi_constant_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "mpi_constant"
	// AcslParser.g:640:1: mpi_constant : ( MPI_COMM_RANK | MPI_COMM_SIZE );
	public final AcslParser.mpi_constant_return mpi_constant() throws RecognitionException {
		AcslParser.mpi_constant_return retval = new AcslParser.mpi_constant_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set307=null;

		Object set307_tree=null;

		try {
			// AcslParser.g:641:5: ( MPI_COMM_RANK | MPI_COMM_SIZE )
			// AcslParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set307=input.LT(1);
			if ( (input.LA(1) >= MPI_COMM_RANK && input.LA(1) <= MPI_COMM_SIZE) ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set307));
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
	// $ANTLR end "mpi_constant"


	public static class mpi_collective_kind_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "mpi_collective_kind"
	// AcslParser.g:644:1: mpi_collective_kind : ( COL | P2P | BOTH );
	public final AcslParser.mpi_collective_kind_return mpi_collective_kind() throws RecognitionException {
		AcslParser.mpi_collective_kind_return retval = new AcslParser.mpi_collective_kind_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set308=null;

		Object set308_tree=null;

		try {
			// AcslParser.g:645:5: ( COL | P2P | BOTH )
			// AcslParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set308=input.LT(1);
			if ( input.LA(1)==BOTH||input.LA(1)==COL||input.LA(1)==P2P ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set308));
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
	// $ANTLR end "mpi_collective_kind"


	public static class unary_op_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "unary_op"
	// AcslParser.g:648:1: unary_op : ( PLUS | MINUS | NOT | COMP | STAR | AMPERSAND );
	public final AcslParser.unary_op_return unary_op() throws RecognitionException {
		AcslParser.unary_op_return retval = new AcslParser.unary_op_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set309=null;

		Object set309_tree=null;

		try {
			// AcslParser.g:649:5: ( PLUS | MINUS | NOT | COMP | STAR | AMPERSAND )
			// AcslParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set309=input.LT(1);
			if ( input.LA(1)==AMPERSAND||input.LA(1)==COMP||input.LA(1)==NOT||input.LA(1)==PLUS||input.LA(1)==STAR||input.LA(1)==MINUS ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set309));
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
	// $ANTLR end "unary_op"


	public static class binary_op_return extends ParserRuleReturnScope {
		Object tree;
		@Override
		public Object getTree() { return tree; }
	};


	// $ANTLR start "binary_op"
	// AcslParser.g:652:1: binary_op : ( PLUS | MINUS | STAR | DIVIDE | MOD | LSHIFT | RSHIFT | EQ | NEQ | LTE | GTE | LT | GT | LAND | LOR | XOR | AMPERSAND | BAR | IMPLY | EQUIV | BITXOR );
	public final AcslParser.binary_op_return binary_op() throws RecognitionException {
		AcslParser.binary_op_return retval = new AcslParser.binary_op_return();
		retval.start = input.LT(1);

		Object root_0 = null;

		Token set310=null;

		Object set310_tree=null;

		try {
			// AcslParser.g:653:5: ( PLUS | MINUS | STAR | DIVIDE | MOD | LSHIFT | RSHIFT | EQ | NEQ | LTE | GTE | LT | GT | LAND | LOR | XOR | AMPERSAND | BAR | IMPLY | EQUIV | BITXOR )
			// AcslParser.g:
			{
			root_0 = (Object)adaptor.nil();


			set310=input.LT(1);
			if ( input.LA(1)==AMPERSAND||input.LA(1)==BAR||input.LA(1)==BITXOR||input.LA(1)==DIVIDE||(input.LA(1) >= EQ && input.LA(1) <= EQUIV)||(input.LA(1) >= GT && input.LA(1) <= GTE)||input.LA(1)==IMPLY||input.LA(1)==LAND||input.LA(1)==LOR||(input.LA(1) >= LT && input.LA(1) <= LTE)||input.LA(1)==MOD||input.LA(1)==NEQ||input.LA(1)==PLUS||input.LA(1)==STAR||input.LA(1)==XOR||(input.LA(1) >= LSHIFT && input.LA(1) <= MINUS)||input.LA(1)==RSHIFT ) {
				input.consume();
				if ( state.backtracking==0 ) adaptor.addChild(root_0, (Object)adaptor.create(set310));
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
	// $ANTLR end "binary_op"

	// $ANTLR start synpred1_AcslParser
	public final void synpred1_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:76:7: ( function_contract )
		// AcslParser.g:76:7: function_contract
		{
		pushFollow(FOLLOW_function_contract_in_synpred1_AcslParser391);
		function_contract();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred1_AcslParser

	// $ANTLR start synpred10_AcslParser
	public final void synpred10_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:124:7: ( LOOP VARIANT term )
		// AcslParser.g:124:7: LOOP VARIANT term
		{
		match(input,LOOP,FOLLOW_LOOP_in_synpred10_AcslParser816); if (state.failed) return;

		match(input,VARIANT,FOLLOW_VARIANT_in_synpred10_AcslParser818); if (state.failed) return;

		pushFollow(FOLLOW_term_in_synpred10_AcslParser820);
		term();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred10_AcslParser

	// $ANTLR start synpred16_AcslParser
	public final void synpred16_AcslParser_fragment() throws RecognitionException {
		List<Object> list_b=null;
		RuleReturnScope b = null;

		// AcslParser.g:153:30: (b+= named_behavior_block )
		// AcslParser.g:153:30: b+= named_behavior_block
		{
		pushFollow(FOLLOW_named_behavior_block_in_synpred16_AcslParser1044);
		b=named_behavior_block();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred16_AcslParser

	// $ANTLR start synpred17_AcslParser
	public final void synpred17_AcslParser_fragment() throws RecognitionException {
		List<Object> list_c=null;
		RuleReturnScope c = null;

		// AcslParser.g:154:10: (c+= completeness_clause_block )
		// AcslParser.g:154:10: c+= completeness_clause_block
		{
		pushFollow(FOLLOW_completeness_clause_block_in_synpred17_AcslParser1060);
		c=completeness_clause_block();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred17_AcslParser

	// $ANTLR start synpred19_AcslParser
	public final void synpred19_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:165:28: ( completeness_clause_block )
		// AcslParser.g:165:28: completeness_clause_block
		{
		pushFollow(FOLLOW_completeness_clause_block_in_synpred19_AcslParser1119);
		completeness_clause_block();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred19_AcslParser

	// $ANTLR start synpred40_AcslParser
	public final void synpred40_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:225:7: ( variable_ident_base LSQUARE RSQUARE )
		// AcslParser.g:225:7: variable_ident_base LSQUARE RSQUARE
		{
		pushFollow(FOLLOW_variable_ident_base_in_synpred40_AcslParser1594);
		variable_ident_base();
		state._fsp--;
		if (state.failed) return;

		match(input,LSQUARE,FOLLOW_LSQUARE_in_synpred40_AcslParser1596); if (state.failed) return;

		match(input,RSQUARE,FOLLOW_RSQUARE_in_synpred40_AcslParser1598); if (state.failed) return;

		}

	}
	// $ANTLR end synpred40_AcslParser

	// $ANTLR start synpred50_AcslParser
	public final void synpred50_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:281:7: ( event_base PLUS event_base )
		// AcslParser.g:281:7: event_base PLUS event_base
		{
		pushFollow(FOLLOW_event_base_in_synpred50_AcslParser1981);
		event_base();
		state._fsp--;
		if (state.failed) return;

		match(input,PLUS,FOLLOW_PLUS_in_synpred50_AcslParser1983); if (state.failed) return;

		pushFollow(FOLLOW_event_base_in_synpred50_AcslParser1985);
		event_base();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred50_AcslParser

	// $ANTLR start synpred51_AcslParser
	public final void synpred51_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:283:7: ( event_base SUB event_base )
		// AcslParser.g:283:7: event_base SUB event_base
		{
		pushFollow(FOLLOW_event_base_in_synpred51_AcslParser2011);
		event_base();
		state._fsp--;
		if (state.failed) return;

		match(input,SUB,FOLLOW_SUB_in_synpred51_AcslParser2013); if (state.failed) return;

		pushFollow(FOLLOW_event_base_in_synpred51_AcslParser2015);
		event_base();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred51_AcslParser

	// $ANTLR start synpred52_AcslParser
	public final void synpred52_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:285:7: ( event_base AMPERSAND event_base )
		// AcslParser.g:285:7: event_base AMPERSAND event_base
		{
		pushFollow(FOLLOW_event_base_in_synpred52_AcslParser2041);
		event_base();
		state._fsp--;
		if (state.failed) return;

		match(input,AMPERSAND,FOLLOW_AMPERSAND_in_synpred52_AcslParser2043); if (state.failed) return;

		pushFollow(FOLLOW_event_base_in_synpred52_AcslParser2045);
		event_base();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred52_AcslParser

	// $ANTLR start synpred70_AcslParser
	public final void synpred70_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:350:7: ( LCURLY term BAR binders ( SEMICOL term )? RCURLY )
		// AcslParser.g:350:7: LCURLY term BAR binders ( SEMICOL term )? RCURLY
		{
		match(input,LCURLY,FOLLOW_LCURLY_in_synpred70_AcslParser2608); if (state.failed) return;

		pushFollow(FOLLOW_term_in_synpred70_AcslParser2610);
		term();
		state._fsp--;
		if (state.failed) return;

		match(input,BAR,FOLLOW_BAR_in_synpred70_AcslParser2612); if (state.failed) return;

		pushFollow(FOLLOW_binders_in_synpred70_AcslParser2614);
		binders();
		state._fsp--;
		if (state.failed) return;

		// AcslParser.g:350:31: ( SEMICOL term )?
		int alt66=2;
		int LA66_0 = input.LA(1);
		if ( (LA66_0==SEMICOL) ) {
			alt66=1;
		}
		switch (alt66) {
			case 1 :
				// AcslParser.g:350:32: SEMICOL term
				{
				match(input,SEMICOL,FOLLOW_SEMICOL_in_synpred70_AcslParser2617); if (state.failed) return;

				pushFollow(FOLLOW_term_in_synpred70_AcslParser2619);
				term();
				state._fsp--;
				if (state.failed) return;

				}
				break;

		}

		match(input,RCURLY,FOLLOW_RCURLY_in_synpred70_AcslParser2623); if (state.failed) return;

		}

	}
	// $ANTLR end synpred70_AcslParser

	// $ANTLR start synpred71_AcslParser
	public final void synpred71_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:352:7: ( LCURLY term RCURLY )
		// AcslParser.g:352:7: LCURLY term RCURLY
		{
		match(input,LCURLY,FOLLOW_LCURLY_in_synpred71_AcslParser2651); if (state.failed) return;

		pushFollow(FOLLOW_term_in_synpred71_AcslParser2653);
		term();
		state._fsp--;
		if (state.failed) return;

		match(input,RCURLY,FOLLOW_RCURLY_in_synpred71_AcslParser2655); if (state.failed) return;

		}

	}
	// $ANTLR end synpred71_AcslParser

	// $ANTLR start synpred79_AcslParser
	public final void synpred79_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:384:26: ( COMMA assignmentExpression )
		// AcslParser.g:384:26: COMMA assignmentExpression
		{
		match(input,COMMA,FOLLOW_COMMA_in_synpred79_AcslParser2965); if (state.failed) return;

		pushFollow(FOLLOW_assignmentExpression_in_synpred79_AcslParser2967);
		assignmentExpression();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred79_AcslParser

	// $ANTLR start synpred82_AcslParser
	public final void synpred82_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:393:4: ( SIZEOF LPAREN type_expr )
		// AcslParser.g:393:5: SIZEOF LPAREN type_expr
		{
		match(input,SIZEOF,FOLLOW_SIZEOF_in_synpred82_AcslParser3024); if (state.failed) return;

		match(input,LPAREN,FOLLOW_LPAREN_in_synpred82_AcslParser3026); if (state.failed) return;

		pushFollow(FOLLOW_type_expr_in_synpred82_AcslParser3028);
		type_expr();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred82_AcslParser

	// $ANTLR start synpred83_AcslParser
	public final void synpred83_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:395:4: ( SIZEOF unaryExpression )
		// AcslParser.g:395:4: SIZEOF unaryExpression
		{
		match(input,SIZEOF,FOLLOW_SIZEOF_in_synpred83_AcslParser3054); if (state.failed) return;

		pushFollow(FOLLOW_unaryExpression_in_synpred83_AcslParser3056);
		unaryExpression();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred83_AcslParser

	// $ANTLR start synpred86_AcslParser
	public final void synpred86_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:420:4: ( LPAREN type_expr RPAREN )
		// AcslParser.g:420:5: LPAREN type_expr RPAREN
		{
		match(input,LPAREN,FOLLOW_LPAREN_in_synpred86_AcslParser3203); if (state.failed) return;

		pushFollow(FOLLOW_type_expr_in_synpred86_AcslParser3205);
		type_expr();
		state._fsp--;
		if (state.failed) return;

		match(input,RPAREN,FOLLOW_RPAREN_in_synpred86_AcslParser3207); if (state.failed) return;

		}

	}
	// $ANTLR end synpred86_AcslParser

	// $ANTLR start synpred87_AcslParser
	public final void synpred87_AcslParser_fragment() throws RecognitionException {
		ParserRuleReturnScope y =null;


		// AcslParser.g:427:4: ( HASH y= castExpression )
		// AcslParser.g:427:4: HASH y= castExpression
		{
		match(input,HASH,FOLLOW_HASH_in_synpred87_AcslParser3258); if (state.failed) return;

		pushFollow(FOLLOW_castExpression_in_synpred87_AcslParser3262);
		y=castExpression();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred87_AcslParser

	// $ANTLR start synpred105_AcslParser
	public final void synpred105_AcslParser_fragment() throws RecognitionException {
		ParserRuleReturnScope y =null;


		// AcslParser.g:519:6: ( BAR y= exclusiveOrExpression )
		// AcslParser.g:519:6: BAR y= exclusiveOrExpression
		{
		match(input,BAR,FOLLOW_BAR_in_synpred105_AcslParser4074); if (state.failed) return;

		pushFollow(FOLLOW_exclusiveOrExpression_in_synpred105_AcslParser4078);
		y=exclusiveOrExpression();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred105_AcslParser

	// $ANTLR start synpred111_AcslParser
	public final void synpred111_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:592:4: ( unaryExpression ASSIGN )
		// AcslParser.g:592:5: unaryExpression ASSIGN
		{
		pushFollow(FOLLOW_unaryExpression_in_synpred111_AcslParser4498);
		unaryExpression();
		state._fsp--;
		if (state.failed) return;

		match(input,ASSIGN,FOLLOW_ASSIGN_in_synpred111_AcslParser4500); if (state.failed) return;

		}

	}
	// $ANTLR end synpred111_AcslParser

	// $ANTLR start synpred112_AcslParser
	public final void synpred112_AcslParser_fragment() throws RecognitionException {
		// AcslParser.g:596:4: ( conditionalExpression )
		// AcslParser.g:596:4: conditionalExpression
		{
		pushFollow(FOLLOW_conditionalExpression_in_synpred112_AcslParser4543);
		conditionalExpression();
		state._fsp--;
		if (state.failed) return;

		}

	}
	// $ANTLR end synpred112_AcslParser

	// Delegated rules

	public final boolean synpred82_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred82_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred10_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred10_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred105_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred105_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred112_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred112_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred87_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred87_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred51_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred51_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred79_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred79_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred111_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred111_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred52_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred52_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred70_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred70_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred17_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred17_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred19_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred19_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred83_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred83_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred40_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred40_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred71_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred71_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred1_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred1_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred86_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred86_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred16_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred16_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred50_AcslParser() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred50_AcslParser_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}


	protected DFA16 dfa16 = new DFA16(this);
	protected DFA17 dfa17 = new DFA17(this);
	static final String DFA16_eotS =
		"\23\uffff";
	static final String DFA16_eofS =
		"\1\3\22\uffff";
	static final String DFA16_minS =
		"\1\15\2\16\1\uffff\2\76\1\0\1\27\1\0\1\27\1\uffff\1\76\1\0\1\76\1\0\2"+
		"\27\2\0";
	static final String DFA16_maxS =
		"\1\157\2\16\1\uffff\2\174\1\0\1\174\1\0\1\174\1\uffff\1\76\1\0\1\76\1"+
		"\0\2\174\2\0";
	static final String DFA16_acceptS =
		"\3\uffff\1\2\6\uffff\1\1\10\uffff";
	static final String DFA16_specialS =
		"\6\uffff\1\4\1\uffff\1\5\3\uffff\1\3\1\uffff\1\2\2\uffff\1\1\1\0}>";
	static final String[] DFA16_transitionS = {
			"\1\3\13\uffff\1\1\2\uffff\1\2\71\uffff\1\3\30\uffff\1\3",
			"\1\4",
			"\1\5",
			"",
			"\1\7\75\uffff\1\6",
			"\1\11\75\uffff\1\10",
			"\1\uffff",
			"\1\13\144\uffff\1\14",
			"\1\uffff",
			"\1\15\144\uffff\1\16",
			"",
			"\1\17",
			"\1\uffff",
			"\1\20",
			"\1\uffff",
			"\1\13\144\uffff\1\21",
			"\1\15\144\uffff\1\22",
			"\1\uffff",
			"\1\uffff"
	};

	static final short[] DFA16_eot = DFA.unpackEncodedString(DFA16_eotS);
	static final short[] DFA16_eof = DFA.unpackEncodedString(DFA16_eofS);
	static final char[] DFA16_min = DFA.unpackEncodedStringToUnsignedChars(DFA16_minS);
	static final char[] DFA16_max = DFA.unpackEncodedStringToUnsignedChars(DFA16_maxS);
	static final short[] DFA16_accept = DFA.unpackEncodedString(DFA16_acceptS);
	static final short[] DFA16_special = DFA.unpackEncodedString(DFA16_specialS);
	static final short[][] DFA16_transition;

	static {
		int numStates = DFA16_transitionS.length;
		DFA16_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA16_transition[i] = DFA.unpackEncodedString(DFA16_transitionS[i]);
		}
	}

	protected class DFA16 extends DFA {

		public DFA16(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 16;
			this.eot = DFA16_eot;
			this.eof = DFA16_eof;
			this.min = DFA16_min;
			this.max = DFA16_max;
			this.accept = DFA16_accept;
			this.special = DFA16_special;
			this.transition = DFA16_transition;
		}
		@Override
		public String getDescription() {
			return "()* loopback of 154:9: (c+= completeness_clause_block )*";
		}
		@Override
		public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
			TokenStream input = (TokenStream)_input;
			int _s = s;
			switch ( s ) {
					case 0 : 
						int LA16_18 = input.LA(1);
						 
						int index16_18 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred17_AcslParser()) ) {s = 10;}
						else if ( (true) ) {s = 3;}
						 
						input.seek(index16_18);
						if ( s>=0 ) return s;
						break;

					case 1 : 
						int LA16_17 = input.LA(1);
						 
						int index16_17 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred17_AcslParser()) ) {s = 10;}
						else if ( (true) ) {s = 3;}
						 
						input.seek(index16_17);
						if ( s>=0 ) return s;
						break;

					case 2 : 
						int LA16_14 = input.LA(1);
						 
						int index16_14 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred17_AcslParser()) ) {s = 10;}
						else if ( (true) ) {s = 3;}
						 
						input.seek(index16_14);
						if ( s>=0 ) return s;
						break;

					case 3 : 
						int LA16_12 = input.LA(1);
						 
						int index16_12 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred17_AcslParser()) ) {s = 10;}
						else if ( (true) ) {s = 3;}
						 
						input.seek(index16_12);
						if ( s>=0 ) return s;
						break;

					case 4 : 
						int LA16_6 = input.LA(1);
						 
						int index16_6 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred17_AcslParser()) ) {s = 10;}
						else if ( (true) ) {s = 3;}
						 
						input.seek(index16_6);
						if ( s>=0 ) return s;
						break;

					case 5 : 
						int LA16_8 = input.LA(1);
						 
						int index16_8 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred17_AcslParser()) ) {s = 10;}
						else if ( (true) ) {s = 3;}
						 
						input.seek(index16_8);
						if ( s>=0 ) return s;
						break;
			}
			if (state.backtracking>0) {state.failed=true; return -1;}
			NoViableAltException nvae =
				new NoViableAltException(getDescription(), 16, _s, input);
			error(nvae);
			throw nvae;
		}
	}

	static final String DFA17_eotS =
		"\23\uffff";
	static final String DFA17_eofS =
		"\1\3\22\uffff";
	static final String DFA17_minS =
		"\1\15\2\16\1\uffff\2\76\1\0\1\27\1\0\1\27\1\uffff\1\76\1\0\1\76\1\0\2"+
		"\27\2\0";
	static final String DFA17_maxS =
		"\1\157\2\16\1\uffff\2\174\1\0\1\174\1\0\1\174\1\uffff\1\76\1\0\1\76\1"+
		"\0\2\174\2\0";
	static final String DFA17_acceptS =
		"\3\uffff\1\2\6\uffff\1\1\10\uffff";
	static final String DFA17_specialS =
		"\6\uffff\1\4\1\uffff\1\5\3\uffff\1\3\1\uffff\1\2\2\uffff\1\1\1\0}>";
	static final String[] DFA17_transitionS = {
			"\1\3\13\uffff\1\1\2\uffff\1\2\71\uffff\1\3\30\uffff\1\3",
			"\1\4",
			"\1\5",
			"",
			"\1\7\75\uffff\1\6",
			"\1\11\75\uffff\1\10",
			"\1\uffff",
			"\1\13\144\uffff\1\14",
			"\1\uffff",
			"\1\15\144\uffff\1\16",
			"",
			"\1\17",
			"\1\uffff",
			"\1\20",
			"\1\uffff",
			"\1\13\144\uffff\1\21",
			"\1\15\144\uffff\1\22",
			"\1\uffff",
			"\1\uffff"
	};

	static final short[] DFA17_eot = DFA.unpackEncodedString(DFA17_eotS);
	static final short[] DFA17_eof = DFA.unpackEncodedString(DFA17_eofS);
	static final char[] DFA17_min = DFA.unpackEncodedStringToUnsignedChars(DFA17_minS);
	static final char[] DFA17_max = DFA.unpackEncodedStringToUnsignedChars(DFA17_maxS);
	static final short[] DFA17_accept = DFA.unpackEncodedString(DFA17_acceptS);
	static final short[] DFA17_special = DFA.unpackEncodedString(DFA17_specialS);
	static final short[][] DFA17_transition;

	static {
		int numStates = DFA17_transitionS.length;
		DFA17_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA17_transition[i] = DFA.unpackEncodedString(DFA17_transitionS[i]);
		}
	}

	protected class DFA17 extends DFA {

		public DFA17(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 17;
			this.eot = DFA17_eot;
			this.eof = DFA17_eof;
			this.min = DFA17_min;
			this.max = DFA17_max;
			this.accept = DFA17_accept;
			this.special = DFA17_special;
			this.transition = DFA17_transition;
		}
		@Override
		public String getDescription() {
			return "165:28: ( completeness_clause_block )?";
		}
		@Override
		public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
			TokenStream input = (TokenStream)_input;
			int _s = s;
			switch ( s ) {
					case 0 : 
						int LA17_18 = input.LA(1);
						 
						int index17_18 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred19_AcslParser()) ) {s = 10;}
						else if ( (true) ) {s = 3;}
						 
						input.seek(index17_18);
						if ( s>=0 ) return s;
						break;

					case 1 : 
						int LA17_17 = input.LA(1);
						 
						int index17_17 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred19_AcslParser()) ) {s = 10;}
						else if ( (true) ) {s = 3;}
						 
						input.seek(index17_17);
						if ( s>=0 ) return s;
						break;

					case 2 : 
						int LA17_14 = input.LA(1);
						 
						int index17_14 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred19_AcslParser()) ) {s = 10;}
						else if ( (true) ) {s = 3;}
						 
						input.seek(index17_14);
						if ( s>=0 ) return s;
						break;

					case 3 : 
						int LA17_12 = input.LA(1);
						 
						int index17_12 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred19_AcslParser()) ) {s = 10;}
						else if ( (true) ) {s = 3;}
						 
						input.seek(index17_12);
						if ( s>=0 ) return s;
						break;

					case 4 : 
						int LA17_6 = input.LA(1);
						 
						int index17_6 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred19_AcslParser()) ) {s = 10;}
						else if ( (true) ) {s = 3;}
						 
						input.seek(index17_6);
						if ( s>=0 ) return s;
						break;

					case 5 : 
						int LA17_8 = input.LA(1);
						 
						int index17_8 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred19_AcslParser()) ) {s = 10;}
						else if ( (true) ) {s = 3;}
						 
						input.seek(index17_8);
						if ( s>=0 ) return s;
						break;
			}
			if (state.backtracking>0) {state.failed=true; return -1;}
			NoViableAltException nvae =
				new NoViableAltException(getDescription(), 17, _s, input);
			error(nvae);
			throw nvae;
		}
	}

	public static final BitSet FOLLOW_function_contract_in_contract391 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_loop_contract_in_contract415 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LCOMMENT_in_loop_contract448 = new BitSet(new long[]{0x0000800000000000L,0x0000800000001000L});
	public static final BitSet FOLLOW_loop_contract_block_in_loop_contract450 = new BitSet(new long[]{0x0000000000000000L,0x0000800000000000L});
	public static final BitSet FOLLOW_RCOMMENT_in_loop_contract452 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_loop_clause_in_loop_contract_block486 = new BitSet(new long[]{0x0000800000000002L,0x0000000000001000L});
	public static final BitSet FOLLOW_loop_behavior_in_loop_contract_block491 = new BitSet(new long[]{0x0000800000000002L,0x0000000000001000L});
	public static final BitSet FOLLOW_loop_variant_in_loop_contract_block496 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_loop_invariant_in_loop_clause539 = new BitSet(new long[]{0x0000000000000000L,0x1000000000000000L});
	public static final BitSet FOLLOW_SEMICOL_in_loop_clause541 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_loop_assigns_in_loop_clause564 = new BitSet(new long[]{0x0000000000000000L,0x1000000000000000L});
	public static final BitSet FOLLOW_SEMICOL_in_loop_clause566 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_loop_allocation_in_loop_clause589 = new BitSet(new long[]{0x0000000000000000L,0x1000000000000000L});
	public static final BitSet FOLLOW_SEMICOL_in_loop_clause591 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LOOP_in_loop_invariant623 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
	public static final BitSet FOLLOW_INVARIANT_in_loop_invariant625 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_loop_invariant627 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LOOP_in_loop_assigns659 = new BitSet(new long[]{0x0000000000000200L});
	public static final BitSet FOLLOW_ASSIGNS_in_loop_assigns661 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_argumentExpressionList_in_loop_assigns663 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LOOP_in_loop_allocation695 = new BitSet(new long[]{0x0000000000000010L});
	public static final BitSet FOLLOW_ALLOC_in_loop_allocation697 = new BitSet(new long[]{0x4001521001800020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_argumentExpressionList_in_loop_allocation699 = new BitSet(new long[]{0x0000000000800002L});
	public static final BitSet FOLLOW_COMMA_in_loop_allocation702 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_loop_allocation704 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LOOP_in_loop_allocation732 = new BitSet(new long[]{0x0002000000000000L});
	public static final BitSet FOLLOW_FREES_in_loop_allocation734 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_argumentExpressionList_in_loop_allocation736 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FOR_in_loop_behavior768 = new BitSet(new long[]{0x4000000000400000L});
	public static final BitSet FOLLOW_id_list_in_loop_behavior772 = new BitSet(new long[]{0x0000000000400000L});
	public static final BitSet FOLLOW_COLON_in_loop_behavior774 = new BitSet(new long[]{0x0000000000000002L,0x0000000000001000L});
	public static final BitSet FOLLOW_loop_clause_in_loop_behavior778 = new BitSet(new long[]{0x0000000000000002L,0x0000000000001000L});
	public static final BitSet FOLLOW_LOOP_in_loop_variant816 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000400L});
	public static final BitSet FOLLOW_VARIANT_in_loop_variant818 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_loop_variant820 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LOOP_in_loop_variant843 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000400L});
	public static final BitSet FOLLOW_VARIANT_in_loop_variant845 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_loop_variant847 = new BitSet(new long[]{0x0000800000000000L});
	public static final BitSet FOLLOW_FOR_in_loop_variant849 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_ID_in_loop_variant851 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LCOMMENT_in_function_contract887 = new BitSet(new long[]{0x004200401A002210L,0x0048A00000400000L,0x2000000000000000L});
	public static final BitSet FOLLOW_pure_function_in_function_contract889 = new BitSet(new long[]{0x004200401A002210L,0x0048800000400000L,0x2000000000000000L});
	public static final BitSet FOLLOW_full_contract_block_in_function_contract892 = new BitSet(new long[]{0x0000000000000000L,0x0000800000000000L});
	public static final BitSet FOLLOW_RCOMMENT_in_function_contract894 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_PURE_in_pure_function928 = new BitSet(new long[]{0x0000000000000000L,0x1000000000000000L});
	public static final BitSet FOLLOW_SEMICOL_in_pure_function930 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_function_clause_in_full_contract_block963 = new BitSet(new long[]{0x004200401A002212L,0x0048000000400000L,0x2000000000000000L});
	public static final BitSet FOLLOW_contract_block_in_full_contract_block970 = new BitSet(new long[]{0x0000000012002002L,0x0000000000400000L});
	public static final BitSet FOLLOW_completeness_clause_block_in_full_contract_block985 = new BitSet(new long[]{0x0000000012000002L});
	public static final BitSet FOLLOW_function_clause_in_partial_contract_block1037 = new BitSet(new long[]{0x004200401A002212L,0x0048000000000000L,0x2000000000000000L});
	public static final BitSet FOLLOW_named_behavior_block_in_partial_contract_block1044 = new BitSet(new long[]{0x0000000012002002L});
	public static final BitSet FOLLOW_completeness_clause_block_in_partial_contract_block1060 = new BitSet(new long[]{0x0000000012000002L});
	public static final BitSet FOLLOW_mpi_collective_block_in_contract_block1109 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_named_behavior_block_in_contract_block1117 = new BitSet(new long[]{0x0000000012000002L});
	public static final BitSet FOLLOW_completeness_clause_block_in_contract_block1119 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_requires_clause_in_function_clause1137 = new BitSet(new long[]{0x0000000000000000L,0x1000000000000000L});
	public static final BitSet FOLLOW_SEMICOL_in_function_clause1139 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_terminates_clause_in_function_clause1154 = new BitSet(new long[]{0x0000000000000000L,0x1000000000000000L});
	public static final BitSet FOLLOW_SEMICOL_in_function_clause1156 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_simple_clause_in_function_clause1171 = new BitSet(new long[]{0x0000000000000000L,0x1000000000000000L});
	public static final BitSet FOLLOW_SEMICOL_in_function_clause1173 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_named_behavior_in_named_behavior_block1198 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_completeness_clause_in_completeness_clause_block1223 = new BitSet(new long[]{0x0000000000000000L,0x1000000000000000L});
	public static final BitSet FOLLOW_SEMICOL_in_completeness_clause_block1225 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REQUIRES_in_requires_clause1250 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_requires_clause1252 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_TEMINATES_in_terminates_clause1277 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_terminates_clause1279 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_binder_in_binders1341 = new BitSet(new long[]{0x0000000000800002L});
	public static final BitSet FOLLOW_COMMA_in_binders1344 = new BitSet(new long[]{0x4000200100110000L,0x8010000000000803L,0x0000000000000800L});
	public static final BitSet FOLLOW_binder_in_binders1346 = new BitSet(new long[]{0x0000000000800002L});
	public static final BitSet FOLLOW_type_expr_in_binder1381 = new BitSet(new long[]{0x4000000000000000L,0x0000000000004000L,0x0000000000000002L});
	public static final BitSet FOLLOW_variable_ident_in_binder1383 = new BitSet(new long[]{0x0000000000800002L});
	public static final BitSet FOLLOW_COMMA_in_binder1386 = new BitSet(new long[]{0x4000000000000000L,0x0000000000004000L,0x0000000000000002L});
	public static final BitSet FOLLOW_variable_ident_in_binder1388 = new BitSet(new long[]{0x0000000000800002L});
	public static final BitSet FOLLOW_logic_type_expr_in_type_expr1425 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_c_type_in_type_expr1440 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_built_in_logic_type_in_logic_type_expr1464 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_logic_type_expr1479 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STAR_in_variable_ident1569 = new BitSet(new long[]{0x4000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_variable_ident_base_in_variable_ident1571 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_variable_ident_base_in_variable_ident1594 = new BitSet(new long[]{0x0000000000000000L,0x0000000000008000L});
	public static final BitSet FOLLOW_LSQUARE_in_variable_ident1596 = new BitSet(new long[]{0x0000000000000000L,0x0200000000000000L});
	public static final BitSet FOLLOW_RSQUARE_in_variable_ident1598 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_variable_ident_base_in_variable_ident1621 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_variable_ident_base1653 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_variable_ident_base1672 = new BitSet(new long[]{0x4000000000000000L,0x0000000000004000L,0x0000000000000002L});
	public static final BitSet FOLLOW_variable_ident_in_variable_ident_base1674 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_variable_ident_base1676 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_GUARDS_in_guards_clause1706 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_guards_clause1708 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_assigns_clause_in_simple_clause1732 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ensures_clause_in_simple_clause1740 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_allocation_clause_in_simple_clause1749 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_reads_clause_in_simple_clause1757 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_depends_clause_in_simple_clause1765 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_guards_clause_in_simple_clause1773 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSIGNS_in_assigns_clause1790 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_argumentExpressionList_in_assigns_clause1792 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ENSURES_in_ensures_clause1816 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_ensures_clause1818 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ALLOC_in_allocation_clause1842 = new BitSet(new long[]{0x4001521001800020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_argumentExpressionList_in_allocation_clause1844 = new BitSet(new long[]{0x0000000000800002L});
	public static final BitSet FOLLOW_COMMA_in_allocation_clause1847 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_allocation_clause1849 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FREES_in_allocation_clause1869 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_argumentExpressionList_in_allocation_clause1871 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_READS_in_reads_clause1895 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_argumentExpressionList_in_reads_clause1897 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DEPENDS_in_depends_clause1922 = new BitSet(new long[]{0x0000000000080040L,0x0006000080004000L,0x0000000000002000L});
	public static final BitSet FOLLOW_event_list_in_depends_clause1924 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_event_in_event_list1948 = new BitSet(new long[]{0x0000000000800002L});
	public static final BitSet FOLLOW_COMMA_in_event_list1951 = new BitSet(new long[]{0x0000000000080040L,0x0006000080004000L,0x0000000000002000L});
	public static final BitSet FOLLOW_event_in_event_list1953 = new BitSet(new long[]{0x0000000000800002L});
	public static final BitSet FOLLOW_event_base_in_event1981 = new BitSet(new long[]{0x0000000000000000L,0x0000080000000000L});
	public static final BitSet FOLLOW_PLUS_in_event1983 = new BitSet(new long[]{0x0000000000080040L,0x0006000080004000L,0x0000000000002000L});
	public static final BitSet FOLLOW_event_base_in_event1985 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_event_base_in_event2011 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_SUB_in_event2013 = new BitSet(new long[]{0x0000000000080040L,0x0006000080004000L,0x0000000000002000L});
	public static final BitSet FOLLOW_event_base_in_event2015 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_event_base_in_event2041 = new BitSet(new long[]{0x0000000000000020L});
	public static final BitSet FOLLOW_AMPERSAND_in_event2043 = new BitSet(new long[]{0x0000000000080040L,0x0006000080004000L,0x0000000000002000L});
	public static final BitSet FOLLOW_event_base_in_event2045 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_event_base_in_event2071 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_READ_in_event_base2104 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_event_base2106 = new BitSet(new long[]{0x4001521001000020L,0x09A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_argumentExpressionList_in_event_base2108 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_event_base2110 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_WRITE_in_event_base2134 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_event_base2136 = new BitSet(new long[]{0x4001521001000020L,0x09A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_argumentExpressionList_in_event_base2138 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_event_base2140 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REACH_in_event_base2164 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_event_base2166 = new BitSet(new long[]{0x4001521001000020L,0x09A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_argumentExpressionList_in_event_base2168 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_event_base2170 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_CALL_in_event_base2194 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_event_base2196 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_ID_in_event_base2198 = new BitSet(new long[]{0x0000000000800000L,0x0100000000000000L});
	public static final BitSet FOLLOW_COMMA_in_event_base2201 = new BitSet(new long[]{0x4001521001000020L,0x09A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_argumentExpressionList_in_event_base2203 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_event_base2207 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NOACT_in_event_base2234 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ANYACT_in_event_base2256 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_event_base2278 = new BitSet(new long[]{0x0000000000080040L,0x0006000080004000L,0x0000000000002000L});
	public static final BitSet FOLLOW_event_in_event_base2280 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_event_base2282 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MPI_COLLECTIVE_in_mpi_collective_block2317 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_mpi_collective_block2319 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_ID_in_mpi_collective_block2321 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_COMMA_in_mpi_collective_block2323 = new BitSet(new long[]{0x0000000000220000L,0x0000040000000000L});
	public static final BitSet FOLLOW_mpi_collective_kind_in_mpi_collective_block2327 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_mpi_collective_block2330 = new BitSet(new long[]{0x0000000000400000L});
	public static final BitSet FOLLOW_COLON_in_mpi_collective_block2332 = new BitSet(new long[]{0x004200401A002210L,0x0048000000000000L,0x2000000000000000L});
	public static final BitSet FOLLOW_partial_contract_block_in_mpi_collective_block2342 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BEHAVIOR_in_named_behavior2377 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_ID_in_named_behavior2379 = new BitSet(new long[]{0x0000000000400000L});
	public static final BitSet FOLLOW_COLON_in_named_behavior2381 = new BitSet(new long[]{0x0042004008000610L,0x0048000000000000L});
	public static final BitSet FOLLOW_behavior_body_in_named_behavior2383 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_behavior_clause_in_behavior_body2412 = new BitSet(new long[]{0x0000000000000000L,0x1000000000000000L});
	public static final BitSet FOLLOW_SEMICOL_in_behavior_body2414 = new BitSet(new long[]{0x0042004008000612L,0x0048000000000000L});
	public static final BitSet FOLLOW_assumes_clause_in_behavior_clause2443 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_requires_clause_in_behavior_clause2452 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_simple_clause_in_behavior_clause2460 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ASSUMES_in_assumes_clause2477 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_assumes_clause2479 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_COMPLETE_in_completeness_clause2503 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_BEHAVIORS_in_completeness_clause2505 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_id_list_in_completeness_clause2507 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_DISJOINT_in_completeness_clause2522 = new BitSet(new long[]{0x0000000000004000L});
	public static final BitSet FOLLOW_BEHAVIORS_in_completeness_clause2524 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_id_list_in_completeness_clause2526 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_id_list2556 = new BitSet(new long[]{0x0000000000800002L});
	public static final BitSet FOLLOW_COMMA_in_id_list2559 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_ID_in_id_list2561 = new BitSet(new long[]{0x0000000000800002L});
	public static final BitSet FOLLOW_constant_in_primaryExpression2587 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ID_in_primaryExpression2595 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_STRING_LITERAL_in_primaryExpression2600 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LCURLY_in_primaryExpression2608 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_primaryExpression2610 = new BitSet(new long[]{0x0000000000001000L});
	public static final BitSet FOLLOW_BAR_in_primaryExpression2612 = new BitSet(new long[]{0x4000200100110000L,0x8010000000000803L,0x0000000000000800L});
	public static final BitSet FOLLOW_binders_in_primaryExpression2614 = new BitSet(new long[]{0x0000000000000000L,0x1001000000000000L});
	public static final BitSet FOLLOW_SEMICOL_in_primaryExpression2617 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_primaryExpression2619 = new BitSet(new long[]{0x0000000000000000L,0x0001000000000000L});
	public static final BitSet FOLLOW_RCURLY_in_primaryExpression2623 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LCURLY_in_primaryExpression2651 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_primaryExpression2653 = new BitSet(new long[]{0x0000000000000000L,0x0001000000000000L});
	public static final BitSet FOLLOW_RCURLY_in_primaryExpression2655 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_primaryExpression2675 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_primaryExpression2677 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_primaryExpression2679 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_mpi_expression_in_primaryExpression2699 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_REMOTE_ACCESS_in_primaryExpression2715 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_primaryExpression2717 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_ID_in_primaryExpression2721 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_COMMA_in_primaryExpression2723 = new BitSet(new long[]{0x4000501000000000L,0x08A000061FA04204L,0x0000000001000024L});
	public static final BitSet FOLLOW_primaryExpression_in_primaryExpression2727 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_primaryExpression2729 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_primaryExpression_in_postfixExpression2761 = new BitSet(new long[]{0x0000000040000082L,0x000000000000C000L});
	public static final BitSet FOLLOW_LSQUARE_in_postfixExpression2778 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_postfixExpression2780 = new BitSet(new long[]{0x0000000000000000L,0x0200000000000000L});
	public static final BitSet FOLLOW_RSQUARE_in_postfixExpression2782 = new BitSet(new long[]{0x0000000040000082L,0x000000000000C000L});
	public static final BitSet FOLLOW_LPAREN_in_postfixExpression2856 = new BitSet(new long[]{0x4001521001000020L,0x09A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_argumentExpressionList_in_postfixExpression2858 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_postfixExpression2860 = new BitSet(new long[]{0x0000000040000082L,0x000000000000C000L});
	public static final BitSet FOLLOW_DOT_in_postfixExpression2891 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_ID_in_postfixExpression2893 = new BitSet(new long[]{0x0000000040000082L,0x000000000000C000L});
	public static final BitSet FOLLOW_ARROW_in_postfixExpression2916 = new BitSet(new long[]{0x4000000000000000L});
	public static final BitSet FOLLOW_ID_in_postfixExpression2918 = new BitSet(new long[]{0x0000000040000082L,0x000000000000C000L});
	public static final BitSet FOLLOW_assignmentExpression_in_argumentExpressionList2962 = new BitSet(new long[]{0x0000000000800002L});
	public static final BitSet FOLLOW_COMMA_in_argumentExpressionList2965 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_assignmentExpression_in_argumentExpressionList2967 = new BitSet(new long[]{0x0000000000800002L});
	public static final BitSet FOLLOW_postfixExpression_in_unaryExpression2994 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unary_op_in_unaryExpression2999 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_castExpression_in_unaryExpression3001 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SIZEOF_in_unaryExpression3032 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_unaryExpression3034 = new BitSet(new long[]{0x4000200100110000L,0x8010000000000803L,0x0000000000000800L});
	public static final BitSet FOLLOW_type_expr_in_unaryExpression3036 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_unaryExpression3038 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SIZEOF_in_unaryExpression3054 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_unaryExpression_in_unaryExpression3056 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_UNION_in_unaryExpression3077 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_unaryExpression3079 = new BitSet(new long[]{0x4001521001000020L,0x09A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_argumentExpressionList_in_unaryExpression3081 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_unaryExpression3083 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INTER_in_unaryExpression3107 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_unaryExpression3109 = new BitSet(new long[]{0x4001521001000020L,0x09A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_argumentExpressionList_in_unaryExpression3111 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_unaryExpression3113 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_VALID_in_unaryExpression3137 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_unaryExpression3139 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_unaryExpression3141 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_unaryExpression3143 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_castExpression3213 = new BitSet(new long[]{0x4000200100110000L,0x8010000000000803L,0x0000000000000800L});
	public static final BitSet FOLLOW_type_expr_in_castExpression3215 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_castExpression3217 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_castExpression_in_castExpression3219 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unaryExpression_in_castExpression3237 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_castExpression_in_remoteExpression3248 = new BitSet(new long[]{0x0080000000000002L});
	public static final BitSet FOLLOW_HASH_in_remoteExpression3258 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_castExpression_in_remoteExpression3262 = new BitSet(new long[]{0x0080000000000002L});
	public static final BitSet FOLLOW_remoteExpression_in_multiplicativeExpression3304 = new BitSet(new long[]{0x0000000020000002L,0x0000000000100000L,0x0000000000000002L});
	public static final BitSet FOLLOW_STAR_in_multiplicativeExpression3314 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_remoteExpression_in_multiplicativeExpression3318 = new BitSet(new long[]{0x0000000020000002L,0x0000000000100000L,0x0000000000000002L});
	public static final BitSet FOLLOW_DIVIDE_in_multiplicativeExpression3344 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_remoteExpression_in_multiplicativeExpression3348 = new BitSet(new long[]{0x0000000020000002L,0x0000000000100000L,0x0000000000000002L});
	public static final BitSet FOLLOW_MOD_in_multiplicativeExpression3377 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_remoteExpression_in_multiplicativeExpression3381 = new BitSet(new long[]{0x0000000020000002L,0x0000000000100000L,0x0000000000000002L});
	public static final BitSet FOLLOW_multiplicativeExpression_in_additiveExpression3423 = new BitSet(new long[]{0x0000000000000002L,0x0000080000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_PLUS_in_additiveExpression3440 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_multiplicativeExpression_in_additiveExpression3444 = new BitSet(new long[]{0x0000000000000002L,0x0000080000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_SUB_in_additiveExpression3484 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_multiplicativeExpression_in_additiveExpression3488 = new BitSet(new long[]{0x0000000000000002L,0x0000080000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_additiveExpression_in_rangeExpression3542 = new BitSet(new long[]{0x0000000080000002L});
	public static final BitSet FOLLOW_DOTDOT_in_rangeExpression3557 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_additiveExpression_in_rangeExpression3561 = new BitSet(new long[]{0x0080000000000002L});
	public static final BitSet FOLLOW_HASH_in_rangeExpression3595 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_additiveExpression_in_rangeExpression3599 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_rangeExpression_in_shiftExpression3660 = new BitSet(new long[]{0x0000000000000002L,0x6000000000000000L});
	public static final BitSet FOLLOW_SHIFTLEFT_in_shiftExpression3677 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_rangeExpression_in_shiftExpression3681 = new BitSet(new long[]{0x0000000000000002L,0x6000000000000000L});
	public static final BitSet FOLLOW_SHIFTRIGHT_in_shiftExpression3721 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_rangeExpression_in_shiftExpression3725 = new BitSet(new long[]{0x0000000000000002L,0x6000000000000000L});
	public static final BitSet FOLLOW_shiftExpression_in_relationalExpression3779 = new BitSet(new long[]{0x0030000000000002L,0x0000000000030000L});
	public static final BitSet FOLLOW_relationalOperator_in_relationalExpression3792 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_shiftExpression_in_relationalExpression3796 = new BitSet(new long[]{0x0030000000000002L,0x0000000000030000L});
	public static final BitSet FOLLOW_relationalExpression_in_equalityExpression3864 = new BitSet(new long[]{0x0000008000000002L,0x0000000020000000L});
	public static final BitSet FOLLOW_equalityOperator_in_equalityExpression3877 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_relationalExpression_in_equalityExpression3881 = new BitSet(new long[]{0x0000008000000002L,0x0000000020000000L});
	public static final BitSet FOLLOW_equalityExpression_in_andExpression3940 = new BitSet(new long[]{0x0000000000000022L});
	public static final BitSet FOLLOW_AMPERSAND_in_andExpression3953 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_equalityExpression_in_andExpression3957 = new BitSet(new long[]{0x0000000000000022L});
	public static final BitSet FOLLOW_andExpression_in_exclusiveOrExpression4000 = new BitSet(new long[]{0x0000000000008002L});
	public static final BitSet FOLLOW_BITXOR_in_exclusiveOrExpression4013 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_andExpression_in_exclusiveOrExpression4017 = new BitSet(new long[]{0x0000000000008002L});
	public static final BitSet FOLLOW_exclusiveOrExpression_in_inclusiveOrExpression4061 = new BitSet(new long[]{0x0000000000001002L});
	public static final BitSet FOLLOW_BAR_in_inclusiveOrExpression4074 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_exclusiveOrExpression_in_inclusiveOrExpression4078 = new BitSet(new long[]{0x0000000000001002L});
	public static final BitSet FOLLOW_inclusiveOrExpression_in_logicalAndExpression4122 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000080L});
	public static final BitSet FOLLOW_LAND_in_logicalAndExpression4135 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_inclusiveOrExpression_in_logicalAndExpression4139 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000080L});
	public static final BitSet FOLLOW_logicalAndExpression_in_logicalOrExpression4183 = new BitSet(new long[]{0x0000000000000002L,0x0000000000002000L});
	public static final BitSet FOLLOW_LOR_in_logicalOrExpression4196 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_logicalAndExpression_in_logicalOrExpression4200 = new BitSet(new long[]{0x0000000000000002L,0x0000000000002000L});
	public static final BitSet FOLLOW_logicalOrExpression_in_logicalImpliesExpression4245 = new BitSet(new long[]{0x8000000000000002L});
	public static final BitSet FOLLOW_IMPLY_in_logicalImpliesExpression4258 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_logicalOrExpression_in_logicalImpliesExpression4262 = new BitSet(new long[]{0x8000000000000002L});
	public static final BitSet FOLLOW_logicalImpliesExpression_in_conditionalExpression4308 = new BitSet(new long[]{0x0000000000000002L,0x0000400000000000L});
	public static final BitSet FOLLOW_QUESTION_in_conditionalExpression4324 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_conditionalExpression4326 = new BitSet(new long[]{0x0000000000400000L});
	public static final BitSet FOLLOW_COLON_in_conditionalExpression4328 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_conditionalExpression_in_conditionalExpression4330 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifier_in_quantifierExpression4429 = new BitSet(new long[]{0x4000200100110000L,0x8010000000000803L,0x0000000000000800L});
	public static final BitSet FOLLOW_binders_in_quantifierExpression4431 = new BitSet(new long[]{0x0000000000000000L,0x1000000000000000L});
	public static final BitSet FOLLOW_SEMICOL_in_quantifierExpression4433 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_assignmentExpression_in_quantifierExpression4435 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unaryExpression_in_assignmentExpression4507 = new BitSet(new long[]{0x0000000000000100L});
	public static final BitSet FOLLOW_ASSIGN_in_assignmentExpression4509 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_assignmentExpression_in_assignmentExpression4511 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_conditionalExpression_in_assignmentExpression4543 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_quantifierExpression_in_assignmentExpression4548 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_assignmentExpression_in_term4561 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_conditionalExpression_in_constantExpression4580 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_INTEGER_CONSTANT_in_constant4592 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FLOATING_CONSTANT_in_constant4597 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_CHARACTER_CONSTANT_in_constant4602 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_TRUE_in_constant4607 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_FALSE_in_constant4611 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_RESULT_in_constant4615 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NOTHING_in_constant4619 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_ELLIPSIS_in_constant4623 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SELF_in_constant4631 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_NULL_in_constant4635 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_mpi_constant_in_constant4643 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MPI_EMPTY_IN_in_mpi_expression4667 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_mpi_expression4669 = new BitSet(new long[]{0x4000501000000000L,0x08A000061FA04204L,0x0000000001000024L});
	public static final BitSet FOLLOW_primaryExpression_in_mpi_expression4671 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_mpi_expression4673 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MPI_EMPTY_OUT_in_mpi_expression4695 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_mpi_expression4697 = new BitSet(new long[]{0x4000501000000000L,0x08A000061FA04204L,0x0000000001000024L});
	public static final BitSet FOLLOW_primaryExpression_in_mpi_expression4699 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_mpi_expression4701 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MPI_AGREE_in_mpi_expression4723 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_mpi_expression4725 = new BitSet(new long[]{0x4000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_variable_ident_base_in_mpi_expression4729 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_mpi_expression4731 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MPI_REGION_in_mpi_expression4757 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_mpi_expression4759 = new BitSet(new long[]{0x4000501000000000L,0x08A000061FA04204L,0x0000000001000024L});
	public static final BitSet FOLLOW_primaryExpression_in_mpi_expression4763 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_COMMA_in_mpi_expression4765 = new BitSet(new long[]{0x4000501000000000L,0x08A000061FA04204L,0x0000000001000024L});
	public static final BitSet FOLLOW_primaryExpression_in_mpi_expression4769 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_COMMA_in_mpi_expression4771 = new BitSet(new long[]{0x4000501000000000L,0x08A000061FA04204L,0x0000000001000024L});
	public static final BitSet FOLLOW_primaryExpression_in_mpi_expression4775 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_mpi_expression4777 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_MPI_EQUALS_in_mpi_expression4806 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_mpi_expression4808 = new BitSet(new long[]{0x4000501000000000L,0x08A000061FA04204L,0x0000000001000024L});
	public static final BitSet FOLLOW_primaryExpression_in_mpi_expression4812 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_COMMA_in_mpi_expression4814 = new BitSet(new long[]{0x4000501000000000L,0x08A000061FA04204L,0x0000000001000024L});
	public static final BitSet FOLLOW_primaryExpression_in_mpi_expression4818 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_COMMA_in_mpi_expression4820 = new BitSet(new long[]{0x4000501000000000L,0x08A000061FA04204L,0x0000000001000024L});
	public static final BitSet FOLLOW_primaryExpression_in_mpi_expression4824 = new BitSet(new long[]{0x0000000000800000L});
	public static final BitSet FOLLOW_COMMA_in_mpi_expression4826 = new BitSet(new long[]{0x4000501000000000L,0x08A000061FA04204L,0x0000000001000024L});
	public static final BitSet FOLLOW_primaryExpression_in_mpi_expression4830 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_mpi_expression4832 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_function_contract_in_synpred1_AcslParser391 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LOOP_in_synpred10_AcslParser816 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000400L});
	public static final BitSet FOLLOW_VARIANT_in_synpred10_AcslParser818 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_synpred10_AcslParser820 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_named_behavior_block_in_synpred16_AcslParser1044 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_completeness_clause_block_in_synpred17_AcslParser1060 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_completeness_clause_block_in_synpred19_AcslParser1119 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_variable_ident_base_in_synpred40_AcslParser1594 = new BitSet(new long[]{0x0000000000000000L,0x0000000000008000L});
	public static final BitSet FOLLOW_LSQUARE_in_synpred40_AcslParser1596 = new BitSet(new long[]{0x0000000000000000L,0x0200000000000000L});
	public static final BitSet FOLLOW_RSQUARE_in_synpred40_AcslParser1598 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_event_base_in_synpred50_AcslParser1981 = new BitSet(new long[]{0x0000000000000000L,0x0000080000000000L});
	public static final BitSet FOLLOW_PLUS_in_synpred50_AcslParser1983 = new BitSet(new long[]{0x0000000000080040L,0x0006000080004000L,0x0000000000002000L});
	public static final BitSet FOLLOW_event_base_in_synpred50_AcslParser1985 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_event_base_in_synpred51_AcslParser2011 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_SUB_in_synpred51_AcslParser2013 = new BitSet(new long[]{0x0000000000080040L,0x0006000080004000L,0x0000000000002000L});
	public static final BitSet FOLLOW_event_base_in_synpred51_AcslParser2015 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_event_base_in_synpred52_AcslParser2041 = new BitSet(new long[]{0x0000000000000020L});
	public static final BitSet FOLLOW_AMPERSAND_in_synpred52_AcslParser2043 = new BitSet(new long[]{0x0000000000080040L,0x0006000080004000L,0x0000000000002000L});
	public static final BitSet FOLLOW_event_base_in_synpred52_AcslParser2045 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LCURLY_in_synpred70_AcslParser2608 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_synpred70_AcslParser2610 = new BitSet(new long[]{0x0000000000001000L});
	public static final BitSet FOLLOW_BAR_in_synpred70_AcslParser2612 = new BitSet(new long[]{0x4000200100110000L,0x8010000000000803L,0x0000000000000800L});
	public static final BitSet FOLLOW_binders_in_synpred70_AcslParser2614 = new BitSet(new long[]{0x0000000000000000L,0x1001000000000000L});
	public static final BitSet FOLLOW_SEMICOL_in_synpred70_AcslParser2617 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_synpred70_AcslParser2619 = new BitSet(new long[]{0x0000000000000000L,0x0001000000000000L});
	public static final BitSet FOLLOW_RCURLY_in_synpred70_AcslParser2623 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LCURLY_in_synpred71_AcslParser2651 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_term_in_synpred71_AcslParser2653 = new BitSet(new long[]{0x0000000000000000L,0x0001000000000000L});
	public static final BitSet FOLLOW_RCURLY_in_synpred71_AcslParser2655 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_COMMA_in_synpred79_AcslParser2965 = new BitSet(new long[]{0x4001521001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_assignmentExpression_in_synpred79_AcslParser2967 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SIZEOF_in_synpred82_AcslParser3024 = new BitSet(new long[]{0x0000000000000000L,0x0000000000004000L});
	public static final BitSet FOLLOW_LPAREN_in_synpred82_AcslParser3026 = new BitSet(new long[]{0x4000200100110000L,0x8010000000000803L,0x0000000000000800L});
	public static final BitSet FOLLOW_type_expr_in_synpred82_AcslParser3028 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_SIZEOF_in_synpred83_AcslParser3054 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_unaryExpression_in_synpred83_AcslParser3056 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_LPAREN_in_synpred86_AcslParser3203 = new BitSet(new long[]{0x4000200100110000L,0x8010000000000803L,0x0000000000000800L});
	public static final BitSet FOLLOW_type_expr_in_synpred86_AcslParser3205 = new BitSet(new long[]{0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_RPAREN_in_synpred86_AcslParser3207 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_HASH_in_synpred87_AcslParser3258 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_castExpression_in_synpred87_AcslParser3262 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_BAR_in_synpred105_AcslParser4074 = new BitSet(new long[]{0x4000501001000020L,0x08A008071FA0420CL,0x0010000001000267L});
	public static final BitSet FOLLOW_exclusiveOrExpression_in_synpred105_AcslParser4078 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unaryExpression_in_synpred111_AcslParser4498 = new BitSet(new long[]{0x0000000000000100L});
	public static final BitSet FOLLOW_ASSIGN_in_synpred111_AcslParser4500 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_conditionalExpression_in_synpred112_AcslParser4543 = new BitSet(new long[]{0x0000000000000002L});
}
