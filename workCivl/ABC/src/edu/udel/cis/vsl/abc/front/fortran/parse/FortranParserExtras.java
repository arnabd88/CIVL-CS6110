package edu.udel.cis.vsl.abc.front.fortran.parse;
import edu.udel.cis.vsl.abc.front.fortran.parse.IActionEnums;

// $ANTLR 3.5.2 FortranParserExtras.g 2016-04-11 02:07:00

import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;

/**
 * FortranParserExtras.g - this file is needed because adding more rules to FortranParser08
 * currently will cause javac to fail with a "Code too large" error.  Removing some of
 * the rules to an inherited grammar is a workaround to the problem.
 */
@SuppressWarnings("all")
public class FortranParserExtras extends AbstractFortranParser {
	public static final String[] tokenNames = new String[] {
		"<invalid>", "<EOR>", "<DOWN>", "<UP>", "Alphanumeric_Character", "BINARY_CONSTANT", 
		"CONTINUE_CHAR", "DQ_Rep_Char", "Digit", "Digit_String", "HEX_CONSTANT", 
		"LINE_COMMENT", "Letter", "MISC_CHAR", "OCTAL_CONSTANT", "PREPROCESS_LINE", 
		"Rep_Char", "SQ_Rep_Char", "Special_Character", "T_ABSTRACT", "T_ACQUIRED_LOCK", 
		"T_ALL", "T_ALLOCATABLE", "T_ALLOCATE", "T_ALLOCATE_STMT_1", "T_AND", 
		"T_ARITHMETIC_IF_STMT", "T_ASSIGN", "T_ASSIGNMENT", "T_ASSIGNMENT_STMT", 
		"T_ASSOCIATE", "T_ASTERISK", "T_ASYNCHRONOUS", "T_AT", "T_BACKSPACE", 
		"T_BEGIN_KEYWORDS", "T_BIND", "T_BLOCK", "T_BLOCKDATA", "T_CALL", "T_CASE", 
		"T_CHARACTER", "T_CHAR_CONSTANT", "T_CHAR_STRING_EDIT_DESC", "T_CLASS", 
		"T_CLOSE", "T_CODIMENSION", "T_COLON", "T_COLON_COLON", "T_COMMA", "T_COMMON", 
		"T_COMPLEX", "T_CONCURRENT", "T_CONTAINS", "T_CONTIGUOUS", "T_CONTINUE", 
		"T_CONTROL_EDIT_DESC", "T_COPOINTER", "T_COTARGET", "T_CRITICAL", "T_CYCLE", 
		"T_DATA", "T_DATA_EDIT_DESC", "T_DEALLOCATE", "T_DEFAULT", "T_DEFERRED", 
		"T_DEFINED_OP", "T_DIGIT_STRING", "T_DIMENSION", "T_DO", "T_DOUBLE", "T_DOUBLECOMPLEX", 
		"T_DOUBLEPRECISION", "T_EDIT_DESC_MISC", "T_ELEMENTAL", "T_ELSE", "T_ELSEIF", 
		"T_ELSEWHERE", "T_END", "T_ENDASSOCIATE", "T_ENDBLOCK", "T_ENDBLOCKDATA", 
		"T_ENDCRITICAL", "T_ENDDO", "T_ENDENUM", "T_ENDFILE", "T_ENDFORALL", "T_ENDFUNCTION", 
		"T_ENDIF", "T_ENDINTERFACE", "T_ENDMODULE", "T_ENDPROCEDURE", "T_ENDPROGRAM", 
		"T_ENDSELECT", "T_ENDSUBMODULE", "T_ENDSUBROUTINE", "T_ENDTYPE", "T_ENDWHERE", 
		"T_END_KEYWORDS", "T_ENTRY", "T_ENUM", "T_ENUMERATOR", "T_EOF", "T_EOS", 
		"T_EQ", "T_EQUALS", "T_EQUIVALENCE", "T_EQV", "T_EQ_EQ", "T_EQ_GT", "T_ERROR", 
		"T_EVENT", "T_EXIT", "T_EXTENDS", "T_EXTERNAL", "T_FALSE", "T_FILE", "T_FINAL", 
		"T_FINISH", "T_FLUSH", "T_FORALL", "T_FORALL_CONSTRUCT_STMT", "T_FORALL_STMT", 
		"T_FORMAT", "T_FORMATTED", "T_FUNCTION", "T_GE", "T_GENERIC", "T_GO", 
		"T_GOTO", "T_GREATERTHAN", "T_GREATERTHAN_EQ", "T_GT", "T_HOLLERITH", 
		"T_IDENT", "T_IF", "T_IF_STMT", "T_IMAGES", "T_IMPLICIT", "T_IMPORT", 
		"T_IN", "T_INCLUDE", "T_INCLUDE_NAME", "T_INOUT", "T_INQUIRE", "T_INQUIRE_STMT_2", 
		"T_INTEGER", "T_INTENT", "T_INTERFACE", "T_INTRINSIC", "T_KIND", "T_LABEL_DO_TERMINAL", 
		"T_LBRACKET", "T_LE", "T_LEN", "T_LESSTHAN", "T_LESSTHAN_EQ", "T_LOCK", 
		"T_LOCKSET", "T_LOGICAL", "T_LPAREN", "T_LT", "T_MEMORY", "T_MINUS", "T_MODULE", 
		"T_NAMELIST", "T_NE", "T_NEQV", "T_NONE", "T_NON_INTRINSIC", "T_NON_OVERRIDABLE", 
		"T_NOPASS", "T_NOT", "T_NO_LANGUAGE_EXTENSION", "T_NULLIFY", "T_ONLY", 
		"T_OPEN", "T_OPERATOR", "T_OPTIONAL", "T_OR", "T_OUT", "T_PARAMETER", 
		"T_PASS", "T_PAUSE", "T_PERCENT", "T_PERIOD", "T_PERIOD_EXPONENT", "T_PLUS", 
		"T_POINTER", "T_POWER", "T_PRECISION", "T_PRINT", "T_PRIVATE", "T_PROCEDURE", 
		"T_PROGRAM", "T_PROTECTED", "T_PTR_ASSIGNMENT_STMT", "T_PUBLIC", "T_PURE", 
		"T_RBRACKET", "T_READ", "T_REAL", "T_REAL_CONSTANT", "T_RECURSIVE", "T_RESULT", 
		"T_RETURN", "T_REWIND", "T_RPAREN", "T_SAVE", "T_SELECT", "T_SELECTCASE", 
		"T_SELECTTYPE", "T_SEQUENCE", "T_SLASH", "T_SLASH_EQ", "T_SLASH_SLASH", 
		"T_SPAWN", "T_STMT_FUNCTION", "T_STOP", "T_SUBMODULE", "T_SUBROUTINE", 
		"T_SYNC", "T_TARGET", "T_TEAM", "T_THEN", "T_TO", "T_TOPOLOGY", "T_TRUE", 
		"T_TYPE", "T_UNDERSCORE", "T_UNFORMATTED", "T_UNLOCK", "T_USE", "T_VALUE", 
		"T_VOLATILE", "T_WAIT", "T_WHERE", "T_WHERE_CONSTRUCT_STMT", "T_WHERE_STMT", 
		"T_WHILE", "T_WITH", "T_WITHTEAM", "T_WRITE", "WS", "244", "245", "246", 
		"247", "248", "249", "250", "251", "252", "253", "254", "255", "256", 
		"257", "258", "259", "260", "261", "262", "263", "264", "265", "266", 
		"267", "268", "269", "270", "271", "272", "273", "274", "275", "276", 
		"277", "278", "279", "280", "281", "282", "283", "284", "285", "286", 
		"287", "288", "289", "290", "291", "292", "293", "294", "295", "296", 
		"297", "298", "299", "300", "301", "302", "303", "304", "305", "306", 
		"307", "308", "309", "310", "311", "312", "313", "314", "315", "316", 
		"317", "318", "319", "320", "321", "322", "323", "324", "325", "326", 
		"327", "328", "329", "330", "331", "332", "333", "334", "335", "336", 
		"337", "338", "339", "340", "341", "342", "343", "344", "345", "346", 
		"347", "348", "349", "350", "351", "352", "353", "354", "355", "356", 
		"357", "358", "359", "360", "361", "362", "363", "364", "365", "366", 
		"367", "368", "369", "370", "371", "372", "373", "374", "375", "376", 
		"377", "378", "379", "380", "381", "382", "383", "384", "385", "386", 
		"387", "388", "389", "390", "391", "392", "393", "394", "395", "396", 
		"397", "398", "399", "400", "401", "402", "403", "404", "405", "406", 
		"407", "408", "409", "410", "411", "412", "413", "414", "415", "416", 
		"417", "418", "419", "420", "421", "422", "423", "424", "425", "426", 
		"427", "428", "429", "430", "431", "432", "433", "434", "435", "436", 
		"437", "438", "439", "440", "441", "442", "443", "444", "445", "446", 
		"447", "448", "449"
	};
	public static final int EOF=-1;
	public static final int Alphanumeric_Character=4;
	public static final int BINARY_CONSTANT=5;
	public static final int CONTINUE_CHAR=6;
	public static final int DQ_Rep_Char=7;
	public static final int Digit=8;
	public static final int Digit_String=9;
	public static final int HEX_CONSTANT=10;
	public static final int LINE_COMMENT=11;
	public static final int Letter=12;
	public static final int MISC_CHAR=13;
	public static final int OCTAL_CONSTANT=14;
	public static final int PREPROCESS_LINE=15;
	public static final int Rep_Char=16;
	public static final int SQ_Rep_Char=17;
	public static final int Special_Character=18;
	public static final int T_ABSTRACT=19;
	public static final int T_ACQUIRED_LOCK=20;
	public static final int T_ALL=21;
	public static final int T_ALLOCATABLE=22;
	public static final int T_ALLOCATE=23;
	public static final int T_ALLOCATE_STMT_1=24;
	public static final int T_AND=25;
	public static final int T_ARITHMETIC_IF_STMT=26;
	public static final int T_ASSIGN=27;
	public static final int T_ASSIGNMENT=28;
	public static final int T_ASSIGNMENT_STMT=29;
	public static final int T_ASSOCIATE=30;
	public static final int T_ASTERISK=31;
	public static final int T_ASYNCHRONOUS=32;
	public static final int T_AT=33;
	public static final int T_BACKSPACE=34;
	public static final int T_BEGIN_KEYWORDS=35;
	public static final int T_BIND=36;
	public static final int T_BLOCK=37;
	public static final int T_BLOCKDATA=38;
	public static final int T_CALL=39;
	public static final int T_CASE=40;
	public static final int T_CHARACTER=41;
	public static final int T_CHAR_CONSTANT=42;
	public static final int T_CHAR_STRING_EDIT_DESC=43;
	public static final int T_CLASS=44;
	public static final int T_CLOSE=45;
	public static final int T_CODIMENSION=46;
	public static final int T_COLON=47;
	public static final int T_COLON_COLON=48;
	public static final int T_COMMA=49;
	public static final int T_COMMON=50;
	public static final int T_COMPLEX=51;
	public static final int T_CONCURRENT=52;
	public static final int T_CONTAINS=53;
	public static final int T_CONTIGUOUS=54;
	public static final int T_CONTINUE=55;
	public static final int T_CONTROL_EDIT_DESC=56;
	public static final int T_COPOINTER=57;
	public static final int T_COTARGET=58;
	public static final int T_CRITICAL=59;
	public static final int T_CYCLE=60;
	public static final int T_DATA=61;
	public static final int T_DATA_EDIT_DESC=62;
	public static final int T_DEALLOCATE=63;
	public static final int T_DEFAULT=64;
	public static final int T_DEFERRED=65;
	public static final int T_DEFINED_OP=66;
	public static final int T_DIGIT_STRING=67;
	public static final int T_DIMENSION=68;
	public static final int T_DO=69;
	public static final int T_DOUBLE=70;
	public static final int T_DOUBLECOMPLEX=71;
	public static final int T_DOUBLEPRECISION=72;
	public static final int T_EDIT_DESC_MISC=73;
	public static final int T_ELEMENTAL=74;
	public static final int T_ELSE=75;
	public static final int T_ELSEIF=76;
	public static final int T_ELSEWHERE=77;
	public static final int T_END=78;
	public static final int T_ENDASSOCIATE=79;
	public static final int T_ENDBLOCK=80;
	public static final int T_ENDBLOCKDATA=81;
	public static final int T_ENDCRITICAL=82;
	public static final int T_ENDDO=83;
	public static final int T_ENDENUM=84;
	public static final int T_ENDFILE=85;
	public static final int T_ENDFORALL=86;
	public static final int T_ENDFUNCTION=87;
	public static final int T_ENDIF=88;
	public static final int T_ENDINTERFACE=89;
	public static final int T_ENDMODULE=90;
	public static final int T_ENDPROCEDURE=91;
	public static final int T_ENDPROGRAM=92;
	public static final int T_ENDSELECT=93;
	public static final int T_ENDSUBMODULE=94;
	public static final int T_ENDSUBROUTINE=95;
	public static final int T_ENDTYPE=96;
	public static final int T_ENDWHERE=97;
	public static final int T_END_KEYWORDS=98;
	public static final int T_ENTRY=99;
	public static final int T_ENUM=100;
	public static final int T_ENUMERATOR=101;
	public static final int T_EOF=102;
	public static final int T_EOS=103;
	public static final int T_EQ=104;
	public static final int T_EQUALS=105;
	public static final int T_EQUIVALENCE=106;
	public static final int T_EQV=107;
	public static final int T_EQ_EQ=108;
	public static final int T_EQ_GT=109;
	public static final int T_ERROR=110;
	public static final int T_EVENT=111;
	public static final int T_EXIT=112;
	public static final int T_EXTENDS=113;
	public static final int T_EXTERNAL=114;
	public static final int T_FALSE=115;
	public static final int T_FILE=116;
	public static final int T_FINAL=117;
	public static final int T_FINISH=118;
	public static final int T_FLUSH=119;
	public static final int T_FORALL=120;
	public static final int T_FORALL_CONSTRUCT_STMT=121;
	public static final int T_FORALL_STMT=122;
	public static final int T_FORMAT=123;
	public static final int T_FORMATTED=124;
	public static final int T_FUNCTION=125;
	public static final int T_GE=126;
	public static final int T_GENERIC=127;
	public static final int T_GO=128;
	public static final int T_GOTO=129;
	public static final int T_GREATERTHAN=130;
	public static final int T_GREATERTHAN_EQ=131;
	public static final int T_GT=132;
	public static final int T_HOLLERITH=133;
	public static final int T_IDENT=134;
	public static final int T_IF=135;
	public static final int T_IF_STMT=136;
	public static final int T_IMAGES=137;
	public static final int T_IMPLICIT=138;
	public static final int T_IMPORT=139;
	public static final int T_IN=140;
	public static final int T_INCLUDE=141;
	public static final int T_INCLUDE_NAME=142;
	public static final int T_INOUT=143;
	public static final int T_INQUIRE=144;
	public static final int T_INQUIRE_STMT_2=145;
	public static final int T_INTEGER=146;
	public static final int T_INTENT=147;
	public static final int T_INTERFACE=148;
	public static final int T_INTRINSIC=149;
	public static final int T_KIND=150;
	public static final int T_LABEL_DO_TERMINAL=151;
	public static final int T_LBRACKET=152;
	public static final int T_LE=153;
	public static final int T_LEN=154;
	public static final int T_LESSTHAN=155;
	public static final int T_LESSTHAN_EQ=156;
	public static final int T_LOCK=157;
	public static final int T_LOCKSET=158;
	public static final int T_LOGICAL=159;
	public static final int T_LPAREN=160;
	public static final int T_LT=161;
	public static final int T_MEMORY=162;
	public static final int T_MINUS=163;
	public static final int T_MODULE=164;
	public static final int T_NAMELIST=165;
	public static final int T_NE=166;
	public static final int T_NEQV=167;
	public static final int T_NONE=168;
	public static final int T_NON_INTRINSIC=169;
	public static final int T_NON_OVERRIDABLE=170;
	public static final int T_NOPASS=171;
	public static final int T_NOT=172;
	public static final int T_NO_LANGUAGE_EXTENSION=173;
	public static final int T_NULLIFY=174;
	public static final int T_ONLY=175;
	public static final int T_OPEN=176;
	public static final int T_OPERATOR=177;
	public static final int T_OPTIONAL=178;
	public static final int T_OR=179;
	public static final int T_OUT=180;
	public static final int T_PARAMETER=181;
	public static final int T_PASS=182;
	public static final int T_PAUSE=183;
	public static final int T_PERCENT=184;
	public static final int T_PERIOD=185;
	public static final int T_PERIOD_EXPONENT=186;
	public static final int T_PLUS=187;
	public static final int T_POINTER=188;
	public static final int T_POWER=189;
	public static final int T_PRECISION=190;
	public static final int T_PRINT=191;
	public static final int T_PRIVATE=192;
	public static final int T_PROCEDURE=193;
	public static final int T_PROGRAM=194;
	public static final int T_PROTECTED=195;
	public static final int T_PTR_ASSIGNMENT_STMT=196;
	public static final int T_PUBLIC=197;
	public static final int T_PURE=198;
	public static final int T_RBRACKET=199;
	public static final int T_READ=200;
	public static final int T_REAL=201;
	public static final int T_REAL_CONSTANT=202;
	public static final int T_RECURSIVE=203;
	public static final int T_RESULT=204;
	public static final int T_RETURN=205;
	public static final int T_REWIND=206;
	public static final int T_RPAREN=207;
	public static final int T_SAVE=208;
	public static final int T_SELECT=209;
	public static final int T_SELECTCASE=210;
	public static final int T_SELECTTYPE=211;
	public static final int T_SEQUENCE=212;
	public static final int T_SLASH=213;
	public static final int T_SLASH_EQ=214;
	public static final int T_SLASH_SLASH=215;
	public static final int T_SPAWN=216;
	public static final int T_STMT_FUNCTION=217;
	public static final int T_STOP=218;
	public static final int T_SUBMODULE=219;
	public static final int T_SUBROUTINE=220;
	public static final int T_SYNC=221;
	public static final int T_TARGET=222;
	public static final int T_TEAM=223;
	public static final int T_THEN=224;
	public static final int T_TO=225;
	public static final int T_TOPOLOGY=226;
	public static final int T_TRUE=227;
	public static final int T_TYPE=228;
	public static final int T_UNDERSCORE=229;
	public static final int T_UNFORMATTED=230;
	public static final int T_UNLOCK=231;
	public static final int T_USE=232;
	public static final int T_VALUE=233;
	public static final int T_VOLATILE=234;
	public static final int T_WAIT=235;
	public static final int T_WHERE=236;
	public static final int T_WHERE_CONSTRUCT_STMT=237;
	public static final int T_WHERE_STMT=238;
	public static final int T_WHILE=239;
	public static final int T_WITH=240;
	public static final int T_WITHTEAM=241;
	public static final int T_WRITE=242;
	public static final int WS=243;

	// delegates
	public FortranParserExtras_FortranParser08 gFortranParser08;
	public AbstractFortranParser[] getDelegates() {
		return new AbstractFortranParser[] {gFortranParser08};
	}

	// delegators


	public FortranParserExtras(TokenStream input) {
		this(input, new RecognizerSharedState());
	}
	public FortranParserExtras(TokenStream input, RecognizerSharedState state) {
		super(input, state);
		gFortranParser08 = new FortranParserExtras_FortranParser08(input, state, this);
	}

	@Override public String[] getTokenNames() { return FortranParserExtras.tokenNames; }
	@Override public String getGrammarFileName() { return "FortranParserExtras.g"; }


	   int gCount1;
	   int gCount2;

	   public void initialize(String[] args, String kind, String filename, String path) {
	      action = FortranParserActionFactory.newAction(args, this, kind, filename);

	      initialize(this, action, filename, path);
	      gFortranParser08.initialize(this, action, filename, path);

	      action.start_of_file(filename, path);
	   }

	   public void eofAction() {
	      gFortranParser08.eofAction();
	   }




	// $ANTLR start "specification_part"
	// FortranParserExtras.g:71:1: specification_part : ( use_stmt )* ( import_stmt )* implicit_part_recursion ( declaration_construct )* ;
	public final void specification_part() throws RecognitionException {
		int numUseStmts=0; int numImportStmts=0; gCount1=0; gCount2=0;
		try {
			// FortranParserExtras.g:73:4: ( ( use_stmt )* ( import_stmt )* implicit_part_recursion ( declaration_construct )* )
			// FortranParserExtras.g:73:8: ( use_stmt )* ( import_stmt )* implicit_part_recursion ( declaration_construct )*
			{
			// FortranParserExtras.g:73:8: ( use_stmt )*
			loop1:
			while (true) {
				int alt1=2;
				int LA1_0 = input.LA(1);
				if ( (LA1_0==T_DIGIT_STRING) ) {
					int LA1_1 = input.LA(2);
					if ( (LA1_1==T_USE) ) {
						alt1=1;
					}

				}
				else if ( (LA1_0==T_USE) ) {
					alt1=1;
				}

				switch (alt1) {
				case 1 :
					// FortranParserExtras.g:73:10: use_stmt
					{
					pushFollow(FOLLOW_use_stmt_in_specification_part92);
					use_stmt();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) {numUseStmts++;}
					}
					break;

				default :
					break loop1;
				}
			}

			// FortranParserExtras.g:74:8: ( import_stmt )*
			loop2:
			while (true) {
				int alt2=2;
				int LA2_0 = input.LA(1);
				if ( (LA2_0==T_DIGIT_STRING) ) {
					int LA2_1 = input.LA(2);
					if ( (LA2_1==T_IMPORT) ) {
						alt2=1;
					}

				}
				else if ( (LA2_0==T_IMPORT) ) {
					alt2=1;
				}

				switch (alt2) {
				case 1 :
					// FortranParserExtras.g:74:10: import_stmt
					{
					pushFollow(FOLLOW_import_stmt_in_specification_part108);
					import_stmt();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) {numImportStmts++;}
					}
					break;

				default :
					break loop2;
				}
			}

			pushFollow(FOLLOW_implicit_part_recursion_in_specification_part122);
			implicit_part_recursion();
			state._fsp--;
			if (state.failed) return;
			// FortranParserExtras.g:76:8: ( declaration_construct )*
			loop3:
			while (true) {
				int alt3=2;
				int LA3_0 = input.LA(1);
				if ( (LA3_0==T_DIGIT_STRING) ) {
					int LA3_1 = input.LA(2);
					if ( (LA3_1==T_ABSTRACT||LA3_1==T_ALLOCATABLE||LA3_1==T_ASYNCHRONOUS||LA3_1==T_BIND||LA3_1==T_CHARACTER||LA3_1==T_CLASS||LA3_1==T_CODIMENSION||(LA3_1 >= T_COMMON && LA3_1 <= T_COMPLEX)||LA3_1==T_DATA||LA3_1==T_DIMENSION||(LA3_1 >= T_DOUBLE && LA3_1 <= T_DOUBLEPRECISION)||(LA3_1 >= T_ENTRY && LA3_1 <= T_ENUM)||LA3_1==T_EQUIVALENCE||LA3_1==T_EXTERNAL||LA3_1==T_FORMAT||(LA3_1 >= T_INTEGER && LA3_1 <= T_INTRINSIC)||LA3_1==T_LOGICAL||LA3_1==T_NAMELIST||LA3_1==T_OPTIONAL||LA3_1==T_PARAMETER||LA3_1==T_POINTER||(LA3_1 >= T_PRIVATE && LA3_1 <= T_PROCEDURE)||LA3_1==T_PROTECTED||LA3_1==T_PUBLIC||LA3_1==T_REAL||LA3_1==T_SAVE||LA3_1==T_STMT_FUNCTION||LA3_1==T_TARGET||LA3_1==T_TYPE||(LA3_1 >= T_VALUE && LA3_1 <= T_VOLATILE)) ) {
						alt3=1;
					}

				}
				else if ( (LA3_0==T_ABSTRACT||LA3_0==T_ALLOCATABLE||LA3_0==T_ASYNCHRONOUS||LA3_0==T_BIND||LA3_0==T_CHARACTER||LA3_0==T_CLASS||LA3_0==T_CODIMENSION||(LA3_0 >= T_COMMON && LA3_0 <= T_COMPLEX)||LA3_0==T_DATA||LA3_0==T_DIMENSION||(LA3_0 >= T_DOUBLE && LA3_0 <= T_DOUBLEPRECISION)||(LA3_0 >= T_ENTRY && LA3_0 <= T_ENUM)||LA3_0==T_EQUIVALENCE||LA3_0==T_EXTERNAL||LA3_0==T_FORMAT||(LA3_0 >= T_INTEGER && LA3_0 <= T_INTRINSIC)||LA3_0==T_LOGICAL||LA3_0==T_NAMELIST||LA3_0==T_OPTIONAL||LA3_0==T_PARAMETER||LA3_0==T_POINTER||(LA3_0 >= T_PRIVATE && LA3_0 <= T_PROCEDURE)||LA3_0==T_PROTECTED||LA3_0==T_PUBLIC||LA3_0==T_REAL||LA3_0==T_SAVE||LA3_0==T_STMT_FUNCTION||LA3_0==T_TARGET||LA3_0==T_TYPE||(LA3_0 >= T_VALUE && LA3_0 <= T_VOLATILE)) ) {
					alt3=1;
				}

				switch (alt3) {
				case 1 :
					// FortranParserExtras.g:76:10: declaration_construct
					{
					pushFollow(FOLLOW_declaration_construct_in_specification_part134);
					declaration_construct();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) {gCount2++;}
					}
					break;

				default :
					break loop3;
				}
			}

			if ( state.backtracking==0 ) {action.specification_part(numUseStmts, numImportStmts, gCount1, gCount2);}
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "specification_part"



	// $ANTLR start "implicit_part_recursion"
	// FortranParserExtras.g:96:1: implicit_part_recursion : ( ( ( label )? T_IMPLICIT )=> implicit_stmt implicit_part_recursion | ( ( label )? T_PARAMETER )=> parameter_stmt implicit_part_recursion | ( ( label )? T_FORMAT )=> format_stmt implicit_part_recursion | ( ( label )? T_ENTRY )=> entry_stmt implicit_part_recursion |);
	public final void implicit_part_recursion() throws RecognitionException {
		try {
			// FortranParserExtras.g:97:4: ( ( ( label )? T_IMPLICIT )=> implicit_stmt implicit_part_recursion | ( ( label )? T_PARAMETER )=> parameter_stmt implicit_part_recursion | ( ( label )? T_FORMAT )=> format_stmt implicit_part_recursion | ( ( label )? T_ENTRY )=> entry_stmt implicit_part_recursion |)
			int alt4=5;
			alt4 = dfa4.predict(input);
			switch (alt4) {
				case 1 :
					// FortranParserExtras.g:97:8: ( ( label )? T_IMPLICIT )=> implicit_stmt implicit_part_recursion
					{
					pushFollow(FOLLOW_implicit_stmt_in_implicit_part_recursion191);
					implicit_stmt();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) {gCount1++;}
					pushFollow(FOLLOW_implicit_part_recursion_in_implicit_part_recursion196);
					implicit_part_recursion();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 2 :
					// FortranParserExtras.g:98:8: ( ( label )? T_PARAMETER )=> parameter_stmt implicit_part_recursion
					{
					pushFollow(FOLLOW_parameter_stmt_in_implicit_part_recursion216);
					parameter_stmt();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) {gCount2++;}
					pushFollow(FOLLOW_implicit_part_recursion_in_implicit_part_recursion220);
					implicit_part_recursion();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 3 :
					// FortranParserExtras.g:99:8: ( ( label )? T_FORMAT )=> format_stmt implicit_part_recursion
					{
					pushFollow(FOLLOW_format_stmt_in_implicit_part_recursion243);
					format_stmt();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) {gCount2++;}
					pushFollow(FOLLOW_implicit_part_recursion_in_implicit_part_recursion250);
					implicit_part_recursion();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 4 :
					// FortranParserExtras.g:100:8: ( ( label )? T_ENTRY )=> entry_stmt implicit_part_recursion
					{
					pushFollow(FOLLOW_entry_stmt_in_implicit_part_recursion274);
					entry_stmt();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) {gCount2++;}
					pushFollow(FOLLOW_implicit_part_recursion_in_implicit_part_recursion282);
					implicit_part_recursion();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 5 :
					// FortranParserExtras.g:102:4: 
					{
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "implicit_part_recursion"



	// $ANTLR start "executable_construct"
	// FortranParserExtras.g:121:1: executable_construct : ( action_stmt | associate_construct | block_construct | case_construct | critical_construct | do_construct | forall_construct | if_construct | select_type_construct | where_construct );
	public final void executable_construct() throws RecognitionException {
		try {
			// FortranParserExtras.g:123:4: ( action_stmt | associate_construct | block_construct | case_construct | critical_construct | do_construct | forall_construct | if_construct | select_type_construct | where_construct )
			int alt5=10;
			switch ( input.LA(1) ) {
			case T_DIGIT_STRING:
				{
				switch ( input.LA(2) ) {
				case T_ALLOCATE:
				case T_ALLOCATE_STMT_1:
				case T_ARITHMETIC_IF_STMT:
				case T_ASSIGN:
				case T_ASSIGNMENT_STMT:
				case T_BACKSPACE:
				case T_CALL:
				case T_CLOSE:
				case T_CONTINUE:
				case T_CYCLE:
				case T_DEALLOCATE:
				case T_END:
				case T_ENDFILE:
				case T_ERROR:
				case T_EXIT:
				case T_FLUSH:
				case T_FORALL_STMT:
				case T_GO:
				case T_GOTO:
				case T_IF_STMT:
				case T_INQUIRE:
				case T_INQUIRE_STMT_2:
				case T_LOCK:
				case T_NULLIFY:
				case T_OPEN:
				case T_PAUSE:
				case T_PRINT:
				case T_PTR_ASSIGNMENT_STMT:
				case T_READ:
				case T_RETURN:
				case T_REWIND:
				case T_STOP:
				case T_SYNC:
				case T_UNLOCK:
				case T_WAIT:
				case T_WHERE_STMT:
				case T_WRITE:
					{
					alt5=1;
					}
					break;
				case T_IDENT:
					{
					int LA5_14 = input.LA(3);
					if ( (LA5_14==T_COLON) ) {
						switch ( input.LA(4) ) {
						case T_ASSOCIATE:
							{
							alt5=2;
							}
							break;
						case T_BLOCK:
							{
							alt5=3;
							}
							break;
						case T_SELECT:
							{
							int LA5_6 = input.LA(5);
							if ( (LA5_6==T_CASE) ) {
								alt5=4;
							}
							else if ( (LA5_6==T_TYPE) ) {
								alt5=9;
							}

							else {
								if (state.backtracking>0) {state.failed=true; return;}
								int nvaeMark = input.mark();
								try {
									for (int nvaeConsume = 0; nvaeConsume < 5 - 1; nvaeConsume++) {
										input.consume();
									}
									NoViableAltException nvae =
										new NoViableAltException("", 5, 6, input);
									throw nvae;
								} finally {
									input.rewind(nvaeMark);
								}
							}

							}
							break;
						case T_SELECTCASE:
							{
							alt5=4;
							}
							break;
						case T_CRITICAL:
							{
							alt5=5;
							}
							break;
						case T_DO:
							{
							alt5=6;
							}
							break;
						case T_FORALL_CONSTRUCT_STMT:
							{
							alt5=7;
							}
							break;
						case T_IF:
							{
							alt5=8;
							}
							break;
						case T_SELECTTYPE:
							{
							alt5=9;
							}
							break;
						default:
							if (state.backtracking>0) {state.failed=true; return;}
							int nvaeMark = input.mark();
							try {
								for (int nvaeConsume = 0; nvaeConsume < 4 - 1; nvaeConsume++) {
									input.consume();
								}
								NoViableAltException nvae =
									new NoViableAltException("", 5, 16, input);
								throw nvae;
							} finally {
								input.rewind(nvaeMark);
							}
						}
					}

					else {
						if (state.backtracking>0) {state.failed=true; return;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 5, 14, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

					}
					break;
				case T_ASSOCIATE:
					{
					alt5=2;
					}
					break;
				case T_BLOCK:
					{
					alt5=3;
					}
					break;
				case T_SELECT:
					{
					int LA5_6 = input.LA(3);
					if ( (LA5_6==T_CASE) ) {
						alt5=4;
					}
					else if ( (LA5_6==T_TYPE) ) {
						alt5=9;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 5, 6, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

					}
					break;
				case T_SELECTCASE:
					{
					alt5=4;
					}
					break;
				case T_CRITICAL:
					{
					alt5=5;
					}
					break;
				case T_DO:
					{
					alt5=6;
					}
					break;
				case T_FORALL_CONSTRUCT_STMT:
					{
					alt5=7;
					}
					break;
				case T_IF:
					{
					alt5=8;
					}
					break;
				case T_SELECTTYPE:
					{
					alt5=9;
					}
					break;
				default:
					if (state.backtracking>0) {state.failed=true; return;}
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
				break;
			case T_ALLOCATE:
			case T_ALLOCATE_STMT_1:
			case T_ARITHMETIC_IF_STMT:
			case T_ASSIGN:
			case T_ASSIGNMENT_STMT:
			case T_BACKSPACE:
			case T_CALL:
			case T_CLOSE:
			case T_CONTINUE:
			case T_CYCLE:
			case T_DEALLOCATE:
			case T_END:
			case T_ENDFILE:
			case T_ERROR:
			case T_EXIT:
			case T_FLUSH:
			case T_FORALL_STMT:
			case T_GO:
			case T_GOTO:
			case T_IF_STMT:
			case T_INQUIRE:
			case T_INQUIRE_STMT_2:
			case T_LOCK:
			case T_NULLIFY:
			case T_OPEN:
			case T_PAUSE:
			case T_PRINT:
			case T_PTR_ASSIGNMENT_STMT:
			case T_READ:
			case T_RETURN:
			case T_REWIND:
			case T_STOP:
			case T_SYNC:
			case T_UNLOCK:
			case T_WAIT:
			case T_WHERE_STMT:
			case T_WRITE:
				{
				alt5=1;
				}
				break;
			case T_IDENT:
				{
				int LA5_3 = input.LA(2);
				if ( (LA5_3==T_COLON) ) {
					switch ( input.LA(3) ) {
					case T_ASSOCIATE:
						{
						alt5=2;
						}
						break;
					case T_BLOCK:
						{
						alt5=3;
						}
						break;
					case T_SELECT:
						{
						int LA5_6 = input.LA(4);
						if ( (LA5_6==T_CASE) ) {
							alt5=4;
						}
						else if ( (LA5_6==T_TYPE) ) {
							alt5=9;
						}

						else {
							if (state.backtracking>0) {state.failed=true; return;}
							int nvaeMark = input.mark();
							try {
								for (int nvaeConsume = 0; nvaeConsume < 4 - 1; nvaeConsume++) {
									input.consume();
								}
								NoViableAltException nvae =
									new NoViableAltException("", 5, 6, input);
								throw nvae;
							} finally {
								input.rewind(nvaeMark);
							}
						}

						}
						break;
					case T_SELECTCASE:
						{
						alt5=4;
						}
						break;
					case T_CRITICAL:
						{
						alt5=5;
						}
						break;
					case T_DO:
						{
						alt5=6;
						}
						break;
					case T_FORALL_CONSTRUCT_STMT:
						{
						alt5=7;
						}
						break;
					case T_IF:
						{
						alt5=8;
						}
						break;
					case T_SELECTTYPE:
						{
						alt5=9;
						}
						break;
					case T_WHERE_CONSTRUCT_STMT:
						{
						alt5=10;
						}
						break;
					default:
						if (state.backtracking>0) {state.failed=true; return;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 5, 15, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}
				}

				else {
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 5, 3, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case T_ASSOCIATE:
				{
				alt5=2;
				}
				break;
			case T_BLOCK:
				{
				alt5=3;
				}
				break;
			case T_SELECT:
				{
				int LA5_6 = input.LA(2);
				if ( (LA5_6==T_CASE) ) {
					alt5=4;
				}
				else if ( (LA5_6==T_TYPE) ) {
					alt5=9;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 5, 6, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case T_SELECTCASE:
				{
				alt5=4;
				}
				break;
			case T_CRITICAL:
				{
				alt5=5;
				}
				break;
			case T_DO:
				{
				alt5=6;
				}
				break;
			case T_FORALL_CONSTRUCT_STMT:
				{
				alt5=7;
				}
				break;
			case T_IF:
				{
				alt5=8;
				}
				break;
			case T_SELECTTYPE:
				{
				alt5=9;
				}
				break;
			case T_WHERE_CONSTRUCT_STMT:
				{
				alt5=10;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 5, 0, input);
				throw nvae;
			}
			switch (alt5) {
				case 1 :
					// FortranParserExtras.g:123:8: action_stmt
					{
					pushFollow(FOLLOW_action_stmt_in_executable_construct318);
					action_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 2 :
					// FortranParserExtras.g:124:8: associate_construct
					{
					pushFollow(FOLLOW_associate_construct_in_executable_construct327);
					associate_construct();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 3 :
					// FortranParserExtras.g:125:8: block_construct
					{
					pushFollow(FOLLOW_block_construct_in_executable_construct336);
					block_construct();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 4 :
					// FortranParserExtras.g:126:8: case_construct
					{
					pushFollow(FOLLOW_case_construct_in_executable_construct362);
					case_construct();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 5 :
					// FortranParserExtras.g:127:8: critical_construct
					{
					pushFollow(FOLLOW_critical_construct_in_executable_construct371);
					critical_construct();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 6 :
					// FortranParserExtras.g:128:8: do_construct
					{
					pushFollow(FOLLOW_do_construct_in_executable_construct394);
					do_construct();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 7 :
					// FortranParserExtras.g:129:8: forall_construct
					{
					pushFollow(FOLLOW_forall_construct_in_executable_construct403);
					forall_construct();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 8 :
					// FortranParserExtras.g:130:8: if_construct
					{
					pushFollow(FOLLOW_if_construct_in_executable_construct412);
					if_construct();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 9 :
					// FortranParserExtras.g:131:8: select_type_construct
					{
					pushFollow(FOLLOW_select_type_construct_in_executable_construct421);
					select_type_construct();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 10 :
					// FortranParserExtras.g:132:8: where_construct
					{
					pushFollow(FOLLOW_where_construct_in_executable_construct430);
					where_construct();
					state._fsp--;
					if (state.failed) return;
					}
					break;

			}
			if ( state.backtracking==0 ) {action.executable_construct();}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "executable_construct"



	// $ANTLR start "action_stmt"
	// FortranParserExtras.g:189:1: action_stmt : ( allocate_stmt | assignment_stmt | backspace_stmt | call_stmt | close_stmt | continue_stmt | cycle_stmt | deallocate_stmt | endfile_stmt | errorstop_stmt | exit_stmt | flush_stmt | forall_stmt | goto_stmt | if_stmt | inquire_stmt | lock_stmt | nullify_stmt | open_stmt | pointer_assignment_stmt | print_stmt | read_stmt | return_stmt | rewind_stmt | stop_stmt | sync_all_stmt | sync_images_stmt | sync_memory_stmt | unlock_stmt | wait_stmt | where_stmt | write_stmt | arithmetic_if_stmt | computed_goto_stmt | assign_stmt | assigned_goto_stmt | pause_stmt );
	public final void action_stmt() throws RecognitionException {
		try {
			// FortranParserExtras.g:197:4: ( allocate_stmt | assignment_stmt | backspace_stmt | call_stmt | close_stmt | continue_stmt | cycle_stmt | deallocate_stmt | endfile_stmt | errorstop_stmt | exit_stmt | flush_stmt | forall_stmt | goto_stmt | if_stmt | inquire_stmt | lock_stmt | nullify_stmt | open_stmt | pointer_assignment_stmt | print_stmt | read_stmt | return_stmt | rewind_stmt | stop_stmt | sync_all_stmt | sync_images_stmt | sync_memory_stmt | unlock_stmt | wait_stmt | where_stmt | write_stmt | arithmetic_if_stmt | computed_goto_stmt | assign_stmt | assigned_goto_stmt | pause_stmt )
			int alt6=37;
			switch ( input.LA(1) ) {
			case T_DIGIT_STRING:
				{
				switch ( input.LA(2) ) {
				case T_ALLOCATE:
				case T_ALLOCATE_STMT_1:
					{
					alt6=1;
					}
					break;
				case T_ASSIGNMENT_STMT:
					{
					alt6=2;
					}
					break;
				case T_BACKSPACE:
					{
					alt6=3;
					}
					break;
				case T_CALL:
					{
					alt6=4;
					}
					break;
				case T_CLOSE:
					{
					alt6=5;
					}
					break;
				case T_CONTINUE:
					{
					alt6=6;
					}
					break;
				case T_CYCLE:
					{
					alt6=7;
					}
					break;
				case T_DEALLOCATE:
					{
					alt6=8;
					}
					break;
				case T_END:
				case T_ENDFILE:
					{
					alt6=9;
					}
					break;
				case T_ERROR:
					{
					alt6=10;
					}
					break;
				case T_EXIT:
					{
					alt6=11;
					}
					break;
				case T_FLUSH:
					{
					alt6=12;
					}
					break;
				case T_FORALL_STMT:
					{
					alt6=13;
					}
					break;
				case T_GO:
					{
					int LA6_15 = input.LA(3);
					if ( (LA6_15==T_TO) ) {
						switch ( input.LA(4) ) {
						case T_DIGIT_STRING:
							{
							alt6=14;
							}
							break;
						case T_LPAREN:
							{
							alt6=34;
							}
							break;
						case T_IDENT:
							{
							alt6=36;
							}
							break;
						default:
							if (state.backtracking>0) {state.failed=true; return;}
							int nvaeMark = input.mark();
							try {
								for (int nvaeConsume = 0; nvaeConsume < 4 - 1; nvaeConsume++) {
									input.consume();
								}
								NoViableAltException nvae =
									new NoViableAltException("", 6, 36, input);
								throw nvae;
							} finally {
								input.rewind(nvaeMark);
							}
						}
					}

					else {
						if (state.backtracking>0) {state.failed=true; return;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 6, 15, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

					}
					break;
				case T_GOTO:
					{
					switch ( input.LA(3) ) {
					case T_DIGIT_STRING:
						{
						alt6=14;
						}
						break;
					case T_LPAREN:
						{
						alt6=34;
						}
						break;
					case T_IDENT:
						{
						alt6=36;
						}
						break;
					default:
						if (state.backtracking>0) {state.failed=true; return;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 6, 16, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}
					}
					break;
				case T_IF_STMT:
					{
					alt6=15;
					}
					break;
				case T_INQUIRE:
				case T_INQUIRE_STMT_2:
					{
					alt6=16;
					}
					break;
				case T_LOCK:
					{
					alt6=17;
					}
					break;
				case T_NULLIFY:
					{
					alt6=18;
					}
					break;
				case T_OPEN:
					{
					alt6=19;
					}
					break;
				case T_PTR_ASSIGNMENT_STMT:
					{
					alt6=20;
					}
					break;
				case T_PRINT:
					{
					alt6=21;
					}
					break;
				case T_READ:
					{
					alt6=22;
					}
					break;
				case T_RETURN:
					{
					alt6=23;
					}
					break;
				case T_REWIND:
					{
					alt6=24;
					}
					break;
				case T_STOP:
					{
					alt6=25;
					}
					break;
				case T_SYNC:
					{
					switch ( input.LA(3) ) {
					case T_ALL:
						{
						alt6=26;
						}
						break;
					case T_IMAGES:
						{
						alt6=27;
						}
						break;
					case T_MEMORY:
						{
						alt6=28;
						}
						break;
					default:
						if (state.backtracking>0) {state.failed=true; return;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 6, 28, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}
					}
					break;
				case T_UNLOCK:
					{
					alt6=29;
					}
					break;
				case T_WAIT:
					{
					alt6=30;
					}
					break;
				case T_WHERE_STMT:
					{
					alt6=31;
					}
					break;
				case T_WRITE:
					{
					alt6=32;
					}
					break;
				case T_ARITHMETIC_IF_STMT:
					{
					alt6=33;
					}
					break;
				case T_ASSIGN:
					{
					alt6=35;
					}
					break;
				case T_PAUSE:
					{
					alt6=37;
					}
					break;
				default:
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 6, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}
				}
				break;
			case T_ALLOCATE:
			case T_ALLOCATE_STMT_1:
				{
				alt6=1;
				}
				break;
			case T_ASSIGNMENT_STMT:
				{
				alt6=2;
				}
				break;
			case T_BACKSPACE:
				{
				alt6=3;
				}
				break;
			case T_CALL:
				{
				alt6=4;
				}
				break;
			case T_CLOSE:
				{
				alt6=5;
				}
				break;
			case T_CONTINUE:
				{
				alt6=6;
				}
				break;
			case T_CYCLE:
				{
				alt6=7;
				}
				break;
			case T_DEALLOCATE:
				{
				alt6=8;
				}
				break;
			case T_END:
			case T_ENDFILE:
				{
				alt6=9;
				}
				break;
			case T_ERROR:
				{
				alt6=10;
				}
				break;
			case T_EXIT:
				{
				alt6=11;
				}
				break;
			case T_FLUSH:
				{
				alt6=12;
				}
				break;
			case T_FORALL_STMT:
				{
				alt6=13;
				}
				break;
			case T_GO:
				{
				int LA6_15 = input.LA(2);
				if ( (LA6_15==T_TO) ) {
					switch ( input.LA(3) ) {
					case T_DIGIT_STRING:
						{
						alt6=14;
						}
						break;
					case T_LPAREN:
						{
						alt6=34;
						}
						break;
					case T_IDENT:
						{
						alt6=36;
						}
						break;
					default:
						if (state.backtracking>0) {state.failed=true; return;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 6, 36, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}
				}

				else {
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 6, 15, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case T_GOTO:
				{
				switch ( input.LA(2) ) {
				case T_DIGIT_STRING:
					{
					alt6=14;
					}
					break;
				case T_LPAREN:
					{
					alt6=34;
					}
					break;
				case T_IDENT:
					{
					alt6=36;
					}
					break;
				default:
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 6, 16, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}
				}
				break;
			case T_IF_STMT:
				{
				alt6=15;
				}
				break;
			case T_INQUIRE:
			case T_INQUIRE_STMT_2:
				{
				alt6=16;
				}
				break;
			case T_LOCK:
				{
				alt6=17;
				}
				break;
			case T_NULLIFY:
				{
				alt6=18;
				}
				break;
			case T_OPEN:
				{
				alt6=19;
				}
				break;
			case T_PTR_ASSIGNMENT_STMT:
				{
				alt6=20;
				}
				break;
			case T_PRINT:
				{
				alt6=21;
				}
				break;
			case T_READ:
				{
				alt6=22;
				}
				break;
			case T_RETURN:
				{
				alt6=23;
				}
				break;
			case T_REWIND:
				{
				alt6=24;
				}
				break;
			case T_STOP:
				{
				alt6=25;
				}
				break;
			case T_SYNC:
				{
				switch ( input.LA(2) ) {
				case T_ALL:
					{
					alt6=26;
					}
					break;
				case T_IMAGES:
					{
					alt6=27;
					}
					break;
				case T_MEMORY:
					{
					alt6=28;
					}
					break;
				default:
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 6, 28, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}
				}
				break;
			case T_UNLOCK:
				{
				alt6=29;
				}
				break;
			case T_WAIT:
				{
				alt6=30;
				}
				break;
			case T_WHERE_STMT:
				{
				alt6=31;
				}
				break;
			case T_WRITE:
				{
				alt6=32;
				}
				break;
			case T_ARITHMETIC_IF_STMT:
				{
				alt6=33;
				}
				break;
			case T_ASSIGN:
				{
				alt6=35;
				}
				break;
			case T_PAUSE:
				{
				alt6=37;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 6, 0, input);
				throw nvae;
			}
			switch (alt6) {
				case 1 :
					// FortranParserExtras.g:197:8: allocate_stmt
					{
					pushFollow(FOLLOW_allocate_stmt_in_action_stmt473);
					allocate_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 2 :
					// FortranParserExtras.g:198:8: assignment_stmt
					{
					pushFollow(FOLLOW_assignment_stmt_in_action_stmt482);
					assignment_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 3 :
					// FortranParserExtras.g:199:8: backspace_stmt
					{
					pushFollow(FOLLOW_backspace_stmt_in_action_stmt491);
					backspace_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 4 :
					// FortranParserExtras.g:200:8: call_stmt
					{
					pushFollow(FOLLOW_call_stmt_in_action_stmt500);
					call_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 5 :
					// FortranParserExtras.g:201:8: close_stmt
					{
					pushFollow(FOLLOW_close_stmt_in_action_stmt509);
					close_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 6 :
					// FortranParserExtras.g:202:8: continue_stmt
					{
					pushFollow(FOLLOW_continue_stmt_in_action_stmt518);
					continue_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 7 :
					// FortranParserExtras.g:203:8: cycle_stmt
					{
					pushFollow(FOLLOW_cycle_stmt_in_action_stmt527);
					cycle_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 8 :
					// FortranParserExtras.g:204:8: deallocate_stmt
					{
					pushFollow(FOLLOW_deallocate_stmt_in_action_stmt536);
					deallocate_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 9 :
					// FortranParserExtras.g:212:8: endfile_stmt
					{
					pushFollow(FOLLOW_endfile_stmt_in_action_stmt552);
					endfile_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 10 :
					// FortranParserExtras.g:213:8: errorstop_stmt
					{
					pushFollow(FOLLOW_errorstop_stmt_in_action_stmt561);
					errorstop_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 11 :
					// FortranParserExtras.g:214:8: exit_stmt
					{
					pushFollow(FOLLOW_exit_stmt_in_action_stmt586);
					exit_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 12 :
					// FortranParserExtras.g:215:8: flush_stmt
					{
					pushFollow(FOLLOW_flush_stmt_in_action_stmt595);
					flush_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 13 :
					// FortranParserExtras.g:216:8: forall_stmt
					{
					pushFollow(FOLLOW_forall_stmt_in_action_stmt604);
					forall_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 14 :
					// FortranParserExtras.g:217:8: goto_stmt
					{
					pushFollow(FOLLOW_goto_stmt_in_action_stmt613);
					goto_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 15 :
					// FortranParserExtras.g:218:8: if_stmt
					{
					pushFollow(FOLLOW_if_stmt_in_action_stmt622);
					if_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 16 :
					// FortranParserExtras.g:219:8: inquire_stmt
					{
					pushFollow(FOLLOW_inquire_stmt_in_action_stmt631);
					inquire_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 17 :
					// FortranParserExtras.g:220:8: lock_stmt
					{
					pushFollow(FOLLOW_lock_stmt_in_action_stmt642);
					lock_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 18 :
					// FortranParserExtras.g:221:8: nullify_stmt
					{
					pushFollow(FOLLOW_nullify_stmt_in_action_stmt672);
					nullify_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 19 :
					// FortranParserExtras.g:222:8: open_stmt
					{
					pushFollow(FOLLOW_open_stmt_in_action_stmt681);
					open_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 20 :
					// FortranParserExtras.g:223:8: pointer_assignment_stmt
					{
					pushFollow(FOLLOW_pointer_assignment_stmt_in_action_stmt690);
					pointer_assignment_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 21 :
					// FortranParserExtras.g:224:8: print_stmt
					{
					pushFollow(FOLLOW_print_stmt_in_action_stmt699);
					print_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 22 :
					// FortranParserExtras.g:225:8: read_stmt
					{
					pushFollow(FOLLOW_read_stmt_in_action_stmt708);
					read_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 23 :
					// FortranParserExtras.g:226:8: return_stmt
					{
					pushFollow(FOLLOW_return_stmt_in_action_stmt717);
					return_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 24 :
					// FortranParserExtras.g:227:8: rewind_stmt
					{
					pushFollow(FOLLOW_rewind_stmt_in_action_stmt726);
					rewind_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 25 :
					// FortranParserExtras.g:228:8: stop_stmt
					{
					pushFollow(FOLLOW_stop_stmt_in_action_stmt735);
					stop_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 26 :
					// FortranParserExtras.g:229:8: sync_all_stmt
					{
					pushFollow(FOLLOW_sync_all_stmt_in_action_stmt744);
					sync_all_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 27 :
					// FortranParserExtras.g:230:8: sync_images_stmt
					{
					pushFollow(FOLLOW_sync_images_stmt_in_action_stmt770);
					sync_images_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 28 :
					// FortranParserExtras.g:231:8: sync_memory_stmt
					{
					pushFollow(FOLLOW_sync_memory_stmt_in_action_stmt793);
					sync_memory_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 29 :
					// FortranParserExtras.g:232:8: unlock_stmt
					{
					pushFollow(FOLLOW_unlock_stmt_in_action_stmt816);
					unlock_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 30 :
					// FortranParserExtras.g:233:8: wait_stmt
					{
					pushFollow(FOLLOW_wait_stmt_in_action_stmt844);
					wait_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 31 :
					// FortranParserExtras.g:234:8: where_stmt
					{
					pushFollow(FOLLOW_where_stmt_in_action_stmt853);
					where_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 32 :
					// FortranParserExtras.g:235:8: write_stmt
					{
					pushFollow(FOLLOW_write_stmt_in_action_stmt862);
					write_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 33 :
					// FortranParserExtras.g:236:8: arithmetic_if_stmt
					{
					pushFollow(FOLLOW_arithmetic_if_stmt_in_action_stmt871);
					arithmetic_if_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 34 :
					// FortranParserExtras.g:237:8: computed_goto_stmt
					{
					pushFollow(FOLLOW_computed_goto_stmt_in_action_stmt880);
					computed_goto_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 35 :
					// FortranParserExtras.g:238:8: assign_stmt
					{
					pushFollow(FOLLOW_assign_stmt_in_action_stmt889);
					assign_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 36 :
					// FortranParserExtras.g:239:8: assigned_goto_stmt
					{
					pushFollow(FOLLOW_assigned_goto_stmt_in_action_stmt917);
					assigned_goto_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;
				case 37 :
					// FortranParserExtras.g:240:8: pause_stmt
					{
					pushFollow(FOLLOW_pause_stmt_in_action_stmt938);
					pause_stmt();
					state._fsp--;
					if (state.failed) return;
					}
					break;

			}
			if ( state.backtracking==0 ) {action.action_stmt();}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "action_stmt"



	// $ANTLR start "type_declaration_stmt"
	// FortranParserExtras.g:259:1: type_declaration_stmt : ( label )? declaration_type_spec ( ( T_COMMA attr_spec )* T_COLON_COLON )? entity_decl_list end_of_stmt ;
	public final void type_declaration_stmt() throws RecognitionException {
		Token label1 =null;
		Token end_of_stmt2 =null;

		Token lbl = null; int numAttrSpecs = 0;
		try {
			// FortranParserExtras.g:262:5: ( ( label )? declaration_type_spec ( ( T_COMMA attr_spec )* T_COLON_COLON )? entity_decl_list end_of_stmt )
			// FortranParserExtras.g:262:7: ( label )? declaration_type_spec ( ( T_COMMA attr_spec )* T_COLON_COLON )? entity_decl_list end_of_stmt
			{
			// FortranParserExtras.g:262:7: ( label )?
			int alt7=2;
			int LA7_0 = input.LA(1);
			if ( (LA7_0==T_DIGIT_STRING) ) {
				alt7=1;
			}
			switch (alt7) {
				case 1 :
					// FortranParserExtras.g:262:8: label
					{
					pushFollow(FOLLOW_label_in_type_declaration_stmt997);
					label1=label();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) {lbl=label1;}
					}
					break;

			}

			pushFollow(FOLLOW_declaration_type_spec_in_type_declaration_stmt1003);
			declaration_type_spec();
			state._fsp--;
			if (state.failed) return;
			// FortranParserExtras.g:263:3: ( ( T_COMMA attr_spec )* T_COLON_COLON )?
			int alt9=2;
			int LA9_0 = input.LA(1);
			if ( ((LA9_0 >= T_COLON_COLON && LA9_0 <= T_COMMA)) ) {
				alt9=1;
			}
			switch (alt9) {
				case 1 :
					// FortranParserExtras.g:263:5: ( T_COMMA attr_spec )* T_COLON_COLON
					{
					// FortranParserExtras.g:263:5: ( T_COMMA attr_spec )*
					loop8:
					while (true) {
						int alt8=2;
						int LA8_0 = input.LA(1);
						if ( (LA8_0==T_COMMA) ) {
							alt8=1;
						}

						switch (alt8) {
						case 1 :
							// FortranParserExtras.g:263:6: T_COMMA attr_spec
							{
							match(input,T_COMMA,FOLLOW_T_COMMA_in_type_declaration_stmt1010); if (state.failed) return;
							pushFollow(FOLLOW_attr_spec_in_type_declaration_stmt1012);
							attr_spec();
							state._fsp--;
							if (state.failed) return;
							if ( state.backtracking==0 ) {numAttrSpecs += 1;}
							}
							break;

						default :
							break loop8;
						}
					}

					match(input,T_COLON_COLON,FOLLOW_T_COLON_COLON_in_type_declaration_stmt1018); if (state.failed) return;
					}
					break;

			}

			pushFollow(FOLLOW_entity_decl_list_in_type_declaration_stmt1025);
			entity_decl_list();
			state._fsp--;
			if (state.failed) return;
			pushFollow(FOLLOW_end_of_stmt_in_type_declaration_stmt1027);
			end_of_stmt2=end_of_stmt();
			state._fsp--;
			if (state.failed) return;
			if ( state.backtracking==0 ) { action.type_declaration_stmt(lbl, numAttrSpecs, end_of_stmt2); }
			}

			if ( state.backtracking==0 ) {checkForInclude();}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "type_declaration_stmt"



	// $ANTLR start "part_ref"
	// FortranParserExtras.g:311:1: part_ref options {k=2; } : ( ( T_IDENT T_LPAREN )=> T_IDENT T_LPAREN section_subscript_list T_RPAREN ( image_selector )? | ( T_IDENT T_LBRACKET )=> T_IDENT image_selector | T_IDENT );
	public final void part_ref() throws RecognitionException {
		Token T_IDENT3=null;
		Token T_IDENT4=null;
		Token T_IDENT5=null;

		boolean hasSSL = false; boolean hasImageSelector = false;
		try {
			// FortranParserExtras.g:314:4: ( ( T_IDENT T_LPAREN )=> T_IDENT T_LPAREN section_subscript_list T_RPAREN ( image_selector )? | ( T_IDENT T_LBRACKET )=> T_IDENT image_selector | T_IDENT )
			int alt11=3;
			int LA11_0 = input.LA(1);
			if ( (LA11_0==T_IDENT) ) {
				int LA11_1 = input.LA(2);
				if ( (LA11_1==T_LPAREN) ) {
					int LA11_2 = input.LA(3);
					if ( (synpred5_FortranParserExtras()) ) {
						alt11=1;
					}
					else if ( (true) ) {
						alt11=3;
					}

				}
				else if ( (LA11_1==T_LBRACKET) && (synpred6_FortranParserExtras())) {
					alt11=2;
				}
				else if ( (LA11_1==EOF||LA11_1==T_AND||LA11_1==T_ASTERISK||(LA11_1 >= T_COLON && LA11_1 <= T_COMMA)||LA11_1==T_DEFINED_OP||(LA11_1 >= T_EOS && LA11_1 <= T_EQUALS)||(LA11_1 >= T_EQV && LA11_1 <= T_EQ_GT)||LA11_1==T_GE||(LA11_1 >= T_GREATERTHAN && LA11_1 <= T_GT)||LA11_1==T_LE||(LA11_1 >= T_LESSTHAN && LA11_1 <= T_LESSTHAN_EQ)||LA11_1==T_LT||LA11_1==T_MINUS||(LA11_1 >= T_NE && LA11_1 <= T_NEQV)||LA11_1==T_OR||LA11_1==T_PERCENT||LA11_1==T_PLUS||LA11_1==T_POWER||LA11_1==T_RBRACKET||LA11_1==T_RPAREN||(LA11_1 >= T_SLASH && LA11_1 <= T_SLASH_SLASH)) ) {
					alt11=3;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 11, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}

			else {
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 11, 0, input);
				throw nvae;
			}

			switch (alt11) {
				case 1 :
					// FortranParserExtras.g:314:8: ( T_IDENT T_LPAREN )=> T_IDENT T_LPAREN section_subscript_list T_RPAREN ( image_selector )?
					{
					T_IDENT3=(Token)match(input,T_IDENT,FOLLOW_T_IDENT_in_part_ref1122); if (state.failed) return;
					match(input,T_LPAREN,FOLLOW_T_LPAREN_in_part_ref1124); if (state.failed) return;
					pushFollow(FOLLOW_section_subscript_list_in_part_ref1126);
					section_subscript_list();
					state._fsp--;
					if (state.failed) return;
					match(input,T_RPAREN,FOLLOW_T_RPAREN_in_part_ref1128); if (state.failed) return;
					// FortranParserExtras.g:315:30: ( image_selector )?
					int alt10=2;
					int LA10_0 = input.LA(1);
					if ( (LA10_0==T_LBRACKET) ) {
						alt10=1;
					}
					switch (alt10) {
						case 1 :
							// FortranParserExtras.g:315:31: image_selector
							{
							pushFollow(FOLLOW_image_selector_in_part_ref1160);
							image_selector();
							state._fsp--;
							if (state.failed) return;
							if ( state.backtracking==0 ) {hasImageSelector=true;}
							}
							break;

					}

					if ( state.backtracking==0 ) {hasSSL=true; action.part_ref(T_IDENT3, hasSSL, hasImageSelector);}
					}
					break;
				case 2 :
					// FortranParserExtras.g:317:8: ( T_IDENT T_LBRACKET )=> T_IDENT image_selector
					{
					T_IDENT4=(Token)match(input,T_IDENT,FOLLOW_T_IDENT_in_part_ref1194); if (state.failed) return;
					pushFollow(FOLLOW_image_selector_in_part_ref1196);
					image_selector();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) {hasImageSelector=true; action.part_ref(T_IDENT4, hasSSL, hasImageSelector);}
					}
					break;
				case 3 :
					// FortranParserExtras.g:319:8: T_IDENT
					{
					T_IDENT5=(Token)match(input,T_IDENT,FOLLOW_T_IDENT_in_part_ref1218); if (state.failed) return;
					if ( state.backtracking==0 ) {action.part_ref(T_IDENT5, hasSSL, hasImageSelector);}
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "part_ref"



	// $ANTLR start "part_ref_no_image_selector"
	// FortranParserExtras.g:323:1: part_ref_no_image_selector options {k=2; } : ( ( T_IDENT T_LPAREN )=> T_IDENT T_LPAREN section_subscript_list T_RPAREN | T_IDENT );
	public final void part_ref_no_image_selector() throws RecognitionException {
		Token T_IDENT6=null;
		Token T_IDENT7=null;

		boolean hasSSL = false; boolean hasImageSelector = false;
		try {
			// FortranParserExtras.g:326:4: ( ( T_IDENT T_LPAREN )=> T_IDENT T_LPAREN section_subscript_list T_RPAREN | T_IDENT )
			int alt12=2;
			int LA12_0 = input.LA(1);
			if ( (LA12_0==T_IDENT) ) {
				int LA12_1 = input.LA(2);
				if ( (LA12_1==T_LPAREN) && (synpred7_FortranParserExtras())) {
					alt12=1;
				}
				else if ( (LA12_1==EOF||LA12_1==T_COMMA||LA12_1==T_LBRACKET||LA12_1==T_PERCENT||LA12_1==T_RPAREN) ) {
					alt12=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 12, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}

			else {
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 12, 0, input);
				throw nvae;
			}

			switch (alt12) {
				case 1 :
					// FortranParserExtras.g:326:8: ( T_IDENT T_LPAREN )=> T_IDENT T_LPAREN section_subscript_list T_RPAREN
					{
					T_IDENT6=(Token)match(input,T_IDENT,FOLLOW_T_IDENT_in_part_ref_no_image_selector1267); if (state.failed) return;
					match(input,T_LPAREN,FOLLOW_T_LPAREN_in_part_ref_no_image_selector1269); if (state.failed) return;
					pushFollow(FOLLOW_section_subscript_list_in_part_ref_no_image_selector1271);
					section_subscript_list();
					state._fsp--;
					if (state.failed) return;
					match(input,T_RPAREN,FOLLOW_T_RPAREN_in_part_ref_no_image_selector1273); if (state.failed) return;
					if ( state.backtracking==0 ) {hasSSL=true; action.part_ref(T_IDENT6, hasSSL, hasImageSelector);}
					}
					break;
				case 2 :
					// FortranParserExtras.g:328:8: T_IDENT
					{
					T_IDENT7=(Token)match(input,T_IDENT,FOLLOW_T_IDENT_in_part_ref_no_image_selector1295); if (state.failed) return;
					if ( state.backtracking==0 ) {action.part_ref(T_IDENT7, hasSSL, hasImageSelector);}
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "part_ref_no_image_selector"



	// $ANTLR start "section_subscript"
	// FortranParserExtras.g:346:1: section_subscript returns [boolean isEmpty] : ( expr section_subscript_ambiguous | T_COLON ( expr )? ( T_COLON expr )? | T_COLON_COLON expr | T_IDENT T_EQUALS expr | T_IDENT T_EQUALS T_ASTERISK label | T_ASTERISK label |);
	public final boolean section_subscript() throws RecognitionException {
		boolean isEmpty = false;


		Token T_IDENT8=null;
		Token T_IDENT10=null;
		Token label9 =null;
		Token label11 =null;


		   boolean hasLowerBounds = false;
		   boolean hasUpperBounds = false;
		   boolean hasStride = false;
		   boolean hasExpr = false;

		try {
			// FortranParserExtras.g:353:4: ( expr section_subscript_ambiguous | T_COLON ( expr )? ( T_COLON expr )? | T_COLON_COLON expr | T_IDENT T_EQUALS expr | T_IDENT T_EQUALS T_ASTERISK label | T_ASTERISK label |)
			int alt15=7;
			switch ( input.LA(1) ) {
			case BINARY_CONSTANT:
			case HEX_CONSTANT:
			case OCTAL_CONSTANT:
			case T_CHAR_CONSTANT:
			case T_DEFINED_OP:
			case T_DIGIT_STRING:
			case T_FALSE:
			case T_HOLLERITH:
			case T_LBRACKET:
			case T_LPAREN:
			case T_MINUS:
			case T_NOT:
			case T_PLUS:
			case T_REAL_CONSTANT:
			case T_TRUE:
				{
				alt15=1;
				}
				break;
			case T_IDENT:
				{
				int LA15_2 = input.LA(2);
				if ( (LA15_2==T_AND||LA15_2==T_ASTERISK||LA15_2==T_CHAR_CONSTANT||(LA15_2 >= T_COLON && LA15_2 <= T_COMMA)||LA15_2==T_DEFINED_OP||LA15_2==T_EQ||(LA15_2 >= T_EQV && LA15_2 <= T_EQ_EQ)||LA15_2==T_GE||(LA15_2 >= T_GREATERTHAN && LA15_2 <= T_GT)||(LA15_2 >= T_LBRACKET && LA15_2 <= T_LE)||(LA15_2 >= T_LESSTHAN && LA15_2 <= T_LESSTHAN_EQ)||(LA15_2 >= T_LPAREN && LA15_2 <= T_LT)||LA15_2==T_MINUS||(LA15_2 >= T_NE && LA15_2 <= T_NEQV)||LA15_2==T_OR||LA15_2==T_PERCENT||LA15_2==T_PLUS||LA15_2==T_POWER||LA15_2==T_RPAREN||(LA15_2 >= T_SLASH && LA15_2 <= T_SLASH_SLASH)) ) {
					alt15=1;
				}
				else if ( (LA15_2==T_EQUALS) ) {
					int LA15_7 = input.LA(3);
					if ( (LA15_7==T_ASTERISK) ) {
						alt15=5;
					}
					else if ( (LA15_7==BINARY_CONSTANT||LA15_7==HEX_CONSTANT||LA15_7==OCTAL_CONSTANT||LA15_7==T_CHAR_CONSTANT||(LA15_7 >= T_DEFINED_OP && LA15_7 <= T_DIGIT_STRING)||LA15_7==T_FALSE||(LA15_7 >= T_HOLLERITH && LA15_7 <= T_IDENT)||LA15_7==T_LBRACKET||LA15_7==T_LPAREN||LA15_7==T_MINUS||LA15_7==T_NOT||LA15_7==T_PLUS||LA15_7==T_REAL_CONSTANT||LA15_7==T_TRUE) ) {
						alt15=4;
					}

					else {
						if (state.backtracking>0) {state.failed=true; return isEmpty;}
						int nvaeMark = input.mark();
						try {
							for (int nvaeConsume = 0; nvaeConsume < 3 - 1; nvaeConsume++) {
								input.consume();
							}
							NoViableAltException nvae =
								new NoViableAltException("", 15, 7, input);
							throw nvae;
						} finally {
							input.rewind(nvaeMark);
						}
					}

				}

				else {
					if (state.backtracking>0) {state.failed=true; return isEmpty;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 15, 2, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

				}
				break;
			case T_COLON:
				{
				alt15=2;
				}
				break;
			case T_COLON_COLON:
				{
				alt15=3;
				}
				break;
			case T_ASTERISK:
				{
				alt15=6;
				}
				break;
			case T_COMMA:
			case T_RPAREN:
				{
				alt15=7;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return isEmpty;}
				NoViableAltException nvae =
					new NoViableAltException("", 15, 0, input);
				throw nvae;
			}
			switch (alt15) {
				case 1 :
					// FortranParserExtras.g:353:8: expr section_subscript_ambiguous
					{
					pushFollow(FOLLOW_expr_in_section_subscript1344);
					expr();
					state._fsp--;
					if (state.failed) return isEmpty;
					pushFollow(FOLLOW_section_subscript_ambiguous_in_section_subscript1346);
					section_subscript_ambiguous();
					state._fsp--;
					if (state.failed) return isEmpty;
					}
					break;
				case 2 :
					// FortranParserExtras.g:354:8: T_COLON ( expr )? ( T_COLON expr )?
					{
					match(input,T_COLON,FOLLOW_T_COLON_in_section_subscript1355); if (state.failed) return isEmpty;
					// FortranParserExtras.g:354:16: ( expr )?
					int alt13=2;
					int LA13_0 = input.LA(1);
					if ( (LA13_0==BINARY_CONSTANT||LA13_0==HEX_CONSTANT||LA13_0==OCTAL_CONSTANT||LA13_0==T_CHAR_CONSTANT||(LA13_0 >= T_DEFINED_OP && LA13_0 <= T_DIGIT_STRING)||LA13_0==T_FALSE||(LA13_0 >= T_HOLLERITH && LA13_0 <= T_IDENT)||LA13_0==T_LBRACKET||LA13_0==T_LPAREN||LA13_0==T_MINUS||LA13_0==T_NOT||LA13_0==T_PLUS||LA13_0==T_REAL_CONSTANT||LA13_0==T_TRUE) ) {
						alt13=1;
					}
					switch (alt13) {
						case 1 :
							// FortranParserExtras.g:354:17: expr
							{
							pushFollow(FOLLOW_expr_in_section_subscript1358);
							expr();
							state._fsp--;
							if (state.failed) return isEmpty;
							if ( state.backtracking==0 ) {hasUpperBounds=true;}
							}
							break;

					}

					// FortranParserExtras.g:354:47: ( T_COLON expr )?
					int alt14=2;
					int LA14_0 = input.LA(1);
					if ( (LA14_0==T_COLON) ) {
						alt14=1;
					}
					switch (alt14) {
						case 1 :
							// FortranParserExtras.g:354:48: T_COLON expr
							{
							match(input,T_COLON,FOLLOW_T_COLON_in_section_subscript1365); if (state.failed) return isEmpty;
							pushFollow(FOLLOW_expr_in_section_subscript1367);
							expr();
							state._fsp--;
							if (state.failed) return isEmpty;
							if ( state.backtracking==0 ) {hasStride=true;}
							}
							break;

					}

					if ( state.backtracking==0 ) { action.section_subscript(hasLowerBounds, hasUpperBounds, hasStride, false); }
					}
					break;
				case 3 :
					// FortranParserExtras.g:356:8: T_COLON_COLON expr
					{
					match(input,T_COLON_COLON,FOLLOW_T_COLON_COLON_in_section_subscript1393); if (state.failed) return isEmpty;
					pushFollow(FOLLOW_expr_in_section_subscript1395);
					expr();
					state._fsp--;
					if (state.failed) return isEmpty;
					if ( state.backtracking==0 ) { hasStride=true;
					             action.section_subscript(hasLowerBounds, hasUpperBounds, hasStride, false);}
					}
					break;
				case 4 :
					// FortranParserExtras.g:359:8: T_IDENT T_EQUALS expr
					{
					T_IDENT8=(Token)match(input,T_IDENT,FOLLOW_T_IDENT_in_section_subscript1417); if (state.failed) return isEmpty;
					match(input,T_EQUALS,FOLLOW_T_EQUALS_in_section_subscript1419); if (state.failed) return isEmpty;
					pushFollow(FOLLOW_expr_in_section_subscript1421);
					expr();
					state._fsp--;
					if (state.failed) return isEmpty;
					if ( state.backtracking==0 ) { hasExpr=true; action.actual_arg(hasExpr, null); 
					             action.actual_arg_spec(T_IDENT8); }
					}
					break;
				case 5 :
					// FortranParserExtras.g:362:8: T_IDENT T_EQUALS T_ASTERISK label
					{
					T_IDENT10=(Token)match(input,T_IDENT,FOLLOW_T_IDENT_in_section_subscript1444); if (state.failed) return isEmpty;
					match(input,T_EQUALS,FOLLOW_T_EQUALS_in_section_subscript1446); if (state.failed) return isEmpty;
					match(input,T_ASTERISK,FOLLOW_T_ASTERISK_in_section_subscript1448); if (state.failed) return isEmpty;
					pushFollow(FOLLOW_label_in_section_subscript1450);
					label9=label();
					state._fsp--;
					if (state.failed) return isEmpty;
					if ( state.backtracking==0 ) { action.actual_arg(hasExpr, label9); action.actual_arg_spec(T_IDENT10); }
					}
					break;
				case 6 :
					// FortranParserExtras.g:364:8: T_ASTERISK label
					{
					match(input,T_ASTERISK,FOLLOW_T_ASTERISK_in_section_subscript1473); if (state.failed) return isEmpty;
					pushFollow(FOLLOW_label_in_section_subscript1475);
					label11=label();
					state._fsp--;
					if (state.failed) return isEmpty;
					if ( state.backtracking==0 ) { action.actual_arg(hasExpr, label11); action.actual_arg_spec(null); }
					}
					break;
				case 7 :
					// FortranParserExtras.g:366:12: 
					{
					if ( state.backtracking==0 ) { isEmpty = true; /* empty could be an actual-arg, see R1220 */ }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
		return isEmpty;
	}
	// $ANTLR end "section_subscript"



	// $ANTLR start "section_subscript_ambiguous"
	// FortranParserExtras.g:369:1: section_subscript_ambiguous : ( T_COLON ( expr )? ( T_COLON expr )? | T_COLON_COLON expr |);
	public final void section_subscript_ambiguous() throws RecognitionException {

		   boolean hasLowerBound = true;
		   boolean hasUpperBound = false;
		   boolean hasStride = false;
		   boolean isAmbiguous = false; 

		try {
			// FortranParserExtras.g:376:4: ( T_COLON ( expr )? ( T_COLON expr )? | T_COLON_COLON expr |)
			int alt18=3;
			switch ( input.LA(1) ) {
			case T_COLON:
				{
				alt18=1;
				}
				break;
			case T_COLON_COLON:
				{
				alt18=2;
				}
				break;
			case T_COMMA:
			case T_RPAREN:
				{
				alt18=3;
				}
				break;
			default:
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 18, 0, input);
				throw nvae;
			}
			switch (alt18) {
				case 1 :
					// FortranParserExtras.g:376:8: T_COLON ( expr )? ( T_COLON expr )?
					{
					match(input,T_COLON,FOLLOW_T_COLON_in_section_subscript_ambiguous1525); if (state.failed) return;
					// FortranParserExtras.g:376:16: ( expr )?
					int alt16=2;
					int LA16_0 = input.LA(1);
					if ( (LA16_0==BINARY_CONSTANT||LA16_0==HEX_CONSTANT||LA16_0==OCTAL_CONSTANT||LA16_0==T_CHAR_CONSTANT||(LA16_0 >= T_DEFINED_OP && LA16_0 <= T_DIGIT_STRING)||LA16_0==T_FALSE||(LA16_0 >= T_HOLLERITH && LA16_0 <= T_IDENT)||LA16_0==T_LBRACKET||LA16_0==T_LPAREN||LA16_0==T_MINUS||LA16_0==T_NOT||LA16_0==T_PLUS||LA16_0==T_REAL_CONSTANT||LA16_0==T_TRUE) ) {
						alt16=1;
					}
					switch (alt16) {
						case 1 :
							// FortranParserExtras.g:376:17: expr
							{
							pushFollow(FOLLOW_expr_in_section_subscript_ambiguous1528);
							expr();
							state._fsp--;
							if (state.failed) return;
							if ( state.backtracking==0 ) {hasUpperBound=true;}
							}
							break;

					}

					// FortranParserExtras.g:376:46: ( T_COLON expr )?
					int alt17=2;
					int LA17_0 = input.LA(1);
					if ( (LA17_0==T_COLON) ) {
						alt17=1;
					}
					switch (alt17) {
						case 1 :
							// FortranParserExtras.g:376:47: T_COLON expr
							{
							match(input,T_COLON,FOLLOW_T_COLON_in_section_subscript_ambiguous1535); if (state.failed) return;
							pushFollow(FOLLOW_expr_in_section_subscript_ambiguous1537);
							expr();
							state._fsp--;
							if (state.failed) return;
							if ( state.backtracking==0 ) {hasStride=true;}
							}
							break;

					}

					if ( state.backtracking==0 ) { action.section_subscript(hasLowerBound, hasUpperBound, hasStride, isAmbiguous);}
					}
					break;
				case 2 :
					// FortranParserExtras.g:383:7: T_COLON_COLON expr
					{
					match(input,T_COLON_COLON,FOLLOW_T_COLON_COLON_in_section_subscript_ambiguous1602); if (state.failed) return;
					pushFollow(FOLLOW_expr_in_section_subscript_ambiguous1604);
					expr();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) { hasStride=true; 
					             action.section_subscript(hasLowerBound, hasUpperBound, hasStride, isAmbiguous);}
					}
					break;
				case 3 :
					// FortranParserExtras.g:386:12: 
					{
					if ( state.backtracking==0 ) { /* empty, could be an actual-arg, see R1220 */
					             isAmbiguous=true; 
					             action.section_subscript(hasLowerBound, hasUpperBound, hasStride, isAmbiguous);
					           }
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "section_subscript_ambiguous"



	// $ANTLR start "section_subscript_list"
	// FortranParserExtras.g:406:1: section_subscript_list :isEmpty= section_subscript ( T_COMMA section_subscript )* ;
	public final void section_subscript_list() throws RecognitionException {
		boolean isEmpty =false;

		int count = 0;
		try {
			// FortranParserExtras.g:408:4: (isEmpty= section_subscript ( T_COMMA section_subscript )* )
			// FortranParserExtras.g:408:12: isEmpty= section_subscript ( T_COMMA section_subscript )*
			{
			if ( state.backtracking==0 ) { action.section_subscript_list__begin(); }
			pushFollow(FOLLOW_section_subscript_in_section_subscript_list1676);
			isEmpty=section_subscript();
			state._fsp--;
			if (state.failed) return;
			if ( state.backtracking==0 ) {
			               if (isEmpty == false) count += 1;
			           }
			// FortranParserExtras.g:413:8: ( T_COMMA section_subscript )*
			loop19:
			while (true) {
				int alt19=2;
				int LA19_0 = input.LA(1);
				if ( (LA19_0==T_COMMA) ) {
					alt19=1;
				}

				switch (alt19) {
				case 1 :
					// FortranParserExtras.g:413:9: T_COMMA section_subscript
					{
					match(input,T_COMMA,FOLLOW_T_COMMA_in_section_subscript_list1699); if (state.failed) return;
					pushFollow(FOLLOW_section_subscript_in_section_subscript_list1701);
					section_subscript();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) {count += 1;}
					}
					break;

				default :
					break loop19;
				}
			}

			if ( state.backtracking==0 ) { action.section_subscript_list(count); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "section_subscript_list"



	// $ANTLR start "image_selector"
	// FortranParserExtras.g:426:1: image_selector : T_LBRACKET cosubscript_list T_RBRACKET ;
	public final void image_selector() throws RecognitionException {
		Token T_LBRACKET12=null;
		Token T_RBRACKET13=null;

		try {
			// FortranParserExtras.g:427:4: ( T_LBRACKET cosubscript_list T_RBRACKET )
			// FortranParserExtras.g:427:8: T_LBRACKET cosubscript_list T_RBRACKET
			{
			T_LBRACKET12=(Token)match(input,T_LBRACKET,FOLLOW_T_LBRACKET_in_image_selector1742); if (state.failed) return;
			pushFollow(FOLLOW_cosubscript_list_in_image_selector1744);
			cosubscript_list();
			state._fsp--;
			if (state.failed) return;
			T_RBRACKET13=(Token)match(input,T_RBRACKET,FOLLOW_T_RBRACKET_in_image_selector1746); if (state.failed) return;
			if ( state.backtracking==0 ) {action.image_selector(T_LBRACKET12, T_RBRACKET13);}
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "image_selector"



	// $ANTLR start "cosubscript"
	// FortranParserExtras.g:439:1: cosubscript : scalar_int_expr ;
	public final void cosubscript() throws RecognitionException {
		try {
			// FortranParserExtras.g:440:4: ( scalar_int_expr )
			// FortranParserExtras.g:440:8: scalar_int_expr
			{
			pushFollow(FOLLOW_scalar_int_expr_in_cosubscript1782);
			scalar_int_expr();
			state._fsp--;
			if (state.failed) return;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "cosubscript"



	// $ANTLR start "cosubscript_list"
	// FortranParserExtras.g:443:1: cosubscript_list : cosubscript ( T_COMMA cosubscript )* ;
	public final void cosubscript_list() throws RecognitionException {
		int count=0;
		try {
			// FortranParserExtras.g:445:4: ( cosubscript ( T_COMMA cosubscript )* )
			// FortranParserExtras.g:445:12: cosubscript ( T_COMMA cosubscript )*
			{
			if ( state.backtracking==0 ) {action.cosubscript_list__begin();}
			pushFollow(FOLLOW_cosubscript_in_cosubscript_list1816);
			cosubscript();
			state._fsp--;
			if (state.failed) return;
			if ( state.backtracking==0 ) {count++;}
			// FortranParserExtras.g:446:31: ( T_COMMA cosubscript )*
			loop20:
			while (true) {
				int alt20=2;
				int LA20_0 = input.LA(1);
				if ( (LA20_0==T_COMMA) ) {
					alt20=1;
				}

				switch (alt20) {
				case 1 :
					// FortranParserExtras.g:446:33: T_COMMA cosubscript
					{
					match(input,T_COMMA,FOLLOW_T_COMMA_in_cosubscript_list1822); if (state.failed) return;
					pushFollow(FOLLOW_cosubscript_in_cosubscript_list1824);
					cosubscript();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) {count++;}
					}
					break;

				default :
					break loop20;
				}
			}

			if ( state.backtracking==0 ) {action.cosubscript_list(count, null);}
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "cosubscript_list"



	// $ANTLR start "allocation"
	// FortranParserExtras.g:461:1: allocation : ( ( allocate_object T_LBRACKET )=> allocate_object T_LBRACKET allocate_coarray_spec T_RBRACKET | ( allocate_object )=> allocate_object );
	public final void allocation() throws RecognitionException {
		boolean hasAllocateShapeSpecList = false; boolean hasAllocateCoarraySpec = false;
		try {
			// FortranParserExtras.g:463:4: ( ( allocate_object T_LBRACKET )=> allocate_object T_LBRACKET allocate_coarray_spec T_RBRACKET | ( allocate_object )=> allocate_object )
			int alt21=2;
			int LA21_0 = input.LA(1);
			if ( (LA21_0==T_IDENT) ) {
				int LA21_1 = input.LA(2);
				if ( (synpred8_FortranParserExtras()) ) {
					alt21=1;
				}
				else if ( (synpred9_FortranParserExtras()) ) {
					alt21=2;
				}

				else {
					if (state.backtracking>0) {state.failed=true; return;}
					int nvaeMark = input.mark();
					try {
						input.consume();
						NoViableAltException nvae =
							new NoViableAltException("", 21, 1, input);
						throw nvae;
					} finally {
						input.rewind(nvaeMark);
					}
				}

			}

			else {
				if (state.backtracking>0) {state.failed=true; return;}
				NoViableAltException nvae =
					new NoViableAltException("", 21, 0, input);
				throw nvae;
			}

			switch (alt21) {
				case 1 :
					// FortranParserExtras.g:463:8: ( allocate_object T_LBRACKET )=> allocate_object T_LBRACKET allocate_coarray_spec T_RBRACKET
					{
					pushFollow(FOLLOW_allocate_object_in_allocation1889);
					allocate_object();
					state._fsp--;
					if (state.failed) return;
					match(input,T_LBRACKET,FOLLOW_T_LBRACKET_in_allocation1891); if (state.failed) return;
					pushFollow(FOLLOW_allocate_coarray_spec_in_allocation1893);
					allocate_coarray_spec();
					state._fsp--;
					if (state.failed) return;
					match(input,T_RBRACKET,FOLLOW_T_RBRACKET_in_allocation1895); if (state.failed) return;
					if ( state.backtracking==0 ) {hasAllocateCoarraySpec=true;}
					if ( state.backtracking==0 ) {action.allocation(hasAllocateShapeSpecList, hasAllocateCoarraySpec);}
					}
					break;
				case 2 :
					// FortranParserExtras.g:476:8: ( allocate_object )=> allocate_object
					{
					pushFollow(FOLLOW_allocate_object_in_allocation1967);
					allocate_object();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) {action.allocation(hasAllocateShapeSpecList, hasAllocateCoarraySpec);}
					}
					break;

			}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "allocation"



	// $ANTLR start "allocate_object"
	// FortranParserExtras.g:498:1: allocate_object : part_ref_no_image_selector ( T_PERCENT part_ref_no_image_selector )* ;
	public final void allocate_object() throws RecognitionException {
		int numPartRefs = 0;
		try {
			// FortranParserExtras.g:500:4: ( part_ref_no_image_selector ( T_PERCENT part_ref_no_image_selector )* )
			// FortranParserExtras.g:500:8: part_ref_no_image_selector ( T_PERCENT part_ref_no_image_selector )*
			{
			pushFollow(FOLLOW_part_ref_no_image_selector_in_allocate_object2021);
			part_ref_no_image_selector();
			state._fsp--;
			if (state.failed) return;
			if ( state.backtracking==0 ) {numPartRefs += 1;}
			// FortranParserExtras.g:501:8: ( T_PERCENT part_ref_no_image_selector )*
			loop22:
			while (true) {
				int alt22=2;
				int LA22_0 = input.LA(1);
				if ( (LA22_0==T_PERCENT) ) {
					alt22=1;
				}

				switch (alt22) {
				case 1 :
					// FortranParserExtras.g:501:9: T_PERCENT part_ref_no_image_selector
					{
					match(input,T_PERCENT,FOLLOW_T_PERCENT_in_allocate_object2033); if (state.failed) return;
					pushFollow(FOLLOW_part_ref_no_image_selector_in_allocate_object2035);
					part_ref_no_image_selector();
					state._fsp--;
					if (state.failed) return;
					if ( state.backtracking==0 ) {numPartRefs += 1;}
					}
					break;

				default :
					break loop22;
				}
			}

			if ( state.backtracking==0 ) {action.data_ref(numPartRefs); action.allocate_object();}
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "allocate_object"



	// $ANTLR start "allocate_coarray_spec"
	// FortranParserExtras.g:513:1: allocate_coarray_spec options {k=3; } : ( ( T_ASTERISK )=> T_ASTERISK | ( expr T_COLON T_ASTERISK )=> expr T_COLON T_ASTERISK );
	public final void allocate_coarray_spec() throws RecognitionException {
		try {
			// FortranParserExtras.g:516:4: ( ( T_ASTERISK )=> T_ASTERISK | ( expr T_COLON T_ASTERISK )=> expr T_COLON T_ASTERISK )
			int alt23=2;
			int LA23_0 = input.LA(1);
			if ( (LA23_0==T_ASTERISK) && (synpred10_FortranParserExtras())) {
				alt23=1;
			}
			else if ( (LA23_0==T_NOT) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==T_PLUS) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==T_MINUS) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==T_DEFINED_OP) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==T_IDENT) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==T_DIGIT_STRING) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==T_CHAR_CONSTANT) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==T_REAL_CONSTANT) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==T_LPAREN) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==T_TRUE) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==T_FALSE) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==BINARY_CONSTANT) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==OCTAL_CONSTANT) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==HEX_CONSTANT) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==T_HOLLERITH) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}
			else if ( (LA23_0==T_LBRACKET) && (synpred11_FortranParserExtras())) {
				alt23=2;
			}

			switch (alt23) {
				case 1 :
					// FortranParserExtras.g:516:8: ( T_ASTERISK )=> T_ASTERISK
					{
					match(input,T_ASTERISK,FOLLOW_T_ASTERISK_in_allocate_coarray_spec2106); if (state.failed) return;
					}
					break;
				case 2 :
					// FortranParserExtras.g:517:8: ( expr T_COLON T_ASTERISK )=> expr T_COLON T_ASTERISK
					{
					pushFollow(FOLLOW_expr_in_allocate_coarray_spec2125);
					expr();
					state._fsp--;
					if (state.failed) return;
					match(input,T_COLON,FOLLOW_T_COLON_in_allocate_coarray_spec2127); if (state.failed) return;
					match(input,T_ASTERISK,FOLLOW_T_ASTERISK_in_allocate_coarray_spec2129); if (state.failed) return;
					}
					break;

			}
			if ( state.backtracking==0 ) {action.allocate_coarray_spec();}
		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "allocate_coarray_spec"



	// $ANTLR start "logical_expr"
	// FortranParserExtras.g:535:1: logical_expr : expr ;
	public final void logical_expr() throws RecognitionException {
		try {
			// FortranParserExtras.g:536:4: ( expr )
			// FortranParserExtras.g:536:8: expr
			{
			pushFollow(FOLLOW_expr_in_logical_expr2158);
			expr();
			state._fsp--;
			if (state.failed) return;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "logical_expr"



	// $ANTLR start "scalar_logical_expr"
	// FortranParserExtras.g:539:1: scalar_logical_expr : expr ;
	public final void scalar_logical_expr() throws RecognitionException {
		try {
			// FortranParserExtras.g:540:4: ( expr )
			// FortranParserExtras.g:540:8: expr
			{
			pushFollow(FOLLOW_expr_in_scalar_logical_expr2175);
			expr();
			state._fsp--;
			if (state.failed) return;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "scalar_logical_expr"



	// $ANTLR start "int_expr"
	// FortranParserExtras.g:552:1: int_expr : expr ;
	public final void int_expr() throws RecognitionException {
		try {
			// FortranParserExtras.g:553:4: ( expr )
			// FortranParserExtras.g:553:8: expr
			{
			pushFollow(FOLLOW_expr_in_int_expr2199);
			expr();
			state._fsp--;
			if (state.failed) return;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "int_expr"



	// $ANTLR start "scalar_int_expr"
	// FortranParserExtras.g:556:1: scalar_int_expr : expr ;
	public final void scalar_int_expr() throws RecognitionException {
		try {
			// FortranParserExtras.g:557:4: ( expr )
			// FortranParserExtras.g:557:8: expr
			{
			pushFollow(FOLLOW_expr_in_scalar_int_expr2216);
			expr();
			state._fsp--;
			if (state.failed) return;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "scalar_int_expr"



	// $ANTLR start "scalar_variable"
	// FortranParserExtras.g:565:1: scalar_variable : expr ;
	public final void scalar_variable() throws RecognitionException {
		try {
			// FortranParserExtras.g:566:4: ( expr )
			// FortranParserExtras.g:566:8: expr
			{
			pushFollow(FOLLOW_expr_in_scalar_variable2238);
			expr();
			state._fsp--;
			if (state.failed) return;
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "scalar_variable"



	// $ANTLR start "lock_variable"
	// FortranParserExtras.g:583:1: lock_variable : scalar_variable ;
	public final void lock_variable() throws RecognitionException {
		try {
			// FortranParserExtras.g:584:4: ( scalar_variable )
			// FortranParserExtras.g:584:8: scalar_variable
			{
			pushFollow(FOLLOW_scalar_variable_in_lock_variable2267);
			scalar_variable();
			state._fsp--;
			if (state.failed) return;
			if ( state.backtracking==0 ) { action.lock_variable(); }
			}

		}
		catch (RecognitionException re) {
			reportError(re);
			recover(input,re);
		}
		finally {
			// do for sure before leaving
		}
	}
	// $ANTLR end "lock_variable"

	// $ANTLR start synpred1_FortranParserExtras
	public final void synpred1_FortranParserExtras_fragment() throws RecognitionException {
		// FortranParserExtras.g:97:8: ( ( label )? T_IMPLICIT )
		// FortranParserExtras.g:97:9: ( label )? T_IMPLICIT
		{
		// FortranParserExtras.g:97:9: ( label )?
		int alt24=2;
		int LA24_0 = input.LA(1);
		if ( (LA24_0==T_DIGIT_STRING) ) {
			alt24=1;
		}
		switch (alt24) {
			case 1 :
				// FortranParserExtras.g:97:10: label
				{
				pushFollow(FOLLOW_label_in_synpred1_FortranParserExtras181);
				label();
				state._fsp--;
				if (state.failed) return;
				}
				break;

		}

		match(input,T_IMPLICIT,FOLLOW_T_IMPLICIT_in_synpred1_FortranParserExtras185); if (state.failed) return;
		}

	}
	// $ANTLR end synpred1_FortranParserExtras

	// $ANTLR start synpred2_FortranParserExtras
	public final void synpred2_FortranParserExtras_fragment() throws RecognitionException {
		// FortranParserExtras.g:98:8: ( ( label )? T_PARAMETER )
		// FortranParserExtras.g:98:9: ( label )? T_PARAMETER
		{
		// FortranParserExtras.g:98:9: ( label )?
		int alt25=2;
		int LA25_0 = input.LA(1);
		if ( (LA25_0==T_DIGIT_STRING) ) {
			alt25=1;
		}
		switch (alt25) {
			case 1 :
				// FortranParserExtras.g:98:10: label
				{
				pushFollow(FOLLOW_label_in_synpred2_FortranParserExtras207);
				label();
				state._fsp--;
				if (state.failed) return;
				}
				break;

		}

		match(input,T_PARAMETER,FOLLOW_T_PARAMETER_in_synpred2_FortranParserExtras211); if (state.failed) return;
		}

	}
	// $ANTLR end synpred2_FortranParserExtras

	// $ANTLR start synpred3_FortranParserExtras
	public final void synpred3_FortranParserExtras_fragment() throws RecognitionException {
		// FortranParserExtras.g:99:8: ( ( label )? T_FORMAT )
		// FortranParserExtras.g:99:9: ( label )? T_FORMAT
		{
		// FortranParserExtras.g:99:9: ( label )?
		int alt26=2;
		int LA26_0 = input.LA(1);
		if ( (LA26_0==T_DIGIT_STRING) ) {
			alt26=1;
		}
		switch (alt26) {
			case 1 :
				// FortranParserExtras.g:99:10: label
				{
				pushFollow(FOLLOW_label_in_synpred3_FortranParserExtras231);
				label();
				state._fsp--;
				if (state.failed) return;
				}
				break;

		}

		match(input,T_FORMAT,FOLLOW_T_FORMAT_in_synpred3_FortranParserExtras235); if (state.failed) return;
		}

	}
	// $ANTLR end synpred3_FortranParserExtras

	// $ANTLR start synpred4_FortranParserExtras
	public final void synpred4_FortranParserExtras_fragment() throws RecognitionException {
		// FortranParserExtras.g:100:8: ( ( label )? T_ENTRY )
		// FortranParserExtras.g:100:9: ( label )? T_ENTRY
		{
		// FortranParserExtras.g:100:9: ( label )?
		int alt27=2;
		int LA27_0 = input.LA(1);
		if ( (LA27_0==T_DIGIT_STRING) ) {
			alt27=1;
		}
		switch (alt27) {
			case 1 :
				// FortranParserExtras.g:100:10: label
				{
				pushFollow(FOLLOW_label_in_synpred4_FortranParserExtras261);
				label();
				state._fsp--;
				if (state.failed) return;
				}
				break;

		}

		match(input,T_ENTRY,FOLLOW_T_ENTRY_in_synpred4_FortranParserExtras265); if (state.failed) return;
		}

	}
	// $ANTLR end synpred4_FortranParserExtras

	// $ANTLR start synpred5_FortranParserExtras
	public final void synpred5_FortranParserExtras_fragment() throws RecognitionException {
		// FortranParserExtras.g:314:8: ( T_IDENT T_LPAREN )
		// FortranParserExtras.g:314:9: T_IDENT T_LPAREN
		{
		match(input,T_IDENT,FOLLOW_T_IDENT_in_synpred5_FortranParserExtras1115); if (state.failed) return;
		match(input,T_LPAREN,FOLLOW_T_LPAREN_in_synpred5_FortranParserExtras1117); if (state.failed) return;
		}

	}
	// $ANTLR end synpred5_FortranParserExtras

	// $ANTLR start synpred6_FortranParserExtras
	public final void synpred6_FortranParserExtras_fragment() throws RecognitionException {
		// FortranParserExtras.g:317:8: ( T_IDENT T_LBRACKET )
		// FortranParserExtras.g:317:9: T_IDENT T_LBRACKET
		{
		match(input,T_IDENT,FOLLOW_T_IDENT_in_synpred6_FortranParserExtras1187); if (state.failed) return;
		match(input,T_LBRACKET,FOLLOW_T_LBRACKET_in_synpred6_FortranParserExtras1189); if (state.failed) return;
		}

	}
	// $ANTLR end synpred6_FortranParserExtras

	// $ANTLR start synpred7_FortranParserExtras
	public final void synpred7_FortranParserExtras_fragment() throws RecognitionException {
		// FortranParserExtras.g:326:8: ( T_IDENT T_LPAREN )
		// FortranParserExtras.g:326:9: T_IDENT T_LPAREN
		{
		match(input,T_IDENT,FOLLOW_T_IDENT_in_synpred7_FortranParserExtras1260); if (state.failed) return;
		match(input,T_LPAREN,FOLLOW_T_LPAREN_in_synpred7_FortranParserExtras1262); if (state.failed) return;
		}

	}
	// $ANTLR end synpred7_FortranParserExtras

	// $ANTLR start synpred8_FortranParserExtras
	public final void synpred8_FortranParserExtras_fragment() throws RecognitionException {
		// FortranParserExtras.g:463:8: ( allocate_object T_LBRACKET )
		// FortranParserExtras.g:463:9: allocate_object T_LBRACKET
		{
		pushFollow(FOLLOW_allocate_object_in_synpred8_FortranParserExtras1872);
		allocate_object();
		state._fsp--;
		if (state.failed) return;
		match(input,T_LBRACKET,FOLLOW_T_LBRACKET_in_synpred8_FortranParserExtras1874); if (state.failed) return;
		}

	}
	// $ANTLR end synpred8_FortranParserExtras

	// $ANTLR start synpred9_FortranParserExtras
	public final void synpred9_FortranParserExtras_fragment() throws RecognitionException {
		// FortranParserExtras.g:476:8: ( allocate_object )
		// FortranParserExtras.g:476:9: allocate_object
		{
		pushFollow(FOLLOW_allocate_object_in_synpred9_FortranParserExtras1952);
		allocate_object();
		state._fsp--;
		if (state.failed) return;
		}

	}
	// $ANTLR end synpred9_FortranParserExtras

	// $ANTLR start synpred10_FortranParserExtras
	public final void synpred10_FortranParserExtras_fragment() throws RecognitionException {
		// FortranParserExtras.g:516:8: ( T_ASTERISK )
		// FortranParserExtras.g:516:9: T_ASTERISK
		{
		match(input,T_ASTERISK,FOLLOW_T_ASTERISK_in_synpred10_FortranParserExtras2088); if (state.failed) return;
		}

	}
	// $ANTLR end synpred10_FortranParserExtras

	// $ANTLR start synpred11_FortranParserExtras
	public final void synpred11_FortranParserExtras_fragment() throws RecognitionException {
		// FortranParserExtras.g:517:8: ( expr T_COLON T_ASTERISK )
		// FortranParserExtras.g:517:9: expr T_COLON T_ASTERISK
		{
		pushFollow(FOLLOW_expr_in_synpred11_FortranParserExtras2116);
		expr();
		state._fsp--;
		if (state.failed) return;
		match(input,T_COLON,FOLLOW_T_COLON_in_synpred11_FortranParserExtras2118); if (state.failed) return;
		match(input,T_ASTERISK,FOLLOW_T_ASTERISK_in_synpred11_FortranParserExtras2120); if (state.failed) return;
		}

	}
	// $ANTLR end synpred11_FortranParserExtras

	// Delegated rules
	public void forall_construct() throws RecognitionException { gFortranParser08.forall_construct(); }

	public void generic_name_list() throws RecognitionException { gFortranParser08.generic_name_list(); }

	public Token name() throws RecognitionException { return gFortranParser08.name(); }

	public void allocation_list() throws RecognitionException { gFortranParser08.allocation_list(); }

	public void output_item() throws RecognitionException { gFortranParser08.output_item(); }

	public void format_specification() throws RecognitionException { gFortranParser08.format_specification(); }

	public void v_list() throws RecognitionException { gFortranParser08.v_list(); }

	public void call_stmt() throws RecognitionException { gFortranParser08.call_stmt(); }

	public void close_spec() throws RecognitionException { gFortranParser08.close_spec(); }

	public void char_selector() throws RecognitionException { gFortranParser08.char_selector(); }

	public void associate_construct() throws RecognitionException { gFortranParser08.associate_construct(); }

	public void imag_part() throws RecognitionException { gFortranParser08.imag_part(); }

	public void rename() throws RecognitionException { gFortranParser08.rename(); }

	public void private_or_sequence() throws RecognitionException { gFortranParser08.private_or_sequence(); }

	public void select_type() throws RecognitionException { gFortranParser08.select_type(); }

	public void where_stmt() throws RecognitionException { gFortranParser08.where_stmt(); }

	public void final_binding() throws RecognitionException { gFortranParser08.final_binding(); }

	public void namelist_stmt() throws RecognitionException { gFortranParser08.namelist_stmt(); }

	public boolean substring_range_or_arg_list() throws RecognitionException { return gFortranParser08.substring_range_or_arg_list(); }

	public void equivalence_object() throws RecognitionException { gFortranParser08.equivalence_object(); }

	public void critical_construct() throws RecognitionException { gFortranParser08.critical_construct(); }

	public void component_attr_spec_list() throws RecognitionException { gFortranParser08.component_attr_spec_list(); }

	public void case_value() throws RecognitionException { gFortranParser08.case_value(); }

	public void specification_part_and_block() throws RecognitionException { gFortranParser08.specification_part_and_block(); }

	public void expr() throws RecognitionException { gFortranParser08.expr(); }

	public void assignment_stmt() throws RecognitionException { gFortranParser08.assignment_stmt(); }

	public void data_pointer_object() throws RecognitionException { gFortranParser08.data_pointer_object(); }

	public void flush_spec_list() throws RecognitionException { gFortranParser08.flush_spec_list(); }

	public void component_def_stmt() throws RecognitionException { gFortranParser08.component_def_stmt(); }

	public void block() throws RecognitionException { gFortranParser08.block(); }

	public void deferred_shape_spec_list() throws RecognitionException { gFortranParser08.deferred_shape_spec_list(); }

	public void errorstop_stmt() throws RecognitionException { gFortranParser08.errorstop_stmt(); }

	public void default_char_variable() throws RecognitionException { gFortranParser08.default_char_variable(); }

	public void end_submodule_stmt() throws RecognitionException { gFortranParser08.end_submodule_stmt(); }

	public void block_construct() throws RecognitionException { gFortranParser08.block_construct(); }

	public void bounds_spec() throws RecognitionException { gFortranParser08.bounds_spec(); }

	public void derived_type_stmt() throws RecognitionException { gFortranParser08.derived_type_stmt(); }

	public void scalar_int_variable() throws RecognitionException { gFortranParser08.scalar_int_variable(); }

	public void allocate_coshape_spec_list() throws RecognitionException { gFortranParser08.allocate_coshape_spec_list(); }

	public void contains_stmt() throws RecognitionException { gFortranParser08.contains_stmt(); }

	public void scalar_constant() throws RecognitionException { gFortranParser08.scalar_constant(); }

	public void where_construct_stmt() throws RecognitionException { gFortranParser08.where_construct_stmt(); }

	public void component_spec() throws RecognitionException { gFortranParser08.component_spec(); }

	public void value_stmt() throws RecognitionException { gFortranParser08.value_stmt(); }

	public void logical_literal_constant() throws RecognitionException { gFortranParser08.logical_literal_constant(); }

	public void interface_block() throws RecognitionException { gFortranParser08.interface_block(); }

	public void letter_spec_list() throws RecognitionException { gFortranParser08.letter_spec_list(); }

	public void substring() throws RecognitionException { gFortranParser08.substring(); }

	public boolean substr_range_or_arg_list_suffix() throws RecognitionException { return gFortranParser08.substr_range_or_arg_list_suffix(); }

	public void selector() throws RecognitionException { gFortranParser08.selector(); }

	public void end_module_stmt() throws RecognitionException { gFortranParser08.end_module_stmt(); }

	public void do_term_action_stmt() throws RecognitionException { gFortranParser08.do_term_action_stmt(); }

	public Token common_block_name() throws RecognitionException { return gFortranParser08.common_block_name(); }

	public void save_stmt() throws RecognitionException { gFortranParser08.save_stmt(); }

	public void component_decl_list() throws RecognitionException { gFortranParser08.component_decl_list(); }

	public void mult_operand() throws RecognitionException { gFortranParser08.mult_operand(); }

	public void volatile_stmt() throws RecognitionException { gFortranParser08.volatile_stmt(); }

	public void end_subroutine_stmt() throws RecognitionException { gFortranParser08.end_subroutine_stmt(); }

	public void block_data() throws RecognitionException { gFortranParser08.block_data(); }

	public void if_then_stmt() throws RecognitionException { gFortranParser08.if_then_stmt(); }

	public void end_select_stmt() throws RecognitionException { gFortranParser08.end_select_stmt(); }

	public void pointer_decl_list() throws RecognitionException { gFortranParser08.pointer_decl_list(); }

	public void ac_spec() throws RecognitionException { gFortranParser08.ac_spec(); }

	public void print_stmt() throws RecognitionException { gFortranParser08.print_stmt(); }

	public Token add_op() throws RecognitionException { return gFortranParser08.add_op(); }

	public void subroutine_subprogram() throws RecognitionException { gFortranParser08.subroutine_subprogram(); }

	public void constant() throws RecognitionException { gFortranParser08.constant(); }

	public void procedure_designator() throws RecognitionException { gFortranParser08.procedure_designator(); }

	public void cray_pointer_assoc() throws RecognitionException { gFortranParser08.cray_pointer_assoc(); }

	public void alloc_opt_list() throws RecognitionException { gFortranParser08.alloc_opt_list(); }

	public void deallocate_stmt() throws RecognitionException { gFortranParser08.deallocate_stmt(); }

	public void inquire_stmt() throws RecognitionException { gFortranParser08.inquire_stmt(); }

	public void actual_arg_spec() throws RecognitionException { gFortranParser08.actual_arg_spec(); }

	public Token object_name() throws RecognitionException { return gFortranParser08.object_name(); }

	public void variable() throws RecognitionException { gFortranParser08.variable(); }

	public void mp_subprogram_stmt() throws RecognitionException { gFortranParser08.mp_subprogram_stmt(); }

	public void parameter_stmt() throws RecognitionException { gFortranParser08.parameter_stmt(); }

	public void where_body_construct() throws RecognitionException { gFortranParser08.where_body_construct(); }

	public void case_construct() throws RecognitionException { gFortranParser08.case_construct(); }

	public void dummy_arg_list() throws RecognitionException { gFortranParser08.dummy_arg_list(); }

	public void allocate_shape_spec() throws RecognitionException { gFortranParser08.allocate_shape_spec(); }

	public void allocate_coshape_spec() throws RecognitionException { gFortranParser08.allocate_coshape_spec(); }

	public void internal_subprogram() throws RecognitionException { gFortranParser08.internal_subprogram(); }

	public void end_enum_stmt() throws RecognitionException { gFortranParser08.end_enum_stmt(); }

	public void dealloc_opt_list() throws RecognitionException { gFortranParser08.dealloc_opt_list(); }

	public void component_decl() throws RecognitionException { gFortranParser08.component_decl(); }

	public void parent_identifier() throws RecognitionException { gFortranParser08.parent_identifier(); }

	public void type_attr_spec() throws RecognitionException { gFortranParser08.type_attr_spec(); }

	public void saved_entity_list() throws RecognitionException { gFortranParser08.saved_entity_list(); }

	public void length_selector() throws RecognitionException { gFortranParser08.length_selector(); }

	public void submodule() throws RecognitionException { gFortranParser08.submodule(); }

	public void cray_pointer_assoc_list() throws RecognitionException { gFortranParser08.cray_pointer_assoc_list(); }

	public void char_constant() throws RecognitionException { gFortranParser08.char_constant(); }

	public void io_implied_do() throws RecognitionException { gFortranParser08.io_implied_do(); }

	public void scalar_default_char_variable() throws RecognitionException { gFortranParser08.scalar_default_char_variable(); }

	public void level_5_expr() throws RecognitionException { gFortranParser08.level_5_expr(); }

	public void case_stmt() throws RecognitionException { gFortranParser08.case_stmt(); }

	public void explicit_shape_spec_list() throws RecognitionException { gFortranParser08.explicit_shape_spec_list(); }

	public void critical_stmt() throws RecognitionException { gFortranParser08.critical_stmt(); }

	public void wait_spec_list() throws RecognitionException { gFortranParser08.wait_spec_list(); }

	public void sync_images_stmt() throws RecognitionException { gFortranParser08.sync_images_stmt(); }

	public void protected_stmt() throws RecognitionException { gFortranParser08.protected_stmt(); }

	public void complex_literal_constant() throws RecognitionException { gFortranParser08.complex_literal_constant(); }

	public void sync_memory_stmt() throws RecognitionException { gFortranParser08.sync_memory_stmt(); }

	public void ac_value() throws RecognitionException { gFortranParser08.ac_value(); }

	public Token extended_intrinsic_op() throws RecognitionException { return gFortranParser08.extended_intrinsic_op(); }

	public void language_binding_spec() throws RecognitionException { gFortranParser08.language_binding_spec(); }

	public void int_variable() throws RecognitionException { gFortranParser08.int_variable(); }

	public void dummy_arg() throws RecognitionException { gFortranParser08.dummy_arg(); }

	public void case_value_range_list() throws RecognitionException { gFortranParser08.case_value_range_list(); }

	public void intrinsic_stmt() throws RecognitionException { gFortranParser08.intrinsic_stmt(); }

	public void allocatable_stmt() throws RecognitionException { gFortranParser08.allocatable_stmt(); }

	public void enum_def() throws RecognitionException { gFortranParser08.enum_def(); }

	public void end_where_stmt() throws RecognitionException { gFortranParser08.end_where_stmt(); }

	public void forall_triplet_spec() throws RecognitionException { gFortranParser08.forall_triplet_spec(); }

	public void scalar_int_constant() throws RecognitionException { gFortranParser08.scalar_int_constant(); }

	public void arithmetic_if_stmt() throws RecognitionException { gFortranParser08.arithmetic_if_stmt(); }

	public Token and_op() throws RecognitionException { return gFortranParser08.and_op(); }

	public void lock_stat() throws RecognitionException { gFortranParser08.lock_stat(); }

	public void proc_attr_spec() throws RecognitionException { gFortranParser08.proc_attr_spec(); }

	public void implicit_spec() throws RecognitionException { gFortranParser08.implicit_spec(); }

	public void data_i_do_object() throws RecognitionException { gFortranParser08.data_i_do_object(); }

	public void generic_binding() throws RecognitionException { gFortranParser08.generic_binding(); }

	public void assign_stmt() throws RecognitionException { gFortranParser08.assign_stmt(); }

	public void signed_int_literal_constant() throws RecognitionException { gFortranParser08.signed_int_literal_constant(); }

	public void char_literal_constant() throws RecognitionException { gFortranParser08.char_literal_constant(); }

	public void allocate_object_list() throws RecognitionException { gFortranParser08.allocate_object_list(); }

	public void rewind_stmt() throws RecognitionException { gFortranParser08.rewind_stmt(); }

	public void end_forall_stmt() throws RecognitionException { gFortranParser08.end_forall_stmt(); }

	public void access_id_list() throws RecognitionException { gFortranParser08.access_id_list(); }

	public void designator_or_func_ref() throws RecognitionException { gFortranParser08.designator_or_func_ref(); }

	public void result_name() throws RecognitionException { gFortranParser08.result_name(); }

	public void module_subprogram() throws RecognitionException { gFortranParser08.module_subprogram(); }

	public void target_stmt() throws RecognitionException { gFortranParser08.target_stmt(); }

	public void enum_def_stmt() throws RecognitionException { gFortranParser08.enum_def_stmt(); }

	public void select_case_stmt() throws RecognitionException { gFortranParser08.select_case_stmt(); }

	public void pointer_assignment_stmt() throws RecognitionException { gFortranParser08.pointer_assignment_stmt(); }

	public void separate_module_subprogram() throws RecognitionException { gFortranParser08.separate_module_subprogram(); }

	public void sync_stat() throws RecognitionException { gFortranParser08.sync_stat(); }

	public void codimension_stmt() throws RecognitionException { gFortranParser08.codimension_stmt(); }

	public void common_block_object() throws RecognitionException { gFortranParser08.common_block_object(); }

	public void proc_component_attr_spec_list() throws RecognitionException { gFortranParser08.proc_component_attr_spec_list(); }

	public void type_param_or_comp_def_stmt() throws RecognitionException { gFortranParser08.type_param_or_comp_def_stmt(); }

	public void equivalence_set_list() throws RecognitionException { gFortranParser08.equivalence_set_list(); }

	public void block_data_stmt() throws RecognitionException { gFortranParser08.block_data_stmt(); }

	public void block_stmt() throws RecognitionException { gFortranParser08.block_stmt(); }

	public void sync_stat_list() throws RecognitionException { gFortranParser08.sync_stat_list(); }

	public void data_component_def_stmt() throws RecognitionException { gFortranParser08.data_component_def_stmt(); }

	public void level_1_expr() throws RecognitionException { gFortranParser08.level_1_expr(); }

	public void attr_spec_extension() throws RecognitionException { gFortranParser08.attr_spec_extension(); }

	public void array_constructor() throws RecognitionException { gFortranParser08.array_constructor(); }

	public void io_control_spec_list() throws RecognitionException { gFortranParser08.io_control_spec_list(); }

	public void bounds_remapping_list() throws RecognitionException { gFortranParser08.bounds_remapping_list(); }

	public void coarray_spec() throws RecognitionException { gFortranParser08.coarray_spec(); }

	public void where_construct() throws RecognitionException { gFortranParser08.where_construct(); }

	public void inquire_spec() throws RecognitionException { gFortranParser08.inquire_spec(); }

	public void private_components_stmt() throws RecognitionException { gFortranParser08.private_components_stmt(); }

	public void connect_spec_list() throws RecognitionException { gFortranParser08.connect_spec_list(); }

	public void derived_type_def() throws RecognitionException { gFortranParser08.derived_type_def(); }

	public void actual_arg_spec_list() throws RecognitionException { gFortranParser08.actual_arg_spec_list(); }

	public void defined_io_generic_spec() throws RecognitionException { gFortranParser08.defined_io_generic_spec(); }

	public void prefix() throws RecognitionException { gFortranParser08.prefix(); }

	public void null_init() throws RecognitionException { gFortranParser08.null_init(); }

	public void return_stmt() throws RecognitionException { gFortranParser08.return_stmt(); }

	public void format_item_list() throws RecognitionException { gFortranParser08.format_item_list(); }

	public void implicit_stmt() throws RecognitionException { gFortranParser08.implicit_stmt(); }

	public void data_stmt_value_list() throws RecognitionException { gFortranParser08.data_stmt_value_list(); }

	public void logical_variable() throws RecognitionException { gFortranParser08.logical_variable(); }

	public void explicit_shape_spec() throws RecognitionException { gFortranParser08.explicit_shape_spec(); }

	public void allocatable_decl() throws RecognitionException { gFortranParser08.allocatable_decl(); }

	public void pointer_object_list() throws RecognitionException { gFortranParser08.pointer_object_list(); }

	public void ac_value_list() throws RecognitionException { gFortranParser08.ac_value_list(); }

	public void flush_stmt() throws RecognitionException { gFortranParser08.flush_stmt(); }

	public void unlock_stmt() throws RecognitionException { gFortranParser08.unlock_stmt(); }

	public void power_operand() throws RecognitionException { gFortranParser08.power_operand(); }

	public void data_stmt_set() throws RecognitionException { gFortranParser08.data_stmt_set(); }

	public void if_stmt() throws RecognitionException { gFortranParser08.if_stmt(); }

	public void lock_stat_list() throws RecognitionException { gFortranParser08.lock_stat_list(); }

	public void only_list() throws RecognitionException { gFortranParser08.only_list(); }

	public void procedure_stmt() throws RecognitionException { gFortranParser08.procedure_stmt(); }

	public void case_selector() throws RecognitionException { gFortranParser08.case_selector(); }

	public void end_associate_stmt() throws RecognitionException { gFortranParser08.end_associate_stmt(); }

	public void initialization() throws RecognitionException { gFortranParser08.initialization(); }

	public void interface_stmt() throws RecognitionException { gFortranParser08.interface_stmt(); }

	public void end_mp_subprogram_stmt() throws RecognitionException { gFortranParser08.end_mp_subprogram_stmt(); }

	public void array_spec() throws RecognitionException { gFortranParser08.array_spec(); }

	public void derived_type_spec() throws RecognitionException { gFortranParser08.derived_type_spec(); }

	public void io_implied_do_object() throws RecognitionException { gFortranParser08.io_implied_do_object(); }

	public Token rel_op() throws RecognitionException { return gFortranParser08.rel_op(); }

	public void end_function_stmt() throws RecognitionException { gFortranParser08.end_function_stmt(); }

	public void end_type_stmt() throws RecognitionException { gFortranParser08.end_type_stmt(); }

	public void lock_stmt() throws RecognitionException { gFortranParser08.lock_stmt(); }

	public void only() throws RecognitionException { gFortranParser08.only(); }

	public void forall_body_construct() throws RecognitionException { gFortranParser08.forall_body_construct(); }

	public void proc_decl_list() throws RecognitionException { gFortranParser08.proc_decl_list(); }

	public void named_constant_def() throws RecognitionException { gFortranParser08.named_constant_def(); }

	public void write_stmt() throws RecognitionException { gFortranParser08.write_stmt(); }

	public void access_id() throws RecognitionException { gFortranParser08.access_id(); }

	public void if_construct() throws RecognitionException { gFortranParser08.if_construct(); }

	public void forall_construct_stmt() throws RecognitionException { gFortranParser08.forall_construct_stmt(); }

	public void binding_attr_list() throws RecognitionException { gFortranParser08.binding_attr_list(); }

	public void format_item() throws RecognitionException { gFortranParser08.format_item(); }

	public void scalar_int_literal_constant() throws RecognitionException { gFortranParser08.scalar_int_literal_constant(); }

	public void exit_stmt() throws RecognitionException { gFortranParser08.exit_stmt(); }

	public void loop_control() throws RecognitionException { gFortranParser08.loop_control(); }

	public Token or_op() throws RecognitionException { return gFortranParser08.or_op(); }

	public void data_stmt_value() throws RecognitionException { gFortranParser08.data_stmt_value(); }

	public void target_decl_list() throws RecognitionException { gFortranParser08.target_decl_list(); }

	public void case_value_range() throws RecognitionException { gFortranParser08.case_value_range(); }

	public void stop_code() throws RecognitionException { gFortranParser08.stop_code(); }

	public void access_spec() throws RecognitionException { gFortranParser08.access_spec(); }

	public void end_interface_stmt() throws RecognitionException { gFortranParser08.end_interface_stmt(); }

	public void kind_selector() throws RecognitionException { gFortranParser08.kind_selector(); }

	public void implicit_spec_list() throws RecognitionException { gFortranParser08.implicit_spec_list(); }

	public void import_stmt() throws RecognitionException { gFortranParser08.import_stmt(); }

	public void intrinsic_type_spec() throws RecognitionException { gFortranParser08.intrinsic_type_spec(); }

	public void allocatable_decl_list() throws RecognitionException { gFortranParser08.allocatable_decl_list(); }

	public void module() throws RecognitionException { gFortranParser08.module(); }

	public void signed_operand() throws RecognitionException { gFortranParser08.signed_operand(); }

	public void bind_stmt() throws RecognitionException { gFortranParser08.bind_stmt(); }

	public void assigned_goto_stmt() throws RecognitionException { gFortranParser08.assigned_goto_stmt(); }

	public void rename_list() throws RecognitionException { gFortranParser08.rename_list(); }

	public void target_decl() throws RecognitionException { gFortranParser08.target_decl(); }

	public void codimension_decl_list() throws RecognitionException { gFortranParser08.codimension_decl_list(); }

	public void equivalence_stmt() throws RecognitionException { gFortranParser08.equivalence_stmt(); }

	public void interface_body() throws RecognitionException { gFortranParser08.interface_body(); }

	public void intent_spec() throws RecognitionException { gFortranParser08.intent_spec(); }

	public void data_stmt_constant() throws RecognitionException { gFortranParser08.data_stmt_constant(); }

	public void module_nature() throws RecognitionException { gFortranParser08.module_nature(); }

	public void io_implied_do_control() throws RecognitionException { gFortranParser08.io_implied_do_control(); }

	public void type_param_attr_spec() throws RecognitionException { gFortranParser08.type_param_attr_spec(); }

	public void common_block_object_list() throws RecognitionException { gFortranParser08.common_block_object_list(); }

	public void do_variable() throws RecognitionException { gFortranParser08.do_variable(); }

	public void masked_elsewhere_stmt() throws RecognitionException { gFortranParser08.masked_elsewhere_stmt(); }

	public void type_param_value() throws RecognitionException { gFortranParser08.type_param_value(); }

	public Token mult_op() throws RecognitionException { return gFortranParser08.mult_op(); }

	public void continue_stmt() throws RecognitionException { gFortranParser08.continue_stmt(); }

	public void execution_part_construct() throws RecognitionException { gFortranParser08.execution_part_construct(); }

	public Token label() throws RecognitionException { return gFortranParser08.label(); }

	public void char_length() throws RecognitionException { gFortranParser08.char_length(); }

	public void stmt_label_list() throws RecognitionException { gFortranParser08.stmt_label_list(); }

	public void codimension_decl() throws RecognitionException { gFortranParser08.codimension_decl(); }

	public void boz_literal_constant() throws RecognitionException { gFortranParser08.boz_literal_constant(); }

	public void wait_stmt() throws RecognitionException { gFortranParser08.wait_stmt(); }

	public void and_operand() throws RecognitionException { gFortranParser08.and_operand(); }

	public void int_constant() throws RecognitionException { gFortranParser08.int_constant(); }

	public void dealloc_opt() throws RecognitionException { gFortranParser08.dealloc_opt(); }

	public void label_list() throws RecognitionException { gFortranParser08.label_list(); }

	public void io_control_spec() throws RecognitionException { gFortranParser08.io_control_spec(); }

	public void function_stmt() throws RecognitionException { gFortranParser08.function_stmt(); }

	public void do_stmt() throws RecognitionException { gFortranParser08.do_stmt(); }

	public Token concat_op() throws RecognitionException { return gFortranParser08.concat_op(); }

	public void entry_stmt() throws RecognitionException { gFortranParser08.entry_stmt(); }

	public void vector_subscript() throws RecognitionException { gFortranParser08.vector_subscript(); }

	public void nullify_stmt() throws RecognitionException { gFortranParser08.nullify_stmt(); }

	public void data_ref() throws RecognitionException { gFortranParser08.data_ref(); }

	public void signed_real_literal_constant() throws RecognitionException { gFortranParser08.signed_real_literal_constant(); }

	public void proc_interface() throws RecognitionException { gFortranParser08.proc_interface(); }

	public void substring_range() throws RecognitionException { gFortranParser08.substring_range(); }

	public void end_if_stmt() throws RecognitionException { gFortranParser08.end_if_stmt(); }

	public void endfile_stmt() throws RecognitionException { gFortranParser08.endfile_stmt(); }

	public Token not_op() throws RecognitionException { return gFortranParser08.not_op(); }

	public void use_stmt() throws RecognitionException { gFortranParser08.use_stmt(); }

	public void level_3_expr() throws RecognitionException { gFortranParser08.level_3_expr(); }

	public void image_set() throws RecognitionException { gFortranParser08.image_set(); }

	public void procedure_declaration_stmt() throws RecognitionException { gFortranParser08.procedure_declaration_stmt(); }

	public void type_param_decl() throws RecognitionException { gFortranParser08.type_param_decl(); }

	public void goto_stmt() throws RecognitionException { gFortranParser08.goto_stmt(); }

	public void type_param_or_comp_def_stmt_list() throws RecognitionException { gFortranParser08.type_param_or_comp_def_stmt_list(); }

	public void sequence_stmt() throws RecognitionException { gFortranParser08.sequence_stmt(); }

	public void file_unit_number() throws RecognitionException { gFortranParser08.file_unit_number(); }

	public void structure_constructor() throws RecognitionException { gFortranParser08.structure_constructor(); }

	public void proc_pointer_object() throws RecognitionException { gFortranParser08.proc_pointer_object(); }

	public void designator() throws RecognitionException { gFortranParser08.designator(); }

	public Token intrinsic_operator() throws RecognitionException { return gFortranParser08.intrinsic_operator(); }

	public void dimension_stmt() throws RecognitionException { gFortranParser08.dimension_stmt(); }

	public void t_prefix() throws RecognitionException { gFortranParser08.t_prefix(); }

	public void specific_binding() throws RecognitionException { gFortranParser08.specific_binding(); }

	public void hollerith_literal_constant() throws RecognitionException { gFortranParser08.hollerith_literal_constant(); }

	public void read_stmt() throws RecognitionException { gFortranParser08.read_stmt(); }

	public void execution_part() throws RecognitionException { gFortranParser08.execution_part(); }

	public void data_stmt() throws RecognitionException { gFortranParser08.data_stmt(); }

	public void binding_private_stmt() throws RecognitionException { gFortranParser08.binding_private_stmt(); }

	public void equivalence_object_list() throws RecognitionException { gFortranParser08.equivalence_object_list(); }

	public void actual_arg() throws RecognitionException { gFortranParser08.actual_arg(); }

	public void inquire_spec_list() throws RecognitionException { gFortranParser08.inquire_spec_list(); }

	public void generic_spec() throws RecognitionException { gFortranParser08.generic_spec(); }

	public void prefix_spec() throws RecognitionException { gFortranParser08.prefix_spec(); }

	public void function_subprogram() throws RecognitionException { gFortranParser08.function_subprogram(); }

	public void scalar_char_constant() throws RecognitionException { gFortranParser08.scalar_char_constant(); }

	public void block_do_construct() throws RecognitionException { gFortranParser08.block_do_construct(); }

	public void real_literal_constant() throws RecognitionException { gFortranParser08.real_literal_constant(); }

	public void end_block_stmt() throws RecognitionException { gFortranParser08.end_block_stmt(); }

	public void case_value_range_suffix() throws RecognitionException { gFortranParser08.case_value_range_suffix(); }

	public void equivalence_set() throws RecognitionException { gFortranParser08.equivalence_set(); }

	public void ac_implied_do_control() throws RecognitionException { gFortranParser08.ac_implied_do_control(); }

	public void cycle_stmt() throws RecognitionException { gFortranParser08.cycle_stmt(); }

	public void pointer_object() throws RecognitionException { gFortranParser08.pointer_object(); }

	public Token equiv_op() throws RecognitionException { return gFortranParser08.equiv_op(); }

	public void module_stmt() throws RecognitionException { gFortranParser08.module_stmt(); }

	public void type_param_decl_list() throws RecognitionException { gFortranParser08.type_param_decl_list(); }

	public void other_specification_stmt() throws RecognitionException { gFortranParser08.other_specification_stmt(); }

	public void label_do_stmt() throws RecognitionException { gFortranParser08.label_do_stmt(); }

	public void submodule_stmt() throws RecognitionException { gFortranParser08.submodule_stmt(); }

	public void stop_stmt() throws RecognitionException { gFortranParser08.stop_stmt(); }

	public void letter_spec() throws RecognitionException { gFortranParser08.letter_spec(); }

	public void connect_spec() throws RecognitionException { gFortranParser08.connect_spec(); }

	public void declaration_type_spec() throws RecognitionException { gFortranParser08.declaration_type_spec(); }

	public void internal_subprogram_part() throws RecognitionException { gFortranParser08.internal_subprogram_part(); }

	public void enumerator() throws RecognitionException { gFortranParser08.enumerator(); }

	public void type_attr_spec_list() throws RecognitionException { gFortranParser08.type_attr_spec_list(); }

	public void forall_stmt() throws RecognitionException { gFortranParser08.forall_stmt(); }

	public void declaration_construct_and_block() throws RecognitionException { gFortranParser08.declaration_construct_and_block(); }

	public void program_stmt() throws RecognitionException { gFortranParser08.program_stmt(); }

	public void subroutine_stmt() throws RecognitionException { gFortranParser08.subroutine_stmt(); }

	public Token defined_unary_op() throws RecognitionException { return gFortranParser08.defined_unary_op(); }

	public void end_program_stmt() throws RecognitionException { gFortranParser08.end_program_stmt(); }

	public void else_if_stmt() throws RecognitionException { gFortranParser08.else_if_stmt(); }

	public void component_spec_list() throws RecognitionException { gFortranParser08.component_spec_list(); }

	public void optional_stmt() throws RecognitionException { gFortranParser08.optional_stmt(); }

	public void type_spec() throws RecognitionException { gFortranParser08.type_spec(); }

	public void entity_decl() throws RecognitionException { gFortranParser08.entity_decl(); }

	public void char_variable() throws RecognitionException { gFortranParser08.char_variable(); }

	public void allocate_stmt() throws RecognitionException { gFortranParser08.allocate_stmt(); }

	public void type_bound_procedure_part() throws RecognitionException { gFortranParser08.type_bound_procedure_part(); }

	public void close_stmt() throws RecognitionException { gFortranParser08.close_stmt(); }

	public void pointer_stmt() throws RecognitionException { gFortranParser08.pointer_stmt(); }

	public void dtv_type_spec() throws RecognitionException { gFortranParser08.dtv_type_spec(); }

	public void saved_entity() throws RecognitionException { gFortranParser08.saved_entity(); }

	public void proc_binding_stmt() throws RecognitionException { gFortranParser08.proc_binding_stmt(); }

	public void named_constant_def_list() throws RecognitionException { gFortranParser08.named_constant_def_list(); }

	public void select_type_stmt() throws RecognitionException { gFortranParser08.select_type_stmt(); }

	public void add_operand() throws RecognitionException { gFortranParser08.add_operand(); }

	public void associate_stmt() throws RecognitionException { gFortranParser08.associate_stmt(); }

	public void output_item_list() throws RecognitionException { gFortranParser08.output_item_list(); }

	public void intent_stmt() throws RecognitionException { gFortranParser08.intent_stmt(); }

	public void pointer_decl() throws RecognitionException { gFortranParser08.pointer_decl(); }

	public void real_part() throws RecognitionException { gFortranParser08.real_part(); }

	public void allocate_shape_spec_list() throws RecognitionException { gFortranParser08.allocate_shape_spec_list(); }

	public void declaration_construct() throws RecognitionException { gFortranParser08.declaration_construct(); }

	public void component_initialization() throws RecognitionException { gFortranParser08.component_initialization(); }

	public void alloc_opt() throws RecognitionException { gFortranParser08.alloc_opt(); }

	public void format() throws RecognitionException { gFortranParser08.format(); }

	public void namelist_group_object_list() throws RecognitionException { gFortranParser08.namelist_group_object_list(); }

	public void dimension_decl() throws RecognitionException { gFortranParser08.dimension_decl(); }

	public void bounds_remapping() throws RecognitionException { gFortranParser08.bounds_remapping(); }

	public void position_spec_list() throws RecognitionException { gFortranParser08.position_spec_list(); }

	public void type_guard_stmt() throws RecognitionException { gFortranParser08.type_guard_stmt(); }

	public void attr_spec() throws RecognitionException { gFortranParser08.attr_spec(); }

	public void forall_assignment_stmt() throws RecognitionException { gFortranParser08.forall_assignment_stmt(); }

	public void data_stmt_object_list() throws RecognitionException { gFortranParser08.data_stmt_object_list(); }

	public void component_attr_spec_extension() throws RecognitionException { gFortranParser08.component_attr_spec_extension(); }

	public Token power_op() throws RecognitionException { return gFortranParser08.power_op(); }

	public void end_block_data_stmt() throws RecognitionException { gFortranParser08.end_block_data_stmt(); }

	public void literal_constant() throws RecognitionException { gFortranParser08.literal_constant(); }

	public void external_stmt() throws RecognitionException { gFortranParser08.external_stmt(); }

	public void int_literal_constant() throws RecognitionException { gFortranParser08.int_literal_constant(); }

	public void proc_decl() throws RecognitionException { gFortranParser08.proc_decl(); }

	public void flush_spec() throws RecognitionException { gFortranParser08.flush_spec(); }

	public void else_stmt() throws RecognitionException { gFortranParser08.else_stmt(); }

	public void format_stmt() throws RecognitionException { gFortranParser08.format_stmt(); }

	public void end_select_type_stmt() throws RecognitionException { gFortranParser08.end_select_type_stmt(); }

	public void forall_triplet_spec_list() throws RecognitionException { gFortranParser08.forall_triplet_spec_list(); }

	public void elsewhere_stmt() throws RecognitionException { gFortranParser08.elsewhere_stmt(); }

	public void data_i_do_object_list() throws RecognitionException { gFortranParser08.data_i_do_object_list(); }

	public void equiv_operand() throws RecognitionException { gFortranParser08.equiv_operand(); }

	public void interface_specification() throws RecognitionException { gFortranParser08.interface_specification(); }

	public void proc_component_def_stmt() throws RecognitionException { gFortranParser08.proc_component_def_stmt(); }

	public Token end_of_stmt() throws RecognitionException { return gFortranParser08.end_of_stmt(); }

	public void position_spec() throws RecognitionException { gFortranParser08.position_spec(); }

	public void primary() throws RecognitionException { gFortranParser08.primary(); }

	public void forall_header() throws RecognitionException { gFortranParser08.forall_header(); }

	public void array_spec_element() throws RecognitionException { gFortranParser08.array_spec_element(); }

	public void main_program() throws RecognitionException { gFortranParser08.main_program(); }

	public void open_stmt() throws RecognitionException { gFortranParser08.open_stmt(); }

	public void suffix() throws RecognitionException { gFortranParser08.suffix(); }

	public void binding_attr() throws RecognitionException { gFortranParser08.binding_attr(); }

	public void data_stmt_object() throws RecognitionException { gFortranParser08.data_stmt_object(); }

	public void type_param_spec() throws RecognitionException { gFortranParser08.type_param_spec(); }

	public void io_unit() throws RecognitionException { gFortranParser08.io_unit(); }

	public Token keyword() throws RecognitionException { return gFortranParser08.keyword(); }

	public void level_2_expr() throws RecognitionException { gFortranParser08.level_2_expr(); }

	public void type_param_spec_list() throws RecognitionException { gFortranParser08.type_param_spec_list(); }

	public void end_do() throws RecognitionException { gFortranParser08.end_do(); }

	public void common_stmt() throws RecognitionException { gFortranParser08.common_stmt(); }

	public void bind_entity_list() throws RecognitionException { gFortranParser08.bind_entity_list(); }

	public void data_implied_do() throws RecognitionException { gFortranParser08.data_implied_do(); }

	public void do_construct() throws RecognitionException { gFortranParser08.do_construct(); }

	public void backspace_stmt() throws RecognitionException { gFortranParser08.backspace_stmt(); }

	public void access_stmt() throws RecognitionException { gFortranParser08.access_stmt(); }

	public void input_item() throws RecognitionException { gFortranParser08.input_item(); }

	public void enumerator_list() throws RecognitionException { gFortranParser08.enumerator_list(); }

	public void end_do_stmt() throws RecognitionException { gFortranParser08.end_do_stmt(); }

	public void or_operand() throws RecognitionException { gFortranParser08.or_operand(); }

	public void proc_attr_spec_extension() throws RecognitionException { gFortranParser08.proc_attr_spec_extension(); }

	public void bind_entity() throws RecognitionException { gFortranParser08.bind_entity(); }

	public void asynchronous_stmt() throws RecognitionException { gFortranParser08.asynchronous_stmt(); }

	public void association_list() throws RecognitionException { gFortranParser08.association_list(); }

	public void end_critical_stmt() throws RecognitionException { gFortranParser08.end_critical_stmt(); }

	public void component_array_spec() throws RecognitionException { gFortranParser08.component_array_spec(); }

	public void wait_spec() throws RecognitionException { gFortranParser08.wait_spec(); }

	public void ext_function_subprogram() throws RecognitionException { gFortranParser08.ext_function_subprogram(); }

	public void module_subprogram_part() throws RecognitionException { gFortranParser08.module_subprogram_part(); }

	public void pause_stmt() throws RecognitionException { gFortranParser08.pause_stmt(); }

	public Token defined_binary_op() throws RecognitionException { return gFortranParser08.defined_binary_op(); }

	public void ac_implied_do() throws RecognitionException { gFortranParser08.ac_implied_do(); }

	public void io_implied_do_suffix() throws RecognitionException { gFortranParser08.io_implied_do_suffix(); }

	public void stmt_function_stmt() throws RecognitionException { gFortranParser08.stmt_function_stmt(); }

	public void sync_all_stmt() throws RecognitionException { gFortranParser08.sync_all_stmt(); }

	public void proc_language_binding_spec() throws RecognitionException { gFortranParser08.proc_language_binding_spec(); }

	public Token kind_param() throws RecognitionException { return gFortranParser08.kind_param(); }

	public void component_attr_spec() throws RecognitionException { gFortranParser08.component_attr_spec(); }

	public void input_item_list() throws RecognitionException { gFortranParser08.input_item_list(); }

	public void component_data_source() throws RecognitionException { gFortranParser08.component_data_source(); }

	public void entity_decl_list() throws RecognitionException { gFortranParser08.entity_decl_list(); }

	public void enumerator_def_stmt() throws RecognitionException { gFortranParser08.enumerator_def_stmt(); }

	public void defined_operator() throws RecognitionException { gFortranParser08.defined_operator(); }

	public void t_prefix_spec() throws RecognitionException { gFortranParser08.t_prefix_spec(); }

	public void proc_component_attr_spec() throws RecognitionException { gFortranParser08.proc_component_attr_spec(); }

	public void computed_goto_stmt() throws RecognitionException { gFortranParser08.computed_goto_stmt(); }

	public void association() throws RecognitionException { gFortranParser08.association(); }

	public void select_type_construct() throws RecognitionException { gFortranParser08.select_type_construct(); }

	public void close_spec_list() throws RecognitionException { gFortranParser08.close_spec_list(); }

	public void default_logical_variable() throws RecognitionException { gFortranParser08.default_logical_variable(); }

	public void bounds_spec_list() throws RecognitionException { gFortranParser08.bounds_spec_list(); }

	public void scalar_default_logical_variable() throws RecognitionException { gFortranParser08.scalar_default_logical_variable(); }

	public final boolean synpred6_FortranParserExtras() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred6_FortranParserExtras_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred4_FortranParserExtras() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred4_FortranParserExtras_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred8_FortranParserExtras() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred8_FortranParserExtras_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred11_FortranParserExtras() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred11_FortranParserExtras_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred10_FortranParserExtras() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred10_FortranParserExtras_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred3_FortranParserExtras() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred3_FortranParserExtras_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred5_FortranParserExtras() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred5_FortranParserExtras_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred7_FortranParserExtras() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred7_FortranParserExtras_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred2_FortranParserExtras() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred2_FortranParserExtras_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred1_FortranParserExtras() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred1_FortranParserExtras_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}
	public final boolean synpred9_FortranParserExtras() {
		state.backtracking++;
		int start = input.mark();
		try {
			synpred9_FortranParserExtras_fragment(); // can never throw exception
		} catch (RecognitionException re) {
			System.err.println("impossible: "+re);
		}
		boolean success = !state.failed;
		input.rewind(start);
		state.backtracking--;
		state.failed=false;
		return success;
	}


	protected DFA4 dfa4 = new DFA4(this);
	static final String DFA4_eotS =
		"\145\uffff";
	static final String DFA4_eofS =
		"\145\uffff";
	static final String DFA4_minS =
		"\1\23\1\0\1\uffff\3\0\137\uffff";
	static final String DFA4_maxS =
		"\1\u00f2\1\0\1\uffff\3\0\137\uffff";
	static final String DFA4_acceptS =
		"\2\uffff\1\1\3\uffff\1\5\133\uffff\1\2\1\3\1\4";
	static final String DFA4_specialS =
		"\1\0\1\1\1\uffff\1\2\1\3\1\4\137\uffff}>";
	static final String[] DFA4_transitionS = {
			"\1\6\2\uffff\3\6\1\uffff\2\6\1\uffff\2\6\1\uffff\1\6\1\uffff\1\6\1\uffff"+
			"\2\6\1\uffff\1\6\1\uffff\1\6\2\uffff\3\6\3\uffff\2\6\1\uffff\1\6\1\uffff"+
			"\1\6\3\uffff\3\6\1\uffff\1\6\3\uffff\1\1\5\6\5\uffff\1\6\1\uffff\2\6"+
			"\3\uffff\1\6\1\uffff\1\6\2\uffff\3\6\2\uffff\1\6\3\uffff\1\5\1\6\5\uffff"+
			"\1\6\3\uffff\1\6\1\uffff\1\6\1\uffff\1\6\4\uffff\1\6\1\uffff\2\6\1\4"+
			"\4\uffff\2\6\4\uffff\3\6\1\uffff\1\2\5\uffff\6\6\7\uffff\1\6\1\uffff"+
			"\1\6\5\uffff\1\6\10\uffff\1\6\1\uffff\1\6\1\uffff\1\6\2\uffff\1\3\1\uffff"+
			"\1\6\4\uffff\1\6\2\uffff\3\6\1\uffff\3\6\2\uffff\2\6\3\uffff\2\6\1\uffff"+
			"\4\6\5\uffff\2\6\2\uffff\2\6\5\uffff\1\6\2\uffff\1\6\1\uffff\3\6\1\uffff"+
			"\2\6\3\uffff\1\6",
			"\1\uffff",
			"",
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
			"",
			"",
			""
	};

	static final short[] DFA4_eot = DFA.unpackEncodedString(DFA4_eotS);
	static final short[] DFA4_eof = DFA.unpackEncodedString(DFA4_eofS);
	static final char[] DFA4_min = DFA.unpackEncodedStringToUnsignedChars(DFA4_minS);
	static final char[] DFA4_max = DFA.unpackEncodedStringToUnsignedChars(DFA4_maxS);
	static final short[] DFA4_accept = DFA.unpackEncodedString(DFA4_acceptS);
	static final short[] DFA4_special = DFA.unpackEncodedString(DFA4_specialS);
	static final short[][] DFA4_transition;

	static {
		int numStates = DFA4_transitionS.length;
		DFA4_transition = new short[numStates][];
		for (int i=0; i<numStates; i++) {
			DFA4_transition[i] = DFA.unpackEncodedString(DFA4_transitionS[i]);
		}
	}

	protected class DFA4 extends DFA {

		public DFA4(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			this.decisionNumber = 4;
			this.eot = DFA4_eot;
			this.eof = DFA4_eof;
			this.min = DFA4_min;
			this.max = DFA4_max;
			this.accept = DFA4_accept;
			this.special = DFA4_special;
			this.transition = DFA4_transition;
		}
		@Override
		public String getDescription() {
			return "96:1: implicit_part_recursion : ( ( ( label )? T_IMPLICIT )=> implicit_stmt implicit_part_recursion | ( ( label )? T_PARAMETER )=> parameter_stmt implicit_part_recursion | ( ( label )? T_FORMAT )=> format_stmt implicit_part_recursion | ( ( label )? T_ENTRY )=> entry_stmt implicit_part_recursion |);";
		}
		@Override
		public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
			TokenStream input = (TokenStream)_input;
			int _s = s;
			switch ( s ) {
					case 0 : 
						int LA4_0 = input.LA(1);
						 
						int index4_0 = input.index();
						input.rewind();
						s = -1;
						if ( (LA4_0==T_DIGIT_STRING) ) {s = 1;}
						else if ( (LA4_0==T_IMPLICIT) && (synpred1_FortranParserExtras())) {s = 2;}
						else if ( (LA4_0==T_PARAMETER) ) {s = 3;}
						else if ( (LA4_0==T_FORMAT) ) {s = 4;}
						else if ( (LA4_0==T_ENTRY) ) {s = 5;}
						else if ( (LA4_0==T_ABSTRACT||(LA4_0 >= T_ALLOCATABLE && LA4_0 <= T_ALLOCATE_STMT_1)||(LA4_0 >= T_ARITHMETIC_IF_STMT && LA4_0 <= T_ASSIGN)||(LA4_0 >= T_ASSIGNMENT_STMT && LA4_0 <= T_ASSOCIATE)||LA4_0==T_ASYNCHRONOUS||LA4_0==T_BACKSPACE||(LA4_0 >= T_BIND && LA4_0 <= T_BLOCK)||LA4_0==T_CALL||LA4_0==T_CHARACTER||(LA4_0 >= T_CLASS && LA4_0 <= T_CODIMENSION)||(LA4_0 >= T_COMMON && LA4_0 <= T_COMPLEX)||LA4_0==T_CONTAINS||LA4_0==T_CONTINUE||(LA4_0 >= T_CRITICAL && LA4_0 <= T_DATA)||LA4_0==T_DEALLOCATE||(LA4_0 >= T_DIMENSION && LA4_0 <= T_DOUBLEPRECISION)||LA4_0==T_END||(LA4_0 >= T_ENDBLOCK && LA4_0 <= T_ENDBLOCKDATA)||LA4_0==T_ENDFILE||LA4_0==T_ENDFUNCTION||(LA4_0 >= T_ENDMODULE && LA4_0 <= T_ENDPROGRAM)||LA4_0==T_ENDSUBROUTINE||LA4_0==T_ENUM||LA4_0==T_EQUIVALENCE||LA4_0==T_ERROR||LA4_0==T_EXIT||LA4_0==T_EXTERNAL||LA4_0==T_FLUSH||(LA4_0 >= T_FORALL_CONSTRUCT_STMT && LA4_0 <= T_FORALL_STMT)||(LA4_0 >= T_GO && LA4_0 <= T_GOTO)||(LA4_0 >= T_IDENT && LA4_0 <= T_IF_STMT)||(LA4_0 >= T_INQUIRE && LA4_0 <= T_INTRINSIC)||LA4_0==T_LOCK||LA4_0==T_LOGICAL||LA4_0==T_NAMELIST||LA4_0==T_NULLIFY||LA4_0==T_OPEN||LA4_0==T_OPTIONAL||LA4_0==T_PAUSE||LA4_0==T_POINTER||(LA4_0 >= T_PRINT && LA4_0 <= T_PROCEDURE)||(LA4_0 >= T_PROTECTED && LA4_0 <= T_PUBLIC)||(LA4_0 >= T_READ && LA4_0 <= T_REAL)||(LA4_0 >= T_RETURN && LA4_0 <= T_REWIND)||(LA4_0 >= T_SAVE && LA4_0 <= T_SELECTTYPE)||(LA4_0 >= T_STMT_FUNCTION && LA4_0 <= T_STOP)||(LA4_0 >= T_SYNC && LA4_0 <= T_TARGET)||LA4_0==T_TYPE||LA4_0==T_UNLOCK||(LA4_0 >= T_VALUE && LA4_0 <= T_WAIT)||(LA4_0 >= T_WHERE_CONSTRUCT_STMT && LA4_0 <= T_WHERE_STMT)||LA4_0==T_WRITE) ) {s = 6;}
						 
						input.seek(index4_0);
						if ( s>=0 ) return s;
						break;

					case 1 : 
						int LA4_1 = input.LA(1);
						 
						int index4_1 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred1_FortranParserExtras()) ) {s = 2;}
						else if ( (synpred2_FortranParserExtras()) ) {s = 98;}
						else if ( (synpred3_FortranParserExtras()) ) {s = 99;}
						else if ( (synpred4_FortranParserExtras()) ) {s = 100;}
						else if ( (true) ) {s = 6;}
						 
						input.seek(index4_1);
						if ( s>=0 ) return s;
						break;

					case 2 : 
						int LA4_3 = input.LA(1);
						 
						int index4_3 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred2_FortranParserExtras()) ) {s = 98;}
						else if ( (true) ) {s = 6;}
						 
						input.seek(index4_3);
						if ( s>=0 ) return s;
						break;

					case 3 : 
						int LA4_4 = input.LA(1);
						 
						int index4_4 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred3_FortranParserExtras()) ) {s = 99;}
						else if ( (true) ) {s = 6;}
						 
						input.seek(index4_4);
						if ( s>=0 ) return s;
						break;

					case 4 : 
						int LA4_5 = input.LA(1);
						 
						int index4_5 = input.index();
						input.rewind();
						s = -1;
						if ( (synpred4_FortranParserExtras()) ) {s = 100;}
						else if ( (true) ) {s = 6;}
						 
						input.seek(index4_5);
						if ( s>=0 ) return s;
						break;
			}
			if (state.backtracking>0) {state.failed=true; return -1;}
			NoViableAltException nvae =
				new NoViableAltException(getDescription(), 4, _s, input);
			error(nvae);
			throw nvae;
		}
	}

	public static final BitSet FOLLOW_use_stmt_in_specification_part92 = new BitSet(new long[]{0x200C521100480000L,0x08040418000001D8L,0x10240020803C0C00L,0x000007104201022BL});
	public static final BitSet FOLLOW_import_stmt_in_specification_part108 = new BitSet(new long[]{0x200C521100480000L,0x08040418000001D8L,0x10240020803C0C00L,0x000006104201022BL});
	public static final BitSet FOLLOW_implicit_part_recursion_in_specification_part122 = new BitSet(new long[]{0x200C521100480002L,0x08040418000001D8L,0x10240020803C0000L,0x000006104201022BL});
	public static final BitSet FOLLOW_declaration_construct_in_specification_part134 = new BitSet(new long[]{0x200C521100480002L,0x08040418000001D8L,0x10240020803C0000L,0x000006104201022BL});
	public static final BitSet FOLLOW_implicit_stmt_in_implicit_part_recursion191 = new BitSet(new long[]{0x0000000000000000L,0x0800000800000008L,0x0020000000000400L});
	public static final BitSet FOLLOW_implicit_part_recursion_in_implicit_part_recursion196 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_parameter_stmt_in_implicit_part_recursion216 = new BitSet(new long[]{0x0000000000000000L,0x0800000800000008L,0x0020000000000400L});
	public static final BitSet FOLLOW_implicit_part_recursion_in_implicit_part_recursion220 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_format_stmt_in_implicit_part_recursion243 = new BitSet(new long[]{0x0000000000000000L,0x0800000800000008L,0x0020000000000400L});
	public static final BitSet FOLLOW_implicit_part_recursion_in_implicit_part_recursion250 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_entry_stmt_in_implicit_part_recursion274 = new BitSet(new long[]{0x0000000000000000L,0x0800000800000008L,0x0020000000000400L});
	public static final BitSet FOLLOW_implicit_part_recursion_in_implicit_part_recursion282 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_action_stmt_in_executable_construct318 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_associate_construct_in_executable_construct327 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_block_construct_in_executable_construct336 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_case_construct_in_executable_construct362 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_critical_construct_in_executable_construct371 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_do_construct_in_executable_construct394 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_forall_construct_in_executable_construct403 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_if_construct_in_executable_construct412 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_select_type_construct_in_executable_construct421 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_where_construct_in_executable_construct430 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_allocate_stmt_in_action_stmt473 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_assignment_stmt_in_action_stmt482 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_backspace_stmt_in_action_stmt491 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_call_stmt_in_action_stmt500 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_close_stmt_in_action_stmt509 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_continue_stmt_in_action_stmt518 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cycle_stmt_in_action_stmt527 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_deallocate_stmt_in_action_stmt536 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_endfile_stmt_in_action_stmt552 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_errorstop_stmt_in_action_stmt561 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_exit_stmt_in_action_stmt586 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_flush_stmt_in_action_stmt595 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_forall_stmt_in_action_stmt604 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_goto_stmt_in_action_stmt613 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_if_stmt_in_action_stmt622 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_inquire_stmt_in_action_stmt631 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_lock_stmt_in_action_stmt642 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_nullify_stmt_in_action_stmt672 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_open_stmt_in_action_stmt681 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_pointer_assignment_stmt_in_action_stmt690 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_print_stmt_in_action_stmt699 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_read_stmt_in_action_stmt708 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_return_stmt_in_action_stmt717 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_rewind_stmt_in_action_stmt726 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_stop_stmt_in_action_stmt735 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_sync_all_stmt_in_action_stmt744 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_sync_images_stmt_in_action_stmt770 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_sync_memory_stmt_in_action_stmt793 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_unlock_stmt_in_action_stmt816 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_wait_stmt_in_action_stmt844 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_where_stmt_in_action_stmt853 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_write_stmt_in_action_stmt862 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_arithmetic_if_stmt_in_action_stmt871 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_computed_goto_stmt_in_action_stmt880 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_assign_stmt_in_action_stmt889 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_assigned_goto_stmt_in_action_stmt917 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_pause_stmt_in_action_stmt938 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_type_declaration_stmt997 = new BitSet(new long[]{0x0008120000000000L,0x00000000000001C0L,0x0000000080040000L,0x0000001000000200L});
	public static final BitSet FOLLOW_declaration_type_spec_in_type_declaration_stmt1003 = new BitSet(new long[]{0x0003000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_T_COMMA_in_type_declaration_stmt1010 = new BitSet(new long[]{0x0040401100400000L,0x0004000000000010L,0x1024200004680000L,0x0000060040010029L});
	public static final BitSet FOLLOW_attr_spec_in_type_declaration_stmt1012 = new BitSet(new long[]{0x0003000000000000L});
	public static final BitSet FOLLOW_T_COLON_COLON_in_type_declaration_stmt1018 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_entity_decl_list_in_type_declaration_stmt1025 = new BitSet(new long[]{0x0000000000000000L,0x0000008000000000L});
	public static final BitSet FOLLOW_end_of_stmt_in_type_declaration_stmt1027 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_IDENT_in_part_ref1122 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_T_LPAREN_in_part_ref1124 = new BitSet(new long[]{0x0003840080004420L,0x000800000000000CL,0x0800100901000060L,0x0000000800000400L});
	public static final BitSet FOLLOW_section_subscript_list_in_part_ref1126 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000008000L});
	public static final BitSet FOLLOW_T_RPAREN_in_part_ref1128 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0000000001000000L});
	public static final BitSet FOLLOW_image_selector_in_part_ref1160 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_IDENT_in_part_ref1194 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000001000000L});
	public static final BitSet FOLLOW_image_selector_in_part_ref1196 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_IDENT_in_part_ref1218 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_IDENT_in_part_ref_no_image_selector1267 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_T_LPAREN_in_part_ref_no_image_selector1269 = new BitSet(new long[]{0x0003840080004420L,0x000800000000000CL,0x0800100901000060L,0x0000000800000400L});
	public static final BitSet FOLLOW_section_subscript_list_in_part_ref_no_image_selector1271 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000008000L});
	public static final BitSet FOLLOW_T_RPAREN_in_part_ref_no_image_selector1273 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_IDENT_in_part_ref_no_image_selector1295 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_expr_in_section_subscript1344 = new BitSet(new long[]{0x0001800000000000L});
	public static final BitSet FOLLOW_section_subscript_ambiguous_in_section_subscript1346 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_COLON_in_section_subscript1355 = new BitSet(new long[]{0x0000840000004422L,0x000800000000000CL,0x0800100901000060L,0x0000000800000400L});
	public static final BitSet FOLLOW_expr_in_section_subscript1358 = new BitSet(new long[]{0x0000800000000002L});
	public static final BitSet FOLLOW_T_COLON_in_section_subscript1365 = new BitSet(new long[]{0x0000040000004420L,0x000800000000000CL,0x0800100901000060L,0x0000000800000400L});
	public static final BitSet FOLLOW_expr_in_section_subscript1367 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_COLON_COLON_in_section_subscript1393 = new BitSet(new long[]{0x0000040000004420L,0x000800000000000CL,0x0800100901000060L,0x0000000800000400L});
	public static final BitSet FOLLOW_expr_in_section_subscript1395 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_IDENT_in_section_subscript1417 = new BitSet(new long[]{0x0000000000000000L,0x0000020000000000L});
	public static final BitSet FOLLOW_T_EQUALS_in_section_subscript1419 = new BitSet(new long[]{0x0000040000004420L,0x000800000000000CL,0x0800100901000060L,0x0000000800000400L});
	public static final BitSet FOLLOW_expr_in_section_subscript1421 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_IDENT_in_section_subscript1444 = new BitSet(new long[]{0x0000000000000000L,0x0000020000000000L});
	public static final BitSet FOLLOW_T_EQUALS_in_section_subscript1446 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_T_ASTERISK_in_section_subscript1448 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_label_in_section_subscript1450 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_ASTERISK_in_section_subscript1473 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
	public static final BitSet FOLLOW_label_in_section_subscript1475 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_COLON_in_section_subscript_ambiguous1525 = new BitSet(new long[]{0x0000840000004422L,0x000800000000000CL,0x0800100901000060L,0x0000000800000400L});
	public static final BitSet FOLLOW_expr_in_section_subscript_ambiguous1528 = new BitSet(new long[]{0x0000800000000002L});
	public static final BitSet FOLLOW_T_COLON_in_section_subscript_ambiguous1535 = new BitSet(new long[]{0x0000040000004420L,0x000800000000000CL,0x0800100901000060L,0x0000000800000400L});
	public static final BitSet FOLLOW_expr_in_section_subscript_ambiguous1537 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_COLON_COLON_in_section_subscript_ambiguous1602 = new BitSet(new long[]{0x0000040000004420L,0x000800000000000CL,0x0800100901000060L,0x0000000800000400L});
	public static final BitSet FOLLOW_expr_in_section_subscript_ambiguous1604 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_section_subscript_in_section_subscript_list1676 = new BitSet(new long[]{0x0002000000000002L});
	public static final BitSet FOLLOW_T_COMMA_in_section_subscript_list1699 = new BitSet(new long[]{0x0003840080004420L,0x000800000000000CL,0x0800100901000060L,0x0000000800000400L});
	public static final BitSet FOLLOW_section_subscript_in_section_subscript_list1701 = new BitSet(new long[]{0x0002000000000002L});
	public static final BitSet FOLLOW_T_LBRACKET_in_image_selector1742 = new BitSet(new long[]{0x0000040000004420L,0x000800000000000CL,0x0800100901000060L,0x0000000800000400L});
	public static final BitSet FOLLOW_cosubscript_list_in_image_selector1744 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_T_RBRACKET_in_image_selector1746 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_scalar_int_expr_in_cosubscript1782 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_cosubscript_in_cosubscript_list1816 = new BitSet(new long[]{0x0002000000000002L});
	public static final BitSet FOLLOW_T_COMMA_in_cosubscript_list1822 = new BitSet(new long[]{0x0000040000004420L,0x000800000000000CL,0x0800100901000060L,0x0000000800000400L});
	public static final BitSet FOLLOW_cosubscript_in_cosubscript_list1824 = new BitSet(new long[]{0x0002000000000002L});
	public static final BitSet FOLLOW_allocate_object_in_allocation1889 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000001000000L});
	public static final BitSet FOLLOW_T_LBRACKET_in_allocation1891 = new BitSet(new long[]{0x0000040080004420L,0x000800000000000CL,0x0800100901000060L,0x0000000800000400L});
	public static final BitSet FOLLOW_allocate_coarray_spec_in_allocation1893 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000000L,0x0000000000000080L});
	public static final BitSet FOLLOW_T_RBRACKET_in_allocation1895 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_allocate_object_in_allocation1967 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_part_ref_no_image_selector_in_allocate_object2021 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_T_PERCENT_in_allocate_object2033 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000040L});
	public static final BitSet FOLLOW_part_ref_no_image_selector_in_allocate_object2035 = new BitSet(new long[]{0x0000000000000002L,0x0000000000000000L,0x0100000000000000L});
	public static final BitSet FOLLOW_T_ASTERISK_in_allocate_coarray_spec2106 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_expr_in_allocate_coarray_spec2125 = new BitSet(new long[]{0x0000800000000000L});
	public static final BitSet FOLLOW_T_COLON_in_allocate_coarray_spec2127 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_T_ASTERISK_in_allocate_coarray_spec2129 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_expr_in_logical_expr2158 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_expr_in_scalar_logical_expr2175 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_expr_in_int_expr2199 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_expr_in_scalar_int_expr2216 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_expr_in_scalar_variable2238 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_scalar_variable_in_lock_variable2267 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_synpred1_FortranParserExtras181 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000000000400L});
	public static final BitSet FOLLOW_T_IMPLICIT_in_synpred1_FortranParserExtras185 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_synpred2_FortranParserExtras207 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0020000000000000L});
	public static final BitSet FOLLOW_T_PARAMETER_in_synpred2_FortranParserExtras211 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_synpred3_FortranParserExtras231 = new BitSet(new long[]{0x0000000000000000L,0x0800000000000000L});
	public static final BitSet FOLLOW_T_FORMAT_in_synpred3_FortranParserExtras235 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_label_in_synpred4_FortranParserExtras261 = new BitSet(new long[]{0x0000000000000000L,0x0000000800000000L});
	public static final BitSet FOLLOW_T_ENTRY_in_synpred4_FortranParserExtras265 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_IDENT_in_synpred5_FortranParserExtras1115 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_T_LPAREN_in_synpred5_FortranParserExtras1117 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_IDENT_in_synpred6_FortranParserExtras1187 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000001000000L});
	public static final BitSet FOLLOW_T_LBRACKET_in_synpred6_FortranParserExtras1189 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_IDENT_in_synpred7_FortranParserExtras1260 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000100000000L});
	public static final BitSet FOLLOW_T_LPAREN_in_synpred7_FortranParserExtras1262 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_allocate_object_in_synpred8_FortranParserExtras1872 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000000L,0x0000000001000000L});
	public static final BitSet FOLLOW_T_LBRACKET_in_synpred8_FortranParserExtras1874 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_allocate_object_in_synpred9_FortranParserExtras1952 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_T_ASTERISK_in_synpred10_FortranParserExtras2088 = new BitSet(new long[]{0x0000000000000002L});
	public static final BitSet FOLLOW_expr_in_synpred11_FortranParserExtras2116 = new BitSet(new long[]{0x0000800000000000L});
	public static final BitSet FOLLOW_T_COLON_in_synpred11_FortranParserExtras2118 = new BitSet(new long[]{0x0000000080000000L});
	public static final BitSet FOLLOW_T_ASTERISK_in_synpred11_FortranParserExtras2120 = new BitSet(new long[]{0x0000000000000002L});
}
