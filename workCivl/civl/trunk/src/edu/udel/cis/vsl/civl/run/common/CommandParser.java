// Generated from Command.g4 by ANTLR 4.4
package edu.udel.cis.vsl.civl.run.common;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class CommandParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.4", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__3=1, T__2=2, T__1=3, T__0=4, BOOLEAN=5, NUMBER=6, SPEC=7, IMPL=8, INPUT=9, 
		MACRO=10, COMMAND=11, REPLAY=12, OPTION_NAME=13, VAR=14, PATH=15, NEWLINE=16, 
		STRING=17, WS=18;
	public static final String[] tokenNames = {
		"<INVALID>", "'config'", "'='", "'help'", "'compare'", "BOOLEAN", "NUMBER", 
		"'-spec'", "'-impl'", "'-input'", "'-D'", "COMMAND", "'replay'", "OPTION_NAME", 
		"VAR", "PATH", "NEWLINE", "STRING", "WS"
	};
	public static final int
		RULE_start = 0, RULE_specAndImplCommand = 1, RULE_commonOption = 2, RULE_specCommand = 3, 
		RULE_implCommand = 4, RULE_commandBody = 5, RULE_option = 6, RULE_file = 7, 
		RULE_value = 8;
	public static final String[] ruleNames = {
		"start", "specAndImplCommand", "commonOption", "specCommand", "implCommand", 
		"commandBody", "option", "file", "value"
	};

	@Override
	public String getGrammarFileName() { return "Command.g4"; }

	@Override
	public String[] getTokenNames() { return tokenNames; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public CommandParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}
	public static class StartContext extends ParserRuleContext {
		public StartContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start; }
	 
		public StartContext() { }
		public void copyFrom(StartContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class ReplayCompareContext extends StartContext {
		public TerminalNode NEWLINE() { return getToken(CommandParser.NEWLINE, 0); }
		public CommonOptionContext commonOption() {
			return getRuleContext(CommonOptionContext.class,0);
		}
		public SpecAndImplCommandContext specAndImplCommand() {
			return getRuleContext(SpecAndImplCommandContext.class,0);
		}
		public TerminalNode REPLAY() { return getToken(CommandParser.REPLAY, 0); }
		public ReplayCompareContext(StartContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterReplayCompare(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitReplayCompare(this);
		}
	}
	public static class HelpContext extends StartContext {
		public TerminalNode NEWLINE() { return getToken(CommandParser.NEWLINE, 0); }
		public TerminalNode COMMAND() { return getToken(CommandParser.COMMAND, 0); }
		public TerminalNode REPLAY() { return getToken(CommandParser.REPLAY, 0); }
		public HelpContext(StartContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterHelp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitHelp(this);
		}
	}
	public static class NormalContext extends StartContext {
		public TerminalNode NEWLINE() { return getToken(CommandParser.NEWLINE, 0); }
		public TerminalNode COMMAND() { return getToken(CommandParser.COMMAND, 0); }
		public TerminalNode REPLAY() { return getToken(CommandParser.REPLAY, 0); }
		public CommandBodyContext commandBody() {
			return getRuleContext(CommandBodyContext.class,0);
		}
		public NormalContext(StartContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterNormal(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitNormal(this);
		}
	}
	public static class CompareContext extends StartContext {
		public TerminalNode NEWLINE() { return getToken(CommandParser.NEWLINE, 0); }
		public CommonOptionContext commonOption() {
			return getRuleContext(CommonOptionContext.class,0);
		}
		public SpecAndImplCommandContext specAndImplCommand() {
			return getRuleContext(SpecAndImplCommandContext.class,0);
		}
		public CompareContext(StartContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterCompare(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitCompare(this);
		}
	}
	public static class ConfigContext extends StartContext {
		public TerminalNode NEWLINE() { return getToken(CommandParser.NEWLINE, 0); }
		public ConfigContext(StartContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterConfig(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitConfig(this);
		}
	}

	public final StartContext start() throws RecognitionException {
		StartContext _localctx = new StartContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_start);
		int _la;
		try {
			setState(43);
			switch ( getInterpreter().adaptivePredict(_input,3,_ctx) ) {
			case 1:
				_localctx = new HelpContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(18); match(T__1);
				setState(20);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << T__1) | (1L << T__0) | (1L << COMMAND) | (1L << REPLAY))) != 0)) {
					{
					setState(19);
					_la = _input.LA(1);
					if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << T__1) | (1L << T__0) | (1L << COMMAND) | (1L << REPLAY))) != 0)) ) {
					_errHandler.recoverInline(this);
					}
					consume();
					}
				}

				setState(22); match(NEWLINE);
				}
				break;
			case 2:
				_localctx = new CompareContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(23); match(T__0);
				setState(25);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << INPUT) | (1L << MACRO) | (1L << OPTION_NAME))) != 0)) {
					{
					setState(24); commonOption();
					}
				}

				setState(27); specAndImplCommand();
				setState(28); match(NEWLINE);
				}
				break;
			case 3:
				_localctx = new NormalContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(30);
				_la = _input.LA(1);
				if ( !(_la==COMMAND || _la==REPLAY) ) {
				_errHandler.recoverInline(this);
				}
				consume();
				setState(31); commandBody();
				setState(32); match(NEWLINE);
				}
				break;
			case 4:
				_localctx = new ConfigContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(34); match(T__3);
				setState(35); match(NEWLINE);
				}
				break;
			case 5:
				_localctx = new ReplayCompareContext(_localctx);
				enterOuterAlt(_localctx, 5);
				{
				setState(36); match(REPLAY);
				setState(38);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << INPUT) | (1L << MACRO) | (1L << OPTION_NAME))) != 0)) {
					{
					setState(37); commonOption();
					}
				}

				setState(40); specAndImplCommand();
				setState(41); match(NEWLINE);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SpecAndImplCommandContext extends ParserRuleContext {
		public SpecCommandContext specCommand() {
			return getRuleContext(SpecCommandContext.class,0);
		}
		public ImplCommandContext implCommand() {
			return getRuleContext(ImplCommandContext.class,0);
		}
		public SpecAndImplCommandContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_specAndImplCommand; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterSpecAndImplCommand(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitSpecAndImplCommand(this);
		}
	}

	public final SpecAndImplCommandContext specAndImplCommand() throws RecognitionException {
		SpecAndImplCommandContext _localctx = new SpecAndImplCommandContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_specAndImplCommand);
		try {
			setState(51);
			switch (_input.LA(1)) {
			case SPEC:
				enterOuterAlt(_localctx, 1);
				{
				setState(45); specCommand();
				setState(46); implCommand();
				}
				break;
			case IMPL:
				enterOuterAlt(_localctx, 2);
				{
				setState(48); implCommand();
				setState(49); specCommand();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class CommonOptionContext extends ParserRuleContext {
		public List<OptionContext> option() {
			return getRuleContexts(OptionContext.class);
		}
		public OptionContext option(int i) {
			return getRuleContext(OptionContext.class,i);
		}
		public CommonOptionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_commonOption; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterCommonOption(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitCommonOption(this);
		}
	}

	public final CommonOptionContext commonOption() throws RecognitionException {
		CommonOptionContext _localctx = new CommonOptionContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_commonOption);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(54); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(53); option();
				}
				}
				setState(56); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( (((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << INPUT) | (1L << MACRO) | (1L << OPTION_NAME))) != 0) );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SpecCommandContext extends ParserRuleContext {
		public TerminalNode SPEC() { return getToken(CommandParser.SPEC, 0); }
		public CommandBodyContext commandBody() {
			return getRuleContext(CommandBodyContext.class,0);
		}
		public SpecCommandContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_specCommand; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterSpecCommand(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitSpecCommand(this);
		}
	}

	public final SpecCommandContext specCommand() throws RecognitionException {
		SpecCommandContext _localctx = new SpecCommandContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_specCommand);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(58); match(SPEC);
			setState(59); commandBody();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ImplCommandContext extends ParserRuleContext {
		public TerminalNode IMPL() { return getToken(CommandParser.IMPL, 0); }
		public CommandBodyContext commandBody() {
			return getRuleContext(CommandBodyContext.class,0);
		}
		public ImplCommandContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_implCommand; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterImplCommand(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitImplCommand(this);
		}
	}

	public final ImplCommandContext implCommand() throws RecognitionException {
		ImplCommandContext _localctx = new ImplCommandContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_implCommand);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(61); match(IMPL);
			setState(62); commandBody();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class CommandBodyContext extends ParserRuleContext {
		public List<OptionContext> option() {
			return getRuleContexts(OptionContext.class);
		}
		public OptionContext option(int i) {
			return getRuleContext(OptionContext.class,i);
		}
		public FileContext file(int i) {
			return getRuleContext(FileContext.class,i);
		}
		public List<FileContext> file() {
			return getRuleContexts(FileContext.class);
		}
		public CommandBodyContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_commandBody; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterCommandBody(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitCommandBody(this);
		}
	}

	public final CommandBodyContext commandBody() throws RecognitionException {
		CommandBodyContext _localctx = new CommandBodyContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_commandBody);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(67);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << INPUT) | (1L << MACRO) | (1L << OPTION_NAME))) != 0)) {
				{
				{
				setState(64); option();
				}
				}
				setState(69);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(71); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(70); file();
				}
				}
				setState(73); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==PATH );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class OptionContext extends ParserRuleContext {
		public OptionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_option; }
	 
		public OptionContext() { }
		public void copyFrom(OptionContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class InputOptionContext extends OptionContext {
		public TerminalNode INPUT() { return getToken(CommandParser.INPUT, 0); }
		public ValueContext value() {
			return getRuleContext(ValueContext.class,0);
		}
		public TerminalNode VAR() { return getToken(CommandParser.VAR, 0); }
		public InputOptionContext(OptionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterInputOption(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitInputOption(this);
		}
	}
	public static class MacroOptionContext extends OptionContext {
		public TerminalNode MACRO() { return getToken(CommandParser.MACRO, 0); }
		public ValueContext value() {
			return getRuleContext(ValueContext.class,0);
		}
		public TerminalNode VAR() { return getToken(CommandParser.VAR, 0); }
		public MacroOptionContext(OptionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterMacroOption(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitMacroOption(this);
		}
	}
	public static class NormalOptionContext extends OptionContext {
		public ValueContext value() {
			return getRuleContext(ValueContext.class,0);
		}
		public TerminalNode OPTION_NAME() { return getToken(CommandParser.OPTION_NAME, 0); }
		public NormalOptionContext(OptionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterNormalOption(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitNormalOption(this);
		}
	}

	public final OptionContext option() throws RecognitionException {
		OptionContext _localctx = new OptionContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_option);
		int _la;
		try {
			setState(90);
			switch (_input.LA(1)) {
			case OPTION_NAME:
				_localctx = new NormalOptionContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(75); match(OPTION_NAME);
				setState(78);
				_la = _input.LA(1);
				if (_la==T__2) {
					{
					setState(76); match(T__2);
					setState(77); value();
					}
				}

				}
				break;
			case INPUT:
				_localctx = new InputOptionContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(80); match(INPUT);
				setState(81); match(VAR);
				setState(82); match(T__2);
				setState(83); value();
				}
				break;
			case MACRO:
				_localctx = new MacroOptionContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(84); match(MACRO);
				setState(85); match(VAR);
				setState(88);
				_la = _input.LA(1);
				if (_la==T__2) {
					{
					setState(86); match(T__2);
					setState(87); value();
					}
				}

				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FileContext extends ParserRuleContext {
		public TerminalNode PATH() { return getToken(CommandParser.PATH, 0); }
		public FileContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_file; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterFile(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitFile(this);
		}
	}

	public final FileContext file() throws RecognitionException {
		FileContext _localctx = new FileContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_file);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(92); match(PATH);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ValueContext extends ParserRuleContext {
		public TerminalNode BOOLEAN() { return getToken(CommandParser.BOOLEAN, 0); }
		public TerminalNode VAR() { return getToken(CommandParser.VAR, 0); }
		public TerminalNode NUMBER() { return getToken(CommandParser.NUMBER, 0); }
		public TerminalNode STRING() { return getToken(CommandParser.STRING, 0); }
		public TerminalNode PATH() { return getToken(CommandParser.PATH, 0); }
		public ValueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_value; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).enterValue(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CommandListener ) ((CommandListener)listener).exitValue(this);
		}
	}

	public final ValueContext value() throws RecognitionException {
		ValueContext _localctx = new ValueContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_value);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(94);
			_la = _input.LA(1);
			if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << BOOLEAN) | (1L << NUMBER) | (1L << VAR) | (1L << PATH) | (1L << STRING))) != 0)) ) {
			_errHandler.recoverInline(this);
			}
			consume();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\3\24c\4\2\t\2\4\3\t"+
		"\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\3\2\3\2\5\2"+
		"\27\n\2\3\2\3\2\3\2\5\2\34\n\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2"+
		"\3\2\5\2)\n\2\3\2\3\2\3\2\5\2.\n\2\3\3\3\3\3\3\3\3\3\3\3\3\5\3\66\n\3"+
		"\3\4\6\49\n\4\r\4\16\4:\3\5\3\5\3\5\3\6\3\6\3\6\3\7\7\7D\n\7\f\7\16\7"+
		"G\13\7\3\7\6\7J\n\7\r\7\16\7K\3\b\3\b\3\b\5\bQ\n\b\3\b\3\b\3\b\3\b\3\b"+
		"\3\b\3\b\3\b\5\b[\n\b\5\b]\n\b\3\t\3\t\3\n\3\n\3\n\2\2\13\2\4\6\b\n\f"+
		"\16\20\22\2\5\5\2\3\3\5\6\r\16\3\2\r\16\5\2\7\b\20\21\23\23h\2-\3\2\2"+
		"\2\4\65\3\2\2\2\68\3\2\2\2\b<\3\2\2\2\n?\3\2\2\2\fE\3\2\2\2\16\\\3\2\2"+
		"\2\20^\3\2\2\2\22`\3\2\2\2\24\26\7\5\2\2\25\27\t\2\2\2\26\25\3\2\2\2\26"+
		"\27\3\2\2\2\27\30\3\2\2\2\30.\7\22\2\2\31\33\7\6\2\2\32\34\5\6\4\2\33"+
		"\32\3\2\2\2\33\34\3\2\2\2\34\35\3\2\2\2\35\36\5\4\3\2\36\37\7\22\2\2\37"+
		".\3\2\2\2 !\t\3\2\2!\"\5\f\7\2\"#\7\22\2\2#.\3\2\2\2$%\7\3\2\2%.\7\22"+
		"\2\2&(\7\16\2\2\')\5\6\4\2(\'\3\2\2\2()\3\2\2\2)*\3\2\2\2*+\5\4\3\2+,"+
		"\7\22\2\2,.\3\2\2\2-\24\3\2\2\2-\31\3\2\2\2- \3\2\2\2-$\3\2\2\2-&\3\2"+
		"\2\2.\3\3\2\2\2/\60\5\b\5\2\60\61\5\n\6\2\61\66\3\2\2\2\62\63\5\n\6\2"+
		"\63\64\5\b\5\2\64\66\3\2\2\2\65/\3\2\2\2\65\62\3\2\2\2\66\5\3\2\2\2\67"+
		"9\5\16\b\28\67\3\2\2\29:\3\2\2\2:8\3\2\2\2:;\3\2\2\2;\7\3\2\2\2<=\7\t"+
		"\2\2=>\5\f\7\2>\t\3\2\2\2?@\7\n\2\2@A\5\f\7\2A\13\3\2\2\2BD\5\16\b\2C"+
		"B\3\2\2\2DG\3\2\2\2EC\3\2\2\2EF\3\2\2\2FI\3\2\2\2GE\3\2\2\2HJ\5\20\t\2"+
		"IH\3\2\2\2JK\3\2\2\2KI\3\2\2\2KL\3\2\2\2L\r\3\2\2\2MP\7\17\2\2NO\7\4\2"+
		"\2OQ\5\22\n\2PN\3\2\2\2PQ\3\2\2\2Q]\3\2\2\2RS\7\13\2\2ST\7\20\2\2TU\7"+
		"\4\2\2U]\5\22\n\2VW\7\f\2\2WZ\7\20\2\2XY\7\4\2\2Y[\5\22\n\2ZX\3\2\2\2"+
		"Z[\3\2\2\2[]\3\2\2\2\\M\3\2\2\2\\R\3\2\2\2\\V\3\2\2\2]\17\3\2\2\2^_\7"+
		"\21\2\2_\21\3\2\2\2`a\t\4\2\2a\23\3\2\2\2\r\26\33(-\65:EKPZ\\";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}