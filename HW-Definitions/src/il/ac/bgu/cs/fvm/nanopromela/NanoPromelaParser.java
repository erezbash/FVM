// Generated from NanoPromela.g4 by ANTLR 4.5.1
package il.ac.bgu.cs.fvm.nanopromela;

import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({ "all", "warnings", "unchecked", "unused", "cast" })
public class NanoPromelaParser extends Parser {
	static {
		RuntimeMetaData.checkVersion("4.5.1", RuntimeMetaData.VERSION);
	}

	protected static final DFA[]					_decisionToDFA;
	protected static final PredictionContextCache	_sharedContextCache	= new PredictionContextCache();
	public static final int							T__0				= 1,
															T__1 = 2, T__2 = 3, T__3 = 4, T__4 = 5, T__5 = 6, T__6 = 7, T__7 = 8, T__8 = 9, T__9 = 10, T__10 = 11, T__11 = 12, OR = 13, AND = 14, EQ = 15, NEQ = 16, GT = 17, LT = 18, GTEQ = 19, LTEQ = 20, PLUS = 21, MINUS = 22, MULT = 23, DIV = 24,
															MOD = 25, POW = 26, NOT = 27, SCOL = 28, ASSIGN = 29, OPAR = 30, CPAR = 31, OBRACE = 32, CBRACE = 33, TRUE = 34, FALSE = 35, INT = 36, VARNAME = 37, CHANNAME = 38, ZEROCAPACITYCHANNAME = 39, COMMENT = 40, SPACE = 41, OTHER = 42;
	public static final int							RULE_hsreadstmt		= 0,
															RULE_hswritestmt = 1, RULE_joined = 2, RULE_onesided = 3, RULE_spec = 4, RULE_stmt = 5, RULE_ifstmt = 6, RULE_dostmt = 7, RULE_assstmt = 8, RULE_chanreadstmt = 9, RULE_chanwritestmt = 10, RULE_atomicstmt = 11, RULE_skipstmt = 12,
															RULE_option = 13, RULE_intexpr = 14, RULE_boolexpr = 15;
	public static final String[]					ruleNames			= { "hsreadstmt", "hswritestmt", "joined", "onesided", "spec", "stmt", "ifstmt", "dostmt", "assstmt", "chanreadstmt", "chanwritestmt", "atomicstmt", "skipstmt", "option", "intexpr", "boolexpr" };

	private static final String[]					_LITERAL_NAMES		= { null, "'?'", "'|'", "'if'", "'fi'", "'do'", "'od'", "':='", "'atomic'", "'skip'", "'::'", "'->'", "'size('", "'||'", "'&&'", "'=='", "'!='", "'>'", "'<'", "'>='", "'<='", "'+'", "'-'", "'*'", "'/'", "'%'", "'^'", "'!'",
			"';'", "'='", "'('", "')'", "'{'", "'}'", "'true'", "'false'" };
	private static final String[]					_SYMBOLIC_NAMES		= { null, null, null, null, null, null, null, null, null, null, null, null, null, "OR", "AND", "EQ", "NEQ", "GT", "LT", "GTEQ", "LTEQ", "PLUS", "MINUS", "MULT", "DIV", "MOD", "POW", "NOT", "SCOL", "ASSIGN", "OPAR", "CPAR",
			"OBRACE", "CBRACE", "TRUE", "FALSE", "INT", "VARNAME", "CHANNAME", "ZEROCAPACITYCHANNAME", "COMMENT", "SPACE", "OTHER" };
	public static final Vocabulary					VOCABULARY			= new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[]					tokenNames;

	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() {
		return "NanoPromela.g4";
	}

	@Override
	public String[] getRuleNames() {
		return ruleNames;
	}

	@Override
	public String getSerializedATN() {
		return _serializedATN;
	}

	@Override
	public ATN getATN() {
		return _ATN;
	}

	public NanoPromelaParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this, _ATN, _decisionToDFA, _sharedContextCache);
	}

	public static class HsreadstmtContext extends ParserRuleContext {
		public TerminalNode ZEROCAPACITYCHANNAME() {
			return getToken(NanoPromelaParser.ZEROCAPACITYCHANNAME, 0);
		}

		public TerminalNode VARNAME() {
			return getToken(NanoPromelaParser.VARNAME, 0);
		}

		public HsreadstmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_hsreadstmt;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterHsreadstmt(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitHsreadstmt(this);
		}
	}

	public final HsreadstmtContext hsreadstmt() throws RecognitionException {
		HsreadstmtContext _localctx = new HsreadstmtContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_hsreadstmt);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
				setState(32);
				match(ZEROCAPACITYCHANNAME);
				setState(33);
				match(T__0);
				setState(35);
				_la = _input.LA(1);
				if (_la == VARNAME) {
					{
						setState(34);
						match(VARNAME);
					}
				}

			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			exitRule();
		}
		return _localctx;
	}

	public static class HswritestmtContext extends ParserRuleContext {
		public TerminalNode ZEROCAPACITYCHANNAME() {
			return getToken(NanoPromelaParser.ZEROCAPACITYCHANNAME, 0);
		}

		public IntexprContext intexpr() {
			return getRuleContext(IntexprContext.class, 0);
		}

		public HswritestmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_hswritestmt;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterHswritestmt(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitHswritestmt(this);
		}
	}

	public final HswritestmtContext hswritestmt() throws RecognitionException {
		HswritestmtContext _localctx = new HswritestmtContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_hswritestmt);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
				setState(37);
				match(ZEROCAPACITYCHANNAME);
				setState(38);
				match(NOT);
				setState(40);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__11) | (1L << MINUS) | (1L << OPAR) | (1L << INT) | (1L << VARNAME))) != 0)) {
					{
						setState(39);
						intexpr(0);
					}
				}

			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			exitRule();
		}
		return _localctx;
	}

	public static class JoinedContext extends ParserRuleContext {
		public TerminalNode EOF() {
			return getToken(NanoPromelaParser.EOF, 0);
		}

		public HsreadstmtContext hsreadstmt() {
			return getRuleContext(HsreadstmtContext.class, 0);
		}

		public HswritestmtContext hswritestmt() {
			return getRuleContext(HswritestmtContext.class, 0);
		}

		public JoinedContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_joined;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterJoined(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitJoined(this);
		}
	}

	public final JoinedContext joined() throws RecognitionException {
		JoinedContext _localctx = new JoinedContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_joined);
		try {
			enterOuterAlt(_localctx, 1);
			{
				setState(50);
				switch (getInterpreter().adaptivePredict(_input, 2, _ctx)) {
				case 1: {
					{
						setState(42);
						hsreadstmt();
						setState(43);
						match(T__1);
						setState(44);
						hswritestmt();
					}
				}
					break;
				case 2: {
					{
						setState(46);
						hswritestmt();
						setState(47);
						match(T__1);
						setState(48);
						hsreadstmt();
					}
				}
					break;
				}
				setState(52);
				match(EOF);
			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			exitRule();
		}
		return _localctx;
	}

	public static class OnesidedContext extends ParserRuleContext {
		public TerminalNode EOF() {
			return getToken(NanoPromelaParser.EOF, 0);
		}

		public HsreadstmtContext hsreadstmt() {
			return getRuleContext(HsreadstmtContext.class, 0);
		}

		public HswritestmtContext hswritestmt() {
			return getRuleContext(HswritestmtContext.class, 0);
		}

		public OnesidedContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_onesided;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterOnesided(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitOnesided(this);
		}
	}

	public final OnesidedContext onesided() throws RecognitionException {
		OnesidedContext _localctx = new OnesidedContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_onesided);
		try {
			enterOuterAlt(_localctx, 1);
			{
				setState(56);
				switch (getInterpreter().adaptivePredict(_input, 3, _ctx)) {
				case 1: {
					setState(54);
					hsreadstmt();
				}
					break;
				case 2: {
					setState(55);
					hswritestmt();
				}
					break;
				}
				setState(58);
				match(EOF);
			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SpecContext extends ParserRuleContext {
		public StmtContext stmt() {
			return getRuleContext(StmtContext.class, 0);
		}

		public TerminalNode EOF() {
			return getToken(NanoPromelaParser.EOF, 0);
		}

		public SpecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_spec;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterSpec(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitSpec(this);
		}
	}

	public final SpecContext spec() throws RecognitionException {
		SpecContext _localctx = new SpecContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_spec);
		try {
			enterOuterAlt(_localctx, 1);
			{
				setState(60);
				stmt(0);
				setState(61);
				match(EOF);
			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StmtContext extends ParserRuleContext {
		public IfstmtContext ifstmt() {
			return getRuleContext(IfstmtContext.class, 0);
		}

		public DostmtContext dostmt() {
			return getRuleContext(DostmtContext.class, 0);
		}

		public AssstmtContext assstmt() {
			return getRuleContext(AssstmtContext.class, 0);
		}

		public ChanreadstmtContext chanreadstmt() {
			return getRuleContext(ChanreadstmtContext.class, 0);
		}

		public ChanwritestmtContext chanwritestmt() {
			return getRuleContext(ChanwritestmtContext.class, 0);
		}

		public AtomicstmtContext atomicstmt() {
			return getRuleContext(AtomicstmtContext.class, 0);
		}

		public SkipstmtContext skipstmt() {
			return getRuleContext(SkipstmtContext.class, 0);
		}

		public List<StmtContext> stmt() {
			return getRuleContexts(StmtContext.class);
		}

		public StmtContext stmt(int i) {
			return getRuleContext(StmtContext.class, i);
		}

		public StmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_stmt;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterStmt(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitStmt(this);
		}
	}

	public final StmtContext stmt() throws RecognitionException {
		return stmt(0);
	}

	private StmtContext stmt(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		StmtContext _localctx = new StmtContext(_ctx, _parentState);
		StmtContext _prevctx = _localctx;
		int _startState = 10;
		enterRecursionRule(_localctx, 10, RULE_stmt, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
				setState(71);
				switch (getInterpreter().adaptivePredict(_input, 4, _ctx)) {
				case 1: {
					setState(64);
					ifstmt();
				}
					break;
				case 2: {
					setState(65);
					dostmt();
				}
					break;
				case 3: {
					setState(66);
					assstmt();
				}
					break;
				case 4: {
					setState(67);
					chanreadstmt();
				}
					break;
				case 5: {
					setState(68);
					chanwritestmt();
				}
					break;
				case 6: {
					setState(69);
					atomicstmt();
				}
					break;
				case 7: {
					setState(70);
					skipstmt();
				}
					break;
				}
				_ctx.stop = _input.LT(-1);
				setState(78);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input, 5, _ctx);
				while (_alt != 2 && _alt != org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER) {
					if (_alt == 1) {
						if (_parseListeners != null)
							triggerExitRuleEvent();
						_prevctx = _localctx;
						{
							{
								_localctx = new StmtContext(_parentctx, _parentState);
								pushNewRecursionContext(_localctx, _startState, RULE_stmt);
								setState(73);
								if (!(precpred(_ctx, 1)))
									throw new FailedPredicateException(this, "precpred(_ctx, 1)");
								setState(74);
								match(SCOL);
								setState(75);
								stmt(2);
							}
						}
					}
					setState(80);
					_errHandler.sync(this);
					_alt = getInterpreter().adaptivePredict(_input, 5, _ctx);
				}
			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class IfstmtContext extends ParserRuleContext {
		public List<OptionContext> option() {
			return getRuleContexts(OptionContext.class);
		}

		public OptionContext option(int i) {
			return getRuleContext(OptionContext.class, i);
		}

		public IfstmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_ifstmt;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterIfstmt(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitIfstmt(this);
		}
	}

	public final IfstmtContext ifstmt() throws RecognitionException {
		IfstmtContext _localctx = new IfstmtContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_ifstmt);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
				setState(81);
				match(T__2);
				setState(83);
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
						{
							setState(82);
							option();
						}
					}
					setState(85);
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while (_la == T__9);
				setState(87);
				match(T__3);
			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			exitRule();
		}
		return _localctx;
	}

	public static class DostmtContext extends ParserRuleContext {
		public List<OptionContext> option() {
			return getRuleContexts(OptionContext.class);
		}

		public OptionContext option(int i) {
			return getRuleContext(OptionContext.class, i);
		}

		public DostmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_dostmt;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterDostmt(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitDostmt(this);
		}
	}

	public final DostmtContext dostmt() throws RecognitionException {
		DostmtContext _localctx = new DostmtContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_dostmt);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
				setState(89);
				match(T__4);
				setState(91);
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
						{
							setState(90);
							option();
						}
					}
					setState(93);
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while (_la == T__9);
				setState(95);
				match(T__5);
			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssstmtContext extends ParserRuleContext {
		public TerminalNode VARNAME() {
			return getToken(NanoPromelaParser.VARNAME, 0);
		}

		public IntexprContext intexpr() {
			return getRuleContext(IntexprContext.class, 0);
		}

		public AssstmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_assstmt;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterAssstmt(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitAssstmt(this);
		}
	}

	public final AssstmtContext assstmt() throws RecognitionException {
		AssstmtContext _localctx = new AssstmtContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_assstmt);
		try {
			enterOuterAlt(_localctx, 1);
			{
				setState(97);
				match(VARNAME);
				setState(98);
				match(T__6);
				setState(99);
				intexpr(0);
			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ChanreadstmtContext extends ParserRuleContext {
		public TerminalNode CHANNAME() {
			return getToken(NanoPromelaParser.CHANNAME, 0);
		}

		public TerminalNode VARNAME() {
			return getToken(NanoPromelaParser.VARNAME, 0);
		}

		public ChanreadstmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_chanreadstmt;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterChanreadstmt(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitChanreadstmt(this);
		}
	}

	public final ChanreadstmtContext chanreadstmt() throws RecognitionException {
		ChanreadstmtContext _localctx = new ChanreadstmtContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_chanreadstmt);
		try {
			enterOuterAlt(_localctx, 1);
			{
				setState(101);
				match(CHANNAME);
				setState(102);
				match(T__0);
				setState(103);
				match(VARNAME);
			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ChanwritestmtContext extends ParserRuleContext {
		public TerminalNode CHANNAME() {
			return getToken(NanoPromelaParser.CHANNAME, 0);
		}

		public IntexprContext intexpr() {
			return getRuleContext(IntexprContext.class, 0);
		}

		public ChanwritestmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_chanwritestmt;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterChanwritestmt(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitChanwritestmt(this);
		}
	}

	public final ChanwritestmtContext chanwritestmt() throws RecognitionException {
		ChanwritestmtContext _localctx = new ChanwritestmtContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_chanwritestmt);
		try {
			enterOuterAlt(_localctx, 1);
			{
				setState(105);
				match(CHANNAME);
				setState(106);
				match(NOT);
				setState(107);
				intexpr(0);
			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AtomicstmtContext extends ParserRuleContext {
		public List<TerminalNode> VARNAME() {
			return getTokens(NanoPromelaParser.VARNAME);
		}

		public TerminalNode VARNAME(int i) {
			return getToken(NanoPromelaParser.VARNAME, i);
		}

		public List<IntexprContext> intexpr() {
			return getRuleContexts(IntexprContext.class);
		}

		public IntexprContext intexpr(int i) {
			return getRuleContext(IntexprContext.class, i);
		}

		public AtomicstmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_atomicstmt;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterAtomicstmt(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitAtomicstmt(this);
		}
	}

	public final AtomicstmtContext atomicstmt() throws RecognitionException {
		AtomicstmtContext _localctx = new AtomicstmtContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_atomicstmt);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
				setState(109);
				match(T__7);
				setState(110);
				match(OBRACE);
				setState(118);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input, 8, _ctx);
				while (_alt != 2 && _alt != org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER) {
					if (_alt == 1) {
						{
							{
								setState(111);
								match(VARNAME);
								setState(112);
								match(T__6);
								setState(113);
								intexpr(0);
								setState(114);
								match(SCOL);
							}
						}
					}
					setState(120);
					_errHandler.sync(this);
					_alt = getInterpreter().adaptivePredict(_input, 8, _ctx);
				}
				setState(121);
				match(VARNAME);
				setState(122);
				match(T__6);
				setState(123);
				intexpr(0);
				setState(124);
				match(CBRACE);
			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SkipstmtContext extends ParserRuleContext {
		public SkipstmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_skipstmt;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterSkipstmt(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitSkipstmt(this);
		}
	}

	public final SkipstmtContext skipstmt() throws RecognitionException {
		SkipstmtContext _localctx = new SkipstmtContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_skipstmt);
		try {
			enterOuterAlt(_localctx, 1);
			{
				setState(126);
				match(T__8);
			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			exitRule();
		}
		return _localctx;
	}

	public static class OptionContext extends ParserRuleContext {
		public BoolexprContext boolexpr() {
			return getRuleContext(BoolexprContext.class, 0);
		}

		public StmtContext stmt() {
			return getRuleContext(StmtContext.class, 0);
		}

		public OptionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_option;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterOption(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitOption(this);
		}
	}

	public final OptionContext option() throws RecognitionException {
		OptionContext _localctx = new OptionContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_option);
		try {
			enterOuterAlt(_localctx, 1);
			{
				setState(128);
				match(T__9);
				setState(129);
				boolexpr(0);
				setState(130);
				match(T__10);
				setState(131);
				stmt(0);
			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			exitRule();
		}
		return _localctx;
	}

	public static class IntexprContext extends ParserRuleContext {
		public Token op;

		public TerminalNode MINUS() {
			return getToken(NanoPromelaParser.MINUS, 0);
		}

		public List<IntexprContext> intexpr() {
			return getRuleContexts(IntexprContext.class);
		}

		public IntexprContext intexpr(int i) {
			return getRuleContext(IntexprContext.class, i);
		}

		public TerminalNode INT() {
			return getToken(NanoPromelaParser.INT, 0);
		}

		public TerminalNode CHANNAME() {
			return getToken(NanoPromelaParser.CHANNAME, 0);
		}

		public TerminalNode VARNAME() {
			return getToken(NanoPromelaParser.VARNAME, 0);
		}

		public TerminalNode OPAR() {
			return getToken(NanoPromelaParser.OPAR, 0);
		}

		public TerminalNode CPAR() {
			return getToken(NanoPromelaParser.CPAR, 0);
		}

		public TerminalNode POW() {
			return getToken(NanoPromelaParser.POW, 0);
		}

		public TerminalNode MULT() {
			return getToken(NanoPromelaParser.MULT, 0);
		}

		public TerminalNode DIV() {
			return getToken(NanoPromelaParser.DIV, 0);
		}

		public TerminalNode MOD() {
			return getToken(NanoPromelaParser.MOD, 0);
		}

		public TerminalNode PLUS() {
			return getToken(NanoPromelaParser.PLUS, 0);
		}

		public IntexprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_intexpr;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterIntexpr(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitIntexpr(this);
		}
	}

	public final IntexprContext intexpr() throws RecognitionException {
		return intexpr(0);
	}

	private IntexprContext intexpr(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		IntexprContext _localctx = new IntexprContext(_ctx, _parentState);
		IntexprContext _prevctx = _localctx;
		int _startState = 28;
		enterRecursionRule(_localctx, 28, RULE_intexpr, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
				setState(145);
				switch (_input.LA(1)) {
				case MINUS: {
					setState(134);
					match(MINUS);
					setState(135);
					intexpr(7);
				}
					break;
				case INT: {
					setState(136);
					match(INT);
				}
					break;
				case T__11: {
					setState(137);
					match(T__11);
					setState(138);
					match(CHANNAME);
					setState(139);
					match(CPAR);
				}
					break;
				case VARNAME: {
					setState(140);
					match(VARNAME);
				}
					break;
				case OPAR: {
					setState(141);
					match(OPAR);
					setState(142);
					intexpr(0);
					setState(143);
					match(CPAR);
				}
					break;
				default:
					throw new NoViableAltException(this);
				}
				_ctx.stop = _input.LT(-1);
				setState(158);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input, 11, _ctx);
				while (_alt != 2 && _alt != org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER) {
					if (_alt == 1) {
						if (_parseListeners != null)
							triggerExitRuleEvent();
						_prevctx = _localctx;
						{
							setState(156);
							switch (getInterpreter().adaptivePredict(_input, 10, _ctx)) {
							case 1: {
								_localctx = new IntexprContext(_parentctx, _parentState);
								pushNewRecursionContext(_localctx, _startState, RULE_intexpr);
								setState(147);
								if (!(precpred(_ctx, 8)))
									throw new FailedPredicateException(this, "precpred(_ctx, 8)");
								setState(148);
								match(POW);
								setState(149);
								intexpr(9);
							}
								break;
							case 2: {
								_localctx = new IntexprContext(_parentctx, _parentState);
								pushNewRecursionContext(_localctx, _startState, RULE_intexpr);
								setState(150);
								if (!(precpred(_ctx, 6)))
									throw new FailedPredicateException(this, "precpred(_ctx, 6)");
								setState(151);
								((IntexprContext) _localctx).op = _input.LT(1);
								_la = _input.LA(1);
								if (!((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << MULT) | (1L << DIV) | (1L << MOD))) != 0))) {
									((IntexprContext) _localctx).op = (Token) _errHandler.recoverInline(this);
								} else {
									consume();
								}
								setState(152);
								intexpr(7);
							}
								break;
							case 3: {
								_localctx = new IntexprContext(_parentctx, _parentState);
								pushNewRecursionContext(_localctx, _startState, RULE_intexpr);
								setState(153);
								if (!(precpred(_ctx, 5)))
									throw new FailedPredicateException(this, "precpred(_ctx, 5)");
								setState(154);
								((IntexprContext) _localctx).op = _input.LT(1);
								_la = _input.LA(1);
								if (!(_la == PLUS || _la == MINUS)) {
									((IntexprContext) _localctx).op = (Token) _errHandler.recoverInline(this);
								} else {
									consume();
								}
								setState(155);
								intexpr(6);
							}
								break;
							}
						}
					}
					setState(160);
					_errHandler.sync(this);
					_alt = getInterpreter().adaptivePredict(_input, 11, _ctx);
				}
			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class BoolexprContext extends ParserRuleContext {
		public Token op;

		public TerminalNode NOT() {
			return getToken(NanoPromelaParser.NOT, 0);
		}

		public List<BoolexprContext> boolexpr() {
			return getRuleContexts(BoolexprContext.class);
		}

		public BoolexprContext boolexpr(int i) {
			return getRuleContext(BoolexprContext.class, i);
		}

		public List<IntexprContext> intexpr() {
			return getRuleContexts(IntexprContext.class);
		}

		public IntexprContext intexpr(int i) {
			return getRuleContext(IntexprContext.class, i);
		}

		public TerminalNode LTEQ() {
			return getToken(NanoPromelaParser.LTEQ, 0);
		}

		public TerminalNode GTEQ() {
			return getToken(NanoPromelaParser.GTEQ, 0);
		}

		public TerminalNode LT() {
			return getToken(NanoPromelaParser.LT, 0);
		}

		public TerminalNode GT() {
			return getToken(NanoPromelaParser.GT, 0);
		}

		public TerminalNode EQ() {
			return getToken(NanoPromelaParser.EQ, 0);
		}

		public TerminalNode NEQ() {
			return getToken(NanoPromelaParser.NEQ, 0);
		}

		public TerminalNode TRUE() {
			return getToken(NanoPromelaParser.TRUE, 0);
		}

		public TerminalNode FALSE() {
			return getToken(NanoPromelaParser.FALSE, 0);
		}

		public TerminalNode OPAR() {
			return getToken(NanoPromelaParser.OPAR, 0);
		}

		public TerminalNode CPAR() {
			return getToken(NanoPromelaParser.CPAR, 0);
		}

		public TerminalNode AND() {
			return getToken(NanoPromelaParser.AND, 0);
		}

		public TerminalNode OR() {
			return getToken(NanoPromelaParser.OR, 0);
		}

		public BoolexprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}

		@Override
		public int getRuleIndex() {
			return RULE_boolexpr;
		}

		@Override
		public void enterRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).enterBoolexpr(this);
		}

		@Override
		public void exitRule(ParseTreeListener listener) {
			if (listener instanceof NanoPromelaListener)
				((NanoPromelaListener) listener).exitBoolexpr(this);
		}
	}

	public final BoolexprContext boolexpr() throws RecognitionException {
		return boolexpr(0);
	}

	private BoolexprContext boolexpr(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		BoolexprContext _localctx = new BoolexprContext(_ctx, _parentState);
		BoolexprContext _prevctx = _localctx;
		int _startState = 30;
		enterRecursionRule(_localctx, 30, RULE_boolexpr, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
				setState(178);
				switch (getInterpreter().adaptivePredict(_input, 12, _ctx)) {
				case 1: {
					setState(162);
					match(NOT);
					setState(163);
					boolexpr(8);
				}
					break;
				case 2: {
					setState(164);
					intexpr(0);
					setState(165);
					((BoolexprContext) _localctx).op = _input.LT(1);
					_la = _input.LA(1);
					if (!((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << GT) | (1L << LT) | (1L << GTEQ) | (1L << LTEQ))) != 0))) {
						((BoolexprContext) _localctx).op = (Token) _errHandler.recoverInline(this);
					} else {
						consume();
					}
					setState(166);
					intexpr(0);
				}
					break;
				case 3: {
					setState(168);
					intexpr(0);
					setState(169);
					((BoolexprContext) _localctx).op = _input.LT(1);
					_la = _input.LA(1);
					if (!(_la == EQ || _la == NEQ)) {
						((BoolexprContext) _localctx).op = (Token) _errHandler.recoverInline(this);
					} else {
						consume();
					}
					setState(170);
					intexpr(0);
				}
					break;
				case 4: {
					setState(172);
					match(TRUE);
				}
					break;
				case 5: {
					setState(173);
					match(FALSE);
				}
					break;
				case 6: {
					setState(174);
					match(OPAR);
					setState(175);
					boolexpr(0);
					setState(176);
					match(CPAR);
				}
					break;
				}
				_ctx.stop = _input.LT(-1);
				setState(188);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input, 14, _ctx);
				while (_alt != 2 && _alt != org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER) {
					if (_alt == 1) {
						if (_parseListeners != null)
							triggerExitRuleEvent();
						_prevctx = _localctx;
						{
							setState(186);
							switch (getInterpreter().adaptivePredict(_input, 13, _ctx)) {
							case 1: {
								_localctx = new BoolexprContext(_parentctx, _parentState);
								pushNewRecursionContext(_localctx, _startState, RULE_boolexpr);
								setState(180);
								if (!(precpred(_ctx, 7)))
									throw new FailedPredicateException(this, "precpred(_ctx, 7)");
								setState(181);
								match(AND);
								setState(182);
								boolexpr(8);
							}
								break;
							case 2: {
								_localctx = new BoolexprContext(_parentctx, _parentState);
								pushNewRecursionContext(_localctx, _startState, RULE_boolexpr);
								setState(183);
								if (!(precpred(_ctx, 6)))
									throw new FailedPredicateException(this, "precpred(_ctx, 6)");
								setState(184);
								match(OR);
								setState(185);
								boolexpr(7);
							}
								break;
							}
						}
					}
					setState(190);
					_errHandler.sync(this);
					_alt = getInterpreter().adaptivePredict(_input, 14, _ctx);
				}
			}
		} catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		} finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 5:
			return stmt_sempred((StmtContext) _localctx, predIndex);
		case 14:
			return intexpr_sempred((IntexprContext) _localctx, predIndex);
		case 15:
			return boolexpr_sempred((BoolexprContext) _localctx, predIndex);
		}
		return true;
	}

	private boolean stmt_sempred(StmtContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 1);
		}
		return true;
	}

	private boolean intexpr_sempred(IntexprContext _localctx, int predIndex) {
		switch (predIndex) {
		case 1:
			return precpred(_ctx, 8);
		case 2:
			return precpred(_ctx, 6);
		case 3:
			return precpred(_ctx, 5);
		}
		return true;
	}

	private boolean boolexpr_sempred(BoolexprContext _localctx, int predIndex) {
		switch (predIndex) {
		case 4:
			return precpred(_ctx, 7);
		case 5:
			return precpred(_ctx, 6);
		}
		return true;
	}

	public static final String	_serializedATN	= "\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\3,\u00c2\4\2\t\2\4" + "\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t" + "\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\3\2\3\2\3"
			+ "\2\5\2&\n\2\3\3\3\3\3\3\5\3+\n\3\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\5\4\65" + "\n\4\3\4\3\4\3\5\3\5\5\5;\n\5\3\5\3\5\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3\7" + "\3\7\3\7\3\7\5\7J\n\7\3\7\3\7\3\7\7\7O\n\7\f\7\16\7R\13\7\3\b\3\b\6\b"
			+ "V\n\b\r\b\16\bW\3\b\3\b\3\t\3\t\6\t^\n\t\r\t\16\t_\3\t\3\t\3\n\3\n\3\n" + "\3\n\3\13\3\13\3\13\3\13\3\f\3\f\3\f\3\f\3\r\3\r\3\r\3\r\3\r\3\r\3\r\7" + "\rw\n\r\f\r\16\rz\13\r\3\r\3\r\3\r\3\r\3\r\3\16\3\16\3\17\3\17\3\17\3"
			+ "\17\3\17\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\5" + "\20\u0094\n\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\3\20\7\20\u009f" + "\n\20\f\20\16\20\u00a2\13\20\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3"
			+ "\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\3\21\5\21\u00b5\n\21\3\21\3\21" + "\3\21\3\21\3\21\3\21\7\21\u00bd\n\21\f\21\16\21\u00c0\13\21\3\21\2\5\f" + "\36 \22\2\4\6\b\n\f\16\20\22\24\26\30\32\34\36 \2\6\3\2\31\33\3\2\27\30"
			+ "\3\2\23\26\3\2\21\22\u00cd\2\"\3\2\2\2\4\'\3\2\2\2\6\64\3\2\2\2\b:\3\2" + "\2\2\n>\3\2\2\2\fI\3\2\2\2\16S\3\2\2\2\20[\3\2\2\2\22c\3\2\2\2\24g\3\2" + "\2\2\26k\3\2\2\2\30o\3\2\2\2\32\u0080\3\2\2\2\34\u0082\3\2\2\2\36\u0093"
			+ "\3\2\2\2 \u00b4\3\2\2\2\"#\7)\2\2#%\7\3\2\2$&\7\'\2\2%$\3\2\2\2%&\3\2" + "\2\2&\3\3\2\2\2\'(\7)\2\2(*\7\35\2\2)+\5\36\20\2*)\3\2\2\2*+\3\2\2\2+" + "\5\3\2\2\2,-\5\2\2\2-.\7\4\2\2./\5\4\3\2/\65\3\2\2\2\60\61\5\4\3\2\61"
			+ "\62\7\4\2\2\62\63\5\2\2\2\63\65\3\2\2\2\64,\3\2\2\2\64\60\3\2\2\2\65\66" + "\3\2\2\2\66\67\7\2\2\3\67\7\3\2\2\28;\5\2\2\29;\5\4\3\2:8\3\2\2\2:9\3" + "\2\2\2;<\3\2\2\2<=\7\2\2\3=\t\3\2\2\2>?\5\f\7\2?@\7\2\2\3@\13\3\2\2\2"
			+ "AB\b\7\1\2BJ\5\16\b\2CJ\5\20\t\2DJ\5\22\n\2EJ\5\24\13\2FJ\5\26\f\2GJ\5" + "\30\r\2HJ\5\32\16\2IA\3\2\2\2IC\3\2\2\2ID\3\2\2\2IE\3\2\2\2IF\3\2\2\2" + "IG\3\2\2\2IH\3\2\2\2JP\3\2\2\2KL\f\3\2\2LM\7\36\2\2MO\5\f\7\4NK\3\2\2"
			+ "\2OR\3\2\2\2PN\3\2\2\2PQ\3\2\2\2Q\r\3\2\2\2RP\3\2\2\2SU\7\5\2\2TV\5\34" + "\17\2UT\3\2\2\2VW\3\2\2\2WU\3\2\2\2WX\3\2\2\2XY\3\2\2\2YZ\7\6\2\2Z\17" + "\3\2\2\2[]\7\7\2\2\\^\5\34\17\2]\\\3\2\2\2^_\3\2\2\2_]\3\2\2\2_`\3\2\2"
			+ "\2`a\3\2\2\2ab\7\b\2\2b\21\3\2\2\2cd\7\'\2\2de\7\t\2\2ef\5\36\20\2f\23" + "\3\2\2\2gh\7(\2\2hi\7\3\2\2ij\7\'\2\2j\25\3\2\2\2kl\7(\2\2lm\7\35\2\2" + "mn\5\36\20\2n\27\3\2\2\2op\7\n\2\2px\7\"\2\2qr\7\'\2\2rs\7\t\2\2st\5\36"
			+ "\20\2tu\7\36\2\2uw\3\2\2\2vq\3\2\2\2wz\3\2\2\2xv\3\2\2\2xy\3\2\2\2y{\3" + "\2\2\2zx\3\2\2\2{|\7\'\2\2|}\7\t\2\2}~\5\36\20\2~\177\7#\2\2\177\31\3" + "\2\2\2\u0080\u0081\7\13\2\2\u0081\33\3\2\2\2\u0082\u0083\7\f\2\2\u0083"
			+ "\u0084\5 \21\2\u0084\u0085\7\r\2\2\u0085\u0086\5\f\7\2\u0086\35\3\2\2" + "\2\u0087\u0088\b\20\1\2\u0088\u0089\7\30\2\2\u0089\u0094\5\36\20\t\u008a" + "\u0094\7&\2\2\u008b\u008c\7\16\2\2\u008c\u008d\7(\2\2\u008d\u0094\7!\2"
			+ "\2\u008e\u0094\7\'\2\2\u008f\u0090\7 \2\2\u0090\u0091\5\36\20\2\u0091" + "\u0092\7!\2\2\u0092\u0094\3\2\2\2\u0093\u0087\3\2\2\2\u0093\u008a\3\2" + "\2\2\u0093\u008b\3\2\2\2\u0093\u008e\3\2\2\2\u0093\u008f\3\2\2\2\u0094"
			+ "\u00a0\3\2\2\2\u0095\u0096\f\n\2\2\u0096\u0097\7\34\2\2\u0097\u009f\5" + "\36\20\13\u0098\u0099\f\b\2\2\u0099\u009a\t\2\2\2\u009a\u009f\5\36\20" + "\t\u009b\u009c\f\7\2\2\u009c\u009d\t\3\2\2\u009d\u009f\5\36\20\b\u009e"
			+ "\u0095\3\2\2\2\u009e\u0098\3\2\2\2\u009e\u009b\3\2\2\2\u009f\u00a2\3\2" + "\2\2\u00a0\u009e\3\2\2\2\u00a0\u00a1\3\2\2\2\u00a1\37\3\2\2\2\u00a2\u00a0" + "\3\2\2\2\u00a3\u00a4\b\21\1\2\u00a4\u00a5\7\35\2\2\u00a5\u00b5\5 \21\n"
			+ "\u00a6\u00a7\5\36\20\2\u00a7\u00a8\t\4\2\2\u00a8\u00a9\5\36\20\2\u00a9" + "\u00b5\3\2\2\2\u00aa\u00ab\5\36\20\2\u00ab\u00ac\t\5\2\2\u00ac\u00ad\5" + "\36\20\2\u00ad\u00b5\3\2\2\2\u00ae\u00b5\7$\2\2\u00af\u00b5\7%\2\2\u00b0"
			+ "\u00b1\7 \2\2\u00b1\u00b2\5 \21\2\u00b2\u00b3\7!\2\2\u00b3\u00b5\3\2\2" + "\2\u00b4\u00a3\3\2\2\2\u00b4\u00a6\3\2\2\2\u00b4\u00aa\3\2\2\2\u00b4\u00ae" + "\3\2\2\2\u00b4\u00af\3\2\2\2\u00b4\u00b0\3\2\2\2\u00b5\u00be\3\2\2\2\u00b6"
			+ "\u00b7\f\t\2\2\u00b7\u00b8\7\20\2\2\u00b8\u00bd\5 \21\n\u00b9\u00ba\f" + "\b\2\2\u00ba\u00bb\7\17\2\2\u00bb\u00bd\5 \21\t\u00bc\u00b6\3\2\2\2\u00bc" + "\u00b9\3\2\2\2\u00bd\u00c0\3\2\2\2\u00be\u00bc\3\2\2\2\u00be\u00bf\3\2"
			+ "\2\2\u00bf!\3\2\2\2\u00c0\u00be\3\2\2\2\21%*\64:IPW_x\u0093\u009e\u00a0" + "\u00b4\u00bc\u00be";
	public static final ATN		_ATN			= new ATNDeserializer().deserialize(_serializedATN.toCharArray());

	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}