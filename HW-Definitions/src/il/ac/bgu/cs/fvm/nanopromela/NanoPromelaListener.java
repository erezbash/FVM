// Generated from NanoPromela.g4 by ANTLR 4.5.1
package il.ac.bgu.cs.fvm.nanopromela;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link NanoPromelaParser}.
 */
public interface NanoPromelaListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#hsreadstmt}.
	 * @param ctx the parse tree
	 */
	void enterHsreadstmt(NanoPromelaParser.HsreadstmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#hsreadstmt}.
	 * @param ctx the parse tree
	 */
	void exitHsreadstmt(NanoPromelaParser.HsreadstmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#hswritestmt}.
	 * @param ctx the parse tree
	 */
	void enterHswritestmt(NanoPromelaParser.HswritestmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#hswritestmt}.
	 * @param ctx the parse tree
	 */
	void exitHswritestmt(NanoPromelaParser.HswritestmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#joined}.
	 * @param ctx the parse tree
	 */
	void enterJoined(NanoPromelaParser.JoinedContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#joined}.
	 * @param ctx the parse tree
	 */
	void exitJoined(NanoPromelaParser.JoinedContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#onesided}.
	 * @param ctx the parse tree
	 */
	void enterOnesided(NanoPromelaParser.OnesidedContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#onesided}.
	 * @param ctx the parse tree
	 */
	void exitOnesided(NanoPromelaParser.OnesidedContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#spec}.
	 * @param ctx the parse tree
	 */
	void enterSpec(NanoPromelaParser.SpecContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#spec}.
	 * @param ctx the parse tree
	 */
	void exitSpec(NanoPromelaParser.SpecContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterStmt(NanoPromelaParser.StmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitStmt(NanoPromelaParser.StmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#ifstmt}.
	 * @param ctx the parse tree
	 */
	void enterIfstmt(NanoPromelaParser.IfstmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#ifstmt}.
	 * @param ctx the parse tree
	 */
	void exitIfstmt(NanoPromelaParser.IfstmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#dostmt}.
	 * @param ctx the parse tree
	 */
	void enterDostmt(NanoPromelaParser.DostmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#dostmt}.
	 * @param ctx the parse tree
	 */
	void exitDostmt(NanoPromelaParser.DostmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#assstmt}.
	 * @param ctx the parse tree
	 */
	void enterAssstmt(NanoPromelaParser.AssstmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#assstmt}.
	 * @param ctx the parse tree
	 */
	void exitAssstmt(NanoPromelaParser.AssstmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#chanreadstmt}.
	 * @param ctx the parse tree
	 */
	void enterChanreadstmt(NanoPromelaParser.ChanreadstmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#chanreadstmt}.
	 * @param ctx the parse tree
	 */
	void exitChanreadstmt(NanoPromelaParser.ChanreadstmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#chanwritestmt}.
	 * @param ctx the parse tree
	 */
	void enterChanwritestmt(NanoPromelaParser.ChanwritestmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#chanwritestmt}.
	 * @param ctx the parse tree
	 */
	void exitChanwritestmt(NanoPromelaParser.ChanwritestmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#atomicstmt}.
	 * @param ctx the parse tree
	 */
	void enterAtomicstmt(NanoPromelaParser.AtomicstmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#atomicstmt}.
	 * @param ctx the parse tree
	 */
	void exitAtomicstmt(NanoPromelaParser.AtomicstmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#skipstmt}.
	 * @param ctx the parse tree
	 */
	void enterSkipstmt(NanoPromelaParser.SkipstmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#skipstmt}.
	 * @param ctx the parse tree
	 */
	void exitSkipstmt(NanoPromelaParser.SkipstmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#option}.
	 * @param ctx the parse tree
	 */
	void enterOption(NanoPromelaParser.OptionContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#option}.
	 * @param ctx the parse tree
	 */
	void exitOption(NanoPromelaParser.OptionContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#intexpr}.
	 * @param ctx the parse tree
	 */
	void enterIntexpr(NanoPromelaParser.IntexprContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#intexpr}.
	 * @param ctx the parse tree
	 */
	void exitIntexpr(NanoPromelaParser.IntexprContext ctx);
	/**
	 * Enter a parse tree produced by {@link NanoPromelaParser#boolexpr}.
	 * @param ctx the parse tree
	 */
	void enterBoolexpr(NanoPromelaParser.BoolexprContext ctx);
	/**
	 * Exit a parse tree produced by {@link NanoPromelaParser#boolexpr}.
	 * @param ctx the parse tree
	 */
	void exitBoolexpr(NanoPromelaParser.BoolexprContext ctx);
}