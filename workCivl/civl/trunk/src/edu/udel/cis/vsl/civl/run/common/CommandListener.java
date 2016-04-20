// Generated from Command.g4 by ANTLR 4.4
package edu.udel.cis.vsl.civl.run.common;
import org.antlr.v4.runtime.misc.NotNull;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link CommandParser}.
 */
public interface CommandListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link CommandParser#commonOption}.
	 * @param ctx the parse tree
	 */
	void enterCommonOption(@NotNull CommandParser.CommonOptionContext ctx);
	/**
	 * Exit a parse tree produced by {@link CommandParser#commonOption}.
	 * @param ctx the parse tree
	 */
	void exitCommonOption(@NotNull CommandParser.CommonOptionContext ctx);
	/**
	 * Enter a parse tree produced by {@link CommandParser#specAndImplCommand}.
	 * @param ctx the parse tree
	 */
	void enterSpecAndImplCommand(@NotNull CommandParser.SpecAndImplCommandContext ctx);
	/**
	 * Exit a parse tree produced by {@link CommandParser#specAndImplCommand}.
	 * @param ctx the parse tree
	 */
	void exitSpecAndImplCommand(@NotNull CommandParser.SpecAndImplCommandContext ctx);
	/**
	 * Enter a parse tree produced by the {@code normal}
	 * labeled alternative in {@link CommandParser#start}.
	 * @param ctx the parse tree
	 */
	void enterNormal(@NotNull CommandParser.NormalContext ctx);
	/**
	 * Exit a parse tree produced by the {@code normal}
	 * labeled alternative in {@link CommandParser#start}.
	 * @param ctx the parse tree
	 */
	void exitNormal(@NotNull CommandParser.NormalContext ctx);
	/**
	 * Enter a parse tree produced by the {@code compare}
	 * labeled alternative in {@link CommandParser#start}.
	 * @param ctx the parse tree
	 */
	void enterCompare(@NotNull CommandParser.CompareContext ctx);
	/**
	 * Exit a parse tree produced by the {@code compare}
	 * labeled alternative in {@link CommandParser#start}.
	 * @param ctx the parse tree
	 */
	void exitCompare(@NotNull CommandParser.CompareContext ctx);
	/**
	 * Enter a parse tree produced by the {@code replayCompare}
	 * labeled alternative in {@link CommandParser#start}.
	 * @param ctx the parse tree
	 */
	void enterReplayCompare(@NotNull CommandParser.ReplayCompareContext ctx);
	/**
	 * Exit a parse tree produced by the {@code replayCompare}
	 * labeled alternative in {@link CommandParser#start}.
	 * @param ctx the parse tree
	 */
	void exitReplayCompare(@NotNull CommandParser.ReplayCompareContext ctx);
	/**
	 * Enter a parse tree produced by {@link CommandParser#implCommand}.
	 * @param ctx the parse tree
	 */
	void enterImplCommand(@NotNull CommandParser.ImplCommandContext ctx);
	/**
	 * Exit a parse tree produced by {@link CommandParser#implCommand}.
	 * @param ctx the parse tree
	 */
	void exitImplCommand(@NotNull CommandParser.ImplCommandContext ctx);
	/**
	 * Enter a parse tree produced by {@link CommandParser#commandBody}.
	 * @param ctx the parse tree
	 */
	void enterCommandBody(@NotNull CommandParser.CommandBodyContext ctx);
	/**
	 * Exit a parse tree produced by {@link CommandParser#commandBody}.
	 * @param ctx the parse tree
	 */
	void exitCommandBody(@NotNull CommandParser.CommandBodyContext ctx);
	/**
	 * Enter a parse tree produced by the {@code inputOption}
	 * labeled alternative in {@link CommandParser#option}.
	 * @param ctx the parse tree
	 */
	void enterInputOption(@NotNull CommandParser.InputOptionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code inputOption}
	 * labeled alternative in {@link CommandParser#option}.
	 * @param ctx the parse tree
	 */
	void exitInputOption(@NotNull CommandParser.InputOptionContext ctx);
	/**
	 * Enter a parse tree produced by the {@code help}
	 * labeled alternative in {@link CommandParser#start}.
	 * @param ctx the parse tree
	 */
	void enterHelp(@NotNull CommandParser.HelpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code help}
	 * labeled alternative in {@link CommandParser#start}.
	 * @param ctx the parse tree
	 */
	void exitHelp(@NotNull CommandParser.HelpContext ctx);
	/**
	 * Enter a parse tree produced by {@link CommandParser#file}.
	 * @param ctx the parse tree
	 */
	void enterFile(@NotNull CommandParser.FileContext ctx);
	/**
	 * Exit a parse tree produced by {@link CommandParser#file}.
	 * @param ctx the parse tree
	 */
	void exitFile(@NotNull CommandParser.FileContext ctx);
	/**
	 * Enter a parse tree produced by {@link CommandParser#specCommand}.
	 * @param ctx the parse tree
	 */
	void enterSpecCommand(@NotNull CommandParser.SpecCommandContext ctx);
	/**
	 * Exit a parse tree produced by {@link CommandParser#specCommand}.
	 * @param ctx the parse tree
	 */
	void exitSpecCommand(@NotNull CommandParser.SpecCommandContext ctx);
	/**
	 * Enter a parse tree produced by the {@code macroOption}
	 * labeled alternative in {@link CommandParser#option}.
	 * @param ctx the parse tree
	 */
	void enterMacroOption(@NotNull CommandParser.MacroOptionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code macroOption}
	 * labeled alternative in {@link CommandParser#option}.
	 * @param ctx the parse tree
	 */
	void exitMacroOption(@NotNull CommandParser.MacroOptionContext ctx);
	/**
	 * Enter a parse tree produced by {@link CommandParser#value}.
	 * @param ctx the parse tree
	 */
	void enterValue(@NotNull CommandParser.ValueContext ctx);
	/**
	 * Exit a parse tree produced by {@link CommandParser#value}.
	 * @param ctx the parse tree
	 */
	void exitValue(@NotNull CommandParser.ValueContext ctx);
	/**
	 * Enter a parse tree produced by the {@code config}
	 * labeled alternative in {@link CommandParser#start}.
	 * @param ctx the parse tree
	 */
	void enterConfig(@NotNull CommandParser.ConfigContext ctx);
	/**
	 * Exit a parse tree produced by the {@code config}
	 * labeled alternative in {@link CommandParser#start}.
	 * @param ctx the parse tree
	 */
	void exitConfig(@NotNull CommandParser.ConfigContext ctx);
	/**
	 * Enter a parse tree produced by the {@code normalOption}
	 * labeled alternative in {@link CommandParser#option}.
	 * @param ctx the parse tree
	 */
	void enterNormalOption(@NotNull CommandParser.NormalOptionContext ctx);
	/**
	 * Exit a parse tree produced by the {@code normalOption}
	 * labeled alternative in {@link CommandParser#option}.
	 * @param ctx the parse tree
	 */
	void exitNormalOption(@NotNull CommandParser.NormalOptionContext ctx);
}