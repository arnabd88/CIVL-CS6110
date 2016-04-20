package edu.udel.cis.vsl.civl.run.IF;

import edu.udel.cis.vsl.gmc.GMCConfiguration;

/**
 * A command line represents the command line information for running CIVL.
 * 
 * @author Manchun Zheng
 *
 */
public interface CommandLine {

	public final static String CONFIG = "config";
	public final static String COMPARE = "compare";
	public final static String GUI = "gui";
	public final static String HELP = "help";
	public final static String REPLAY = "replay";
	public final static String RUN = "run";
	public final static String SHOW = "show";
	public final static String VERIFY = "verify";

	/**
	 * CIVL command line kinds: normal, or compare.
	 * 
	 * Normal command line contains one GMC section (anonymous), where compare
	 * command line has three GMC section (anonymous, impl, and spec).
	 * 
	 * @author Manchun Zheng
	 */
	public enum CommandLineKind {
		NORMAL, COMPARE
	}

	/**
	 * The kind of this command line
	 * 
	 * @return
	 */
	CommandLineKind commandLineKind();

	void setCommandString(String string);

	String getCommandString();

	GMCConfiguration gmcConfig();

	void setGMCConfig(GMCConfiguration config);

}
