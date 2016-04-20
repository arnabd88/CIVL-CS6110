package edu.udel.cis.vsl.civl.run.IF;


public interface CommandLine {
	public enum CommandLineKind {
		NORMAL,
		COMPARE
	}

	public enum CommandKind {
		COMPARE,
		GUI,
		HELP,
		REPLAY,
		RUN,
		SHOW,
		VERIFY
	}

	CommandLineKind commandLineKind();

	void setCommandString(String string);

	String getCommandString();

	CommandKind commandKind();

	/**
	 * null unless command kind is HELP.
	 * 
	 * @return
	 */
	CommandKind commandArg();

	void setCommandKind(CommandKind cmd);

	void setCommandArg(CommandKind arg);

}
