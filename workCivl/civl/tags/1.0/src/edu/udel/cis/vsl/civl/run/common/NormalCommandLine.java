package edu.udel.cis.vsl.civl.run.common;

import java.io.File;
import java.util.Collection;

import edu.udel.cis.vsl.civl.run.IF.CommandLine;
import edu.udel.cis.vsl.gmc.GMCSection;

public class NormalCommandLine extends BaseCommandLine implements CommandLine {

	public enum NormalCommandKind {
		CONFIG, SHOW, VERIFY, REPLAY, GUI, HELP, RUN
	}

	protected NormalCommandKind commandKind;
	private GMCSection cmdSection;
	private String[] files;
	private File coreFile;
	private String coreFileName;

	public NormalCommandLine() {
	}

	public NormalCommandLine(NormalCommandKind command,
			GMCSection cmdSection, String[] files) {
		this.commandKind = command;
		this.cmdSection = cmdSection;
		this.files = files;
	}

	public void setCommand(NormalCommandKind cmd) {
		this.commandKind = cmd;
	}

	public NormalCommandKind normalCommandKind() {
		return this.commandKind;
	}

	public GMCSection gmcSection() {
		return this.cmdSection;
	}

	public void setGMCSection(GMCSection config) {
		this.cmdSection = config;
	}

	public void setFiles(Collection<String> files) {
		this.files = new String[files.size()];
		files.toArray(this.files);
	}

	public String[] files() {
		return files;
	}

	@Override
	public CommandLineKind commandLineKind() {
		return CommandLineKind.NORMAL;
	}

	public void complete() {
		this.computeCoreFile();
	}

	public String getCoreFileName() {
		return this.coreFileName;
	}

	public File getCoreFile() {
		return this.coreFile;
	}

	/**
	 * Extracts from a string the "core" part of a filename by removing any
	 * directory prefixes and removing any file suffix. For example, invoking on
	 * "users/siegel/gcd/gcd1.cvl" will return "gcd1". This is the name used to
	 * name the model and other structures; it is used in the log, to name
	 * generated files, and for error reporting.
	 * 
	 * @param filename
	 *            a filename
	 * @return the core part of that filename
	 */
	private void computeCoreFile() {
		String result = this.files[0];
		char sep = File.separatorChar;
		int lastSep = result.lastIndexOf(sep);
		int lastDot;

		this.coreFile = new File(result);
		if (lastSep >= 0) {
			result = result.substring(lastSep + 1);
		}
		lastDot = result.lastIndexOf('.');
		if (lastDot >= 0)
			result = result.substring(0, lastDot);
		this.coreFileName = result;
	}

}
