package edu.udel.cis.vsl.abc.main;

import java.io.File;
import java.io.PrintStream;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.config.IF.Configuration.Architecture;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;

/**
 * A {@link TranslationTask} object specifies all of the options and parameters
 * needed to perform a complete translation task.
 * 
 * @author siegel
 */
public class TranslationTask {

	/**
	 * The language (e.g., {@link Language#C} or {@link Language#CIVL_C}).
	 */
	private Language language;

	/**
	 * List of system include paths for the preprocessor.
	 */
	private File[] systemIncludes;

	/**
	 * List of user include paths for the preprocessor.
	 */
	private File[] userIncludes;

	/**
	 * Map of macros: (name, object).
	 */
	private Map<String, String> macros;

	/**
	 * Output stream: where to print human-readable descriptions of translation
	 * artifacts.
	 */
	private PrintStream out;

	/**
	 * If true, stop after preprocessing. Otherwise, go all the way to
	 * generating and transforming a complete program.
	 */
	private boolean preprocOnly;

	/**
	 * Print out information on intermediate steps, not just the final result.
	 */
	private boolean verbose;

	/**
	 * Print out program in original language, as opposed to a hierarchical
	 * representation.
	 */
	private boolean prettyPrint;

	/**
	 * The source files to translate. Each generates one translation unit.
	 */
	private File[] files;

	/**
	 * The codes specifying the transformations to apply to the program after
	 * linking the translation units.
	 */
	private List<String> transformCodes;

	/**
	 * Show symbol and type tables.
	 */
	private boolean showTables;

	/**
	 * Show the timing of each phase.
	 */
	private boolean showTime;

	/**
	 * Shows the difference of two ASTs.
	 */
	private boolean showDiff = false;

	/**
	 * allows GNU C features?
	 */
	private boolean gnuc = false;

	/**
	 * don't print parsing result
	 */
	private boolean silent = false;

	/**
	 * prints functions that are used but without no definitions are given
	 */
	private boolean unkownFunc = false;

	/**
	 * turns on special configuration for svcomp, including GNU-C features.
	 */
	private boolean svcomp = false;

	/**
	 * the architecture to be assumed for this translation task, unknown by
	 * default
	 */
	private Architecture architecture = Architecture.UNKNOWN;

	/**
	 * Constructs a new task with language C, empty system and user include
	 * paths, output stream {@link System#out}, not preproc only, verbose, no
	 * files, no transform codes.
	 */
	public TranslationTask() {
		language = Language.C;
		systemIncludes = ABC.DEFAULT_SYSTEM_INCLUDE_PATHS;
		userIncludes = ABC.DEFAULT_USER_INCLUDE_PATHS;
		out = System.out;
		preprocOnly = false;
		verbose = true;
		prettyPrint = false;
		files = null;
		transformCodes = new LinkedList<>();
		showTables = false;
		macros = new HashMap<String, String>();
	}

	public TranslationTask(Language language, File[] files) {
		this.language = language;
		this.setFiles(files);
		this.out = System.out;
		systemIncludes = new File[0];
		userIncludes = new File[0];
		preprocOnly = false;
		verbose = true;
		prettyPrint = false;
		transformCodes = new LinkedList<>();
		showTables = false;
		macros = new HashMap<String, String>();

	}

	public TranslationTask(Language language, File file) {
		this(language, new File[] { file });
	}

	/**
	 * @return the language
	 */
	public Language getLanguage() {
		return language;
	}

	/**
	 * @param language
	 *            the language to set
	 */
	public void setLanguage(Language language) {
		this.language = language;
	}

	/**
	 * @return the systemIncludes
	 */
	public File[] getSystemIncludes() {
		return systemIncludes;
	}

	/**
	 * @param systemIncludes
	 *            the systemIncludes to set
	 */
	public void setSystemIncludes(File[] systemIncludes) {
		this.systemIncludes = systemIncludes;
	}

	/**
	 * @return the userIncludes
	 */
	public File[] getUserIncludes() {
		return userIncludes;
	}

	/**
	 * @param userIncludes
	 *            the userIncludes to set
	 */
	public void setUserIncludes(File[] userIncludes) {
		this.userIncludes = userIncludes;
	}

	/**
	 * 
	 * @return the macro names that are predefined.
	 */
	public Map<String, String> getMacros() {
		return this.macros;
	}

	/**
	 * updates the predefined macros.
	 * 
	 * @param macros
	 */
	public void setMacroNames(Map<String, String> macros) {
		this.macros = macros;
	}

	/**
	 * @return the out
	 */
	public PrintStream getOut() {
		return out;
	}

	/**
	 * @param out
	 *            the out to set
	 */
	public void setOut(PrintStream out) {
		this.out = out;
	}

	/**
	 * @return the preprocOnly
	 */
	public boolean isPreprocOnly() {
		return preprocOnly;
	}

	/**
	 * @param preprocOnly
	 *            the preprocOnly to set
	 */
	public void setPreprocOnly(boolean preprocOnly) {
		this.preprocOnly = preprocOnly;
	}

	/**
	 * @return the verbose
	 */
	public boolean isVerbose() {
		return verbose;
	}

	/**
	 * @param verbose
	 *            the verbose to set
	 */
	public void setVerbose(boolean verbose) {
		this.verbose = verbose;
	}

	/**
	 * @return the files
	 */
	public File[] getFiles() {
		return files;
	}

	/**
	 * @param files
	 *            the files to set
	 */
	public void setFiles(File[] files) {
		this.files = files;
	}

	public Collection<String> getTransformCodes() {
		return transformCodes;
	}

	public void addTransformCode(String code) {
		transformCodes.add(code);
	}

	public void addAllTransformCodes(Collection<String> codes) {
		transformCodes.addAll(codes);
	}

	public boolean doPrettyPrint() {
		return prettyPrint;
	}

	public void setPrettyPrint(boolean value) {
		this.prettyPrint = value;
	}

	public boolean doShowTables() {
		return showTables;
	}

	public void setShowTables(boolean value) {
		this.showTables = value;
	}

	public boolean doShowTime() {
		return showTime;
	}

	public boolean doShowDiff() {
		return this.showDiff;
	}

	public void setShowTime(boolean showTime) {
		this.showTime = showTime;
	}

	public void setShowDiff(boolean showDiff) {
		this.showDiff = showDiff;
	}

	/**
	 * @return the gnuc
	 */
	public boolean doGnuc() {
		return gnuc;
	}

	/**
	 * @param gnuc
	 *            the gnuc to set
	 */
	public void setGnuc(boolean gnuc) {
		this.gnuc = gnuc;
	}

	/**
	 * @return the silent
	 */
	public boolean doSilent() {
		return silent;
	}

	/**
	 * @param silent
	 *            the silent to set
	 */
	public void setSilent(boolean silent) {
		this.silent = silent;
	}

	/**
	 * @return the unkownFunc
	 */
	public boolean doUnkownFunc() {
		return unkownFunc;
	}

	/**
	 * @param unkownFunc
	 *            the unkownFunc to set
	 */
	public void setUnkownFunc(boolean unkownFunc) {
		this.unkownFunc = unkownFunc;
	}

	/**
	 * @return the svcomp
	 */
	public boolean doSvcomp() {
		return svcomp;
	}

	/**
	 * @param svcomp
	 *            the svcomp to set
	 */
	public void setSvcomp(boolean svcomp) {
		this.svcomp = svcomp;
		if (svcomp)
			this.setGnuc(true);
	}

	public Architecture doArchitecture() {
		return architecture;
	}

	public void setArchitecture(Architecture architecture) {
		this.architecture = architecture;
	}

}
