package edu.udel.cis.vsl.abc.main;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import edu.udel.cis.vsl.abc.config.IF.Configuration.Architecture;
import edu.udel.cis.vsl.abc.config.IF.Configurations.Language;
import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.front.IF.ParseException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorException;
import edu.udel.cis.vsl.abc.front.IF.PreprocessorRuntimeException;
import edu.udel.cis.vsl.abc.token.IF.Macro;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.transform.IF.Transform;

/**
 * <p>
 * This is the main class for ABC. It provides a simple command line interface
 * for using ABC. Most applications will not use this class, since they will use
 * ABC more as a library and access the functionality through the API. However,
 * the command line is useful for debugging, "seeing what is going on", and
 * general exploration.
 * </p>
 * 
 * <p>
 * By default, this command line interface will open and scan a file, preprocess
 * it, parse it to produce an ANTLR tree, translate that tree into an ABC
 * Abstract Syntax Tree (AST), and analyze the AST to determine scopes, types,
 * and entities associated to every identifier. It prints out the final result
 * in a plain text human-readable form. Various options can control how much
 * information is printed, and can also cause various transformations to be
 * applied to the AST. Executing with no command line arguments will print a
 * help message describing the options.
 * </p>
 * 
 * <p>
 * Include paths are searched as follows: for a file included with angle
 * brackets, first the paths occurring in the array <code>systemIncludes</code>
 * are searched, in order; if the file is not found there, then the built-in
 * system include paths inside of ABC are searched. For a file included with
 * double quotes, first the paths occurring in the array
 * <code>userIncludes</code> are searched (in order) and if the file is not
 * found there, the protocol for angle brackets is followed.
 * </p>
 * 
 * 
 * @author siegel
 * 
 */
public class ABC {

	/**
	 * The version number of this release of ABC: {@value} .
	 */
	public final static String version = "0.2";

	/**
	 * The date of this release of ABC: {@value} .
	 */
	public final static String date = "31-mar-2014";

	/**
	 * The default list of system include paths.
	 */
	public final static File[] DEFAULT_SYSTEM_INCLUDE_PATHS = new File[] {};

	/**
	 * The default list of user include paths.
	 */
	public final static File[] DEFAULT_USER_INCLUDE_PATHS = new File[] {};

	/**
	 * The default list of pre-defined macros, specifies as a mapping from
	 * Strings (macro name) to macros.
	 */
	public final static Map<String, Macro> DEFAULT_IMPLICIT_MACROS = new TreeMap<>();

	/**
	 * Determines language from filename. If it ends in ".cvl" or ".cvh", it's
	 * CIVL_C, else it's C.
	 * 
	 * @param name
	 *            filename
	 * @return CIVL_C or C
	 */
	private static Language getLanguageFromName(String name) {
		int dotIndex = name.lastIndexOf('.');

		if (dotIndex >= 0) {
			String suffix = name.substring(dotIndex + 1, name.length());

			if ("cvl".equals(suffix) || "cvh".equals(suffix))
				return Language.CIVL_C;
			else if ("f".equals(suffix) || "F".equals(suffix))
				return Language.FORTRAN77;
		}
		return Language.C;
	}

	/**
	 * Prints a message to the output stream specifying the command line syntax.
	 * 
	 * @param out
	 *            the stream to which the output should be printed
	 */
	private static void help(PrintStream out) {
		out.println("Usage: abc [options] filename0 filename1 ...");
		out.println("Options:");
		out.println("-I <path>");
		out.println("  add path to system include list");
		out.println("-iquote <path>");
		out.println("  add path to user include list");
		out.println("-D<macro> or -D<macro>=<object>");
		out.println("  define a macro for compilation");
		out.println("-o <filename>");
		out.println("  send output to filename");
		out.println("-E");
		out.println("  preprocess only");
		out.println("-v");
		out.println("  verbose mode, show all processing steps");
		out.println("-p");
		out.println("  pretty print programs in original language (default)");
		out.println("-a");
		out.println("  print the AST(s) using a hierarchical representation");
		out.println("-t");
		out.println("  show symbol and type tables");
		out.println("-time");
		out.println("  show time for each phase");
		out.println("-diff");
		out.println("  show the difference of two ASTs");
		out.println("-svcomp");
		out.println("  turn on special setting for svcomp benchmarks");
		out.println("-gnuc");
		out.println("  support GNU C features");
		out.print("-unknownFunc");
		out.println("  print functions that are used in the program but no definition is given");
		out.println("-lang=[c|civlc]");
		out.println("  set language (default determined by file suffix)");
		out.println("-arch=[i386|amd64|unknown]");
		out.println("  set the architecture, unknown by default");
		for (String code : Transform.getCodes()) {
			String description = Transform.getShortDescription(code);

			out.println("-" + code);
			out.println("  " + description);
		}
		out.println();
		out.flush();
	}

	private static void err(String msg) {
		System.out.println("Error: " + msg);
		System.out.println();
		help(System.out);
		System.out.flush();
		System.exit(1);
	}

	private static TranslationTask parseCommandLine(String[] args)
			throws FileNotFoundException {
		ArrayList<String> infileNames = new ArrayList<>();
		String outfileName = null;
		// the following are updated by -I
		ArrayList<File> systemIncludeList = new ArrayList<>();
		// the following are updated by -iquote
		ArrayList<File> userIncludeList = new ArrayList<>();
		// the following are updated by -D
		Map<String, String> macros = new HashMap<String, String>();
		boolean preprocOnly = false;
		boolean verbose = false;
		boolean pretty = true;
		boolean tables = false; // show symbol and type tables
		boolean showTime = false;
		boolean showDiff = false;
		boolean gnuc = false;
		boolean silent = false;
		boolean unkownFunc = false;
		boolean svcomp = false;
		Architecture architecture = Architecture.UNKNOWN;
		List<String> transformCodes = new LinkedList<>();
		Language language = null;
		TranslationTask result = new TranslationTask();
		int nfiles;

		for (int i = 0; i < args.length; i++) {
			String arg = args[i];

			if (arg.startsWith("-o")) {
				String name;

				if (arg.length() == 2) {
					i++;
					if (i >= args.length)
						err("Filename must follow -o");
					name = args[i];
				} else {
					name = arg.substring(2);
				}
				if (outfileName == null)
					outfileName = name;
				else
					err("More than one use of -o");
			} else if (arg.startsWith("-D")) {
				String name;
				String object = "";

				if (arg.contains("=")) {
					// -D<macro>=<object>
					int indexOfEqual = arg.indexOf('=');

					name = arg.substring(2, indexOfEqual);
					object = arg.substring(indexOfEqual + 1);
				} else {
					// -D<macro>
					name = arg.substring(2);
				}
				if (macros.containsKey(name))
					err("Duplicated macro definition of " + name);
				else
					macros.put(name, object);
			} else if (arg.startsWith("-I")) {
				String name;

				if (arg.length() == 2) {
					i++;
					if (i >= args.length)
						err("Filename must follow -I");
					name = args[i];
				} else {
					name = arg.substring(2);
				}
				systemIncludeList.add(new File(name));
			} else if (arg.startsWith("-iquote")) {
				String name;

				if (arg.length() == "-iquote".length()) {
					i++;
					if (i >= args.length)
						err("Filename must follow -iquote");
					name = args[i];
				} else {
					name = arg.substring("-iquote".length());
				}
				userIncludeList.add(new File(name));
			} else if (arg.equals("-E")) {
				preprocOnly = true;
			} else if (arg.equals("-v")) {
				verbose = true;
			} else if (arg.equals("-p")) {
				pretty = true;
			} else if (arg.equals("-a")) {
				pretty = false;
			} else if (arg.equals("-t")) {
				tables = true;
			} else if (arg.equals("-time")) {
				showTime = true;
			} else if (arg.equals("-diff")) {
				showDiff = true;
			} else if (arg.equals("-gnuc")) {
				gnuc = true;
			} else if (arg.equals("-unknownFunc")) {
				unkownFunc = true;
			} else if (arg.equals("-svcomp")) {
				svcomp = true;
			} else if (arg.startsWith("-lang")) {
				if (arg.equals("-lang=C"))
					language = Language.C;
				else if (arg.equals("-lang=civlc"))
					language = Language.CIVL_C;
				else if (arg.equals("-lang=fortran77"))
					language = Language.FORTRAN77;
				else
					err("Unknown command line option: " + arg);
			} else if (arg.startsWith("-arch")) {
				if (arg.equals("-arch=i386"))
					architecture = Architecture._32_BIT;
				else if (arg.equals("-arch=amd64"))
					architecture = Architecture._64_BIT;
				else if (arg.equals("-arch=unknown"))
					architecture = Architecture.UNKNOWN;
				else
					err("Unknown command line option: " + arg);
			} else if (arg.equals("-silent")) {
				silent = true;
			} else if (arg.startsWith("-")) {
				// try transform code...
				String code = arg.substring(1);

				if (Transform.getCodes().contains(code))
					transformCodes.add(code);
				else
					err("Unknown command line option: " + arg);
			} else {
				infileNames.add(arg);
			}
		}
		nfiles = infileNames.size();
		if (nfiles == 0)
			err("No input file specified");
		result.setFiles(new File[nfiles]);
		for (int i = 0; i < nfiles; i++)
			result.getFiles()[i] = new File(infileNames.get(i));
		result.setUserIncludes(userIncludeList.toArray(new File[0]));
		result.setSystemIncludes(systemIncludeList.toArray(new File[0]));
		result.setMacroNames(macros);
		if (outfileName == null)
			result.setOut(System.out);
		else
			result.setOut(new PrintStream(new File(outfileName)));
		result.setLanguage(language == null ? getLanguageFromName(infileNames
				.get(0)) : language);
		result.setVerbose(verbose);
		result.setPrettyPrint(pretty);
		result.setShowTables(tables);
		result.setShowTime(showTime);
		result.setPreprocOnly(preprocOnly);
		result.setShowDiff(showDiff);
		result.setGnuc(gnuc);
		result.setSilent(silent);
		result.setUnkownFunc(unkownFunc);
		result.setSvcomp(svcomp);
		result.setArchitecture(architecture);
		result.addAllTransformCodes(transformCodes);
		return result;
	}

	/**
	 * Executes the commands specified by the command line.
	 * 
	 * @param args
	 *            the command line arguments
	 * @throws ABCException
	 *             if something goes wrong when processing the file, such as a
	 *             syntax exception
	 * @throws IOException
	 *             if the file cannot be opened
	 */
	public static void main(String[] args) {
		TranslationTask task = null;
		FrontEnd frontEnd;
		PrintStream err = System.err, out = System.out;
		boolean silent = false;

		for (String arg : args) {
			if (arg.equals("-silent"))
				silent = true;
		}
		if (!silent)
			out.println("ABC v" + version + " of " + date
					+ " -- http://vsl.cis.udel.edu/abc\n");
		out.flush();
		try {
			task = parseCommandLine(args);
		} catch (FileNotFoundException e) {
			err.println(e.toString());
			err.flush();
			System.exit(1);
		}
		frontEnd = new FrontEnd(task);
		try {

			if (task.doShowDiff()) {
				frontEnd.compileAndCompare(task);
			} else {
				frontEnd.showTranslation(task);
			}
		} catch (PreprocessorException e) {
			err.println(e.toString());
			err.flush();
			System.exit(2);
		} catch (PreprocessorRuntimeException e) {
			err.println(e.toString());
			err.flush();
			System.exit(2);
		} catch (ParseException e) {
			err.println(e.toString());
			err.flush();
			System.exit(3);
		} catch (SyntaxException e) {
			err.println(e.toString());
			err.flush();
			System.exit(4);
		} catch (IOException e) {
			err.println(e.toString());
			err.flush();
			System.exit(5);
		}
		task.getOut().close();
	}

}
