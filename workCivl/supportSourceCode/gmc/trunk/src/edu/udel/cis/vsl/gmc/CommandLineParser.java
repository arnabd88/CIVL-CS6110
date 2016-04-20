package edu.udel.cis.vsl.gmc;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;

import edu.udel.cis.vsl.gmc.Option.OptionType;

/**
 * A tool for parsing a command line and generating a {@link GMCConfiguration}.
 * 
 * A parser is instantiated by specifying the set of options that it will be
 * able to parse. It can then be used repeatedly to parse a command line and
 * produce a configuration.
 * 
 * @author Stephen F. Siegel
 * 
 */
public class CommandLineParser {

	// Static fields...

	/**
	 * The Boolean value true.
	 */
	private static Boolean trueBoolean = new Boolean(true);

	/**
	 * The Boolean value false.
	 */
	private static Boolean falseBoolean = new Boolean(false);

	// Instance fields...

	/**
	 * Map of all options associated to this parser: key is name of option,
	 * value is the option.
	 */
	private SortedMap<String, Option> optionMap = new TreeMap<>();

	/**
	 * Map of all options of Map type associated to this parser. The entries of
	 * this map are a subset of those of {@link #optionMap}.
	 */
	private Map<String, Option> mapOptionMap = new LinkedHashMap<>();

	// Constructors...

	/**
	 * Constructs a new parser from the given collection of options.
	 * 
	 * @param options
	 *            a collection of non-null options with distinct names
	 * 
	 */
	public CommandLineParser(Collection<Option> options) {
		for (Option option : options) {
			String name = option.name();

			if (optionMap.put(name, option) != null)
				throw new IllegalArgumentException("Saw two options named "
						+ name);
			if (option.type() == OptionType.MAP)
				mapOptionMap.put(name, option);
		}
	}

	// Helper methods...

	private static String unescape(String string) {
		String result = string;

		result = result.replace("\\" + "n", "\n");
		result = result.replace("\\" + "t", "\t");
		result = result.replace("\\" + " ", " ");
		result = result.replace("\\" + "\"", "\"");
		result = result.replace("\\" + "'", "'");
		result = result.replace("\\" + "\\", "\\");
		return result;
	}

	/**
	 * Interprets the string valueString to determine its type and value as a
	 * command line parameter. The rules are:
	 * 
	 * If value is null or the empty string, the parameter will be interpreted
	 * as having boolean type with value true. This conforms with examples such
	 * as <code>-verbose</code>, which usually means parameter "verbose" is a
	 * boolean flag which should be set to true.
	 * 
	 * If value is surrounded by quotes, it will be interpreted as a String,
	 * with the quotes removed. Example: <code>-rep="~/civl/examples/gcd</code>
	 * on the command line yields a key "rep" with value
	 * <code>~/civl/examples/gcd</code>, i.e., the String in between those
	 * quotes.
	 * 
	 * If value is an integer, it will be interpred as an Integer. Example:
	 * <code>-depth=100</code>
	 * 
	 * If value can be interpreted as a floating point number, it will be
	 * interpreted as a Double. Example: <code>-inputPi=3.14</code>
	 * 
	 * If value is "true" or "false", it will be interpreted as a Boolean with
	 * the corresponding value. Example: <code>-verbose=false</code>
	 * 
	 * Otherwise value will be interpreted as a String. Example:
	 * <code>-dir=/usr/local</code>
	 * 
	 * @param key
	 *            the parameter name
	 * @param valueString
	 *            a string which will be interpreted to yield the parameter
	 *            value
	 * @return the value that results from interpreting the valueString
	 */
	private static Object interpretValue(String valueString) {
		if (valueString == null) {
			return trueBoolean;
		} else {
			int length = valueString.length();

			if (length == 0)
				return trueBoolean;
			if (length >= 2) {
				char firstChar = valueString.charAt(0), lastChar = valueString
						.charAt(length - 1);

				if (firstChar == '"' && lastChar == '"')
					return unescape(valueString.substring(1, length - 1));
				if (firstChar == '\'' && lastChar == '\'')
					return valueString.substring(1, length - 1);
			}
			try {
				return new Integer(valueString);
			} catch (Exception e) {
				// proceed...
			}
			try {
				return new Double(valueString);
			} catch (Exception e) {
				// proceed...
			}
			if ("true".equals(valueString))
				return trueBoolean;
			if ("false".equals(valueString))
				return falseBoolean;
			return valueString;
		}
	}

	private static Object parseValue(Option option, String valueString) {
		OptionType type = option.type();
		String name = option.name();

		switch (type) {
		case BOOLEAN:
			if (valueString == null)
				return trueBoolean;
			if ("true".equals(valueString) || "".equals(valueString))
				return trueBoolean;
			if ("false".equals(valueString))
				return falseBoolean;
			throw new IllegalArgumentException("Option " + name
					+ ": expected boolean, saw " + valueString);
		case DOUBLE:
			try {
				return new Double(valueString);
			} catch (Exception e) {
				throw new IllegalArgumentException("Option " + name
						+ ": expected double, saw " + valueString);
			}
		case INTEGER:
			try {
				return new Integer(valueString);
			} catch (Exception e) {
				throw new IllegalArgumentException("Option " + name
						+ ": expected integer, saw " + valueString);
			}
		case MAP:
			throw new IllegalArgumentException("map should not be used here");
		case STRING: {
			int length = valueString.length();

			if (length >= 2) {
				char firstChar = valueString.charAt(0), lastChar = valueString
						.charAt(length - 1);

				if (firstChar == '"' && lastChar == '"')
					return unescape(valueString.substring(1, length - 1));
				if (firstChar == '\'' && lastChar == '\'')
					return valueString.substring(1, length - 1);
			}
			return valueString;
		}
		default:
			throw new RuntimeException("unreachable");
		}
	}

	/**
	 * Processes an argument for a GMC section. The argument is a regular
	 * expression: <code>'-' text ('=' text)? </code> (e.g., -inputB=9,
	 * -showModel=true) or <code>text</code> (e.g.,
	 * /Users/test/civl/examples/dinging.cvl), where <code>text</code> is a
	 * string that doesn't start with '-' and contains no space. The argument
	 * will be translated into either an option or a free argument of the given
	 * section. If an entry is specified in an argument and an entry for the
	 * same option already exists in the section, the old entry is overwritten.
	 * Similarly for map entries.
	 * 
	 * @param section
	 *            The GMC section that the argument to be processed belongs to.
	 * @param arg
	 *            The argument to be processed.
	 * @throws CommandLineException
	 *             when the option referenced in the given argument is not
	 *             defined in the given section.
	 */
	private void processArg(GMCSection section, String arg)
			throws CommandLineException {
		int length = arg.length();

		if (arg.startsWith("-")) {
			int eqIndex = arg.indexOf('=');
			String optionName, valueString;
			Option option;
			Object value;

			if (eqIndex >= 0) {
				optionName = arg.substring(1, eqIndex);
				valueString = arg.substring(eqIndex + 1, length);
			} else {
				optionName = arg.substring(1);
				valueString = null;
			}
			// is it a map?
			for (String mapName : mapOptionMap.keySet()) {
				if (optionName.startsWith(mapName)) {
					String key = optionName.substring(mapName.length(),
							optionName.length());

					option = mapOptionMap.get(mapName);
					value = interpretValue(valueString);
					section.putMapEntry(option, key, value);
					return;
				}
			}
			option = optionMap.get(optionName);
			if (option == null)
				throw new CommandLineException("Unknown command line option "
						+ optionName);
			value = parseValue(option, valueString);
			section.setScalarValue(option, value);
		} else {
			section.addFreeArg(arg);
		}
	}

	// Public methods...

	/**
	 * Returns new, empty configuration with option set equal to the set of
	 * options associated to this parser.
	 * 
	 * @return new empty configuration compatible with this parser
	 */
	public GMCConfiguration newConfig() {
		return new GMCConfiguration(optionMap.values());
	}

	/**
	 * Given a collection of strings and a configuration compatible with this
	 * parser, parses the strings and uses the resulting information to modify
	 * the configuration. The strings are expected to be in the following
	 * format:
	 * 
	 * <pre>
	 * ('-' text '=' text)* text* (('--' text) ('-' text '=' text)* text*)*
	 * </pre>
	 * 
	 * where <code>text</code> is a string that doesn't start with '-' and
	 * contains no space.
	 * 
	 * @param config
	 *            a configuration with the same option set as this parser
	 * @param args
	 *            a collection of strings, the command line arguments
	 * @throws CommandLineException
	 *             if the args do not conform to what is expected. What is
	 *             expected is determined by the set of options associated to
	 *             this parser.
	 */
	public void parse(GMCConfiguration config, Collection<String> args)
			throws CommandLineException {
		GMCSection section = null;
		boolean isDefault = false;

		for (String arg : args) {
			if (arg.startsWith("--")) {
				if (section != null) {
					if (isDefault) {
						config.setAnonymousSection(section);
						isDefault = false;
					} else
						config.addSection(section);
				}
				section = new GMCSection(config, arg.substring(2));
				continue;
			}
			if (section == null) {
				section = new GMCSection(config,
						GMCConfiguration.ANONYMOUS_SECTION);
				isDefault = true;
			}
			processArg(section, arg);
		}
		if (section != null)
			if (isDefault)
				config.setAnonymousSection(section);
			else
				config.addSection(section);
	}

	/**
	 * Given a collection of strings, parses them in the order of their iterator
	 * to produce a new configuration.
	 * 
	 * @param args
	 *            a collection of strings, the command line arguments
	 * @return a new configuration obtained from the information in the args
	 * @throws CommandLineException
	 *             if the args do not conform to what is expected. What is
	 *             expected is determined by the set of options associated to
	 *             this parser.
	 */
	public GMCConfiguration parse(Collection<String> args)
			throws CommandLineException {
		GMCConfiguration config = new GMCConfiguration(optionMap.values());

		parse(config, args);
		return config;
	}

	/**
	 * Parses the reader, interpreting lines as command line args, modifying
	 * given configuration accordingly.
	 * 
	 * Ignores all lines until it reaches a line of the form
	 * "== Begin Configuration ==". Then parses each line as if it were a
	 * command line argument. Continues until end of stream or a line of the
	 * form "== End Configuration ==" is reached.
	 * 
	 * @param config
	 *            a configuration compatible with this parser
	 * @param reader
	 *            a buffered reader which provides a sequence of lines as
	 *            described above
	 * @throws IOException
	 *             if an I/O error occurs in reading the reader
	 * @throws CommandLineException
	 *             if format does not conform to pattern described above
	 */
	public void parse(GMCConfiguration config, BufferedReader reader)
			throws IOException, CommandLineException {
		ArrayList<String> args = new ArrayList<>();

		while (true) {
			String line = reader.readLine();

			if (line == null)
				throw new CommandLineException(
						"Did not find line with ==Begin Configuration== marker in trace file");
			line = line.trim();
			if ("== Begin Configuration ==".equals(line))
				break;
		}
		while (true) {
			String line = reader.readLine();

			if (line == null)
				break;
			line = line.trim();
			if ("== End Configuration ==".equals(line))
				break;
			args.add(line);
		}
		parse(config, args);
	}

	/**
	 * Parses a file containing a configuration section, using the command line
	 * arguments from that section to modify the given configuration.
	 * 
	 * @param config
	 *            a configuration to be modified; it must have the same set of
	 *            options as those associated to this parser
	 * @param file
	 *            the file to open and parse; it must contain a configuration
	 *            section
	 * @throws FileNotFoundException
	 *             if the file does not exist
	 * @throws IOException
	 *             if an I/O error occurs in opening, reading, or closing the
	 *             file
	 * @throws CommandLineException
	 *             if the command lines do not conform to the options of this
	 *             parser
	 */
	public void parse(GMCConfiguration config, File file)
			throws FileNotFoundException, IOException, CommandLineException {
		BufferedReader reader = new BufferedReader(new FileReader(file));

		parse(config, reader);
		reader.close();
	}

	/**
	 * Prints the list of options in a human-readable format. Appropriate for
	 * including in a "usage" message for the user.
	 * 
	 * @param out
	 *            print stream to which to print this information
	 */
	public void printUsage(PrintStream out) {
		for (Option option : optionMap.values()) {
			option.print(out);
		}
		out.flush();
	}

}
