package edu.udel.cis.vsl.gmc;

import java.io.PrintStream;
import java.io.Serializable;
import java.util.LinkedHashMap;

/**
 * An instance of this class represents a command-line parameter for a model
 * checker.
 * 
 * The type of the option specifies the type of the values that the parameter
 * can take.
 * 
 * @author Stephen F. Siegel, University of Delaware
 * 
 */
public class Option implements Serializable {

	/**
	 * 
	 */
	private static final long serialVersionUID = -429399824898015020L;

	/**
	 * The types of option. A MAP indicates a map from Strings to Objects, where
	 * each value is either a Boolean, Integer, Double, or String.
	 */
	public enum OptionType {
		BOOLEAN, INTEGER, DOUBLE, STRING, MAP
	};

	/** The name of this option. */
	private String name;

	/** The type of this option. */
	private OptionType type;

	/** A human-readable description of this option. */
	private String description;

	/** The default value for this option */
	private Object defaultValue;

	private int hashCode = -1;
	private boolean hashed = false;

	/**
	 * Constructs new Option with given fields.
	 * 
	 * @param name
	 *            the name of this option. Example: "verbose". The commandline
	 *            would then look like "-verbose=true".
	 * 
	 * @param type
	 *            the type of values that can be assigned to this option.
	 *            Example: BOOLEAN, for the verbose option.
	 * 
	 * @param description
	 *            a human-readable string describing this option that is
	 *            appropriate for printing in usage information or reporting
	 *            commandline errors to the user
	 * 
	 * @param defaultValue
	 *            the value that will be assigned to this option is none is
	 *            specified on the command line
	 * 
	 * */
	Option(String name, OptionType type, String description, Object defaultValue) {
		this.name = name;
		this.type = type;
		this.description = description;
		this.defaultValue = defaultValue;
	}

	public static Option newScalarOption(String name, OptionType type,
			String description, Object defaultValue) {
		return new Option(name, type, description, defaultValue);
	}

	/**
	 * Returns a new option of type MAP with default value the empty map.
	 * 
	 * @param name
	 *            the name to assign to this option
	 * @param description
	 *            a human readable description of this option
	 * @return new option of type MAP with default value the empty map
	 */
	public static Option newMapOption(String name, String description) {
		return new Option(name, OptionType.MAP, description,
				new LinkedHashMap<String, Object>());
	}

	/**
	 * Returns the name of this option.
	 * 
	 * @return the name of this option
	 */
	public String name() {
		return name;
	}

	/**
	 * Returns the type of this option
	 * 
	 * @return the type of this option
	 */
	public OptionType type() {
		return type;
	}

	/**
	 * Returns the human-readable description of this option.
	 * 
	 * @return the human-readable description of this option
	 */
	public String description() {
		return description;
	}

	/**
	 * Returns the default value for this option
	 * 
	 * @return the default value for this option
	 */
	public Object defaultValue() {
		return defaultValue;
	}

	/**
	 * Prints a human-readable description of this option, including its name,
	 * type, and default value. The form is appropriate for including in a
	 * "usage" message.
	 */
	public String toString() {
		String result = "-" + name;

		if (type == OptionType.BOOLEAN) {
			result += " or -" + name + "=BOOLEAN";
		} else if (type == OptionType.MAP) {
			result += "KEY=VALUE";
		} else {
			result += "=" + type;
		}
		if (type != OptionType.MAP && defaultValue != null) {
			result += " (default: " + defaultValue + ")";
		}
		result += "\n    " + description;
		return result;
	}

	public void print(PrintStream out) {
		out.println("  " + toString());
		out.flush();
	}

	@Override
	public boolean equals(Object object) {
		if (object instanceof Option) {
			Option that = (Option) object;

			return this.name.equals(that.name);
			// && this.description.equals(that.description())
			// && this.type.equals(that.type)
			// && (this.defaultValue != null ? this.defaultValue
			// .equals(that.defaultValue) : true);
		}
		return false;
	}

	@Override
	public int hashCode() {
		// boolean debug = false;
		// if (name.equals("showProgram"))
		// debug = true;
		if (!this.hashed) {
			// final int prime = 31;
			// hashCode = 1;
			// hashCode = prime * hashCode
			// + ((name == null) ? 0 : name.hashCode());
			// if (debug)
			// System.out.println("Hashcode of " + name + " is: "
			// + name.hashCode());
			// hashCode = prime * hashCode
			// + ((description == null) ? 0 : description.hashCode());
			// if (debug)
			// System.out.println("Hashcode of " + description + " is: "
			// + description.hashCode());
			// hashCode = prime * hashCode
			// + ((defaultValue == null) ? 0 : defaultValue.hashCode());
			// if (debug && defaultValue != null)
			// System.out.println("Hashcode of " + defaultValue + " is: "
			// + defaultValue.hashCode());
			// hashCode = prime * hashCode
			// + ((type == null) ? 0 : type.hashCode());
			// if (debug)
			// System.out.println("Hashcode of " + type + " is: "
			// + type.hashCode());
			this.hashCode = name.hashCode();
			this.hashed = true;
		}
		//
		// if (!this.hashed) {
		// this.hashCode = name.hashCode() ^ description.hashCode()
		// ^ type.hashCode();
		// if (this.defaultValue != null)
		// this.hashCode = this.hashCode ^ this.defaultValue.hashCode();
		// this.hashed = true;
		// }
		return this.hashCode;
	}
}
