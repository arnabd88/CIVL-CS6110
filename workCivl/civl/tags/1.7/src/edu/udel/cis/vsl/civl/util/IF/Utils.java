package edu.udel.cis.vsl.civl.util.IF;

import java.util.Collection;
import java.util.HashSet;

public class Utils {

	public enum Color {
		BLACK, RED, GREEN, YELLOW, BLUE, PURPLE, CYAN, WHITE
	}

	/**
	 * <pre>
	 * 0 Normal (clear all)
	 * 1 bold
	 * 2 dim
	 * 4 underline
	 * 5 blink
	 * 7 reverse
	 * 8 blank
	 * 9 overstrike
	 * 22 normal intensity (cancel bold and blank)
	 * 24 underline off
	 * 25 blink off
	 * 27 reverse off
	 * 28 blank off
	 * 29 overstrike off
	 * 30 black
	 * 31 red
	 * 32 green
	 * 33 yellow
	 * 34 blue
	 * 35 magenta
	 * 36 cyan
	 * 37 white
	 * 40 black background
	 * 41 red background
	 * 42 green background
	 * </pre>
	 */

	public static final String ANSI_RESET = "\u001B[0m";
	public static final String ANSI_BLACK = "\u001B[30m";
	public static final String ANSI_BOLD = "\u001B[1m";
	public static final String ANSI_RED = "\u001B[31m";
	public static final String ANSI_GREEN = "\u001B[32m";
	public static final String ANSI_YELLOW = "\u001B[33m";
	public static final String ANSI_BLUE = "\u001B[34m";
	public static final String ANSI_PURPLE = "\u001B[35m";
	public static final String ANSI_CYAN = "\u001B[36m";
	public static final String ANSI_WHITE = "\u001B[37m";
	public static final String ANSI_UNDERLINE = "\u001B[4m";
	public static final String ANSI_UNDERLINE_OFF = "\u001B[24m";
	public static final String ANSI_OVERSTRIKE = "\u001B[9m";
	public static final String ANSI_OVERSTRIKE_OFF = "\u001B[29m";

	public static String overstrikeText(String text) {
		return ANSI_OVERSTRIKE + text + ANSI_OVERSTRIKE_OFF;
	}

	public static String boldText(String text) {
		return ANSI_BOLD + text + ANSI_RESET;
	}

	public static String underlineText(String text) {
		return ANSI_UNDERLINE + text + ANSI_UNDERLINE_OFF;
	}

	public static String coloredText(Color color, String text) {
		StringBuilder result = new StringBuilder();

		switch (color) {
		case BLACK:
			result.append(ANSI_BLACK);
			break;
		case RED:
			result.append(ANSI_RED);
			break;
		case GREEN:
			result.append(ANSI_GREEN);
			break;
		case YELLOW:
			result.append(ANSI_YELLOW);
			break;
		case BLUE:
			result.append(ANSI_BLUE);
			break;
		case PURPLE:
			result.append(ANSI_PURPLE);
			break;
		case CYAN:
			result.append(ANSI_CYAN);
			break;
		case WHITE:
			result.append(ANSI_WHITE);
			break;
		default:
		}
		result.append(text);
		result.append(ANSI_RESET);
		return result.toString();
	}

	/**
	 * returns the difference of first and second (first-second)
	 * 
	 * @param first
	 * @param second
	 * @return
	 */
	public static Collection<? extends Object> difference(
			Collection<? extends Object> first,
			Collection<? extends Object> second) {
		Collection<Object> set = new HashSet<>();

		for (Object element : first) {
			if (!second.contains(element))
				set.add(element);
		}
		return set;
	}
}
