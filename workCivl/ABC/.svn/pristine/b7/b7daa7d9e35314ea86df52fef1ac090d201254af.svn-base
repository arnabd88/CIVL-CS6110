package edu.udel.cis.vsl.abc.util.IF;

import java.io.PrintStream;

/**
 * An object used to print how long it takes to do things.
 * 
 * @author siegel
 *
 */
public class Timer {

	/**
	 * The last marked absolute time, in milliseconds. This is initialized to
	 * the current time when this object is instantiated, and is reset to the
	 * current time whenever method {@link #markTime} is called.
	 */
	private long time;

	/**
	 * The stream to which the output should be printed, or null if the output
	 * should not be printed.
	 */
	private PrintStream out;

	/**
	 * Constructs a new "do-nothing" timer. Nothing is printed, nothing is
	 * timed. Here for convenience only, so that users can say "markTime()"
	 * whenever they want.
	 */
	public Timer() {
		out = null;
	}

	/**
	 * Constructs new timer which will print output to the given stream.
	 * 
	 * @param out
	 *            stream to which output should be printed
	 */
	public Timer(PrintStream out) {
		this.out = out;
		time = System.currentTimeMillis();
	}

	/**
	 * Prints a message which includes the amount of time (in seconds, rounded
	 * to thousandths), since the last call to {@link markTime()}, or since
	 * instantiation if this is the first such call.
	 * 
	 * @param message
	 *            this message is inserted into the actual message that is
	 *            printed. This message should be a simple verbal phrase, such
	 *            as "compile program", or "preprocess source code".
	 */
	public void markTime(String message) {
		if (out != null) {
			long newTime = System.currentTimeMillis();
			double elapsedSeconds = (newTime - time) / 1000.0;

			time = newTime;
			out.printf("%10.3fs: time to %s\n", elapsedSeconds, message);
			out.flush();
		}
	}
}
