package edu.udel.cis.vsl.gmc;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

public class GuidedTransitionChooser<STATE, TRANSITION, TRANSITIONSEQUENCE>
		implements TransitionChooser<STATE, TRANSITION> {

	static class Guide {
		Guide(int length, int[] choices) {
			this.length = length;
			this.choices = choices;
		}

		int length; /* the number of steps in the trace */

		int[] choices; /* transitions to choose when more than 1 enabled */
	}

	private EnablerIF<STATE, TRANSITION, TRANSITIONSEQUENCE> enabler;

	private Guide guide;

	private int guideIndex = 0;

	public GuidedTransitionChooser(
			EnablerIF<STATE, TRANSITION, TRANSITIONSEQUENCE> enabler,
			Guide guide) {
		this.enabler = enabler;
		this.guide = guide;
	}

	public GuidedTransitionChooser(
			EnablerIF<STATE, TRANSITION, TRANSITIONSEQUENCE> enabler,
			File traceFile) throws IOException, MisguidedExecutionException {
		this.enabler = enabler;
		this.guide = makeGuide(traceFile);
	}

	/**
	 * Returns the length of this execution.
	 * 
	 * @return length of this execution
	 */
	public int getLength() {
		return guide.length;
	}

	/**
	 * Creates a guide by parsing from the given buffered reader. This interface
	 * is provided because the buffered reader may point to the middle of a
	 * file. This is provided because the first part of the file might contain
	 * some application-specific information (such as parameter values), and the
	 * part containing the sequence of integers may start in the middle. This
	 * will parse to the end of the file so expects to see a newline-separated
	 * sequence of integers from the given point on. Closes the reader at the
	 * end.
	 * 
	 * @param reader
	 *            a buffered reader containing a newline-separated sequence of
	 *            integers
	 * @return the sequence of integers
	 * @throws IOException
	 *             if an error occurs in reading from or closing the buffered
	 *             reader
	 * @throws MisguidedExecutionException
	 */
	public static Guide makeGuide(BufferedReader reader) throws IOException,
			MisguidedExecutionException {
		List<Integer> intList = new LinkedList<Integer>();
		int numInts, count;
		int length;
		int[] choices;

		while (true) {
			String line = reader.readLine();

			if (line == null)
				throw new MisguidedExecutionException(
						"Trace begin line not found");
			line = line.trim();
			if ("== Begin Trace ==".equals(line))
				break;
		}
		{
			String line = reader.readLine();
			String words[];

			if (line == null)
				throw new MisguidedExecutionException(
						"Trace LENGTH line not found");
			line = line.trim();
			words = line.split(" ");
			if (words.length != 3 || !words[0].equals("LENGTH")
					|| !words[1].equals("="))
				throw new MisguidedExecutionException(
						"Expected \"LENGTH = length\" in trace file, saw "
								+ line);
			try {
				length = new Integer(words[2]);
			} catch (NumberFormatException e) {
				throw new MisguidedExecutionException(
						"Expected integer in trace file, saw " + words[2]);
			}
		}
		while (true) {
			String line = reader.readLine();

			if (line == null)
				break; // end has been reached
			line = line.trim(); // remove white space
			if ("== End Trace ==".equals(line))
				break;
			if (line.isEmpty())
				continue; // skip blank line
			try {
				int theInt = new Integer(line);

				if (theInt < 0) {
					throw new MisguidedExecutionException(
							"Malformed trace file: transition index is negative: "
									+ theInt);
				}
				intList.add(new Integer(theInt));
			} catch (NumberFormatException e) {
				throw new MisguidedExecutionException("Expected integer, saws "
						+ line);
			}
		}
		reader.close();
		numInts = intList.size();
		choices = new int[numInts];
		count = 0;
		for (Integer value : intList) {
			choices[count] = value;
			count++;
		}
		return new Guide(length, choices);
	}

	/**
	 * Creates a guide by parsing a file which is a newline-separated list of
	 * integers.
	 * 
	 * @param file
	 *            a newline-separated list of integers
	 * @return the integers, as an array
	 * @throws IOException
	 *             if a problem occurs in opening, reading from, or closing the
	 *             file
	 * @throws MisguidedExecutionException
	 */
	public static Guide makeGuide(File file) throws IOException,
			MisguidedExecutionException {
		return makeGuide(new BufferedReader(new FileReader(file)));
	}

	@Override
	public TRANSITION chooseEnabledTransition(STATE state)
			throws MisguidedExecutionException {
		TRANSITIONSEQUENCE sequence = enabler.enabledTransitions(state);

		if (!enabler.hasNext(sequence))
			return null;
		if (!enabler.hasMultiple(sequence))
			return enabler.next(sequence);
		else if (guideIndex < guide.length) {
			int index = guide.choices[guideIndex];

			guideIndex++;
			for (int i = 0; i < index; i++) {
				if (enabler.hasNext(sequence))
					enabler.next(sequence);
				else
					throw new MisguidedExecutionException(
							"State has fewer enabled transitions than expected: "
									+ state);
			}
			if (!enabler.hasNext(sequence))
				throw new MisguidedExecutionException(
						"State has fewer enabled transitions than expected: "
								+ state);
			return enabler.next(sequence);
		} else {
			throw new MisguidedExecutionException(
					"Trace file ends before trail is complete.");
		}
	}
}
