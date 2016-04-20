package edu.udel.cis.vsl.abc.util.IF;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;

import org.antlr.runtime.Token;
import org.antlr.runtime.tree.CommonTree;
import org.antlr.runtime.tree.Tree;

public class ANTLRUtils {

	public static void printTree(PrintStream out, Tree tree) {
		if (tree == null) {
			out.println("null");
		} else {
			printNode(out, tree, "");
		}
	}

	/**
	 * Pretty-prints tree using one line per node and nice indentation.
	 * 
	 * @param out
	 *            stream to which output should be sent
	 * @param node
	 *            a non-null instance of CommonTree
	 * @param prefix
	 *            any text you wish to precede output
	 */
	private static void printNode(PrintStream out, Tree node, String prefix) {
		int numChildren;
		Token token = ((CommonTree) node).getToken();
		String nodeString = (token == null ? "null" : token.toString());

		out.print(prefix);
		out.println(nodeString);
		out.flush();
		numChildren = node.getChildCount();
		if (numChildren > 0) {
			String newPrefix = prefix + "| ";

			for (int i = 0; i < numChildren; i++) {
				Tree child = node.getChild(i);

				printNode(out, child, newPrefix);
			}
		}
	}

	/**
	 * Applies method source to the file with the given filename.
	 * 
	 * @param out
	 *            a PrintStream to which the output is sent
	 * @param filename
	 *            name of a file
	 * @throws IOException
	 */
	public static void source(PrintStream out, String filename)
			throws IOException {
		source(out, new File(filename));
	}

	/**
	 * Prints the original text file to the give output stream, unaltered.
	 * 
	 * @param out
	 *            a PrintStream to which the output is sent
	 * @param file
	 *            the file to read
	 * @throws IOException
	 *             if an I/O exception occurs while reading the file
	 */
	public static void source(PrintStream out, File file) throws IOException {
		out.println("Contents of file " + file + ":\n");
		out.println("----------------------------------->");
		FileReader fileReader = new FileReader(file);
		BufferedReader bufferedReader = new BufferedReader(fileReader);
		String line;

		while ((line = bufferedReader.readLine()) != null)
			out.println(line);
		out.println("<-----------------------------------");
		out.flush();
		bufferedReader.close();
		fileReader.close();
	}

}
