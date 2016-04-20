package edu.udel.cis.vsl.civl.model.common;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.abc.ast.node.IF.label.LabelNode;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.Fragment;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.util.IF.Pair;

/**
 * Maintains the information, e.g. labeled location, goto statements,
 * continue/break statement stack, that is required in the translation of the
 * definition of a function from ABC AST to CIVL model.
 * 
 * @author zheng
 */
public class FunctionInfo {

	/* ************************** Instance Fields ************************** */

	/**
	 * Used to keep track of break statements in nested loops/switches. Each
	 * entry on the stack corresponds to a particular loop or switch. The
	 * statements in the set for that entry are noops which need their target
	 * set to the appropriate location at the end of the loop or switch
	 * processing.
	 */
	private Stack<Set<Statement>> breakStatements;

	/**
	 * Used to keep track of continue statements in nested loops. Each entry on
	 * the stack corresponds to a particular loop. The statements in the set for
	 * that entry are noops which need their target set to the appropriate
	 * location at the end of the loop processing.
	 */
	private Stack<Set<Statement>> continueStatements;

	/**
	 * Used to keep track of bound variables. Each entry on the stack is the
	 * identifier for a bound variable corresponding to a particular quantifier.
	 * 
	 */
	private LinkedList<Pair<Identifier, CIVLType>> boundVariables;

	/**
	 * The current function that is being processed
	 */
	private CIVLFunction function;

	/**
	 * Maps from CIVL "goto" statements to the corresponding label nodes.
	 */
	private Map<Statement, LabelNode> gotoStatements;

	/**
	 * This fields maps ABC label nodes to the corresponding CIVL locations.
	 */
	private Map<LabelNode, Location> labeledLocations;

	/* **************************** Constructors *************************** */

	/**
	 * Create a new instance of FunctionInfo
	 * 
	 * @param function
	 *            the CIVL function object that is being processed
	 */
	public FunctionInfo(CIVLFunction function) {
		this.function = function;
		labeledLocations = new LinkedHashMap<LabelNode, Location>();
		gotoStatements = new LinkedHashMap<Statement, LabelNode>();
		continueStatements = new Stack<Set<Statement>>();
		breakStatements = new Stack<Set<Statement>>();
		boundVariables = new LinkedList<Pair<Identifier, CIVLType>>();
	}

	/* *************************** Public Methods ************************** */

	/**
	 * Add a set of statements to the break statement stack <dt>
	 * <b>Preconditions:</b>
	 * <dd>
	 * A new loop or switch is just encountered
	 * 
	 * @param statementSet
	 *            an empty set of statements
	 */
	public void addBreakSet(Set<Statement> statementSet) {
		this.breakStatements.add(statementSet);
	}

	/**
	 * Add a set of statements to the continue statement stack <dt>
	 * <b>Preconditions:</b>
	 * <dd>
	 * A new loop is just encountered
	 * 
	 * @param statementSet
	 *            an empty set of statement
	 */
	public void addContinueSet(Set<Statement> statementSet) {
		this.continueStatements.add(statementSet);
	}

	/**
	 * Add a bound variable to the stack of bound variables.
	 */
	public void addBoundVariable(Identifier name, CIVLType type) {
		this.boundVariables.add(new Pair<Identifier, CIVLType>(name, type));
	}

	/**
	 * 
	 * @param name
	 *            The name of a bound variable.
	 * @return The CIVL type of the bound variable with the given name.
	 */
	public CIVLType boundVariableType(Identifier name) {
		for (Pair<Identifier, CIVLType> p : boundVariables) {
			if (p.left.equals(name)) {
				return p.right;
			}
		}
		throw new CIVLInternalException("Unknown bound variable",
				name.getSource());
	}

	/**
	 * Complete the function with a fragment translated from its body node,
	 * including:
	 * <ol>
	 * <li>set the target location of each goto statement, which can't be
	 * decided when the goto node is translated;</li>
	 * <li>add all locations and statements reachable from the start location of
	 * the body fragment into the function.</li>
	 * </ol>
	 * 
	 * @param functionBody
	 *            a fragment translated from the body of the function
	 */
	public void completeFunction(Fragment functionBody) {
		Location location;
		boolean first = true;
		Stack<Location> working = new Stack<>();
		Set<Location> visited = new HashSet<>();

		for (Statement s : gotoStatements.keySet()) {
			s.setTarget(labeledLocations.get(gotoStatements.get(s)));
		}
		// start from the start location of the fragment
		location = functionBody.startLocation();
		working.add(location);
		while (!working.isEmpty()) {
			Location current = working.pop();
			int outCount = current.getNumOutgoing();

			if (first) {
				function.setStartLocation(current);
				first = false;
			} else
				function.addLocation(current);
			for (int i = outCount - 1; i >= 0; i--) {
				Statement stmt = current.getOutgoing(i);
				Location newLoc = stmt.target();

				function.addStatement(stmt);
				if (newLoc != null)
					if (!visited.contains(newLoc)) {
						working.push(newLoc);
						visited.add(newLoc);
					}
			}
		}
	}

	/**
	 * 
	 * @param name
	 *            The name of a variable.
	 * @return Whether or not this variable is on the stack of bound variables.
	 */
	public boolean containsBoundVariable(Identifier name) {
		for (Pair<Identifier, CIVLType> p : boundVariables) {
			if (p.left.equals(name)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Get the CIVL function that is being processed
	 * 
	 * @return The current function
	 */
	public CIVLFunction function() {
		return this.function;
	}

	/**
	 * Return the map of goto statements
	 * 
	 * @return mapping from goto statement to label node
	 */
	public Map<Statement, LabelNode> gotoStatements() {
		return this.gotoStatements;
	}

	/**
	 * Return the map of labeled locations
	 * 
	 * @return mapping from labeled node to locations
	 */
	public Map<LabelNode, Location> labeledLocations() {
		return this.labeledLocations;
	}

	/**
	 * Peek the break stack, called only when processing a jump node with break
	 * kind
	 * 
	 * @return the set of break statements on the top of the stack
	 */
	public Set<Statement> peekBreakStack() {
		return this.breakStatements.peek();
	}

	/**
	 * Peek the continue stack, called only when processing a jump node with
	 * continue kind
	 * 
	 * @return the set of continue statements on the top of the stack
	 */
	public Set<Statement> peekContinueStack() {
		return this.continueStatements.peek();
	}

	/**
	 * Pop the set of break statements from the stack
	 * 
	 * @return the set of break statements from the top of the stack
	 */
	public Set<Statement> popBreakStack() {
		return this.breakStatements.pop();
	}

	/**
	 * Pop the set of continue statements from the stack
	 * 
	 * @return the set of continue statements from the top of the stack
	 */
	public Set<Statement> popContinueStack() {
		return this.continueStatements.pop();
	}

	/**
	 * Pop the top identifier from the bound variable stack.
	 * 
	 * @return The identifier from the top of the bound variable stack.
	 */
	public Identifier popBoundVariableStack() {
		return boundVariables.pop().left;
	}

	/**
	 * Add a mapping of a goto statement and a label node to the map of goto
	 * statements
	 * 
	 * @param statement
	 *            The goto statement
	 * @param labelNode
	 *            The label node of the target of the goto statement
	 */
	public void putToGotoStatements(Statement statement, LabelNode labelNode) {
		this.gotoStatements.put(statement, labelNode);
	}

	/**
	 * Add a mapping from a label node to a location
	 * 
	 * @param labelNode
	 *            The label node
	 * @param location
	 *            The location corresponding to the label node
	 */
	public void putToLabeledLocations(LabelNode labelNode, Location location) {
		this.labeledLocations.put(labelNode, location);
	}

}
