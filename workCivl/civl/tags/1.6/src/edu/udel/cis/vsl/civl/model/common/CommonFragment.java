package edu.udel.cis.vsl.civl.model.common;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import edu.udel.cis.vsl.civl.model.IF.Fragment;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;

/**
 * A fragment of a CIVL model. Consists of a start location and a last
 * statement. Why not always generate next location.
 * 
 * @author Stephen F. Siegel (siegel)
 * @author Manchun Zheng (zmanchun)
 * 
 */
public class CommonFragment implements Fragment {

	/* ************************** Instance Fields ************************** */

	/**
	 * The last statement of the fragment
	 */
	public Set<Statement> finalStatements;//

	/**
	 * The start location of the fragment
	 */
	public Location startLocation;

	/* **************************** Constructors *************************** */

	/**
	 * create an empty fragment
	 */
	public CommonFragment() {
		this.finalStatements = new HashSet<>();
	}

	/**
	 * create a fragment from two given statements.
	 * 
	 * @param first
	 *            The first statement
	 * @param second
	 *            The second statement
	 */
	public CommonFragment(Statement first, Statement second) {
		this.startLocation = first.source();
		first.setTarget(second.source());
		this.finalStatements = new HashSet<>();
		this.finalStatements.add(second);
	}

	/**
	 * 
	 * @param startLocation
	 *            the start location
	 * @param lastStatement
	 *            the last statement
	 */
	public CommonFragment(Location startLocation, Set<Statement> lastStatements) {
		this.startLocation = startLocation;
		this.finalStatements = lastStatements;
	}

	/**
	 * 
	 * @param startLocation
	 *            the start location
	 * @param lastStatement
	 *            the last statement
	 */
	public CommonFragment(Location startLocation, Statement lastStatement) {
		this.startLocation = startLocation;
		this.finalStatements = new HashSet<>();
		this.finalStatements.add(lastStatement);
	}

	/**
	 * 
	 * @param statement
	 *            use <code>statement</code> to create a new fragment, with the
	 *            start location being the source location of
	 *            <code>statement</code> and the last statement being
	 *            <code>statement</code>
	 */
	public CommonFragment(Statement statement) {
		this.startLocation = statement.source();
		this.finalStatements = new HashSet<>();
		this.finalStatements.add(statement);
	}

	/* ************************** Private Methods ************************** */

	/**
	 * Gets the string representation of the set of final statements of this
	 * fragment.
	 * 
	 * @return
	 */
	private StringBuffer lastStatementsToStringBuffer() {
		StringBuffer result = new StringBuffer();

		for (Statement stmt : finalStatements) {
			result.append("\r\n");
			result.append(stmt);
			result.append(" at location ");
			result.append(stmt.source().id());
			result.append(" ");
			result.append(stmt.getSource());
		}
		return result;
	}

	/* *********************** Methods from Fragment *********************** */

	@Override
	public void addGuardToStartLocation(Expression guard, ModelFactory factory) {
		int statementCount = this.startLocation.getNumOutgoing();

		for (int i = 0; i < statementCount; i++) {
			Statement statement = this.startLocation().getOutgoing(i);
			Expression oldGuard = statement.guard();

			if (factory.isTrue(oldGuard)) {
				statement.setGuard(guard);
			} else if (!factory.isTrue(guard)) {
				Expression newGuard = factory.binaryExpression(
						factory.sourceOfSpan(guard.getSource(),
								oldGuard.getSource()), BINARY_OPERATOR.AND,
						guard, oldGuard);

				statement.setGuard(newGuard);
			}
		}
	}

	@Override
	public Fragment combineWith(Fragment next) {
		if (next == null || next.isEmpty())
			return this;
		if (this.isEmpty())
			return next;
		for (Statement stmt : this.finalStatements) {
			stmt.setTarget(next.startLocation());
		}
		return new CommonFragment(this.startLocation, next.finalStatements());
	}

	@Override
	public boolean isEmpty() {
		if (startLocation == null
				&& (finalStatements == null || finalStatements.isEmpty()))
			return true;
		return false;
	}

	@Override
	public Set<Statement> finalStatements() {
		return finalStatements;
	}

	@Override
	public Fragment parallelCombineWith(Fragment parallel) {
		Set<Statement> newLastStatements = new HashSet<>();

		if (parallel == null || parallel.isEmpty())
			return this;
		if (this.isEmpty())
			return parallel;
		assert this.startLocation.id() == parallel.startLocation().id();
		for (Statement s : finalStatements) {
			newLastStatements.add(s);
		}
		for (Statement s : parallel.finalStatements()) {
			newLastStatements.add(s);
		}
		return new CommonFragment(this.startLocation, newLastStatements);
	}

	@Override
	public void print(PrintStream out) {
		out.println(this.toString());
	}

	@Override
	public void setFinalStatements(Set<Statement> statements) {
		this.finalStatements = statements;
	}

	@Override
	public void setStartLocation(Location location) {
		this.startLocation = location;
	}

	@Override
	public Location startLocation() {
		return startLocation;
	}

	@Override
	public void updateStartLocation(Location newLocation) {
		int oldLocationId;
		int number;
		Stack<Location> workings;
		Set<Integer> locationIds;

		if (isEmpty())
			return;
		oldLocationId = this.startLocation.id();
		number = startLocation.getNumOutgoing();
		workings = new Stack<Location>();
		locationIds = new HashSet<Integer>();
		workings.push(startLocation);
		locationIds.add(startLocation.id());

		// For each statement in the fragment, update its source or target
		// location accordingly if it happens to be the previous start location
		while (!workings.isEmpty()) {
			Location location = workings.pop();

			if (location.getNumOutgoing() > 0) {
				List<Statement> outgoings = new ArrayList<>();

				for (Statement stmt : location.outgoing()) {
					outgoings.add(stmt);
				}
				number = location.getNumOutgoing();
				for (int i = 0; i < number; i++) {
					Statement s = outgoings.get(i);

					if (s.source().id() == oldLocationId) {
						s.setSource(newLocation);
					}
					if (s.target() != null) {
						if (s.target().id() == oldLocationId) {
							s.setTarget(newLocation);
						}
						if (!locationIds.contains(s.target().id())) {
							workings.push(s.target());
							locationIds.add(s.target().id());
						}
					}
				}
			}
		}
		this.startLocation = newLocation;
	}

	/* ************************ Methods from Object ************************ */

	@Override
	public String toString() {
		if (isEmpty())
			return "========Empty=========\r\n";
		String result = "=================\r\n";
		Stack<Location> workings = new Stack<Location>();
		Set<Integer> locationIds = new HashSet<Integer>();

		workings.push(this.startLocation);
		locationIds.add(this.startLocation.id());
		while (!workings.isEmpty()) {
			Location location = workings.pop();

			result += "Location " + location.id() + "\r\n";
			if (location.getNumOutgoing() > 0) {
				for (Statement s : location.outgoing()) {
					result += "when(" + s.guard() + ") " + s + " goto ";
					if (s.target() == null) {
						result += "null";
					} else {
						result += "Location " + s.target().id();
						if (!locationIds.contains(s.target().id())) {
							workings.push(s.target());
							locationIds.add(s.target().id());
						}
					}
				}
				result += "\r\n";
			}
		}
		result += "last statement: "
				+ this.lastStatementsToStringBuffer().toString();
		return result;
	}

	@Override
	public void addFinalStatement(Statement statement) {
		this.finalStatements.add(statement);
	}

	@Override
	public void addNewStatement(Statement statement) {
		Set<Statement> newLastStatements = new HashSet<>();

		if (this.finalStatements.isEmpty())
			this.startLocation = statement.source();
		for (Statement stmt : finalStatements) {
			stmt.setTarget(statement.source());
		}
		newLastStatements.add(statement);
		this.finalStatements = newLastStatements;
	}

	@Override
	public Statement uniqueFinalStatement() {
		assert this.finalStatements.size() == 1;
		for (Statement stmt : this.finalStatements)
			return stmt;
		return null;
	}

	@Override
	public void addFinalStatementSet(Set<Statement> stmtSet) {
		this.finalStatements.addAll(stmtSet);
	}

}
