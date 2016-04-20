package edu.udel.cis.vsl.civl.model.IF.statement;

import java.util.ArrayList;

/**
 * A list a statements that to be executed as one (atomic )step.
 * 
 * @author Manchun Zheng
 *
 */
public interface StatementList extends Statement {
	ArrayList<Statement> statements();

	void add(Statement statement);
}
