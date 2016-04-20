package edu.udel.cis.vsl.civl.model.common.statement;

import java.util.LinkedHashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;

/**
 * Sometimes it is useful for the model builder to return a set of statements.
 * e.g. when exiting a switch the end of the default case and all break
 * statements need their targets set to the source location of the next statement.
 * 
 * @author zirkel
 * 
 */
public class StatementSet implements Statement {

	private Set<Statement> statements;
	private boolean hasDerefs;
	private boolean purelyLocal;
	

	public StatementSet() {
		statements = new LinkedHashSet<Statement>();
	}

	public StatementSet(Set<Statement> statements) {
		this.statements = statements;
	}
	
	public void add(Statement statement) {
		statements.add(statement);
	}

	@Override
	public CIVLSource getSource() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Location source() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Location target() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Expression guard() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Model model() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setSource(Location source) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setTarget(Location target) {
		for (Statement s : statements) {
			s.setTarget(target);
		}
	}

	@Override
	public void setGuard(Expression guard) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setModel(Model model) {
		// TODO Auto-generated method stub

	}

	@Override
	public Scope statementScope() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setStatementScope(Scope statementScope) {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean hasDerefs() {
		return this.hasDerefs;
	}

	@Override
	public void caculateDerefs() {
		this.hasDerefs = false;
		for(Statement s: statements){
			s.caculateDerefs();
			this.hasDerefs = this.hasDerefs || s.hasDerefs();
			//early return
			if(this.hasDerefs)
				return;
		}
	}

	@Override
	public boolean isPurelyLocal() {
		return this.purelyLocal;
	}
	
	@Override
	public void purelyLocalAnalysisOfVariables(Scope funcScope) {
		for(Statement s: statements){
			s.purelyLocalAnalysisOfVariables(funcScope);
		}
	}

	@Override
	public void purelyLocalAnalysis() {
		this.guard().purelyLocalAnalysis();
		if(!this.guard().isPurelyLocal()){
			this.purelyLocal = false;
			return;
		}
		
		for(Statement s: statements){
			s.purelyLocalAnalysis();
			if(!s.isPurelyLocal()){
				this.purelyLocal = false;
				return;
			}
		}
		this.purelyLocal = true;
	}

}
