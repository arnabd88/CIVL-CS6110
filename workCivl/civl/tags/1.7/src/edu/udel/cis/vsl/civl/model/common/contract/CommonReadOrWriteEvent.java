package edu.udel.cis.vsl.civl.model.common.contract;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.contract.DependsEvent;
import edu.udel.cis.vsl.civl.model.IF.contract.ReadOrWriteEvent;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

public class CommonReadOrWriteEvent extends CommonDependsEvent implements
		ReadOrWriteEvent {

	private Set<Expression> memoryUnits = new HashSet<>();

	public CommonReadOrWriteEvent(CIVLSource source, DependsEventKind kind,
			Set<Expression> memoryUnits) {
		super(source, kind);
		assert kind == DependsEventKind.READ || kind == DependsEventKind.WRITE;
		this.memoryUnits = memoryUnits;
	}

	@Override
	public Set<Expression> memoryUnits() {
		return this.memoryUnits;
	}

	@Override
	public int numMemoryUnits() {
		return this.memoryUnits.size();
	}

	@Override
	public boolean isRead() {
		return this.dependsEventKind() == DependsEventKind.READ;
	}

	@Override
	public boolean isWrite() {
		return dependsEventKind() == DependsEventKind.WRITE;
	}

	@Override
	public boolean equalsWork(DependsEvent that) {
		if (that.dependsEventKind() == this.dependsEventKind()) {
			ReadOrWriteEvent readOrWrite = (ReadOrWriteEvent) that;

			if (this.numMemoryUnits() != readOrWrite.numMemoryUnits())
				return false;
			return memoryUnits.containsAll((Collection<Expression>) readOrWrite
					.memoryUnits());
		}
		return false;
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();
		boolean first = true;

		if (isRead())
			result.append("read");
		else
			result.append("write");
		result.append("(");
		for (Expression mu : this.memoryUnits) {
			if (!first)
				result.append(", ");
			else
				first = false;
			result.append(mu);
		}
		result.append(")");
		return result.toString();
	}
}
