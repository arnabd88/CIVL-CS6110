package edu.udel.cis.vsl.civl.model.common.contract;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.contract.DependsEvent;
import edu.udel.cis.vsl.civl.model.common.CommonSourceable;

public class CommonDependsEvent extends CommonSourceable implements
		DependsEvent {

	private DependsEventKind kind;

	public CommonDependsEvent(CIVLSource source, DependsEventKind kind) {
		super(source);
		this.kind = kind;
	}

	@Override
	public DependsEventKind dependsEventKind() {
		return this.kind;
	}

	/**
	 * Does this event equals to that event?
	 * 
	 * @param that
	 * @return
	 */
	@Override
	public boolean equalsWork(DependsEvent that) {
		if (this.kind == that.dependsEventKind())
			return true;
		return false;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == null)
			return false;
		if (obj instanceof DependsEvent) {
			return this.equalsWork((DependsEvent) obj);
		}
		return false;

	}
}
