package edu.udel.cis.vsl.civl.model.common.contract;

import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.contract.CompositeEvent;
import edu.udel.cis.vsl.civl.model.IF.contract.DependsEvent;

public class CommonCompositeEvent extends CommonDependsEvent implements
		CompositeEvent {
	private CompositeEventOperator operator;
	private DependsEvent left;
	private DependsEvent right;

	public CommonCompositeEvent(CIVLSource source, CompositeEventOperator op,
			DependsEvent left, DependsEvent right) {
		super(source, DependsEventKind.COMPOSITE);
		this.left = left;
		this.right = right;
		this.operator = op;
	}

	@Override
	public DependsEvent left() {
		return left;
	}

	@Override
	public DependsEvent right() {
		return right;
	}

	@Override
	public CompositeEventOperator operator() {
		return this.operator;
	}

	@Override
	public boolean equalsWork(DependsEvent that) {
		if (that instanceof CompositeEvent) {
			CompositeEvent thatEvent = (CompositeEvent) that;

			if (this.operator != thatEvent.operator())
				return false;
			switch (operator) {
			case UNION:
			case INTERSECT:
				return this.left.equalsWork(thatEvent.left())
						&& this.right.equalsWork(thatEvent.right())
						|| this.left.equalsWork(thatEvent.right())
						&& this.right.equalsWork(thatEvent.left());
			default:// DIFERENCE
				return this.left.equalsWork(thatEvent.left())
						&& this.right.equalsWork(thatEvent.right());
			}
		}
		return false;
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();

		switch (operator) {
		case UNION:
			result.append("union");
			break;
		case INTERSECT:
			result.append("inter");
			break;
		case DIFFERENCE:
			result.append("diff");
			break;
		default:
		}
		result.append("(");
		result.append(left);
		result.append(",");
		result.append(right);
		result.append(")");
		return result.toString();
	}
}
