package edu.udel.cis.vsl.civl.model.common.contract;

import java.util.List;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.contract.CallEvent;
import edu.udel.cis.vsl.civl.model.IF.contract.DependsEvent;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

public class CommonCallEvent extends CommonDependsEvent implements CallEvent {

	private CIVLFunction function;

	private List<Expression> arguments;

	public CommonCallEvent(CIVLSource source, CIVLFunction function,
			List<Expression> arguments) {
		super(source, DependsEventKind.CALL);
		this.function = function;
		this.arguments = arguments;
	}

	@Override
	public CIVLFunction function() {
		return this.function;
	}

	@Override
	public List<Expression> arguments() {
		return this.arguments;
	}

	@Override
	public int numArguments() {
		return this.arguments.size();
	}

	@Override
	public boolean equalsWork(DependsEvent that) {
		if (that instanceof CallEvent) {
			CallEvent thatCall = (CallEvent) that;
			int numArgs = this.numArguments(), thatNumArgs = thatCall
					.numArguments();

			if (numArgs != thatNumArgs)
				return false;
			if (!this.function.equals(((CallEvent) that).function()))
				return false;
			for (int i = 0; i < numArgs; i++) {
				Expression arg = this.arguments.get(i), thatArg = thatCall
						.arguments().get(i);

				if (!arg.equals(thatArg))
					return false;
			}
			return true;

		}
		return false;
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();

		result.append("call(");
		result.append(function.name().name());
		for (Expression argument : arguments) {
			result.append(", ");
			result.append(argument);
		}
		result.append(")");
		return result.toString();
	}

	@Override
	public void setFunction(CIVLFunction function) {
		this.function = function;
	}
}
