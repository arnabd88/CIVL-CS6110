package edu.udel.cis.vsl.civl.model.common.contract;

import java.util.List;
import java.util.Set;

import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.contract.CallEvent;
import edu.udel.cis.vsl.civl.model.IF.contract.CompositeEvent;
import edu.udel.cis.vsl.civl.model.IF.contract.CompositeEvent.CompositeEventOperator;
import edu.udel.cis.vsl.civl.model.IF.contract.ContractFactory;
import edu.udel.cis.vsl.civl.model.IF.contract.DependsEvent;
import edu.udel.cis.vsl.civl.model.IF.contract.DependsEvent.DependsEventKind;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.FunctionContract;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.MPICollectiveBehavior.MPICommunicationPattern;
import edu.udel.cis.vsl.civl.model.IF.contract.NamedFunctionBehavior;
import edu.udel.cis.vsl.civl.model.IF.contract.ReadOrWriteEvent;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;

public class CommonContractFactory implements ContractFactory {

	@Override
	public FunctionBehavior newFunctionBehavior(CIVLSource source) {
		return new CommonFunctionBehavior(source);
	}

	@Override
	public NamedFunctionBehavior newNamedFunctionBehavior(CIVLSource source,
			String name) {
		return new CommonNamedFunctionBehavior(source, name);
	}

	@Override
	public FunctionContract newFunctionContract(CIVLSource source) {
		return new CommonFunctionContract(source);
	}

	@Override
	public CallEvent newCallEvent(CIVLSource source, CIVLFunction function,
			List<Expression> arguments) {
		return new CommonCallEvent(source, function, arguments);
	}

	@Override
	public CompositeEvent newCompositeEvent(CIVLSource source,
			CompositeEventOperator op, DependsEvent left, DependsEvent right) {
		return new CommonCompositeEvent(source, op, left, right);
	}

	@Override
	public ReadOrWriteEvent newReadEvent(CIVLSource source,
			Set<Expression> memoryUnits) {
		return new CommonReadOrWriteEvent(source, DependsEventKind.READ,
				memoryUnits);
	}

	@Override
	public ReadOrWriteEvent newWriteEvent(CIVLSource source,
			Set<Expression> memoryUnits) {
		return new CommonReadOrWriteEvent(source, DependsEventKind.WRITE,
				memoryUnits);
	}

	@Override
	public DependsEvent newAnyactEvent(CIVLSource source) {
		return new CommonDependsEvent(source, DependsEventKind.ANYACT);
	}

	@Override
	public DependsEvent newNoactEvent(CIVLSource source) {
		return new CommonDependsEvent(source, DependsEventKind.NOACT);
	}

	@Override
	public MPICollectiveBehavior newMPICollectiveBehavior(CIVLSource source,
			Expression communicator, MPICommunicationPattern pattern) {
		return new CommonMPICollectiveBehavior(source, communicator, pattern);
	}

}
