package edu.udel.cis.vsl.abc.analysis.entity;

import edu.udel.cis.vsl.abc.ast.conversion.IF.ConversionFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.ContractNode;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

public class AcslContractAnalyzer {
	/**
	 * The entity analyzer controlling this declaration analyzer.
	 */
	private EntityAnalyzer entityAnalyzer;
	private ConversionFactory conversionFactory;

	AcslContractAnalyzer(EntityAnalyzer entityAnalyzer,
			ConversionFactory conversionFactory) {
		this.entityAnalyzer = entityAnalyzer;
		this.conversionFactory = conversionFactory;
	}

	void processContractNodes(SequenceNode<ContractNode> contract,
			Function result) throws SyntaxException {
		AcslContractAnalyzerWorker worker = new AcslContractAnalyzerWorker(
				this.entityAnalyzer, conversionFactory);

		worker.processContractNodes(contract, result);
	}

	void processLoopContractNodes(SequenceNode<ContractNode> loopContracts) {
		AcslContractAnalyzerWorker worker = new AcslContractAnalyzerWorker(
				this.entityAnalyzer, conversionFactory);

		worker.processLoopContractNodes(loopContracts);
	}
}
