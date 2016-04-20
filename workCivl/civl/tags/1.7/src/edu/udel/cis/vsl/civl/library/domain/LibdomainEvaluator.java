package edu.udel.cis.vsl.civl.library.domain;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.civl.config.IF.CIVLConfiguration;
import edu.udel.cis.vsl.civl.dynamic.IF.SymbolicUtility;
import edu.udel.cis.vsl.civl.library.common.BaseLibraryEvaluator;
import edu.udel.cis.vsl.civl.model.IF.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.semantics.IF.Evaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluator;
import edu.udel.cis.vsl.civl.semantics.IF.LibraryEvaluatorLoader;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicAnalyzer;
import edu.udel.cis.vsl.civl.state.IF.State;
import edu.udel.cis.vsl.civl.util.IF.Pair;
import edu.udel.cis.vsl.sarl.IF.Reasoner;
import edu.udel.cis.vsl.sarl.IF.expr.NumericExpression;
import edu.udel.cis.vsl.sarl.IF.expr.SymbolicExpression;
import edu.udel.cis.vsl.sarl.IF.number.IntegerNumber;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicTupleType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicUnionType;

public class LibdomainEvaluator extends BaseLibraryEvaluator implements
		LibraryEvaluator {

	public LibdomainEvaluator(String name, Evaluator evaluator,
			ModelFactory modelFactory, SymbolicUtility symbolicUtil,
			SymbolicAnalyzer symbolicAnalyzer, CIVLConfiguration civlConfig,
			LibraryEvaluatorLoader libEvaluatorLoader) {
		super(name, evaluator, modelFactory, symbolicUtil, symbolicAnalyzer,
				civlConfig, libEvaluatorLoader);
	}

	/**
	 * Evaluates the decomposition struct of all partition strategy for the
	 * $domain_partition(domain, strategy, number) function.
	 * 
	 * @return All possible domain decomposition objects
	 */
	public List<SymbolicExpression> evaluateDomDecompAllPartition(State state,
			int pid, String process, Expression[] arguments,
			SymbolicExpression[] argumentValues, CIVLSource source) {
		List<SymbolicExpression> allDecomp = new LinkedList<>();
		List<List<Pair<Integer, Integer>>> partitions;
		SymbolicExpression domain = argumentValues[0];
		@SuppressWarnings("unused")
		NumericExpression strategy = (NumericExpression) argumentValues[1];
		NumericExpression numParts = (NumericExpression) argumentValues[2];
		NumericExpression dim;
		Reasoner reasoner = universe.reasoner(state.getPathCondition());
		int numElements_int; // domain size
		int numParts_int;
		Number numPartsNumber, numElementsNumber; // Number type objects
													// extracted by reasoner
		SymbolicType domainElementType = symbolicUtil
				.getDomainElementType(domain);
		SymbolicTupleType decompType;
		SymbolicExpression decomp;

		dim = ((NumericExpression) universe.tupleRead(domain, zeroObject));
		// the following cast should be guaranteed, dimension should always a
		// concrete number
		// assert strategy == DECOMP_ALL;
		numPartsNumber = reasoner.extractNumber(numParts);
		numElementsNumber = reasoner.extractNumber(symbolicUtil
				.getDomainSize(domain));
		decompType = universe.tupleType(
				universe.stringObject("$domain_decomposition"),
				Arrays.asList(universe.integerType(),
						universe.arrayType(domain.type(), numParts)));
		if (numPartsNumber == null)
			throw new CIVLInternalException("Non-concrete partition number",
					arguments[2].getSource());
		if (numElementsNumber == null)
			throw new CIVLInternalException("Non-concrete domain size",
					arguments[0].getSource());
		try {
			numElements_int = ((IntegerNumber) numElementsNumber).intValue();
			numParts_int = ((IntegerNumber) numPartsNumber).intValue();
		} catch (ClassCastException e) {
			throw new CIVLInternalException(
					"Number cannot cast to IntegerNumber", source);
		}
		partitions = this.getAllPartitions(numElements_int, numParts_int);
		// For every partition, make a decomposition struct
		// create sub-domains at first
		for (int i = 0; i < partitions.size(); i++) {
			List<Pair<Integer, Integer>> singlePartition;
			// key: thread id
			// value a list of domain elements which at this point are an array
			// of
			// integers(list of integers).
			Map<Integer, List<List<SymbolicExpression>>> decompedDomainsElements = new HashMap<>();

			singlePartition = partitions.get(i);
			try {
				Iterator<List<SymbolicExpression>> domIter = symbolicUtil
						.getDomainIterator(domain);
				SymbolicUnionType unionType = (SymbolicUnionType) universe
						.tupleRead(domain, twoObject).type();
				List<SymbolicExpression> subDomains = new LinkedList<>();

				for (int j = 0; j < singlePartition.size(); j++) {
					// Get a pair of the element index and thread index
					Pair<Integer, Integer> element_thread = singlePartition
							.get(j);
					List<SymbolicExpression> element;
					List<List<SymbolicExpression>> elements;

					assert element_thread.left == j;
					// Here we don't check if it has next, it should be
					// guaranteed and if a call of next() throws an exception,
					// thats a bug, this "try" will catch it.
					element = domIter.next();
					if (!decompedDomainsElements
							.containsKey(element_thread.right)) {
						elements = new LinkedList<>();
					} else {
						elements = decompedDomainsElements
								.get(element_thread.right);
					}
					elements.add(element);
					decompedDomainsElements.put(element_thread.right, elements);
				}
				if (decompedDomainsElements.keySet().size() < numParts_int)
					continue;
				// creating sub-domains and decomp struct
				for (int j = 0; j < decompedDomainsElements.keySet().size(); j++) {
					List<List<SymbolicExpression>> elements;
					SymbolicExpression myDomain;
					SymbolicExpression literalDomainElement, literalDomain, domainUnion;
					List<SymbolicExpression> litDomEleArrayComp = new LinkedList<>();

					elements = decompedDomainsElements.get(j);
					for (int k = 0; k < elements.size(); k++) {
						literalDomainElement = universe.array(
								universe.integerType(), elements.get(k));
						litDomEleArrayComp.add(literalDomainElement);
					}
					literalDomain = universe.array(domainElementType,
							litDomEleArrayComp);
					domainUnion = universe.unionInject(unionType, oneObject,
							literalDomain);
					myDomain = universe.tuple(
							(SymbolicTupleType) domain.type(),
							Arrays.asList(dim, one, domainUnion));
					subDomains.add(myDomain);
				}
				decomp = universe.tuple(
						decompType,
						Arrays.asList(numParts,
								universe.array(domain.type(), subDomains)));
				allDecomp.add(decomp);

			} catch (NullPointerException e) {
				throw new CIVLInternalException(
						"All partition doesn't give each thread at least one task",
						source);
			} catch (CIVLInternalException e) {
				throw new CIVLInternalException(
						"Unexpected problem happened when iterating a domain for all composition strategy",
						source);
			}
		}
		return allDecomp;
	}

	/**
	 * The returned collection should have such structure: par1:{0:n1, 1:n2,
	 * 2:n2.........numEle:nx}; par2{...}; For every element, it should know
	 * which process owns itself.
	 * 
	 * @param numEle
	 * @param numPart
	 * @return
	 */
	private List<List<Pair<Integer, Integer>>> getAllPartitions(int numEle,
			int numPart) {
		List<List<Pair<Integer, Integer>>> result;
		List<Pair<Integer, Integer>> singlePartiton = new LinkedList<>();

		result = this.getAllPartitionsWorker(singlePartiton, numEle, numPart);
		return result;
	}

	private List<List<Pair<Integer, Integer>>> getAllPartitionsWorker(
			List<Pair<Integer, Integer>> singlePartition, int numEle,
			int numParts) {
		List<List<Pair<Integer, Integer>>> result = new LinkedList<>();
		int startElement = singlePartition.size();

		for (int i = startElement; i < numEle; i++) {
			for (int j = 1; j < numParts; j++) {
				List<Pair<Integer, Integer>> singlePartitionBranch = new LinkedList<>(
						singlePartition);

				singlePartitionBranch.add(new Pair<>(i, j));
				result.addAll(this.getAllPartitionsWorker(
						singlePartitionBranch, numEle, numParts));
			}
			singlePartition.add(new Pair<>(i, 0));
		}
		result.add(singlePartition);
		return result;
	}
}
