package edu.udel.cis.vsl.civl.model.common;

import java.io.PrintStream;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import edu.udel.cis.vsl.civl.err.CIVLSyntaxException;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.CIVLSource;
import edu.udel.cis.vsl.civl.model.IF.Fragment;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelCombiner;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.expression.BinaryExpression.BINARY_OPERATOR;
import edu.udel.cis.vsl.civl.model.IF.expression.Expression;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;

/**
 * A model combiner takes two models and creates a single composite model for
 * comparative symbolic execution.
 * 
 * @author zirkel
 */
public class CommonModelCombiner implements ModelCombiner {

	private ModelFactory factory;

	private boolean debugging = false;

	private PrintStream debugOut = System.out;

	public CommonModelCombiner(ModelFactory factory) {
		this.factory = factory;
	}

	@Override
	public Model combine(Model model0, Model model1) {
		CIVLFunction system;
		CIVLSource source = factory.systemSource();
		Model compositeModel;
		CallOrSpawnStatement spawn0, spawn1;
		Fragment wait0, wait1, systemBody;
		Variable model0proc, model1proc;
		Map<String, Variable> model0outputs, model1outputs;

		system = factory.function(source,
				factory.identifier(factory.systemSource(), "_CIVL_system"),
				new ArrayList<Variable>(), null, null, null);
		// TODO: Combine sources from each model for the composite model
		compositeModel = factory.model(source, system);
		model0.system().setName(
				factory.identifier(model0.getSource(), "_CIVL_system_0"));
		model1.system().setName(
				factory.identifier(model0.getSource(), "_CIVL_system_1"));
		// spawn processes to run both models.
		spawn0 = factory.callOrSpawnStatement(source,
				factory.location(source, system.outerScope()), false,
				factory.functionPointerExpression(source, model0.system()),
				new LinkedList<Expression>(),
				factory.booleanLiteralExpression(source, true));
		model0proc = factory.variable(source, factory.processType(), factory
				.identifier(source, "model0proc"), system.outerScope()
				.numVariables());
		system.outerScope().addVariable(model0proc);
		spawn0.setLhs(factory.variableExpression(source, model0proc));
		systemBody = new CommonFragment(spawn0);
		spawn1 = factory.callOrSpawnStatement(source,
				factory.location(source, system.outerScope()), false,
				factory.functionPointerExpression(source, model1.system()),
				new LinkedList<Expression>(),
				factory.booleanLiteralExpression(source, true));
		model1proc = factory.variable(source, factory.processType(), factory
				.identifier(source, "model1proc"), system.outerScope()
				.numVariables());
		system.outerScope().addVariable(model1proc);
		spawn1.setLhs(factory.variableExpression(source, model1proc));
		systemBody = systemBody.combineWith(new CommonFragment(spawn1));
		// wait on the processes from both models
		wait0 = factory.joinFragment(source,
				factory.location(source, system.outerScope()),
				factory.variableExpression(source, model0proc));
		systemBody = systemBody.combineWith(wait0);
		wait1 = factory.joinFragment(source,
				factory.location(source, system.outerScope()),
				factory.variableExpression(source, model1proc));
		systemBody = systemBody.combineWith(wait1);
		model0outputs = modifyVariables(system.outerScope(), model0, true);
		model1outputs = modifyVariables(system.outerScope(), model1, false);
		model0.system().outerScope().setParent(system.outerScope());
		model1.system().outerScope().setParent(system.outerScope());
		model0.system().setContainingScope(system.outerScope());
		model1.system().setContainingScope(system.outerScope());
		systemBody = systemBody.combineWith(outputAssertions(model0outputs,
				model1outputs));
		systemBody = systemBody.combineWith(factory.returnFragment(source,
				factory.location(source, system.outerScope()), null, system));
		completeFunction(system, systemBody);
		for (CIVLFunction f : model0.functions()) {
			compositeModel.addFunction(f);
		}
		for (CIVLFunction f : model1.functions()) {
			compositeModel.addFunction(f);
		}
		system.setModel(compositeModel);
		completeTypes(compositeModel, model0, model1);
		staticAnalysis(compositeModel);
		return compositeModel;
	}

	/**
	 * Updates types of the composite model using those of the base models.
	 * Assumes that both base models share the same message, queue, comm, gcomm,
	 * barrier, basedFilesystem types, etc.
	 * 
	 * @param compositeModel
	 *            The composite model to be updated.
	 * @param model0
	 *            Base model 0.
	 * @param model1
	 *            Base model 1.
	 */
	private void completeTypes(Model compositeModel, Model model0, Model model1) {
		if (model0.mesageType() != null)
			compositeModel.setMessageType(model0.mesageType());
		else
			compositeModel.setMessageType(model1.mesageType());
		if (model0.queueType() != null)
			compositeModel.setQueueType(model0.queueType());
		else
			compositeModel.setQueueType(model1.queueType());
		if (model0.commType() != null)
			compositeModel.setCommType(model0.commType());
		else
			compositeModel.setCommType(model1.commType());
		if (model0.gcommType() != null)
			compositeModel.setGcommType(model0.gcommType());
		else
			compositeModel.setGcommType(model1.gcommType());
		if (model0.barrierType() != null)
			compositeModel.setBarrierType(model0.barrierType());
		else
			compositeModel.setBarrierType(model1.barrierType());
		if (model0.basedFilesystemType() != null)
			compositeModel.setBasedFilesystemType(model0.basedFilesystemType());
		else
			compositeModel.setBasedFilesystemType(model1.basedFilesystemType());
		if (model0.fileType() != null)
			compositeModel.setFileType(model0.fileType());
		else
			compositeModel.setFileType(model1.fileType());
		if (model0.FILEtype() != null)
			compositeModel.setFILEType(model0.FILEtype());
		else
			compositeModel.setFILEType(model1.FILEtype());
		// TODO: how to build bundle types based on two models?
		// if (model0.bundleType() != null)
		// compositeModel.setBundleType(model0.bundleType());
		// else
		// compositeModel.setBundleType(model1.bundleType());
	}

	/**
	 * Move the input variables of the model to the specified scope. Rename the
	 * output variables of the model and move them to the target scope
	 * 
	 * @param scope
	 *            The destination scope for input and (renamed) output
	 *            variables.
	 * @param model
	 *            The model whose system function is being modified.
	 * @param isSpec
	 *            True iff this is the spec model (not the impl).
	 * @return Mapping from original output variable names to the corresponding
	 *         variable.
	 */
	private Map<String, Variable> modifyVariables(Scope scope, Model model,
			boolean isSpec) {
		Set<Variable> reducedVariableSet = new HashSet<Variable>();
		Map<String, Variable> outputs = new LinkedHashMap<String, Variable>();
		String outputSuffix;

		if (isSpec) {
			outputSuffix = "_spec";
		} else {
			outputSuffix = "_impl";
		}
		for (Variable v : model.system().outerScope().variables()) {
			if (v.isInput()) {
				if (!isSpec) {
					// Don't add duplicates of the same input.
					if (scope.containsVariable(v.name().name())) {
						// Make this version of the input variable point to the
						// right scope
						v.setScope(scope);
						v.setVid(scope.variable(v.name().name()).vid());
						continue;
					}
				}
				v.setVid(scope.numVariables());
				v.setScope(scope);
				scope.addVariable(v);
			} else if (v.isOutput()) {
				outputs.put(v.name().name(), v);
				v.setVid(scope.numVariables());
				v.setName(factory.identifier(v.getSource(), v.name().name()
						+ outputSuffix));
				v.setScope(scope);
				scope.addVariable(v);
			} else {
				v.setVid(reducedVariableSet.size());
				reducedVariableSet.add(v);
			}
		}
		model.system().outerScope().setVariables(reducedVariableSet);
		return outputs;
	}

	/**
	 * 
	 * @param map0
	 *            The map from output variable names to the spec output
	 *            variables.
	 * @param map1
	 *            The map from output variable names to the impl output
	 *            variables.
	 * @return A fragment consisting of a series of assertions of equality
	 *         between corresponding spec and impl output variables.
	 */
	private Fragment outputAssertions(Map<String, Variable> map0,
			Map<String, Variable> map1) {
		Fragment result = new CommonFragment();
		CIVLSource source = factory.systemSource();

		for (String s : map0.keySet()) {
			Variable v0 = map0.get(s);
			Variable v1 = map1.get(s);
			Statement assertion;

			if (v1 == null) {
				throw new CIVLSyntaxException(
						"For comparing functional equivalence, every output "
								+ "variable in the specification program should "
								+ "have a corresponding output variable of the "
								+ "same name in the implementation.", v0);
			}
			assertion = factory.assertStatement(source, factory.location(
					source, v0.scope()), factory.binaryExpression(source,
					BINARY_OPERATOR.EQUAL,
					factory.variableExpression(source, v0),
					factory.variableExpression(source, v1)));
			result = result.combineWith(new CommonFragment(assertion));
		}
		return result;
	}

	/**
	 * Add all statements and locations to the function.
	 * 
	 * @param function
	 *            The function to be completed.
	 * @param functionBody
	 *            The body of the function.
	 */
	private void completeFunction(CIVLFunction function, Fragment functionBody) {
		ArrayDeque<Location> workingLocations = new ArrayDeque<Location>();
		Location location;

		// start from the start location of the fragment
		workingLocations.add(functionBody.startLocation());
		function.setStartLocation(functionBody.startLocation());
		while (workingLocations.size() > 0) {
			// use first-in-first-out order to traverse locations so that they
			// are in natural order of the location id's
			location = workingLocations.pollFirst();
			function.addLocation(location);
			if (location.getNumOutgoing() > 0) {
				// for each statement in the outgoing set of a location, add
				// itself to function, and add its target location into the
				// working stack if it hasn't been encountered before.
				for (Statement statement : location.outgoing()) {
					Location newLocation = statement.target();

					function.addStatement(statement);
					if (newLocation != null) {
						if (!function.locations().contains(newLocation)) {
							workingLocations.add(newLocation);
						}
					}
				}
			}
		}
	}

	/**
	 * Perform static analysis, including: dereferences, purely local
	 * statements, etc.
	 */
	private void staticAnalysis(Model model) {
		Set<Variable> addressedOfVariables = new HashSet<>();
		// TODO: Figure out the right heap type

		for (CIVLFunction f : model.functions()) {
			f.simplify();
			// identify all purely local variables
			f.purelyLocalAnalysis();
			f.setModel(model);
			for (Statement s : f.statements()) {
				Set<Variable> statementResult = s.variableAddressedOf();

				if (statementResult != null) {
					addressedOfVariables.addAll(statementResult);
				}
				s.setModel(model);
				s.calculateDerefs();
			}
		}
		if (debugging) {
			debugOut.println("Variable addressed of:");
			for (Variable variable : addressedOfVariables) {
				debugOut.print(variable.name() + "-" + variable.scope().id()
						+ ", ");
			}
			debugOut.println();
		}
		for (CIVLFunction f : model.functions()) {
			// purely local statements can only be
			// identified after ALL variables have been
			// checked for being purely local or not
			for (Location loc : f.locations()) {
				loc.computeWritableVariables(addressedOfVariables);
				for (Statement s : loc.outgoing()) {
					s.purelyLocalAnalysis();
				}
			}
		}
		for (CIVLFunction f : model.functions()) {
			// purely local locations that enters an atomic block needs future
			// statements to be checked, thus it can only be
			// identified after ALL statements have been
			// checked for being purely local or not
			for (Location loc : f.locations()) {
				loc.purelyLocalAnalysis();
				factory.setImpactScopeOfLocation(loc);
			}
		}
		model.complete();
	}
}
