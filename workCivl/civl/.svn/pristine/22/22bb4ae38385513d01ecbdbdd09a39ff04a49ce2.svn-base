package edu.udel.cis.vsl.civl.model.common;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.FunctionDefinitionNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.civl.err.CIVLInternalException;
import edu.udel.cis.vsl.civl.model.IF.CIVLFunction;
import edu.udel.cis.vsl.civl.model.IF.Identifier;
import edu.udel.cis.vsl.civl.model.IF.Model;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.model.IF.Scope;
import edu.udel.cis.vsl.civl.model.IF.location.Location;
import edu.udel.cis.vsl.civl.model.IF.statement.CallOrSpawnStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.MallocStatement;
import edu.udel.cis.vsl.civl.model.IF.statement.Statement;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLArrayType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLBundleType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLHeapType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLPointerType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLStructOrUnionType;
import edu.udel.cis.vsl.civl.model.IF.type.CIVLType;
import edu.udel.cis.vsl.civl.model.IF.type.StructOrUnionField;
import edu.udel.cis.vsl.civl.model.IF.variable.Variable;
import edu.udel.cis.vsl.civl.model.common.type.CommonType;
import edu.udel.cis.vsl.civl.run.UserInterface;
import edu.udel.cis.vsl.gmc.CommandLineException;
import edu.udel.cis.vsl.gmc.GMCConfiguration;
import edu.udel.cis.vsl.sarl.IF.SymbolicUniverse;
import edu.udel.cis.vsl.sarl.IF.type.SymbolicType;

/**
 * Does the main work translating a single ABC Program to a model.
 * 
 * @author Stephen F. Siegel (siegel)
 * @author Manchun Zheng (zmanchun)
 * @author Timothy K. Zirkel (zirkel)
 */
public class ModelBuilderWorker {

	/* ************************** Instance Fields ************************** */

	/**
	 * Used to give names to anonymous structs and unions.
	 */
	int anonymousStructCounter = 0;

	/** Used to shortcut checking whether circular types are bundleable. */
	private List<CIVLType> bundleableEncountered = new LinkedList<CIVLType>();

	/**
	 * The types that may be part of a bundle.
	 */
	private LinkedList<CIVLType> bundleableTypeList = new LinkedList<CIVLType>();

	/**
	 * The unique type for a bundle.
	 */
	CIVLBundleType bundleType;

	/**
	 * Map whose key set contains all call/spawn statements in the model. The
	 * value associated to the key is the ABC function definition node. This is
	 * built up as call statements are processed. On a later pass, we iterate
	 * over this map and set the function fields of the call/spawn statements to
	 * the corresponding model Function object. Visibility make it
	 * package-private since CommonModelFactory needs to access it
	 */
	Map<CallOrSpawnStatement, Function> callStatements;

	/**
	 * The unique type for a comm.
	 */
	CIVLType commType;

	/**
	 * The unique type for a gcomm
	 */
	CIVLType gcommType;
	/**
	 * Configuration information for the generic model checker.
	 */
	private GMCConfiguration config;

	private boolean debugging = false;

	private PrintStream debugOut = System.out;

	/**
	 * The factory used to create new Model components.
	 */
	private ModelFactory factory;

	/**
	 * Map from ABC Function entity to corresponding CIVL Function.
	 */
	Map<Function, CIVLFunction> functionMap;

	ArrayList<CIVLType> handledObjectTypes = new ArrayList<>();

	/**
	 * The unique type for a heap.
	 */
	CIVLHeapType heapType;

	/**
	 * Set containing the names of all input variables that were initialized
	 * from a commandline argument. This is used at the end of the building
	 * process to determine if there were any command line arguments that were
	 * not used. This usually indicates an error.
	 */
	Set<String> initializedInputs = new HashSet<String>();

	/**
	 * The map formed from parsing the command line for "-input" options that
	 * specifies an initial constant value for some input variables. May be null
	 * if no "-input"s appeared on the command line.
	 */
	Map<String, Object> inputInitMap;

	/**
	 * List of all malloc statements in the program.
	 */
	ArrayList<MallocStatement> mallocStatements = new ArrayList<MallocStatement>();

	/**
	 * The function definition node of the main function
	 */
	FunctionDefinitionNode mainFunctionNode = null;

	/**
	 * The unique type for a message.
	 */
	CIVLType messageType;

	/**
	 * The model being constructed by this worker
	 */
	private Model model;

	/**
	 * The name of the model (i.e., core name of the cvl file)
	 */
	private String modelName;

	/**
	 * The ABC AST being translated by this model builder worker.
	 */
	protected Program program;

	/**
	 * The unique type for a queue.
	 */
	CIVLType queueType;

	/**
	 * The types that may not be part of a bundle.
	 */
	private LinkedList<CIVLType> unbundleableTypeList = new LinkedList<CIVLType>();

	/**
	 * The symbolic universe
	 */
	private SymbolicUniverse universe;

	/**
	 * This field accumulates the AST definition node of every function
	 * definition in the AST.
	 */
	ArrayList<FunctionDefinitionNode> unprocessedFunctions;

	/**
	 * The outermost scope of the model, root of the static scope tree, known as
	 * the "system scope".
	 */
	Scope systemScope;

	/**
	 * Mapping from ABC types to corresponding CIVL types.
	 */
	Map<Type, CIVLType> typeMap = new HashMap<Type, CIVLType>();

	/* **************************** Constructors *************************** */

	/**
	 * Constructs new instance of ModelBuilderWorker.
	 * 
	 * @param config
	 *            the GMC configuration
	 * @param factory
	 *            the model factory
	 * @param program
	 *            the program
	 * @param name
	 *            name of the model, i.e. the file name without .cvl extension
	 * @param debugOut
	 * @param debugging
	 */
	public ModelBuilderWorker(GMCConfiguration config, ModelFactory factory,
			Program program, String name, boolean debugging,
			PrintStream debugOut) {
		this.config = config;
		this.inputInitMap = config.getMapValue(UserInterface.inputO);
		this.factory = factory;
		this.program = program;
		this.factory.setTokenFactory(program.getTokenFactory());
		this.modelName = name;
		this.heapType = factory.heapType(name);
		this.bundleType = factory.newBundleType();
		this.universe = factory.universe();
		((CommonModelFactory) factory).modelBuilder = this;
		this.debugging = debugging;
		this.debugOut = debugOut;
	}

	/* ************************** Protected Methods ************************ */

	protected void initialization(CIVLFunction system) {
		systemScope = system.outerScope();
		callStatements = new LinkedHashMap<CallOrSpawnStatement, Function>();
		functionMap = new LinkedHashMap<Function, CIVLFunction>();
		unprocessedFunctions = new ArrayList<FunctionDefinitionNode>();
		factory.setSystemScope(systemScope);
	}

	/**
	 * Translate the function definition node of unprocessed functions, which
	 * are obtained by translating function declaration node, function call
	 * node, and so on.
	 */
	protected void translateUndefinedFunctions() {
		while (!unprocessedFunctions.isEmpty()) {
			FunctionDefinitionNode functionDefinition = unprocessedFunctions
					.remove(0);

			translateFunctionDefinitionNode(functionDefinition);
		}
	}

	/* *************************** Private Methods ************************* */

	private void completeHeapType() {
		completeHandleObjectTypes();
		factory.completeHeapType(heapType, mallocStatements);
	}

	private void completeHandleObjectTypes() {
		for (CIVLType handleObjectType : this.handledObjectTypes) {
			int mallocId = mallocStatements.size();

			mallocStatements.add(factory.mallocStatement(null, null, null,
					handleObjectType, null,
					factory.sizeofTypeExpression(null, handleObjectType),
					mallocId, null));
			factory.addHeapFieldType(handleObjectType, mallocId);
		}
	}

	/**
	 * Processes the function body of a function definition node. At least one
	 * function declaration for this function should have been processed
	 * already, so the corresponding CIVL function should already exist.
	 * 
	 * @param functionNode
	 *            The function definition node in the AST to be translated.
	 * @throws CIVLInternalException
	 *             if no corresponding CIVL function could be found.
	 */
	private void translateFunctionDefinitionNode(
			FunctionDefinitionNode functionNode) {
		Entity entity = functionNode.getEntity();
		CIVLFunction result;
		FunctionTranslator functionTranslator;

		result = functionMap.get(entity);
		if (result == null)
			throw new CIVLInternalException("Did not process declaration",
					factory.sourceOf(functionNode));
		functionTranslator = new FunctionTranslator(this, factory,
				functionNode.getBody(), result);
		// no return value because the result will be stored in the variable
		// "result" of CIVLFunction type.
		functionTranslator.translateFunction();
	}

	/* *********************************************************************
	 * Post-translation Methods
	 * *********************************************************************
	 */

	/**
	 * Returns false if a type contains a bundle or void (but void* is ok).
	 * 
	 * @param type
	 *            The CIVL type to be checked
	 * @return True of False
	 */
	private boolean bundleableType(CIVLType type) {
		boolean result = true;

		if (bundleableEncountered.contains(type)) {
			// We are in a recursive evaluation that has already encountered
			// this type. E.g. a struct foo with a field of type struct foo,
			// etc. If this type is not bundleable, that will be determined
			// elsewhere.
			return true;
		} else {
			bundleableEncountered.add(type);
		}
		if (type.isBundleType()) {
			result = false;
		} else if (type.isPointerType()) {
			if (((CIVLPointerType) type).baseType().isVoidType()) {
				// void* is bundleable, so catch this before checking base type
				result = true;
			} else {
				result = bundleableType(((CIVLPointerType) type).baseType());
			}
		} else if (type.isVoidType()) {
			result = false;
		} else if (type.isArrayType()) {
			result = bundleableType(((CIVLArrayType) type).elementType());
		} else if (type.isStructType()) {
			for (StructOrUnionField f : ((CIVLStructOrUnionType) type).fields()) {
				result = result && bundleableType(f.type());
				if (!result)
					break;
			}
		}
		// Heaps and primitive types can be bundled.
		bundleableEncountered.remove(type);
		return result;
	}

	/**
	 * Complete the bundle type.
	 */
	protected void completeBundleType() {
		Map<SymbolicType, Integer> dynamicTypeMap = new LinkedHashMap<SymbolicType, Integer>();
		int dynamicTypeCount = 0;

		for (Entry<Type, CIVLType> entry : typeMap.entrySet()) {
			CIVLType thisType = entry.getValue();

			if (bundleableType(thisType)) {
				bundleableTypeList.add(thisType);
			} else {
				unbundleableTypeList.add(thisType);
			}
		}
		for (CIVLType type : bundleableTypeList) {
			SymbolicType dynamicType = type.getDynamicType(universe);
			Integer id = dynamicTypeMap.get(dynamicType);

			if (id == null) {
				id = dynamicTypeCount;
				dynamicTypeMap.put(dynamicType, id);
				dynamicTypeCount++;
			}
			((CommonType) type).setDynamicTypeIndex(id);
		}
		factory.completeBundleType(bundleType, dynamicTypeMap.keySet());
	}

	/**
	 * Set the function field of each call or spawn statements with the
	 * corresponding function. This has to be a post-translation method because
	 * the function might haven't been translated at the time when the function
	 * call is translated.
	 */
	protected void completeCallOrSpawnStatements() {
		for (Entry<CallOrSpawnStatement, Function> entry : callStatements
				.entrySet()) {
			CallOrSpawnStatement call = entry.getKey();
			CIVLFunction function = functionMap.get(entry.getValue());

			call.setFunction(function);
			if (call.isSystemCall()) {
				call.setGuard(factory.systemGuardExpression(call));
			}
		}
	}

	/**
	 * Complete the model by updating its fields according to the information
	 * obtained by the translation.
	 * 
	 * @param system
	 *            The system function of the model, i.e. _CIVL_SYSTEM function.
	 */
	protected void completeModel(CIVLFunction system) {
		model = factory.model(system.getSource(), system);
		model.setMessageType(messageType);
		model.setQueueType(queueType);
		model.setCommType(commType);
		model.setGcommType(gcommType);
		model.setBundleType(this.bundleType);
		model.setName(modelName);
		// add all functions to model except main:
		for (CIVLFunction f : functionMap.values())
			model.addFunction(f);
		((CommonModel) model).setMallocStatements(mallocStatements);
	}

	/**
	 * Perform static analysis, including: dereferences, purely local
	 * statements, etc.
	 */
	protected void staticAnalysis() {
		Set<Variable> addressedOfVariables = new HashSet<>();

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
	}

	/* *************************** Public Methods ************************** */

	/**
	 * Build the CIVL model from the AST
	 * 
	 * @throws CommandLineException
	 */
	public void buildModel() throws CommandLineException {
		Identifier systemID = factory.identifier(factory.systemSource(),
				"_CIVL_system");
		CIVLFunction system = factory.function(
				factory.sourceOf(program.getAST().getRootNode()), systemID,
				new ArrayList<Variable>(), null, null, null);
		ASTNode rootNode = program.getAST().getRootNode();
		FunctionTranslator systemFunctionTranslator = new FunctionTranslator(
				this, factory, system);

		initialization(system);
		systemFunctionTranslator.translateRootFunction(systemScope, rootNode);
		if (inputInitMap != null) {
			// if commandline specified input variables that do not
			// exist, throw exception...
			Set<String> commandLineVars = new HashSet<String>(
					inputInitMap.keySet());

			commandLineVars.removeAll(initializedInputs);
			if (!commandLineVars.isEmpty()) {
				String msg = "Program contains no input variables named ";
				boolean first = true;

				for (String name : commandLineVars) {
					if (first)
						first = false;
					else
						msg += ", ";
					msg += name;
				}
				throw new CommandLineException(msg);
			}
		}
		// translate main function, using system as the CIVL function object,
		// and combining initialization statements with its body
		// translateFunctionDefinitionNode(mainFunctionNode, system,
		// initialization);
		translateUndefinedFunctions();
		completeCallOrSpawnStatements();
		completeBundleType();
		completeHeapType();
		completeModel(system);
		this.staticAnalysis();
	}

	/**
	 * @return The model factory used by this model builder.
	 */
	public ModelFactory factory() {
		return factory;
	}

	/**
	 * @return the configuration
	 */
	public GMCConfiguration getConfiguration() {
		return config;
	}

	/**
	 * @return the model
	 */
	public Model getModel() {
		return model;
	}

}
