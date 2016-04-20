package edu.udel.cis.vsl.abc.program.common;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.udel.cis.vsl.abc.analysis.IF.Analyzer;
import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.entity.IF.OrdinaryEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Scope;
import edu.udel.cis.vsl.abc.ast.entity.IF.TaggedEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Typedef;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.NodeFactory;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.EnumerationTypeNode;
import edu.udel.cis.vsl.abc.ast.node.IF.type.StructureOrUnionTypeNode;
import edu.udel.cis.vsl.abc.ast.type.IF.EnumerationType;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;
import edu.udel.cis.vsl.abc.front.c.parse.CivlCParser;
import edu.udel.cis.vsl.abc.program.IF.Program;
import edu.udel.cis.vsl.abc.program.IF.ProgramFactory;
import edu.udel.cis.vsl.abc.token.IF.CivlcToken;
import edu.udel.cis.vsl.abc.token.IF.Formation;
import edu.udel.cis.vsl.abc.token.IF.Source;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.TokenFactory;

public class CommonProgramFactory implements ProgramFactory {

	/**
	 * Print debugging information?
	 */
	public final static boolean debug = false;

	/**
	 * Where to send output, mainly for debugging.
	 */
	public final static PrintStream out = System.out;

	// Fields...

	/**
	 * The factory that will be used to produce new {@link AST}s, for example,
	 * when merging or transforming ASTs.
	 */
	private ASTFactory astFactory;

	/**
	 * The analyzer that will be used to analyze an AST before it is wrapped
	 * into a program.
	 */
	private Analyzer standardAnalyzer;

	// Constructors...

	/**
	 * Constructs a new program factory that will use the given AST factory and
	 * analyzer.
	 * 
	 * @param factory
	 *            the factory that will be used to produce new {@link AST}s, for
	 *            example, when merging or transforming ASTs
	 * @param standardAnalyzer
	 *            the analyzer that will be used to analyze an AST before it is
	 *            wrapped into a program
	 */
	public CommonProgramFactory(ASTFactory factory, Analyzer standardAnalyzer) {
		this.astFactory = factory;
		this.standardAnalyzer = standardAnalyzer;
	}

	// Supporting methods...

	/**
	 * <p>
	 * Transforms a translation unit AST in preparation for merging it with the
	 * other translation units. The given plan specifies the transformation
	 * actions.
	 * </p>
	 * 
	 * <p>
	 * <strong>Precondition:</strong> the given AST is analyzed.
	 * </p>
	 * 
	 * <p>
	 * <strong>Postcondition:</strong> the resulting transformed AST is
	 * transformed according to the plan but is not yet analyzed.
	 * </p>
	 * 
	 * <p>
	 * <strong>Implementation notes:</strong> the plan specifies entities which
	 * need to be renamed before the merge can take place, because without the
	 * renaming a name collision would occur. In addition the place specifies
	 * tagged entities for which the "complete" part of their definitions should
	 * be removed. This is because two compatible tagged entities from different
	 * translation units will be merged into one, therefore only one AST will
	 * keep the definition. System typedefs require some special handling, as
	 * described in the comments in the code.
	 * </p>
	 * 
	 * @param translationUnit
	 *            an AST representing a translation unit
	 * @param plan
	 *            a plan specifying actions that must be performed on this AST.
	 */
	private void transform(SequenceNode<BlockItemNode> root, Plan plan) {
		Renamer renamer = new Renamer(plan.getRenameMap());

		for (TaggedEntity entity : plan.getMakeIncompleteActions()) {
			DeclarationNode def = entity.getDefinition();

			if (def instanceof StructureOrUnionTypeNode) {
				((StructureOrUnionTypeNode) def).makeIncomplete();
			} else if (def instanceof EnumerationTypeNode) {
				((EnumerationTypeNode) def).makeIncomplete();
			} else
				throw new ABCRuntimeException("unreachable: " + def);
		}
		for (ProgramEntity entity : plan.getEntityRemoveActions()) {
			boolean isSysTypedef = entity instanceof Typedef
					&& ((Typedef) entity).isSystem();

			// system typedefs require special handling because there
			// is one entity shared by all ASTs. The declarations
			// in that entity span all ASTs. But we only want
			// to remove the decl from one AST. We can tell if
			// the decl belongs to the one AST because its parent
			// will be root...
			for (DeclarationNode decl : entity.getDeclarations()) {
				ASTNode parent = decl.parent();

				if (parent != null && (!isSysTypedef || parent == root)) {
					int declIndex = decl.childIndex();

					parent.removeChild(declIndex);
				}
			}
		}
		renamer.renameFrom(root);
	}

	/**
	 * <p>
	 * Determines which non-anonymous tagged classes can be safely merged. This
	 * information can be used so that any incomplete type which can be merged
	 * with a complete one will be completed to be in accord with the complete
	 * version.
	 * </p>
	 * 
	 * <p>
	 * This method does not modify the ASTs. It only creates a set of
	 * {@link TaggedEntityInfo} objects which record the result of the analysis.
	 * </p>
	 * 
	 * <p>
	 * This method first produces a map, the tagged info map, in which the keys
	 * are all the non-null tags of tagged entities (structs, unions, or enums)
	 * in the file scope of any AST. The value associated to a tag is a
	 * {@link TaggedEntityInfo} object. That object records information about
	 * the use of that tag in each AST.
	 * </p>
	 * 
	 * <p>
	 * Next, this method attempts to discover, for each tag T, which of the
	 * entities with tag T can be merged to form a single entity. This modifies
	 * the info objects.
	 * </p>
	 * 
	 * @param asts
	 *            the ASTs that are being merged
	 * 
	 * @return the tagged info map:
	 */
	private Map<String, TaggedEntityInfo> tagMerge(AST[] asts) {
		int n = asts.length;
		boolean changed = true;
		Map<String, TaggedEntityInfo> taggedInfoMap = new HashMap<>();

		for (int i = 0; i < n; i++) {
			Scope scope = asts[i].getRootNode().getScope();

			for (TaggedEntity entity : scope.getTaggedEntities()) {
				String name = entity.getName();

				if (name != null) {
					TaggedEntityInfo info = taggedInfoMap.get(name);

					if (info == null) {
						info = new TaggedEntityInfo(name, n);
						taggedInfoMap.put(name, info);
					}
					info.add(i, entity);
				}
			}
		}
		while (changed) {
			changed = false;
			for (TaggedEntityInfo info : taggedInfoMap.values())
				changed = changed || info.merge();
		}
		return taggedInfoMap;
	}

	/**
	 * Prepares a sequence of ASTs for merging.
	 * 
	 * Clears any previous analysis results from the ASTs. Performs the standard
	 * analysis upon each of them.
	 * 
	 * 
	 * @param translationUnits
	 *            the ASTs of distinct translation units
	 * @throws SyntaxException
	 */
	private void prepareASTs(AST[] translationUnits) throws SyntaxException {
		int n = translationUnits.length;
		Plan[] plans = new Plan[n];
		Map<String, OrdinaryEntityInfo> ordinaryInfoMap = new HashMap<>();
		Map<EnumerationType, Integer> enumMergeMap = new HashMap<>();
		Map<String, TaggedEntityInfo> taggedInfoMap;

		for (int i = 0; i < n; i++)
			plans[i] = new Plan();
		for (AST ast : translationUnits) {
			standardAnalyzer.clear(ast);
			standardAnalyzer.analyze(ast);
		}
		taggedInfoMap = tagMerge(translationUnits);

		for (TaggedEntityInfo info : taggedInfoMap.values())
			info.computeActions(plans, enumMergeMap);

		for (int i = 0; i < n; i++) {
			AST ast = translationUnits[i];
			Scope scope = ast.getRootNode().getScope();

			for (OrdinaryEntity entity : scope.getOrdinaryEntities()) {
				String name = entity.getName();
				OrdinaryEntityInfo info = ordinaryInfoMap.get(name);

				if (info == null) {
					info = new OrdinaryEntityInfo(name, n);
					ordinaryInfoMap.put(name, info);
				}
				info.add(i, entity);
			}
		}
		for (OrdinaryEntityInfo info : ordinaryInfoMap.values())
			info.computeTypedefRemovals(plans, enumMergeMap);

		// System.out.println("enumMergeMap: " + enumMergeMap);
		// System.out.flush();

		for (OrdinaryEntityInfo info : ordinaryInfoMap.values())
			info.computeRenamings(plans, enumMergeMap);
		for (int i = 0; i < n; i++) {
			AST ast = translationUnits[i];
			SequenceNode<BlockItemNode> root = ast.getRootNode();

			ast.release();
			transform(root, plans[i]);
		}
	}

	/**
	 * First, analyzes the ASTs, then links them.
	 * 
	 * <p>
	 * <strong>Precondition:</strong> each AST represents one translation unit.
	 * It does not matter whether they have any analysis data as they will be
	 * cleared and analyzed first.
	 * </p>
	 * 
	 * <p>
	 * <strong>Postcondition:</strong> the original ASTs are destroyed. The
	 * resulting AST is not clean: it needs to be cleared and analyzed.
	 * </p>
	 * 
	 * 
	 * 
	 * @param translationUnits
	 * @return
	 * @throws SyntaxException
	 */
	private AST link(AST[] translationUnits) throws SyntaxException {
		int n = translationUnits.length;
		ArrayList<SequenceNode<BlockItemNode>> roots = new ArrayList<>(n);
		NodeFactory nodeFactory = astFactory.getNodeFactory();
		TokenFactory tokenFactory = astFactory.getTokenFactory();
		Formation formation = tokenFactory.newSystemFormation("Program");
		CivlcToken fakeToken = tokenFactory.newCivlcToken(CivlCParser.PROGRAM,
				"Program", formation);
		Source fakeSource = tokenFactory.newSource(fakeToken);
		List<BlockItemNode> definitions = new LinkedList<>();
		SequenceNode<BlockItemNode> newRoot;
		Collection<SourceFile> allSourceFiles = new LinkedHashSet<>();
		AST result;

		for (int i = 0; i < n; i++) {
			roots.add(translationUnits[i].getRootNode());
			allSourceFiles.addAll(translationUnits[i].getSourceFiles());
		}
		prepareASTs(translationUnits);
		if (debug) {
			out.println("Transformed translation units: ");
			out.println();
			for (int i = 0; i < n; i++) {
				SequenceNode<BlockItemNode> root = roots.get(i);
				SequenceNode<BlockItemNode> rootClone = root.copy();
				Collection<SourceFile> sourceFiles = translationUnits[i]
						.getSourceFiles();
				AST ast = astFactory.newAST(rootClone, sourceFiles, false);

				out.println(ast + ":");
				ast.prettyPrint(out, false);
				out.println();
				out.flush();
			}
		}
		for (SequenceNode<BlockItemNode> root : roots) {
			int numChildren = root.numChildren();

			for (int i = 0; i < numChildren; i++) {
				BlockItemNode def = root.removeChild(i);

				if (def != null) {
					definitions.add(def);
				}
			}
		}
		newRoot = nodeFactory.newProgramNode(fakeSource, definitions);
		result = astFactory.newAST(newRoot, allSourceFiles, true);
		if (debug) {
			out.println("Linked AST (raw):");
			result.prettyPrint(out, false);
			out.println();
			out.flush();
		}
		return result;
	}

	// Public methods from ProgramFactory...

	@Override
	public ASTFactory getASTFactory() {
		return astFactory;
	}

	@Override
	public Program newProgram(AST ast) throws SyntaxException {
		return new CommonProgram(standardAnalyzer, ast);
	}

	@Override
	public Program newProgram(AST[] asts) throws SyntaxException {
		return newProgram(link(asts));
	}
}
