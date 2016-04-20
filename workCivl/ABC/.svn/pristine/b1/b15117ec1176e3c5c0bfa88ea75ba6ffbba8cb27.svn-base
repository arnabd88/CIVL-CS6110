package edu.udel.cis.vsl.abc.ast.common;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.IF.ASTException;
import edu.udel.cis.vsl.abc.ast.IF.ASTFactory;
import edu.udel.cis.vsl.abc.ast.IF.DifferenceObject;
import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.entity.IF.OrdinaryEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.SequenceNode;
import edu.udel.cis.vsl.abc.ast.node.IF.statement.BlockItemNode;
import edu.udel.cis.vsl.abc.token.IF.SourceFile;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;

/**
 * Standard implementation of the {@link AST} interface.
 * 
 * @author siegel
 * 
 */
public class CommonAST implements AST {

	private ASTFactory astFactory;

	private SequenceNode<BlockItemNode> root;

	private int nodeCount;

	private ASTNode[] nodes;

	private Map<String, OrdinaryEntity> internalOrExternalEntityMap;

	private ArrayList<OrdinaryEntity> internalEntities;

	private ArrayList<OrdinaryEntity> externalEntities;

	private Collection<SourceFile> sourceFiles;

	private Function mainFunction = null;

	private boolean isWholeprogram = false;

	public CommonAST(ASTFactory astFactory, SequenceNode<BlockItemNode> root,
			boolean hasOmpPragma, Collection<SourceFile> sourceFiles)
			throws SyntaxException {
		this.root = root;
		this.astFactory = astFactory;
		this.sourceFiles = sourceFiles;
		this.isWholeprogram = false;
		clearEntities();
		initialize();
	}

	public CommonAST(ASTFactory astFactory, SequenceNode<BlockItemNode> root,
			boolean hasOmpPragma, Collection<SourceFile> sourceFiles,
			boolean isWholeprogram) throws SyntaxException {
		this.root = root;
		this.astFactory = astFactory;
		this.sourceFiles = sourceFiles;
		this.isWholeprogram = isWholeprogram;
		clearEntities();
		initialize();
	}

	@Override
	public void clearEntities() {
		internalOrExternalEntityMap = new LinkedHashMap<String, OrdinaryEntity>();
		internalEntities = new ArrayList<OrdinaryEntity>();
		externalEntities = new ArrayList<OrdinaryEntity>();
	}

	@Override
	public ASTFactory getASTFactory() {
		return astFactory;
	}

	@Override
	public SequenceNode<BlockItemNode> getRootNode() {
		return root;
	}

	@Override
	public int getNumberOfNodes() {
		return nodeCount;
	}

	@Override
	public ASTNode getNode(int id) {
		return nodes[id];
	}

	@Override
	public void setMain(Function f) {
		mainFunction = f;
	}

	@Override
	public Function getMain() {
		return mainFunction;
	}

	@Override
	public void print(PrintStream out) {
		print("", out, root, true);
	}

	private void print(String prefix, PrintStream out, ASTNode node,
			boolean includeSource) {
		if (node == null) {
			out.println(prefix + "<absent>");
		} else {
			Iterable<ASTNode> children = node.children();
			int childCount = 0;

			node.print(prefix, out, includeSource);
			out.println();
			prefix += "| ";
			// out.println(prefix + node.getScope());
			for (ASTNode child : children) {
				if (child == null)
					out.println(prefix + childCount + " <absent>");
				else
					print(prefix, out, child, includeSource);
				childCount++;
			}
		}
	}

	@Override
	public void release() {
		nullifyOwners(root);
		externalEntities = null;
		internalEntities = null;
		internalOrExternalEntityMap = null;
		nodeCount = 0;
		nodes = null;
		root = null;
		astFactory = null;
	}

	private void nullifyOwners(ASTNode node) {
		if (node == null)
			return;
		else {
			Iterable<ASTNode> children = node.children();

			node.setOwner(null);
			node.setId(-1);
			for (ASTNode child : children)
				nullifyOwners(child);
		}
	}

	// supporting methods...

	private void initialize() throws SyntaxException {
		this.nodeCount = 0;
		setIDsAndOwner(root);
		this.nodes = new ASTNode[nodeCount];
		initializeNodeArray(root);
		// ScopeAnalyzer.setScopes(this);
	}

	private void setIDsAndOwner(ASTNode node) {
		Iterable<ASTNode> children;

		if (node == null)
			return;
		if (node.getOwner() != null) {
			throw new ASTException(
					"Node cannot be added to new AST until old AST is released:\n"
							+ node);
		}
		node.setId(nodeCount);
		node.setOwner(this);
		nodeCount++;
		children = node.children();
		for (ASTNode child : children) {
			setIDsAndOwner(child);
		}
	}

	private void initializeNodeArray(ASTNode node) {
		Iterable<ASTNode> children;

		if (node == null)
			return;
		this.nodes[node.id()] = node;
		children = node.children();
		for (ASTNode child : children) {
			initializeNodeArray(child);
		}
	}

	@Override
	public void add(OrdinaryEntity entity) {
		ProgramEntity.LinkageKind linkage = entity.getLinkage();

		if (linkage == ProgramEntity.LinkageKind.EXTERNAL)
			externalEntities.add(entity);
		else if (linkage == ProgramEntity.LinkageKind.INTERNAL)
			internalEntities.add(entity);
		else
			throw new IllegalArgumentException(
					"Can only add entities with internal or external linkage to translation unit: "
							+ entity);
		internalOrExternalEntityMap.put(entity.getName(), entity);
	}

	@Override
	public OrdinaryEntity getInternalOrExternalEntity(String name) {
		return internalOrExternalEntityMap.get(name);
	}

	@Override
	public Iterator<OrdinaryEntity> getInternalEntities() {
		return internalEntities.iterator();
	}

	@Override
	public Iterator<OrdinaryEntity> getExternalEntities() {
		return externalEntities.iterator();
	}

	@Override
	public void prettyPrint(PrintStream out, boolean ignoreStdLibs) {
		ASTPrettyPrinter.prettyPrint(this, out, ignoreStdLibs);
	}

	@Override
	public boolean equiv(AST that) {
		return diff(that) == null;
	}

	@Override
	public DifferenceObject diff(AST that) {
		return this.getRootNode().diff(that.getRootNode());
	}

	@Override
	public Collection<SourceFile> getSourceFiles() {
		return sourceFiles;
	}

	@Override
	public String toString() {
		String result = "AST[";
		boolean first = true;

		for (SourceFile sourceFile : sourceFiles) {
			if (first)
				first = false;
			else
				result += ",";
			result += sourceFile.getName();
		}
		result += "]";
		return result;
	}

	@Override
	public boolean isWholeProgram() {
		return this.isWholeprogram;
	}
}
