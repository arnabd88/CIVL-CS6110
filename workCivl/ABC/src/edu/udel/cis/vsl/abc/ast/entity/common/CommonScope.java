package edu.udel.cis.vsl.abc.ast.entity.common;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.IF.AST;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity.EntityKind;
import edu.udel.cis.vsl.abc.ast.entity.IF.Function;
import edu.udel.cis.vsl.abc.ast.entity.IF.Label;
import edu.udel.cis.vsl.abc.ast.entity.IF.OrdinaryEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Scope;
import edu.udel.cis.vsl.abc.ast.entity.IF.TaggedEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.token.IF.SyntaxException;
import edu.udel.cis.vsl.abc.token.IF.UnsourcedException;

public class CommonScope implements Scope {

	private ScopeKind scopeKind;

	/**
	 * The root node of this scope in the AST. Used only for printing as a way
	 * to identify the scope easily.
	 */
	private ASTNode root;

	private int id = -1;

	private AST translationUnit;

	private CommonScope parentScope;

	private ArrayList<Scope> children = new ArrayList<Scope>();

	/**
	 * Contains an entry for each ordinary entity declared in this scope that is
	 * NOT anonymous (i.e., has a non-null name).
	 */
	private Map<String, OrdinaryEntity> ordinaryEntityMap = new LinkedHashMap<String, OrdinaryEntity>();

	/**
	 * Contains an entry for each ordinary entity declared in this scope
	 * (including the anonymous ones).
	 */
	private ArrayList<OrdinaryEntity> ordinaryEntityList = new ArrayList<OrdinaryEntity>();

	private ArrayList<Variable> variableList = new ArrayList<Variable>();

	private ArrayList<Function> functionList = new ArrayList<Function>();

	/**
	 * Contains an entry for each tagged entity declared in this scope that is
	 * NOT anonymous (i.e., has a non-null tag).
	 */
	private Map<String, TaggedEntity> taggedEntityMap = new LinkedHashMap<String, TaggedEntity>();;

	/**
	 * Contains an entry for each tagged entity declared in this scope
	 * (including the anonymous ones).
	 */
	private ArrayList<TaggedEntity> taggedEntityList = new ArrayList<TaggedEntity>();

	private Map<String, Label> labelMap = new LinkedHashMap<String, Label>();

	private ArrayList<Label> labelList = new ArrayList<Label>();

	private int scopeDepth;

	public CommonScope(ScopeKind kind, CommonScope parent, ASTNode root) {
		this.scopeKind = kind;
		this.parentScope = parent;
		if (parent != null) {
			parent.addChild(this);
			scopeDepth = parent.scopeDepth + 1;
		} else {
			scopeDepth = 0;
		}
		this.root = root;
	}

	@Override
	public ScopeKind getScopeKind() {
		return scopeKind;
	}

	@Override
	public AST getAST() {
		return translationUnit;
	}

	@Override
	public CommonScope getParentScope() {
		return parentScope;
	}

	@Override
	public int getNumChildrenScopes() {
		return children.size();
	}

	@Override
	public Scope getChildScope(int scopeId) {
		return children.get(scopeId);
	}

	@Override
	public Iterator<Scope> getChildrenScopes() {
		return children.iterator();
	}

	void addChild(Scope child) {
		children.add(child);
	}

	@Override
	public int getScopeDepth() {
		return scopeDepth;
	}

	@Override
	public int add(OrdinaryEntity entity) throws UnsourcedException {
		EntityKind kind = entity.getEntityKind();
		String name = entity.getName(); // may be null
		int result = ordinaryEntityList.size();

		if (name != null) {
			Entity oldEntity = ordinaryEntityMap.get(name);

			if (oldEntity != null)
				throw new UnsourcedException(
						"Entity with same name already exists "
								+ "in this scope: " + oldEntity);
			ordinaryEntityMap.put(name, entity);
		}
		ordinaryEntityList.add(entity);
		switch (kind) {
		case VARIABLE:
			variableList.add((Variable) entity);
			break;
		case FUNCTION:
			functionList.add((Function) entity);
			break;
		default:
		}
		return result;
	}

	@Override
	public OrdinaryEntity getOrdinaryEntity(boolean isType, String name) {
		OrdinaryEntity entity = ordinaryEntityMap.get(name);

		if (entity != null && isType
				&& entity.getEntityKind() != EntityKind.TYPEDEF)
			return null;
		return entity;
	}

	@Override
	public OrdinaryEntity getLexicalOrdinaryEntity(boolean isType, String name) {
		for (Scope scope = this; scope != null; scope = scope.getParentScope()) {
			OrdinaryEntity result = scope.getOrdinaryEntity(isType, name);

			if (result != null)
				return result;
		}
		return null;
	}

	@Override
	public int getNumVariables() {
		return variableList.size();
	}

	@Override
	public Variable getVariable(int variableId) {
		return variableList.get(variableId);
	}

	@Override
	public Iterable<Variable> getVariables() {
		return variableList;
	}

	@Override
	public int getNumFunctions() {
		return functionList.size();
	}

	@Override
	public Function getFunction(int functionId) {
		return functionList.get(functionId);
	}

	@Override
	public Iterable<Function> getFunctions() {
		return functionList;
	}

	@Override
	public int add(TaggedEntity entity) throws SyntaxException {
		String name = entity.getName();
		int result = taggedEntityList.size();

		if (name != null) {
			TaggedEntity oldEntity = taggedEntityMap.get(name);

			if (oldEntity != null)
				throw new SyntaxException("Tagged entity with name " + name
						+ " already exists " + "in this scope: "
						+ oldEntity.getDeclaration(0).getSource(), entity
						.getDeclaration(0).getSource());
			taggedEntityMap.put(name, entity);
		}
		taggedEntityList.add(entity);
		return result;
	}

	@Override
	public TaggedEntity getTaggedEntity(String tag) {
		return taggedEntityMap.get(tag);
	}

	@Override
	public TaggedEntity getLexicalTaggedEntity(String tag) {
		for (Scope scope = this; scope != null; scope = scope.getParentScope()) {
			TaggedEntity result = scope.getTaggedEntity(tag);

			if (result != null)
				return result;
		}
		return null;
	}

	// Labels...

	@Override
	public int add(Label label) throws UnsourcedException {
		String name = label.getName();
		Entity oldEntity = labelMap.get(name);
		int result = labelList.size();

		if (oldEntity != null)
			throw new UnsourcedException("Label with same name already exists "
					+ "in this scope: " + oldEntity);
		labelList.add(label);
		labelMap.put(name, label);
		return result;
	}

	@Override
	public boolean contains(Label label) {
		return getLabel(label.getName()) != null;
	}

	@Override
	public Label getLabel(String name) {
		return labelMap.get(name);
	}

	@Override
	public Label getLexicalLabel(String name) {
		for (Scope scope = this; scope != null; scope = scope.getParentScope()) {
			Label result = scope.getLabel(name);

			if (result != null)
				return result;
		}
		return null;
	}

	@Override
	public Iterator<Label> getLabels() {
		return labelList.iterator();
	}

	@Override
	public int getNumLabels() {
		return labelList.size();
	}

	@Override
	public Label getLabel(int labelId) {
		return labelList.get(labelId);
	}

	@Override
	public int getId() {
		return id;
	}

	@Override
	public void setId(int id) {
		this.id = id;
	}

	public String toStringLong() {
		String result = "Scope[id=" + id + ", " + scopeKind;

		if (parentScope != null)
			result += ", parent=" + parentScope.id;
		result += ", root=" + root.id() + "]";

		return result;
	}

	@Override
	public String toString() {
		return toStringLong();
	}

	@Override
	public void print(String prefix, PrintStream out) {
		out.println(prefix + toString());
		if (!ordinaryEntityList.isEmpty()) {
			out.println(prefix + "| ordinary entities");
			for (OrdinaryEntity entity : ordinaryEntityList) {
				out.println(prefix + "| | " + entity);
			}
		}
		if (!taggedEntityList.isEmpty()) {
			out.println(prefix + "| tagged entities");
			for (TaggedEntity entity : taggedEntityList) {
				out.println(prefix + "| | " + entity);
			}
		}
		if (!labelList.isEmpty()) {
			out.println(prefix + "| labels");
			for (Label label : labelList) {
				out.println(prefix + "| | " + label);
			}
		}
		if (!children.isEmpty()) {
			out.println(prefix + "| children scopes");
			for (Scope child : children) {
				child.print(prefix + "| | ", out);
			}
		}
		out.flush();
	}

	@Override
	public boolean isDescendantOf(Scope that) {
		for (Scope scope = this; scope != null; scope = scope.getParentScope())
			if (scope == that)
				return true;
		return false;
	}

	@Override
	public void print(PrintStream out) {
		print("", out);
	}

	@Override
	public Iterable<OrdinaryEntity> getOrdinaryEntities() {
		return ordinaryEntityList;
	}

	@Override
	public Iterable<TaggedEntity> getTaggedEntities() {
		return taggedEntityList;
	}

}
