package edu.udel.cis.vsl.abc.ast.entity.IF;

import java.util.ArrayList;

import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;

/**
 * A simple, generic implementation of {@link Entity}. This class may be
 * extended by specific entities, or it may used as a field (as in the
 * Delegation Pattern) to help implement other entities that cannot extend this
 * class for some reason (for example, because they extend some other class.)
 * 
 * @author siegel
 * 
 */
public class CommonEntity implements ProgramEntity {

	private EntityKind entityKind;

	private String name;

	private ProgramEntity.LinkageKind linkage;

	private ArrayList<DeclarationNode> declarations = new ArrayList<DeclarationNode>();

	private DeclarationNode definition;

	private Type type;

	/**
	 * Is this a system-defined entity (as opposed to a user-defined one)?
	 * Examples include standard types, like size_t.
	 */
	private boolean isSystem = false;

	public CommonEntity(EntityKind kind, String name,
			ProgramEntity.LinkageKind linkage) {
		this.entityKind = kind;
		this.name = name;
		this.linkage = linkage;
	}

	@Override
	public void setIsSystem(boolean value) {
		this.isSystem = value;
	}

	@Override
	public boolean isSystem() {
		return isSystem;
	}

	@Override
	public EntityKind getEntityKind() {
		return entityKind;
	}

	@Override
	public Iterable<DeclarationNode> getDeclarations() {
		return declarations;
	}

	@Override
	public DeclarationNode getFirstDeclaration() {
		return declarations.get(0);
	}

	@Override
	public int getNumDeclarations() {
		return declarations.size();
	}

	@Override
	public DeclarationNode getDeclaration(int index) {
		return declarations.get(index);
	}

	@Override
	public void addDeclaration(DeclarationNode declaration) {
		declarations.add(declaration);
	}

	@Override
	public DeclarationNode getDefinition() {
		return definition;
	}

	@Override
	public void setDefinition(DeclarationNode declaration) {
		this.definition = declaration;
	}

	@Override
	public ProgramEntity.LinkageKind getLinkage() {
		return linkage;
	}

	@Override
	public void setLinkage(ProgramEntity.LinkageKind linkage) {
		this.linkage = linkage;
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public Type getType() {
		return type;
	}

	@Override
	public void setType(Type type) {
		this.type = type;
	}

	@Override
	public String toString() {
		DeclarationNode definition = getDefinition();
		String defString;
		Type type = this.getType();

		if (definition != null)
			defString = ", definition=" + definition.id();
		else if (isSystem)
			defString = ", definition=INTERNAL";
		else
			defString = ", definition=UNKNOWN";
		return "Entity[kind=" + entityKind + ", name=" + this.getName()
				+ ", linkage=" + this.getLinkage() + ", type="
				+ (type == null ? "UNKNOWN" : type.getId()) + defString + "]";
	}

}
