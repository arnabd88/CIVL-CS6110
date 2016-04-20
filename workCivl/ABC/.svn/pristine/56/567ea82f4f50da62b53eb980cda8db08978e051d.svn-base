package edu.udel.cis.vsl.abc.ast.entity.common;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Variable;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.InitializerNode;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.VariableDeclarationNode;
import edu.udel.cis.vsl.abc.ast.type.IF.ObjectType;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;

public class CommonVariable extends CommonOrdinaryEntity implements Variable {

	private StorageDurationKind storageDurationKind;

	private InitializerNode initializer;

	private Set<Type> typeAlignments = new HashSet<Type>();

	private Set<Value> constantAlignments = new HashSet<Value>();

	public CommonVariable(String name, ProgramEntity.LinkageKind linkage,
			Type type) {
		super(EntityKind.VARIABLE, name, linkage, type);
	}

	@Override
	public StorageDurationKind getStorageDuration() {
		return storageDurationKind;
	}

	@Override
	public void setStorageDuration(StorageDurationKind duration) {
		this.storageDurationKind = duration;
	}

	@Override
	public InitializerNode getInitializer() {
		return initializer;
	}

	@Override
	public void setInitializer(InitializerNode initializer) {
		this.initializer = initializer;
	}

	@Override
	public Iterator<Type> getTypeAlignments() {
		return typeAlignments.iterator();
	}

	@Override
	public void addTypeAlignment(Type type) {
		typeAlignments.add(type);
	}

	@Override
	public Iterator<Value> getConstantAlignments() {
		return constantAlignments.iterator();
	}

	@Override
	public void addConstantAlignment(Value constant) {
		constantAlignments.add(constant);
	}

	@Override
	public VariableDeclarationNode getDefinition() {
		return (VariableDeclarationNode) super.getDefinition();
	}

	@Override
	public void setDefinition(DeclarationNode declaration) {
		if (!(declaration instanceof VariableDeclarationNode))
			throw new IllegalArgumentException(
					"Variable declaration not instance of VariableDeclarationNode: "
							+ declaration);
		super.setDefinition(declaration);
	}

	@Override
	public ObjectType getType() {
		return (ObjectType) super.getType();
	}

	@Override
	public void setType(Type type) {
		if (!(type instanceof ObjectType))
			throw new IllegalArgumentException(
					"Type of variable must be object type");
		super.setType(type);
	}

	@Override
	public VariableDeclarationNode getDeclaration(int index) {
		return (VariableDeclarationNode) super.getDeclaration(index);
	}

}
