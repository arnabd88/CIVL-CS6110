package edu.udel.cis.vsl.abc.ast.type.common;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Map;

import edu.udel.cis.vsl.abc.ast.entity.IF.CommonEntity;
import edu.udel.cis.vsl.abc.ast.entity.IF.Entity;
import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.DeclarationNode;
import edu.udel.cis.vsl.abc.ast.type.IF.EnumerationType;
import edu.udel.cis.vsl.abc.ast.type.IF.Enumerator;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;
import edu.udel.cis.vsl.abc.err.IF.ABCRuntimeException;

/**
 * Implementation of {@link EnumerationType}. The {@link Entity} methods are
 * implemented using the Delegation Pattern by delegating to an {@link Entity}
 * object which is a field of this class.
 * 
 * @author siegel
 * 
 */
public class CommonEnumerationType extends CommonIntegerType implements
		EnumerationType {

	private final static int classCode = CommonEnumerationType.class.hashCode();

	private ProgramEntity entity;

	private Object key;

	private String tag;

	private ArrayList<Enumerator> enumerators = null;

	public CommonEnumerationType(Object key, String tag) {
		super(TypeKind.ENUMERATION);
		assert key != null;
		this.key = key;
		this.tag = tag;
		this.entity = new CommonEntity(EntityKind.ENUMERATION, tag,
				ProgramEntity.LinkageKind.NONE);
	}

	@Override
	public String getTag() {
		return tag;
	}

	@Override
	public int getNumEnumerators() {
		if (!isComplete())
			throw new RuntimeException("Enumeration type " + tag
					+ " is incomplete");
		return enumerators.size();
	}

	@Override
	public Enumerator getEnumerator(int index) {
		if (!isComplete())
			throw new ABCRuntimeException("Enumeration type " + tag
					+ " is incomplete");
		return enumerators.get(index);
	}

	@Override
	public Iterable<Enumerator> getEnumerators() {
		if (!isComplete())
			throw new ABCRuntimeException("Enumeration type " + tag
					+ " is incomplete");
		return enumerators;
	}

	@Override
	public boolean isComplete() {
		return enumerators != null;
	}

	public void complete(Iterable<Enumerator> enumeratorList) {
		if (isComplete())
			throw new ABCRuntimeException("Enumerator type " + tag
					+ " is already complete");
		enumerators = new ArrayList<>();
		for (Enumerator enumerator : enumeratorList)
			enumerators.add(enumerator);
	}

	@Override
	public boolean isEnumeration() {
		return true;
	}

	/**
	 * Returns the string that is used to check compatibility of this tag with
	 * another tag. This removes any suffix beginning with <code>$TU</code>. In
	 * CIVL-C semantics, such a suffix is ignored for the purposes of checking
	 * compatibility of two tags. It is used by CIVL to give unique names to
	 * tagged entities in different translation units so they can be merged into
	 * a single AST, but such entities should still be considered compatible.
	 * 
	 * NOTE: also removing $anon.
	 * 
	 * @return the tag with any suffix beginning with '$' removed
	 */
	private String getCompatibilityString() {
		if (tag == null)
			return "";
		if (tag.startsWith("$anon")) {
			// "$anon" prefixes are inserted by ABC to give names
			// to anonymous structures. Since the original tag
			// was null, that is what should be used for checking
			// compatibility...
			return "";
		} else {
			int dollarIndex = tag.indexOf("$TU");

			return dollarIndex < 0 ? tag : tag.substring(0, dollarIndex);
		}
	}

	@Override
	public boolean compatibleWith(Type type) {
		if (this == type)
			return true;
		if (type instanceof CommonEnumerationType) {
			CommonEnumerationType that = (CommonEnumerationType) type;

			if (tag == null) {
				if (that.tag != null)
					return false;
			} else if (!getCompatibilityString().equals(
					that.getCompatibilityString()))
				return false;
			if (enumerators == null) {
				if (that.enumerators != null)
					return false;
			} else {
				int numEnumerators = enumerators.size();

				if (that.enumerators == null)
					return false;
				if (numEnumerators != that.enumerators.size())
					return false;
				for (int i = 0; i < numEnumerators; i++) {
					Enumerator enum1 = enumerators.get(i);
					Enumerator enum2 = that.enumerators.get(i);

					if (enum1 == null) {
						if (enum2 != null)
							return false;
					} else {
						String name1 = enum1.getName(), name2;
						Value value1 = enum1.getValue(), value2;

						if (enum2 == null)
							return false;
						name2 = enum2.getName();
						if (name1 == null) {
							if (name2 != null)
								return false;
						} else if (!name1.equals(name2))
							return false;
						value2 = enum2.getValue();
						if (value1 == null) {
							if (value2 != null)
								return false;
						} else if (!value1.equals(value2))
							return false;
					}
				}
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean equivalentTo(Type type) {
		if (this == type)
			return true;
		if (type instanceof CommonEnumerationType) {
			CommonEnumerationType that = (CommonEnumerationType) type;

			if (tag == null) {
				if (that.tag != null)
					return false;
			} else if (!getCompatibilityString().equals(
					that.getCompatibilityString()))
				return false;
			if (enumerators == null) {
				if (that.enumerators != null)
					return false;
			} else {
				int numEnumerators = enumerators.size();

				if (that.enumerators == null)
					return false;
				if (numEnumerators != that.enumerators.size())
					return false;
				for (int i = 0; i < numEnumerators; i++) {
					Enumerator enum1 = enumerators.get(i);
					Enumerator enum2 = that.enumerators.get(i);

					if (enum1 == null) {
						if (enum2 != null)
							return false;
					} else {
						String name1 = enum1.getName(), name2;
						Value value1 = enum1.getValue(), value2;

						if (enum2 == null)
							return false;
						name2 = enum2.getName();
						if (name1 == null) {
							if (name2 != null)
								return false;
						} else if (!name1.equals(name2))
							return false;
						value2 = enum2.getValue();
						if (value1 == null) {
							if (value2 != null)
								return false;
						} else if (!value1.equals(value2))
							return false;
					}
				}
				return true;
			}
		}
		return false;
	}

	@Override
	public void print(String prefix, PrintStream out, boolean abbrv) {
		out.print("Enumeration[tag=" + tag + ", key=" + key + "]");
		if (!abbrv && enumerators != null) {
			for (Enumerator enumerator : enumerators) {
				out.println();
				out.print(prefix + "| " + enumerator.getName());
			}
		}
	}

	@Override
	public boolean isInteger() {
		return true;
	}

	@Override
	public Object getKey() {
		return key;
	}

	@Override
	public void clear() {
		enumerators = null;
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof CommonEnumerationType) {
			CommonEnumerationType that = (CommonEnumerationType) object;

			return key.equals(that.key)
					&& (tag == null || tag.equals(that.tag));
		}
		return false;
	}

	@Override
	public int hashCode() {
		int result = classCode ^ key.hashCode();

		if (tag != null)
			result ^= tag.hashCode();
		return result;
	}

	@Override
	public EntityKind getEntityKind() {
		return entity.getEntityKind();
	}

	@Override
	public String getName() {
		return tag;
	}

	@Override
	public Iterable<DeclarationNode> getDeclarations() {
		return entity.getDeclarations();
	}

	@Override
	public DeclarationNode getFirstDeclaration() {
		return entity.getFirstDeclaration();
	}

	@Override
	public int getNumDeclarations() {
		return entity.getNumDeclarations();
	}

	@Override
	public DeclarationNode getDeclaration(int index) {
		return entity.getDeclaration(index);
	}

	@Override
	public void addDeclaration(DeclarationNode declaration) {
		entity.addDeclaration(declaration);
	}

	@Override
	public DeclarationNode getDefinition() {
		return entity.getDefinition();
	}

	@Override
	public void setDefinition(DeclarationNode declaration) {
		entity.setDefinition(declaration);
	}

	@Override
	public ProgramEntity.LinkageKind getLinkage() {
		return entity.getLinkage();
	}

	@Override
	public void setLinkage(ProgramEntity.LinkageKind linkage) {
		if (linkage != ProgramEntity.LinkageKind.NONE)
			throw new ABCRuntimeException("Linkage of enumeration must be NONE");
	}

	@Override
	public EnumerationType getType() {
		return this;
	}

	@Override
	public void setType(Type type) {
		if (type != this)
			throw new ABCRuntimeException("Cannot change type of enumeration");
	}

	@Override
	public boolean isSystem() {
		return entity.isSystem();
	}

	@Override
	public void setIsSystem(boolean value) {
		entity.setIsSystem(value);
	}

	@Override
	protected boolean similar(Type other, boolean equivalent,
			Map<TypeKey, Type> seen) {
		return equivalent ? equivalentTo(other) : compatibleWith(other);
	}

	@Override
	public String toString() {
			return "enum " + tag;
	}
}
