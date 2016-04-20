package edu.udel.cis.vsl.abc.ast.type.common;

import edu.udel.cis.vsl.abc.ast.entity.IF.ProgramEntity;
import edu.udel.cis.vsl.abc.ast.entity.common.CommonOrdinaryEntity;
import edu.udel.cis.vsl.abc.ast.node.IF.declaration.EnumeratorDeclarationNode;
import edu.udel.cis.vsl.abc.ast.type.IF.EnumerationType;
import edu.udel.cis.vsl.abc.ast.type.IF.Enumerator;
import edu.udel.cis.vsl.abc.ast.value.IF.Value;

public class CommonEnumerator extends CommonOrdinaryEntity implements
		Enumerator {

	private Value value;

	/**
	 * Constructs new Enumerator.
	 * 
	 * @param declaration
	 *            the declaration node for this enumerator
	 * @param type
	 *            the enumeration type to which this enumerator belongs
	 * @param value
	 *            optional constant value; may be null
	 */
	public CommonEnumerator(EnumeratorDeclarationNode declaration,
			EnumerationType enumeration, Value value) {
		super(EntityKind.ENUMERATOR, declaration.getName(), ProgramEntity.LinkageKind.NONE,
				enumeration);
		this.addDeclaration(declaration);
		this.setDefinition(declaration);
		this.value = value;
	}

	@Override
	public EnumeratorDeclarationNode getDefinition() {
		return (EnumeratorDeclarationNode) super.getDefinition();
	}

	@Override
	public EnumerationType getType() {
		return (EnumerationType) super.getType();
	}

	@Override
	public Value getValue() {
		return value;
	}
}
