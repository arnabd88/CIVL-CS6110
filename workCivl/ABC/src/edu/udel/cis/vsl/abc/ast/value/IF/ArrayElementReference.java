package edu.udel.cis.vsl.abc.ast.value.IF;

public interface ArrayElementReference extends AddressValue {

	Value getIndex();

	AddressValue getArrayReference();

}
