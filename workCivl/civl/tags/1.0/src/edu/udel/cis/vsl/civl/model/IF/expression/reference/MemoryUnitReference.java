package edu.udel.cis.vsl.civl.model.IF.expression.reference;

public interface MemoryUnitReference {

	public enum MemoryUnitReferenceKind {
		SELF, /** The whole variable */
		ARRAY_SLICE, /** A slice (one or some elements) of an array */
		STRUCT_OR_UNION_FIELD,
		/** An element of a struct */
	}

	/**
	 * The reference kind of this memory unit.
	 * 
	 * @return
	 */
	public MemoryUnitReferenceKind memoryUnitKind();

	/**
	 * The child of this reference. (in order to support recursive references)
	 * 
	 * @return
	 */
	public MemoryUnitReference child();
}
