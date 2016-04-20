package edu.udel.cis.vsl.abc.ast.conversion.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.Type;

/**
 * A conversion is an implicit operation that may change a value and/or the type
 * of the value. Examples include the usual arithmetic conversions, lvalue
 * conversion, and array and function conversions (which change the type from
 * array of T to pointer to T, and function returning T to pointer to function
 * returning T, respectively).
 * 
 * @author siegel
 * 
 */
public interface Conversion {

	/**
	 * Kind of conversions
	 */
	public enum ConversionKind {
		/** can be safely casted to {@link ArithmeticConversion} */
		ARITHMETIC,
		/** can be safely casted to {@link ArrayConversion} */
		ARRAY,
		/** can be safely casted to {@link CompatiblePointerConversion} */
		COMPATIBLE_POINTER,
		/** can be safely casted to {@link CompatibleStructureOrUnionConversion} */
		COMPATIBLE_STRUCT_UNION,
		/** can be safely casted to {@link FunctionConversion} */
		FUNCTION,
		/** can be safely casted to {@link Integer2PointerConversion} */
		INTEGER_POINTER,
		/** can be safely casted to {@link LvalueConversion} */
		LVALUE,
		/** can be safely casted to {@link MemoryConversion} */
		MEMORY,
		/** can be safely casted to {@link NullPointerConversion} */
		NULL_POINTER,
		/** can be safely casted to {@link PointerBoolConversion} */
		POINTER_BOOL,
		/** can be safely casted to {@link Pointer2IntegerConversion} */
		POINTER_INTEGER,
		/** can be safely casted to {@link RegularRangeToDomainConversion} */
		REG_RANGE_DOMAIN,
		/** can be safely casted to {@link VoidPointerConversion} */
		VOID_POINTER
	}

	/**
	 * Returns the type of the entity before applying this conversion.
	 * 
	 * @return the pre-conversion type
	 */
	Type getOldType();

	/**
	 * Returns the type of the entity after applying this conversion.
	 * 
	 * @return the post-conversion type
	 */
	Type getNewType();

	/**
	 * Returns the kind of the conversion.
	 * 
	 * @return the kind of the conversion
	 */
	ConversionKind conversionKind();

}
