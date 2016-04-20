package edu.udel.cis.vsl.abc.ast.node.IF.expression;

import edu.udel.cis.vsl.abc.ast.value.IF.CharacterValue;

/**
 * <p>
 * An instance of this interface represents a single Unicode character occurring
 * as a literal element in a C program.
 * </p>
 * 
 * <p>
 * Following the information in the C11 Standard, the C11 representation of a
 * character literal is interpreted to yield (1) a Unicode character, and (2) a
 * C type. Both pieces of information are included in an instance of this class.
 * </p>
 * 
 * <p>
 * Character constants are discussed in Section 6.4.4.4 of C11. They have a
 * complex structure.
 * </p>
 * 
 * <p>
 * First, there is a possible prefix: either none, <code>L</code>,
 * <code>u</code>, or <code>U</code>.
 * </p>
 * 
 * <p>
 * Second there is a sequence of "c-char" (enclosed in single quotes).
 * </p>
 * 
 * <p>
 * A c-char is either (1) any member of the source character set other than
 * single-quote, backslash, or newline, or (2) an escape sequence.
 * </p>
 * 
 * <p>
 * An escape sequence is either a simple escape sequence, an octal escape
 * sequence, a hexadecimal escape sequence, or a universal character name.
 * </p>
 * 
 * <p>
 * A simple escape sequence is one of the following:
 * 
 * <pre>
 * \'  \"  \?  \\  \a  \b  \f  \n  \r  \t  \v
 * </pre>
 * 
 * </p>
 * 
 * <p>
 * An octal escape sequence is a backslash followed by 1, 2, or 3 octal digits.
 * </p>
 * 
 * <p>
 * A hexadecimal escape sequence consists of <code>\x</code> followed by 1 or
 * more hexadecimal digits.
 * </p>
 * 
 * <p>
 * Note: it seems that if the sequence of c-char has length greater than one,
 * the behavior is implementation-defined, so we are only going to support
 * sequences of length 1.
 * </p>
 * 
 * <p>
 * Types:
 * </p>
 * 
 * <p>
 * The type is determined from the prefix as follows: <code>int</code> (none),
 * <code>wchar_t</code> (<code>L</code>), <code>char16_t</code> (<code>u</code>
 * ), or <code>char32_t</code> (<code>U</code>). <code>wchar_t</code> is an
 * integer type, described in C11 Sec. 7.19. <code>char16_t</code> and
 * <code>char32_t</code> are described in Sec. 7.28; the first is the smallest
 * unsigned integer type with a width of at least 16; the latter is the smallest
 * unsigned integer type with a width of at least 32.
 * </p>
 * 
 * <p>
 * If there is no prefix, the constant is known as an "integer character
 * constant", otherwise it is a "wide character constant".
 * </p>
 * 
 * <p>
 * Note: the type may be <code>null</code> until it is set. This is because the
 * special types (<code>wchar_t</code>, etc.) are not known until typedefs have
 * been processed.
 * </p>
 * 
 * <p>
 * Values:
 * </p>
 * 
 * <p>
 * This part is very confusing and certainly some of it is
 * implementation-dependent. The procedure outlined here seems to be consistent
 * with what is written in the Standard.
 * </p>
 * 
 * <p>
 * For an integer character constant, the procedure is as follows. The code
 * point (which is a non-negative integer) must lie in the range of the type
 * <code>unsigned char</code>. (If not, an exception is thrown.) It is then
 * converted to a value of type <code>char</code> as follows: if the range of
 * <code>char</code> coincides with that of <code>unsigned char</code>, nothing
 * to do. Otherwise, if the value already lies within the range of
 * <code>signed char</code>, nothing to do. Otherwise, subtract
 * (unsignedCharMax+1) from value. Finally, the <code>char</code> value is
 * converted to a value of type <code>int</code>.
 * </p>
 * 
 * <p>
 * <strong>Example</strong>: if <code>char</code> = <code>unsigned char</code>
 * and has 8 bits, this will yield an <code>int</code> value in the range
 * [0,255]. <code>'\xFF'</code> yields the int value 255.
 * </p>
 * 
 * <p>
 * <strong>Example</strong>: If <code>char</code>=<code>signed char</code> and
 * has 8 bits and two's complement representation is used for integers, then the
 * <code>int</code> value will lie in the range [-128,127]. <code>'\xFF'</code>
 * yields the int value -1 (255-256=-1).
 * </p>
 * 
 * <p>
 * For wide character constants, the value is determined by one of the functions
 * <code>mbtowc</code>, <code>mbrtoc16</code>, or <code>mbrtoc32</code>. For
 * now, we punt on wide characters.
 * </p>
 * 
 * @author siegel
 * 
 */
public interface CharacterConstantNode extends ConstantNode {

	/**
	 * Returns the constant value represented by this expression.
	 * 
	 * @return the constant value, which is a character value
	 */
	CharacterValue getConstantValue();

	@Override
	CharacterConstantNode copy();

}
