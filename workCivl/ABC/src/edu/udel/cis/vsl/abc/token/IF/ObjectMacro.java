package edu.udel.cis.vsl.abc.token.IF;

/**
 * An Object macro represents a C preprocessor object macro: a directive of the
 * form <code>#define X ...</code> where <code>X</code> is the name of the macro
 * and the <code>...</code> is a list of replacement tokens. This is a marker
 * interface to distinguish object macros from other kinds of macros (namely,
 * function macros).
 */
public interface ObjectMacro extends Macro {

}
