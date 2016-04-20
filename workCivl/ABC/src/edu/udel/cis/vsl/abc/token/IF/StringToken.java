package edu.udel.cis.vsl.abc.token.IF;

/**
 * A StringToken is formed from a sequence of one or more CTokens. It presents a
 * sequence of ExecutionCharacter obtained by interpreting String literal(s).
 * 
 * It may be primitive or compound.
 * 
 * @author siegel
 * 
 */
public interface StringToken extends CivlcToken {

	StringLiteral getStringLiteral();

}
