package edu.udel.cis.vsl.abc.ast.entity.IF;

import edu.udel.cis.vsl.abc.ast.entity.IF.Scope.ScopeKind;
import edu.udel.cis.vsl.abc.ast.node.IF.ASTNode;
import edu.udel.cis.vsl.abc.ast.node.IF.acsl.BehaviorNode;
import edu.udel.cis.vsl.abc.ast.node.IF.label.OrdinaryLabelNode;
import edu.udel.cis.vsl.abc.ast.type.IF.Type;

/**
 * A factory for producing instances of {@link Entity}, and some related utility
 * methods.
 * 
 * @author siegel
 * 
 */
public interface EntityFactory {

	/**
	 * Creates a new scope.
	 * 
	 * @param kind
	 *            the kind of scope to create
	 * @param parent
	 *            the scope immediately containing the new scope; can be null
	 *            for the root scope
	 * @param root
	 *            an AST node to associate to the new scope; it is used only for
	 *            printing to make it easy for the reader to identify where the
	 *            scope comes from
	 * @return the new Scope
	 */
	Scope newScope(ScopeKind kind, Scope parent, ASTNode root);

	/**
	 * Creates a new {@link Variable}.
	 * 
	 * @param name
	 *            the name of the variable
	 * @param linkage
	 *            the kind of linkage the variable has
	 * @param type
	 *            the type of the variable
	 * @return the new variable
	 */
	Variable newVariable(String name, ProgramEntity.LinkageKind linkage,
			Type type);

	/**
	 * Creates a new {@link Function}.
	 * 
	 * @param name
	 *            the name of the function
	 * @param linkage
	 *            the kind of linkage the function has
	 * @param type
	 *            the type of the function
	 * @return the new function
	 */
	Function newFunction(String name, ProgramEntity.LinkageKind linkage,
			Type type);

	/**
	 * Creates a new {@link Typedef} entity.
	 * 
	 * @param name
	 *            the name of the typedef
	 * @param type
	 *            the type to which the name is bound in the typedef
	 * @return the new {@link Typedef} entity
	 */
	Typedef newTypedef(String name, Type type);

	/**
	 * Creates a new label entity. This corresponds to an ordinary label
	 * "declaration" in the code. (The name of the label is followed by a colon
	 * and then a statement.)
	 * 
	 * @param declaration
	 *            the ordinary label declaration
	 * @return the new label entity
	 */
	Label newLabel(OrdinaryLabelNode declaration);

	/**
	 * Computes the join of the two scopes in the scope tree and returns it.
	 * 
	 * @param s1
	 *            non-null scope
	 * @param s2
	 *            non-null scope
	 * @return the youngest common ancestor of s1 and s2
	 */
	Scope join(Scope s1, Scope s2);

	/**
	 * Creates a new behavior entity.
	 * 
	 * @param name
	 * @param behavior
	 * @return
	 */
	BehaviorEntity newBehavior(String name, BehaviorNode behavior);

}
