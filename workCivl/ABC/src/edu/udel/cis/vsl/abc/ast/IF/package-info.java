/**
 * <p>Module <strong>ast</strong> defines an Abstract Syntax Tree
 * representation of a program, the
 * {@link edu.udel.cis.vsl.abc.ast.IF.AST AST}.  This module is large
 * and is therefore divided into several submodules.
 * Each submodule has its own interface.  This package proper contains
 * the module entry point, {@link edu.udel.cis.vsl.abc.ast.IF.ASTs}
 * and an exception class specific to ASTs.</p>
 *
 * This module is decomposed into the following submodules:
 * 
 * <ul>
 * 
 * <li>main: this package, declaring the interfaces 
 * {@link edu.udel.cis.vsl.abc.ast.IF.AST AST}
 * and {@link edu.udel.cis.vsl.abc.ast.IF.ASTFactory ASTFactory}.
 * </li>
 * 
 * <li><strong>ast.value</strong>
 *   <ul>
 *   <li>responsibilities: representation of concrete value, such as characters, integers, floating point values</li>
 *   <li>interface: {@link edu.udel.cis.vsl.abc.ast.value.IF}</li>
 *   <li>entry point: {@link edu.udel.cis.vsl.abc.ast.value.IF.Values Values}</li>
 *   </ul>
 * </li>
 * 
 * <li><strong>ast.type</strong>
 *   <ul>
 *   <li>responsibilities: representation of types</li>
 *   <li>interface: {@link edu.udel.cis.vsl.abc.ast.type.IF}</li>
 *   <li>entry point: {@link edu.udel.cis.vsl.abc.ast.type.IF.Types Types}</li>
 *   </ul>
 * </li>
 *
 * <li><strong>ast.entity</strong>
 *   <ul>
 *   <li>responsibilities: representation of abstract program entities which can
 *   be named by an identifier, including variables, functions, labels, scopes, 
 *   structures, unions, enumerations, enumerators, and typedefs</li>
 *   <li>interface: {@link edu.udel.cis.vsl.abc.ast.entity.IF}</li>
 *   <li>entry point: {@link edu.udel.cis.vsl.abc.ast.entity.IF.Entities Entities}</li>
 *   </ul>
 * </li>
 * 
 * <li><strong>ast.conversion</strong>
 *   <ul>
 *   <li>responsibilities: representation of C's implicit conversions, such
 *   as the conversion of an array to a pointer to the first element of the
 *   array, and so on</li>
 *   <li>interface: {@link edu.udel.cis.vsl.abc.ast.conversion.IF}</li>
 *   <li>entry point: {@link edu.udel.cis.vsl.abc.ast.conversion.IF.Conversions Conversions}
 *   </ul>
 * </li>
 *
 * <li><strong>ast.node</strong>
 *   <ul>
 *   <li>responsibilities: representation of AST nodes</li>
 *   <li>interface: {@link edu.udel.cis.vsl.abc.ast.node.IF}</li>
 *   <li>entry point: {@link edu.udel.cis.vsl.abc.ast.node.IF.Nodes Nodes}</li>
 *   </ul>
 * </li>
 * 
 * </ul>
 */
package edu.udel.cis.vsl.abc.ast.IF;

