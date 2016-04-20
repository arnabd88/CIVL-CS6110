package edu.udel.cis.vsl.abc.ast.entity.IF;

import java.util.Enumeration;

/**
 * Marker interfaces for {@link StructureOrUnion} and {@link Enumeration}
 * entities. These are entities that have a "tag", the identifier that appears
 * after the <code>struct</code>, <code>union</code>, or <code>enum</code> token
 * in the declaration. These tags occupy a tag namespace which is distinct from
 * the ordinary namespace used by variables, functions, etc.
 * 
 * @author siegel
 * 
 */
public interface TaggedEntity extends ProgramEntity {

	/**
	 * Is this tagged entity complete? That is, have the members inside curly
	 * braces been specified?
	 * 
	 * @return <code>true</code> iff this is complete
	 */
	boolean isComplete();

}
