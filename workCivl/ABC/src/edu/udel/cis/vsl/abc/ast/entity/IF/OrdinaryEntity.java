package edu.udel.cis.vsl.abc.ast.entity.IF;

import edu.udel.cis.vsl.abc.ast.type.IF.Enumerator;

/**
 * An "ordinary" entity is a {@link Variable}, {@link Function},
 * {@link Enumerator}, or {@link Typedef}. These entities share a single name
 * space. All of these also have a type associated to them. This is a marker
 * interface to indicate the object is an ordinary entity. The interfaces listed
 * above all extend this one.
 * 
 * @author siegel
 * 
 */
public interface OrdinaryEntity extends ProgramEntity {
}
