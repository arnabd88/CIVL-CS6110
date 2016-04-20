/**
 * Module <strong>state</strong> is responsible for the creation and manipulation of
 * states of a CIVL model.
 * 
 * The entry point to this module in the class {@link edu.udel.cis.vsl.civl.state.IF.States}.
 * This class provides static method to obtain state factories.  The state factory
 * is used to produce new states and modify states.
 * 
 * The interface for this module is provided in package {@link edu.udel.cis.vsl.civl.state.IF}.
 * That package defines interfaces for the state factory, the state itself,
 * and various sub-components of the state.    Users of this module should
 * use only elements from the interface, not the implementation packages.
 * 
 * There are currently two alternative implementations of the state module:
 * immutable and transient.  In the immutable implementation, states
 * and their components are (essentially) immutable.  In the transient
 * module states (and their components) begin in a mutable state but
 * can be made immutable at any time by invoking a "commit" method.
 * The relative advantages and disadvantages of the two approaches are
 * being explored.
 */
package edu.udel.cis.vsl.civl.state.IF;

