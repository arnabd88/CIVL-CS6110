/**
 * 
 */
package edu.udel.cis.vsl.civl.predicate.IF;


/**
 * An potential deadlock occurs if all of the following hold:
 * 
 * <ol>
 * <li>not every process has terminated</li>
 * <li>the only enabled transitions are sends for which there is no matching
 * receive</li>
 * </ol>
 * 
 * @author Ziqing Luo
 */
public interface PotentialDeadlock extends CIVLStatePredicate {
}
