package edu.udel.cis.vsl.civl.util.IF;

import java.util.Collection;
import java.util.HashSet;

public class Utils {
	/**
	 * returns the difference of first and second (first-second)
	 * 
	 * @param first
	 * @param second
	 * @return
	 */
	public static Collection<? extends Object> difference(
			Collection<? extends Object> first,
			Collection<? extends Object> second) {
		Collection<Object> set = new HashSet<>();

		for (Object element : first) {
			if (!second.contains(element))
				set.add(element);
		}
		return set;
	}
}
