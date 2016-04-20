package edu.udel.cis.vsl.sarl.ideal.common;

import java.util.Comparator;

import edu.udel.cis.vsl.sarl.ideal.IF.Monic;

/**
 * A {@link Comparator} on {@link Monic}s. Imposes a total order on
 * {@link Monic}s, which is the same as that of the {@link IdealComparator}.
 * 
 * @author siegel
 */
public class MonicComparator implements Comparator<Monic> {

	private IdealComparator ic;

	public MonicComparator(IdealComparator ic) {
		this.ic = ic;
	}

	@Override
	public int compare(Monic o1, Monic o2) {
		return ic.compareMonics(o1, o2);
	}

}
