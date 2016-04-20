package edu.udel.cis.vsl.sarl.simplify.common;

import edu.udel.cis.vsl.sarl.IF.number.Interval;
import edu.udel.cis.vsl.sarl.IF.number.Number;
import edu.udel.cis.vsl.sarl.IF.number.NumberFactory;
import edu.udel.cis.vsl.sarl.number.IF.Numbers;
import edu.udel.cis.vsl.sarl.simplify.IF.Range;
import edu.udel.cis.vsl.sarl.simplify.IF.RangeFactory;

public class IntervalUnionFactory implements RangeFactory {
	private static NumberFactory numberFactory = Numbers.REAL_FACTORY;

	public IntervalUnionFactory() {
		// Nothing
	}

	@Override
	public Range emptySet(boolean isIntegral) {
		return new IntervalUnionSet(isIntegral);
	}

	@Override
	public Range singletonSet(Number number) {
		return new IntervalUnionSet(number);
	}

	@Override
	public Range interval(Number left, boolean strictLeft, Number right,
			boolean strictRight, boolean isIntegral) {
		return new IntervalUnionSet(left, strictLeft, right, strictRight,
				isIntegral);
	}

	@Override
	public Range add(Range lRange, Range rRange) {
		IntervalUnionSet lSet = (IntervalUnionSet) lRange;
		IntervalUnionSet rSet = (IntervalUnionSet) lRange;
		Interval[] lIntervals = lSet.intervals();
		Interval[] rIntervals = rSet.intervals();
		int lSize = lIntervals.length;
		int rSize = rIntervals.length;
		Interval[] resultIntervals = new Interval[lSize * rSize];
		int resultIndex = 0;
		for (int i = 0; i < lSize; ++i) {
			for (int j = 0; j < rSize; ++j) {
				resultIntervals[resultIndex] = numberFactory.add(lIntervals[i],
						rIntervals[j]);
				resultIndex++;
			}
		}
		return new IntervalUnionSet(resultIntervals);
	}

	@Override
	public Range multiply(Range lRange, Range rRange) {
		IntervalUnionSet lSet = (IntervalUnionSet) lRange;
		IntervalUnionSet rSet = (IntervalUnionSet) lRange;
		Interval[] lIntervals = lSet.intervals();
		Interval[] rIntervals = rSet.intervals();
		int lSize = lIntervals.length;
		int rSize = rIntervals.length;
		Interval[] resultIntervals = new Interval[lSize * rSize];
		int resultIndex = 0;
		for (int i = 0; i < lSize; ++i) {
			for (int j = 0; j < rSize; ++j) {
				resultIntervals[resultIndex] = numberFactory.multiply(lIntervals[i],
						rIntervals[j]);
				resultIndex++;
			}
		}
		return new IntervalUnionSet(resultIntervals);
	}

	@Override
	public Range power(Range lRange, int exp) {
		IntervalUnionSet lSet = (IntervalUnionSet) lRange;
		Interval[] lIntervals = lSet.intervals();
		int lSize = lIntervals.length;
		Interval[] resultIntervals = new Interval[lSize];
		for (int i = 0; i < lSize; ++i) {
			resultIntervals[i] = numberFactory.power(lIntervals[i],
					exp);
		}
		return new IntervalUnionSet(resultIntervals);
	}

}// Under testing
