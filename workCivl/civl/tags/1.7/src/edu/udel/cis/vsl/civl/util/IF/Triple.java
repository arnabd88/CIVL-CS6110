package edu.udel.cis.vsl.civl.util.IF;

public class Triple<R, S, T> {
	public R first;
	public S second;
	public T third;

	public Triple(R first, S second, T third) {
		// assert first != null && second != null && third != null;
		this.first = first;
		this.second = second;
		this.third = third;
	}

	public int hashCode() {
		return first.hashCode() + second.hashCode() + third.hashCode();
	}

	public boolean equals(Object object) {
		if (object instanceof Triple<?, ?, ?>) {
			return first.equals(((Triple<?, ?, ?>) object).first)
					&& second.equals(((Triple<?, ?, ?>) object).second)
					&& third.equals(((Triple<?, ?, ?>) object).third);
		} else {
			return false;
		}
	}
}
