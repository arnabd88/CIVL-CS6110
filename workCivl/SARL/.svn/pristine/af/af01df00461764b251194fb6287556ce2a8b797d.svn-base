package edu.udel.cis.vsl.sarl.util;

import java.util.Comparator;

public abstract class SetFactory<V> extends KeySetFactory<V, V> {

	private BinaryOperator<V> project1 = new BinaryOperator<V>() {
		@Override
		public V apply(V x, V y) {
			return x;
		}
	};

	public SetFactory(Comparator<V> comparator) {
		super(comparator);
	}

	protected V key(V value) {
		return value;
	}

	public V[] union(V[] set1, V[] set2) {
		return combine(project1, set1, set2);
	}

	public boolean contains(V[] set, V element) {
		return find(set, element) >= 0;
	}
}
