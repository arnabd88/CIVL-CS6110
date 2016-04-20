package edu.udel.cis.vsl.sarl.util;

import java.util.Comparator;
import java.util.Iterator;

public abstract class KeySetFactory<K extends Object, V extends Object> {

	private V[] emptySet;

	private Comparator<K> keyComparator;

	public KeySetFactory(Comparator<K> keyComparator) {
		this.keyComparator = keyComparator;
		this.emptySet = newSet(0);
	}

	protected abstract V[] newSet(int size);

	protected abstract K key(V value);

	/**
	 * Finds the index of the entry in <code>set</code> with key
	 * <code>key</code> in the array of arguments of the given <code>set</code>.
	 * If there is no entry if there is one. Else returns -1.
	 * 
	 * @param key
	 *            the key to look for; any member of K
	 * @return index of the entry with that key, or -1 if there is none
	 */
	protected int find(V[] set, K key) {
		int lo = 0, hi = set.length - 1;

		while (lo <= hi) {
			int mid = (lo + hi) / 2;
			V value = set[mid];
			int compare = keyComparator.compare(key(value), key);

			if (compare == 0) {
				return mid;
			} else if (compare < 0) { // x<element
				lo = mid + 1;
			} else {
				hi = mid - 1;
			}
		}
		return -1;
	}

	public Comparator<K> keyComparator() {
		return keyComparator;
	}

	public V[] emptySet() {
		return emptySet;
	}

	public V[] singletonSet(V element) {
		V[] set = newSet(1);

		set[0] = element;
		return set;
	}

	public V get(V[] set, K key) {
		int index = find(set, key);

		return index < 0 ? null : set[index];
	}

	public V[] put(V[] set, V value) {
		K key = key(value);
		int lo = 0, hi = set.length - 1;

		// loop invariant: hi-lo >= -1.
		// hi>=lo -> hi-((lo+hi)/2 + 1) >= -1.
		// hi>=lo -> ((lo+hi)/2 -1) - lo >= -1.
		while (lo <= hi) {
			int mid = (lo + hi) / 2;
			V entry = set[mid];
			int keyComparison = keyComparator.compare(key(entry), key);

			if (keyComparison == 0) {
				if (value.equals(entry))
					return set;

				// new version replacing old entry with new one at mid
				V[] newSet = newSet(set.length);

				System.arraycopy(set, 0, newSet, 0, set.length);
				newSet[mid] = value;
				return newSet;
			} else if (keyComparison < 0) { // x<element
				lo = mid + 1;
			} else { // x>element
				hi = mid - 1;
			}
		}
		assert hi - lo == -1;
		// Example: hi=-1, lo=0
		// Example: hi=length-1, lo=length
		// lo is where element should be inserted
		// new version inserting new entry at position lo
		V[] newSet = newSet(set.length + 1);

		System.arraycopy(set, 0, newSet, 0, lo);
		newSet[lo] = value;
		System.arraycopy(set, lo, newSet, lo + 1, set.length - lo);
		return newSet;
	}

	public V[] removeKey(V[] set, K key) {
		int index = find(set, key);

		if (index < 0)
			return set;

		V[] newSet = newSet(set.length - 1);

		System.arraycopy(set, 0, newSet, 0, index);
		System.arraycopy(set, index + 1, newSet, index, set.length - index - 1);
		return newSet;
	}

	public V[] combine(BinaryOperator<V> operator, V[] set1, V[] set2) {
		int n1 = set1.length, n2 = set2.length;

		if (n1 == 0)
			return set2;
		if (n2 == 0)
			return set1;

		V[] newSet = newSet(n1 + n2);
		int i1 = 0, i2 = 0, count = 0;
		V v1 = set1[0], v2 = set2[0];
		K k1 = key(v1), k2 = key(v2);

		while (true) {
			int c = keyComparator.compare(k1, k2);

			if (c < 0) { // key1 comes first
				newSet[count] = v1;
				count++;
				i1++;
				if (i1 >= n1)
					break;
				v1 = set1[i1];
				k1 = key(v1);
			} else if (c > 0) { // key2 comes first
				newSet[count] = v2;
				count++;
				i2++;
				if (i2 >= n2)
					break;
				v2 = set2[i2];
				k2 = key(v2);
			} else {
				V newValue = operator.apply(v1, v2);

				if (newValue != null) {
					newSet[count] = newValue;
					count++;
				}
				i1++;
				i2++;
				if (i1 >= n1 || i2 >= n2)
					break;
				v1 = set1[i1];
				k1 = key(v1);
				v2 = set2[i2];
				k2 = key(v2);
			}
		}

		int delta1 = n1 - i1, delta2 = n2 - i2,
				newLength = count + delta1 + delta2;

		// trim to actual size...
		if (newLength < n1 + n2) {
			V[] tmp = newSet(newLength);

			System.arraycopy(newSet, 0, tmp, 0, count);
			newSet = tmp;
		}
		if (i1 < n1)
			System.arraycopy(set1, i1, newSet, count, delta1);
		else if (i2 < n2)
			System.arraycopy(set2, i2, newSet, count, delta2);
		return newSet;
	}

	private class KeyIterable implements Iterable<K> {
		private int theSize;
		private V[] theSet;

		private class KeyIterator implements Iterator<K> {
			int next = 0;

			@Override
			public boolean hasNext() {
				return next < theSize;
			}

			@Override
			public K next() {
				V val = theSet[next];
				K result = key(val);

				next++;
				return result;
			}
		}

		KeyIterable(V[] set) {
			this.theSize = set.length;
			this.theSet = set;
		}

		@Override
		public Iterator<K> iterator() {
			return new KeyIterator();
		}
	}

	public Iterable<K> getKeys(V[] set) {
		return new KeyIterable(set);
	}

}
