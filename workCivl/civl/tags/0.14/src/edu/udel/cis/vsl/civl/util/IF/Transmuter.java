package edu.udel.cis.vsl.civl.util.IF;

import java.util.ArrayList;

public class Transmuter {

	/**
	 * Given a bijection from a subset S of {0,...,n-1} to {0,...,m-1}, returns
	 * the inverse of that bijection.
	 * 
	 * The given map must have length n and for each i (0<=i<n), either
	 * map[i]=-1, indicating i is not in S, or map[i] is in {0,...,m-1}.
	 * 
	 * The result will be an array of length m satisfying
	 * 
	 * result[map[i]]==i, for all i in S.
	 * 
	 * @param map
	 *            array of ints of length n specifying bijection from a subset
	 *            of 0..n-1 to 0..m-1.
	 * @param m
	 *            cardinality of S
	 * @return inverse of map
	 */
	public static int[] inverse(int[] map, int m) {
		int n = map.length;
		int[] result = new int[m];

		for (int i = 0; i < n; i++) {
			int v = map[i];

			if (v >= 0)
				result[v] = i;
		}
		return result;
	}

	/**
	 * Given a bijection from a subset S of {0,...,n-1} to {0,...,m-1}, returns
	 * the inverse of that bijection. This method will determine m by scanning
	 * map and counting the number of elements that are nonnegative.
	 * 
	 * The given map must have length n and for each i (0<=i<n), either
	 * map[i]=-1, indicating i is not in S, or map[i] is in {0,...,m-1}.
	 * 
	 * The result will be an array of length m satisfying
	 * 
	 * result[map[i]]==i, for all i in S.
	 * 
	 * @param map
	 *            array of ints of length n specifying bijection from a subset
	 *            of 0..n-1 to 0..m-1.
	 * @param m
	 *            cardinality of S
	 * @return inverse of map
	 */
	public static int[] inverse(int[] map) {
		int m = 0;

		for (int v : map)
			if (v >= 0)
				m++;
		return inverse(map, m);
	}

	/**
	 * Returns a new array list obtained from given one by reordering elements
	 * according to a specified map.
	 * 
	 * Let n be the size of a. The map specifies (1) a subset S of {0,1,...,n-1}
	 * and (2) a bijection from S to {0,1,...,m-1}, where m is the cardinality
	 * of S. The elements of a at positions not in S will not be copied to the
	 * new array list b. The other elements will be copied and reordered.
	 * Specifically, for each i in S, we will have
	 * 
	 * b[map[i]] == a[i]
	 * 
	 * where b is the array list returned by this method. Furthermore,
	 * b.size()==m.
	 * 
	 * The map is an array of ints of length n. For 0<=i<n, map[i] is either -1
	 * (indicating i is not in S, i.e., the element a[i] is to be discarded) or
	 * a nonnegative integer giving the new index of the element.
	 * 
	 * Neither map nor a is modified by this method.
	 * 
	 * @param map
	 *            array of ints of length n giving bijection from a subset of
	 *            {0,...,n-1} to {0,...,m-1}
	 * @param a
	 *            array list of length n
	 * @return array list of length m satisfying b[map[i]] == a[i]
	 */
	public static <T> ArrayList<T> transmute(int[] map, ArrayList<T> a) {
		int n = a.size();
		ArrayList<T> b = new ArrayList<T>(n);

		for (int i = 0; i < n; i++) {
			int j = map[i];
			int size = b.size();

			if (j < size)
				b.set(j, a.get(i));
			else {
				while (size < j) {
					b.add(null);
					size++;
				}
				assert size == j;
				b.add(a.get(i));
			}
		}
		return b;
	}

	/**
	 * Permutes in-place the elements of an array list.
	 * 
	 * Let n be the size of a. The map specifies (1) a subset S of {0,1,...,n-1}
	 * and (2) a bijection from S to {0,1,...,m-1}, where m is the cardinality
	 * of S. The elements of a at positions not in S are to be discarded. The
	 * other elements are to be reordered. Specifically, for each i in S, we
	 * will have
	 * 
	 * a'[map[i]] == a[i]
	 * 
	 * where a' is the array list after this method completes. Furthermore,
	 * a'.size()==m.
	 * 
	 * The map is an array of ints of length n. For 0<=i<n, map[i] is either -1
	 * (indicating i is not in S, i.e., the element a[i] is to be discarded) or
	 * a nonnegative integer giving the new index of the element.
	 * 
	 * The inverseMap is the inverse of map and is completely determined by map.
	 * It specifies a function from {0,1,...,m-1} to S. Its length is m and it
	 * satisfies
	 * 
	 * inverseMap[map[i]]==i for i in S
	 * 
	 * map[inverseMap[j]]==j for j in {0,1,...,m-1}.
	 * 
	 * The method may modify inverseMap.
	 * 
	 * @param map
	 *            array of length n specifying bijection from subset of 0..n-1
	 *            to 0..m-1.
	 * @param inverseMap
	 *            inverse of map
	 * @param a
	 *            an array list of length n to be transmuted
	 */
	public static <T> void transmuteInPlace(int[] map, int[] inverseMap,
			ArrayList<T> a) {
		int n = map.length;
		int m = inverseMap.length;

		for (int k = 0; k < m; k++) {
			while (k < m && inverseMap[k] < 0)
				k++;
			if (k == m)
				break;

			int i = k;
			int j = map[i];

			while (j >= 0 && j != k) {
				i = j;
				j = map[i];
			}
			if (j < 0) { /* shift */
				j = i;
				i = j < m ? inverseMap[j] : -1;
				while (i >= 0) {
					a.set(j, a.get(i));
					inverseMap[j] = -1;
					j = i;
					i = j < m ? inverseMap[j] : -1;
				}
			} else { /* cycle */
				if (i != k) {
					T tmp = a.get(j);

					while (i != k) {
						a.set(j, a.get(i));
						inverseMap[j] = -1;
						j = i;
						i = j < m ? inverseMap[j] : -1;
					}
					a.set(j, tmp);
				}
				inverseMap[j] = -1;
			}
		}
		// remove indexes m...n-1
		for (int i = m; i < n; i++)
			a.remove(m);
	}

	public static void transmuteInPlaceMultiple(int[] map, int[] inverseMap,
			ArrayList<Object>[] a) {
		int n = map.length;
		int numArrays = a.length;
		Object[] tmps = new Object[numArrays];

		for (int k = 0; k < n; k++) {
			int i, j;

			while (k < n && inverseMap[k] < 0)
				k++;
			if (k == n)
				break;
			i = k;
			j = map[i];
			while (j >= 0 && j != k) {
				i = j;
				j = map[i];
			}
			if (j < 0) { /* shift */
				j = i;
				i = inverseMap[j];
				while (i >= 0) {
					for (int l = 0; l < numArrays; l++)
						a[l].set(j, a[l].get(i));
					inverseMap[j] = -1;
					j = i;
					i = inverseMap[j];
				}
			} else { /* cycle */
				if (i != k) {
					for (int l = 0; l < numArrays; l++)
						tmps[l] = a[l].get(j);
					while (i != k) {
						for (int l = 0; l < numArrays; l++)
							a[l].set(j, a[l].get(i));
						inverseMap[j] = -1;
						j = i;
						i = inverseMap[j];
					}
					for (int l = 0; l < numArrays; l++)
						a[l].set(j, tmps[l]);
				}
				inverseMap[j] = -1;
			}
		}
	}

}
