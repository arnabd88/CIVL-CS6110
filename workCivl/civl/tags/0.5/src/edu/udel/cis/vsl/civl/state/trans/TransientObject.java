package edu.udel.cis.vsl.civl.state.trans;

public abstract class TransientObject implements Transient {

	/**
	 * Unique ID number among all instances of this class.
	 */
	private long instanceId;

	/**
	 * Has the hash code been cached? Only possible if this instance is
	 * immutable.
	 */
	private boolean hashed = false;

	/**
	 * Is this instance mutable? If so, the static scope and variable values
	 * cannot be modified. Other fields may still be modifiable.
	 */
	protected boolean mutable = true;

	/**
	 * The cached hash code of this object. Only relevant if {@link #hashed} is
	 * <code>true</code>.
	 */
	private int hashCode = -1;

	/**
	 * The canonnic ID number of this object, or -1 if this object is not
	 * canonic.
	 */
	private int canonicId = -1;

	public TransientObject(long instanceId) {
		this.instanceId = instanceId;
	}

	protected abstract int computeHashCode();

	protected abstract boolean computeEquals(Object object);

	@Override
	public int hashCode() {
		if (!hashed) {
			// Experiment: try committing:
			commit();
			hashCode = computeHashCode();
			// if (!mutable)
			hashed = true;
		}
		return hashCode;
	}

	@Override
	public boolean equals(Object object) {
		if (this == object)
			return true;
		if (object instanceof TransientObject) {
			TransientObject that = (TransientObject) object;

			if (canonicId >= 0 && that.canonicId >= 0)
				return false;
			if (hashed && that.hashed && hashCode != that.hashCode)
				return false;
			return computeEquals(that);
		}
		return false;
	}

	@Override
	public boolean isMutable() {
		return mutable;
	}

	@Override
	public boolean isCanonic() {
		return canonicId >= 0;
	}

	@Override
	public void makeCanonic(int id) {
		assert this.canonicId == -1;
		commit();
		this.canonicId = id;
	}

	@Override
	public void commit() {
		mutable = false;
	}

	@Override
	public int getCanonicId() {
		return canonicId;
	}

	@Override
	public String identifier() {
		return canonicId + ":" + instanceId;
	}

}
