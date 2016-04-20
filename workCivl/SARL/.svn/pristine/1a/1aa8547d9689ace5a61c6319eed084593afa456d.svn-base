package edu.udel.cis.vsl.sarl.config.common;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

import edu.udel.cis.vsl.sarl.IF.SARLException;
import edu.udel.cis.vsl.sarl.IF.config.ProverInfo;
import edu.udel.cis.vsl.sarl.IF.config.ProverInfo.ProverKind;
import edu.udel.cis.vsl.sarl.IF.config.SARLConfig;

/**
 * An implementation of {@link SARLConfig} using an array for the
 * {@link ProverInfo}s as well as a map from the prover names to the
 * {@link ProverInfo}s for fast lookup.
 * 
 * @author siegel
 *
 */
public class CommonSARLConfig implements SARLConfig {

	private ProverInfo[] provers;

	private Map<String, ProverInfo> aliasMap = new LinkedHashMap<>();

	public CommonSARLConfig(Collection<ProverInfo> provers) {
		int size = provers.size();
		int count = 0;

		this.provers = new ProverInfo[size];
		for (ProverInfo prover : provers) {
			this.provers[count] = prover;
			count++;
			for (String alias : prover.getAliases()) {
				ProverInfo old = aliasMap.put(alias, prover);

				if (old != null)
					throw new SARLException("Alias " + alias
							+ " used more than once:\n" + old + "\n" + prover);
			}
		}
	}

	@Override
	public int getNumProvers() {
		return provers.length;
	}

	@Override
	public ProverInfo getProver(int index) {
		return provers[index];
	}

	@Override
	public Iterable<ProverInfo> getProvers() {
		return Arrays.asList(provers);
	}

	@Override
	public ProverInfo getProverWithAlias(String alias) {
		return aliasMap.get(alias);
	}

	@Override
	public ProverInfo getProverWithKind(ProverKind kind) {
		for (ProverInfo prover : provers) {
			if (prover.getKind() == kind)
				return prover;
		}
		return null;
	}

}
