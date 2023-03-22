package tlc2.tool;

import java.util.HashSet;
import java.util.Set;
import java.util.regex.Pattern;

import tlc2.Utils;

public class StateVarFunctionType extends StateVarType {
	private final Set<String> rawDomain;
	private final Set<String> rawRange;
	private StateVarType domain;
	private StateVarType range;
	
	public StateVarFunctionType(final String name, final Set<String> rawTlcDomain) {
		super(name, rawTlcDomain);
		this.rawDomain = new HashSet<>();
		this.rawRange = new HashSet<>();
		extractRawDomainAndRange(rawTlcDomain, this.rawDomain, this.rawRange);
	}
	
	@Override
	public String toTlaType() {
		Utils.assertNotNull(this.domain, "domain was never set!");
		Utils.assertNotNull(this.range, "range was never set!");
		return "[" + this.domain.toTlaType() + " -> " + this.range.toTlaType() + "]";
	}
	
	public Set<String> getRawDomain() {
		return this.rawDomain;
	}
	
	public Set<String> getRawRange() {
		return this.rawRange;
	}
	
	public StateVarType getDomain() {
		return this.domain;
	}
	
	public void setDomain(final StateVarType dom) {
		this.domain = dom;
	}
	
	public StateVarType getRange() {
		return this.range;
	}
	
	public void setRange(final StateVarType rng) {
		this.range = rng;
	}
	

	private static void extractRawDomainAndRange(final Set<String> mappings, Set<String> domain, Set<String> range) {
		for (final String m : mappings) {
			final String[] parts = m.split(Pattern.quote(","));
			for (final String asg : parts) {
				final String[] kv = asg.split(Pattern.quote("|->"));
				Utils.assertTrue(kv.length == 2, "Found malformed function mapping!");
				final String domainVal = kv[0].replaceAll("[\\[\\]]", "").trim();
				final String rangeVal = kv[1].replaceAll("[\\[\\]]", "").trim();
				domain.add(domainVal);
				range.add(rangeVal);
			}
		}
	}
}
