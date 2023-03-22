package tlc2.tool;

import java.util.Set;

import tlc2.Utils;

public abstract class StateVarType {
	private final String name;
	private final Set<String> rawTlcDomain;
	
	public StateVarType(final String name, final Set<String> rawTlcDomain) {
		this.name = name;
		this.rawTlcDomain = rawTlcDomain;
		Utils.assertTrue(rawTlcDomain.size() > 0, "creating state var type with empty domain!");
	}
	
	public abstract String toTlaType();
	
	public String getName() {
		return this.name;
	}
	
	public Set<String> getRawTlcDomain() {
		return this.rawTlcDomain;
	}
	
	@Override
	public boolean equals(Object o) {
		if (o instanceof StateVarType) {
			StateVarType other = (StateVarType) o;
			return this.rawTlcDomain.equals(other.rawTlcDomain);
		}
		return false;
	}
	
	@Override
	public int hashCode() {
		return this.rawTlcDomain.hashCode();
	}
	
	
	public static StateVarType createStateVarType(final String name, final Set<String> rawTlcDomain) {
		final boolean functionDomain = rawDomainIsTlaFunctions(rawTlcDomain);
		if (functionDomain) {
			return new StateVarFunctionType(name, rawTlcDomain);
		} else {
			return new StateVarBasicType(name, rawTlcDomain);
		}
	}
	
	private static boolean rawDomainIsTlaFunctions(final Set<String> rawDomain) {
		for (final String e : rawDomain) {
			if (e.contains("|->")) {
				return true;
			}
		}
		return false;
	}
}
