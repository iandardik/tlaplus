package tlc2.tool;

import java.util.Set;

public class StateVarBasicType extends StateVarType {
	private final Set<String> domain;
	
	public StateVarBasicType(final String name, final Set<String> domain) {
		super(name, domain);
		this.domain = domain;
	}
	
	public Set<String> getDomain() {
		return this.domain;
	}
	
	@Override
	public String toTlaType() {
		return "{" + String.join(",", this.domain) + "}";
	}
}
