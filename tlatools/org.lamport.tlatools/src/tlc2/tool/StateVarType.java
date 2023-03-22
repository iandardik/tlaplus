package tlc2.tool;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import tlc2.Utils;
import tlc2.Utils.Pair;

public class StateVarType {
	private String name;
	private Set<String> domain;
	
	public StateVarType(String name, Set<String> domain) {
		this.name = name;
		this.domain = domain;
	}
	
	public String getName() {
		return this.name;
	}
	
	public Set<String> getDomain() {
		return this.domain;
	}
	
	@Override
	public boolean equals(Object o) {
		if (o instanceof StateVarType) {
			StateVarType other = (StateVarType) o;
			return this.domain.equals(other.domain);
		}
		return false;
	}
	
	@Override
	public int hashCode() {
		return this.domain.hashCode();
	}

	
    public static Map<String, StateVarType> determineVarTypes(Set<EKState> stateSpace) {
    	// now that all vars are grouped by common domain, we can assign an official type
    	int typeNum = 1;
    	Map<String, StateVarType> varTypes = new HashMap<>();
    	for (Pair<Set<String>, Set<String>> dvarsPair : domainAndVarsList(stateSpace)) {
    		final String typeName = "Sort" + typeNum++;
    		Set<String> domain = dvarsPair.first;
    		Set<String> varsInType = dvarsPair.second;
    		for (String var : varsInType) {
    			varTypes.put(var, new StateVarType(typeName, domain));
    		}
    	}
    	return varTypes;
    }
    
    public static Set<StateVarType> determineTypes(Set<EKState> stateSpace) {
    	// now that all vars are grouped by common domain, we can assign an official type
    	int typeNum = 1;
    	Set<StateVarType> types = new HashSet<>();
    	for (Pair<Set<String>, Set<String>> dvarsPair : domainAndVarsList(stateSpace)) {
    		final String typeName = "Sort" + typeNum++;
    		Set<String> domain = dvarsPair.first;
    		types.add(new StateVarType(typeName, domain));
    	}
    	return types;
    }
    
	private static List< Pair<Set<String>, Set<String>> > domainAndVarsList(Set<EKState> stateSpace) {
    	// determine the domain for each state var
    	Map<String, Set<String>> varDomain = new HashMap<>();
    	for (EKState state : stateSpace) {
    		ArrayList<Pair<String,String>> stateAssignments = Utils.extractKeyValuePairsFromState(state);
    		for (Pair<String,String> assg : stateAssignments) {
    			final String var = assg.first;
    			final String val = assg.second;
    			if (!varDomain.containsKey(var)) {
    				varDomain.put(var, new HashSet<>());
    			}
    			varDomain.get(var).add(val);
    		}
    	}
    	
    	// group domains that are equal and create a "type"
    	// domainAndVars is a list of pairs of a domain and a set of variables whose type
    	// is the domain its associated with
    	List< Pair<Set<String>, Set<String>> > domainAndVars = new ArrayList<>();
    	for (String var : varDomain.keySet()) {
    		Set<String> domain = varDomain.get(var);
    		boolean domainAlreadyInList = false;
    		for (Pair<Set<String>, Set<String>> dvPair : domainAndVars) {
    			Set<String> domInList = dvPair.first;
    			if (domain.equals(domInList)) {
    				dvPair.second.add(var);
    				domainAlreadyInList = true;
    				break;
    			}
    		}
    		if (!domainAlreadyInList) {
    			Set<String> setOfVar = new HashSet<>();
    			setOfVar.add(var);
    			domainAndVars.add(new Pair<>(domain, setOfVar));
    		}
    	}
    	
    	return domainAndVars;
	}
}
