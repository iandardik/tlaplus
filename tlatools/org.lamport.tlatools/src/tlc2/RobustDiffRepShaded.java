package tlc2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import tlc2.RobustDiffRep.SpecScope;
import tlc2.tool.ExtKripke;
import tlc2.tool.StateVarType;
import tlc2.tool.TLCState;
import tlc2.tool.ExtKripke.Pair;


public class RobustDiffRepShaded {
	private static final String DIFF_REP_FILE = "diff_rep_file";
	private static final String DIFF_REP_FILE1 = "diff_rep_file1";
	private static final String DIFF_REP_FILE2 = "diff_rep_file2";
	
	private static final String CONST_VALUE_CONSTRAINT = "const_value_constraint";
	private static final String CONST_VALUE_CONSTRAINT1 = "const_value_constraint1";
	private static final String CONST_VALUE_CONSTRAINT2 = "const_value_constraint2";
	
	private static final String SEPARATOR_FILE = "separator_file";
	private static final String SEPARATOR1_FILE = "separator1_file";
	private static final String SEPARATOR2_FILE = "separator2_file";
	
	private static final String DIFF_REP_STATES_EMPTY = "diff_rep_states_empty";
	private static final String DIFF_REP_STATES1_EMPTY = "diff_rep_states1_empty";
	private static final String DIFF_REP_STATES2_EMPTY = "diff_rep_states2_empty";
	
	private static final String GROUP_NAMES = "group_names";
	private static final String GROUP_NAMES1 = "group_names1";
	private static final String GROUP_NAMES2 = "group_names2";

	private static final String SORTS_MAP_FILE = "sorts_map_file";
	private static final String SORTS_MAP1_FILE = "sorts_map_file1";
	private static final String SORTS_MAP2_FILE = "sorts_map_file2";

	private static final String TRUE = "true";
	private static final String FALSE = "false";
	
	private static final String NEW_LINE = "\n";
	private static final String UNDERSCORE = "_";
	private static final String DIFF_REP = "diff_rep";
	private static final String DOT_TXT = ".txt";
	
	
	private final String specName;
	private final SpecScope specScope;
	private final String outputLocation;
	private final Set<String> safetyShaded;
	private final Map<String, Set<String>> shadedByGroup;
	private Map<String, String> jsonStrs;
	private Map<String, List<String>> jsonLists;
	
	public RobustDiffRepShaded(String specName, tlc2.RobustDiffRep.SpecScope spec, String outputLoc, Set<String> safetyShaded, Map<String, Set<String>> shadedByGroup,
			Map<String,String> jsonStrs, Map<String, List<String>> jsonLists) {
		this.specName = specName;
		this.specScope = spec;
		this.safetyShaded = safetyShaded;
		this.shadedByGroup = shadedByGroup;
		this.outputLocation = outputLoc;
		this.jsonStrs = jsonStrs;
		this.jsonLists = jsonLists;
		
    	final String groupNamesKey = RobustDiffRep.keyForSpecScope(specScope, GROUP_NAMES, GROUP_NAMES1, GROUP_NAMES2);
    	this.jsonLists.put(groupNamesKey, new ArrayList<>(this.shadedByGroup.keySet()));

    	final String diffRepEmptyKey = RobustDiffRep.keyForSpecScope(specScope, DIFF_REP_STATES_EMPTY, DIFF_REP_STATES1_EMPTY, DIFF_REP_STATES2_EMPTY);
    	this.jsonStrs.put(diffRepEmptyKey, this.safetyShaded.size() > 0 ? FALSE : TRUE);
	}
	
	public void writeShaded() {
		final String fileKeyBase = RobustDiffRep.keyForSpecScope(specScope, DIFF_REP_FILE, DIFF_REP_FILE1, DIFF_REP_FILE2);
		for (final String groupName : this.shadedByGroup.keySet()) {
			final Set<String> group = this.shadedByGroup.get(groupName);
			final String fileName = this.specName + UNDERSCORE + groupName + UNDERSCORE + DIFF_REP + DOT_TXT;
			final String filePath = this.outputLocation + fileName;
			final String diffRepFileNameKey = fileKeyBase + UNDERSCORE + groupName;
	    	final String output = String.join(NEW_LINE, group);
	    	Utils.writeFile(filePath, output);
	    	this.jsonStrs.put(diffRepFileNameKey, filePath);
		}
	}
	
	public void writeShadedFOLSeparatorFile(final ExtKripke kripke, final TLC tlcTypeOK) {
		for (final String groupName : this.shadedByGroup.keySet()) {
			final Set<String> group = this.shadedByGroup.get(groupName);
			createDiffStateRepFormula(group, kripke, tlcTypeOK, groupName);
		}
	}
	
	private void createDiffStateRepFormula(final Set<String> posExamples, final ExtKripke kripke, final TLC tlcTypeOK, final String groupName) {
    	final ExtKripke stateSpaceKripke = tlcTypeOK.getKripke();
    	final Set<TLCState> stateSpace = stateSpaceKripke.reach();
    	final Set<String> stateSpaceStrs = Utils.stateSetToStringSet(stateSpace);

    	// diffRepStateStrs is the set of positive examples
    	// the neg examples are any bad states or any env states
    	// TODO technically this isn't good enough; we need to consider bad states outside of reach (kripke.badStates()
    	// only returns bad states in reach). for now this will work, but the FOL sep tool may infer an incorrect formula.
    	//final Set<String> negExamples = ExtKripke.union(Utils.stateSetToStringSet(kripke.badStates()), Utils.stateSetToStringSet(kripke.envStates()));
    	final Set<String> negExamples = ExtKripke.setMinus(Utils.stateSetToStringSet(kripke.reach()), posExamples);
    	
    	// we can automatically extract types by looking at the states in stateSpace.
    	// there is no need to examine TypeOK
    	// type domains should be mutually exclusive; we issue a warning if they aren't
    	// TODO it would be a nice sanity check to make sure the vars in varTypes match those in tlc1 and tlc2
    	final Map<String, StateVarType> varTypes = StateVarType.determineVarTypes(stateSpaceStrs);
    	domainsAreMutuallyExclusiveCheck(varTypes);
    	
    	// in the posExamples, figure out which state vars may have multiple values.
    	// we will then leverage the FOL separator tool to create a formula that describes these values.
    	// we abuse the word "type" in StateVarType here.
    	final Map<String, StateVarType> posExampleVarDomains = StateVarType.determineVarTypes(posExamples);
    	Set<StateVarType> nonConstValueTypes = new HashSet<>();
    	Set<String> nonConstValueVars = new HashSet<>();
    	Set<String> constValueVars = new HashSet<>();
    	Map<String, String> constValueValues = new HashMap<>();
    	determineConstAndNonConstVars(posExampleVarDomains, varTypes, nonConstValueTypes, nonConstValueVars, constValueVars, constValueValues);
    	
    	// translate (TLA+ state var values) -> (FOL Separator constants)
    	final Map<String,String> valueToConstantMap = tlaValueToSeparatorConstant(nonConstValueTypes);
    	
    	if (constValueVars.size() > 0) {
    		final String constValueConstraintKeyBase = RobustDiffRep.keyForSpecScope(specScope, CONST_VALUE_CONSTRAINT, CONST_VALUE_CONSTRAINT1, CONST_VALUE_CONSTRAINT2);
    		final String constValueConstraintKey = constValueConstraintKeyBase + UNDERSCORE + groupName;
    		final String constValueConstraint = buildConstValueConstraint(constValueVars, constValueValues, this.jsonStrs);
            this.jsonStrs.put(constValueConstraintKey, constValueConstraint);
    	}
    	if (nonConstValueVars.size() > 0) {
    		final String separatorFileKeyBase = RobustDiffRep.keyForSpecScope(specScope, SEPARATOR_FILE, SEPARATOR1_FILE, SEPARATOR2_FILE);
    		final String sortsMapFileKeyBase = RobustDiffRep.keyForSpecScope(specScope, SORTS_MAP_FILE, SORTS_MAP1_FILE, SORTS_MAP2_FILE);
    		final String separatorFileKey = separatorFileKeyBase + UNDERSCORE + groupName;
    		final String sortsMapFileKey = sortsMapFileKeyBase + UNDERSCORE + groupName;
        	final String separatorFile = buildAndWriteSeparatorFOL(posExamples, negExamples, varTypes, nonConstValueVars, nonConstValueTypes,
        			valueToConstantMap, this.specName, groupName, this.outputLocation);
        	final String sortsMapFile = writeSortsMap(nonConstValueTypes, this.specName, groupName, this.outputLocation);
        	this.jsonStrs.put(separatorFileKey, separatorFile);
        	this.jsonStrs.put(sortsMapFileKey, sortsMapFile);
    	}
    }
	
	
	/* Static helper methods */
	
	private static void domainsAreMutuallyExclusiveCheck(final Map<String, StateVarType> varTypes) {
		final List<StateVarType> types = new ArrayList<>(varTypes.values());
		for (int i = 0; i < types.size(); ++i) {
			for (int j = i+1; j < types.size(); ++j) {
				final StateVarType iType = types.get(i);
				final StateVarType jType = types.get(j);
				final boolean differentTypeNames = !iType.getName().equals(jType.getName());
				if (differentTypeNames && !ExtKripke.intersection(iType.getDomain(), jType.getDomain()).isEmpty()) {
					System.err.println("Warning: domains intersect for types " + iType.getName() + " and " + jType.getName());
				}
			}
		}
	}
    
    private static String writeSortsMap(final Set<StateVarType> nonConstValueTypes, final String specName, final String groupName, final String outputLoc) {
    	List<String> mappings = new ArrayList<>();
    	for (StateVarType type : nonConstValueTypes) {
    		final String name = "\"" + type.getName() + "\"";
    		final String domain = "{" + String.join(",", type.getDomain()) + "}";
    		final String mapping = name + ":\"" + Utils.stringEscape(domain) + "\"";
    		mappings.add(mapping);
    	}
    	final String map = "{" + String.join(",", mappings) + "}";
    	
    	final String sortsMapFile = specName + UNDERSCORE + groupName + "_sorts_map.json";
    	final String path = outputLoc + sortsMapFile;
    	Utils.writeFile(path, map);
        return path;
    }
    
    private static String buildAndWriteSeparatorFOL(final Set<String> posExamples, final Set<String> negExamples, final Map<String, StateVarType> varTypes,
    		final Set<String> nonConstValueVars, final Set<StateVarType> nonConstValueTypes, final Map<String,String> valueToConstantMap,
    		final String specName, final String groupName, final String outputLoc) {
    	Set<String> consts = new HashSet<>();
    	Set<String> modelElements = new HashSet<>();
    	Set<String> modelElementDefs = new HashSet<>();
    	for (StateVarType type : nonConstValueTypes) {
    		final String typeName = type.getName();
    		for (String e : type.getDomain()) {
    			assert(valueToConstantMap.containsKey(e));
    			final String elem = valueToConstantMap.get(e);
    			final String elemConst = "e" + elem + "Const";
    	    	consts.add("(constant " + elem + " " + typeName + ")");
    	    	modelElements.add("(" + elemConst + " " + typeName + ")");
    	    	modelElementDefs.add("(= " + elem + " " + elemConst + ")");
    		}
    	}
    	Set<String> sorts = new HashSet<>();
    	for (StateVarType type : nonConstValueTypes) {
    		sorts.add("(sort " + type.getName() + ")");
    	}
    	
    	
    	// create FOL separator file
    	StringBuilder builder = new StringBuilder();
    	
    	// types (sorts)
    	builder.append(String.join("\n", sorts));
    	builder.append("\n\n");
    	
    	// state variables (relations)
    	for (String var : nonConstValueVars) {
    		StateVarType type = varTypes.get(var);
    		builder.append("(relation " + var + " " + type.getName() + ")\n");
    	}
    	builder.append("\n");
    	
    	// constants
    	builder.append(String.join("\n", consts));
    	builder.append("\n\n");
    	
    	// models
    	Set<String> posModels = new HashSet<>();
    	for (String s : posExamples) {
    		final String pos = toSeparatorModel(s, "+", modelElements, modelElementDefs, nonConstValueVars, valueToConstantMap);
    		posModels.add(pos);
    		builder.append(pos);
    	}
    	for (String s : negExamples) {
    		final String neg = toSeparatorModel(s, "-", modelElements, modelElementDefs, nonConstValueVars, valueToConstantMap);
    		if (!posModels.contains(neg.replace('-', '+'))) {
    			builder.append(neg);
    		}
    	}
    	
    	final String separatorFile = specName + UNDERSCORE + groupName + ".fol";
    	final String path = outputLoc + separatorFile;
    	Utils.writeFile(path, builder.toString());
        return path;
    }

    private static String buildConstValueConstraint(final Set<String> constValueVars, final Map<String, String> constValueValues, Map<String,String> jsonOutput) {
        Set<String> constraints = new HashSet<>();
        for (String var : constValueVars) {
        	final String val = constValueValues.get(var);
        	final String constraint = var + " = " + val;
        	constraints.add(constraint);
        }
        final String constValueConstraint = String.join(", ", constraints);
        return Utils.stringEscape(constValueConstraint);
    }
    
    private static void determineConstAndNonConstVars(final Map<String, StateVarType> diffStateVarDomains, final Map<String, StateVarType> varTypes,
    		Set<StateVarType> nonConstValueTypes, Set<String> nonConstValueVars, Set<String> constValueVars, Map<String, String> constValueValues) {
    	for (String var : diffStateVarDomains.keySet()) {
    		StateVarType t = diffStateVarDomains.get(var);
    		assert(t.getDomain().size() > 0);
    		if (t.getDomain().size() == 1) {
    			final String exactValue = ExtKripke.singletonGetElement(t.getDomain());
    			constValueVars.add(var);
    			constValueValues.put(var, exactValue);
    		} else {
    			if (varTypes.containsKey(var)) {
	    			StateVarType varType = varTypes.get(var);
	    			nonConstValueVars.add(var);
	    			nonConstValueTypes.add(varType);
    			}
                else {
                    System.err.println("Warning! TypeOK does not describe all state variables!");
                }
    		}
    	}
    }
    
    private static String toSeparatorModel(final String tlaState, final String label, final Set<String> modelElements,
    		final Set<String> modelElementDefs, final Set<String> nonConstValueVars, final Map<String,String> valueToConstantMap) {
    	final String sms = toSeparatorModelString(tlaState, nonConstValueVars, valueToConstantMap);
    	final String elementsStr = String.join(" ", modelElements);
    	
        StringBuilder builder = new StringBuilder();
    	builder.append("(model ").append(label).append("\n");
    	builder.append("    (");
    	builder.append(elementsStr);
    	builder.append(")\n");
    	for (String elemDef : modelElementDefs) {
        	builder.append("    " + elemDef + "\n");
    	}
    	builder.append(sms);
    	builder.append("\n)\n");
        return builder.toString();
    }
    
    private static String toSeparatorModelString(final String tlaState, final Set<String> nonConstValueVars, final Map<String,String> valueToConstantMap) {
    	ArrayList<String> separatorConjuncts = new ArrayList<>();
    	ArrayList<Pair<String,String>> stateAssignments = Utils.extractKeyValuePairsFromState(tlaState);
    	for (Pair<String,String> assg : stateAssignments) {
    		final String var = assg.first;
    		if (nonConstValueVars.contains(var)) {
    			assert(valueToConstantMap.containsKey(assg.second));
        		final String val = "e" + valueToConstantMap.get(assg.second) + "Const";
        		final String sepConjunct = "    (" + var + " " + val + ")";
        		separatorConjuncts.add(sepConjunct);
    		}
    	}
		return String.join("\n", separatorConjuncts);
    }
    
    // translate (TLA+ state var values) -> (FOL Separator constants)
    private static Map<String,String> tlaValueToSeparatorConstant(Set<StateVarType> types) {
    	Map<String,String> map = new HashMap<>();
    	for (StateVarType type : types) {
    		for (String tlaVarValue : type.getDomain()) {
    			final String folSepConstant = toSeparatorString(tlaVarValue);
    			map.put(tlaVarValue, folSepConstant);
    		}
    	}
    	return map;
    }
    
    private static String toSeparatorString(String str) {
    	return str
    			.replaceAll("[\\s]", "Ss_sS")
    			.replaceAll("[\"]", "Qq_qQ")
    			.replaceAll("[{]", "Lp_pL")
    			.replaceAll("[}]", "Rp_pR");
    }
}
