package tlc2;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.regex.Pattern;

import tlc2.tool.Action;
import tlc2.tool.ExtKripke;
import tlc2.tool.StateVarType;
import tlc2.tool.TLCState;
import tlc2.tool.ExtKripke.Pair;
import tlc2.tool.impl.FastTool;

public class Robustness {

	
	private static final String COMPARISON_TYPE = "comparison_type";
	private static final String SPEC_TO_PROPERTY = "spec_to_property";
	private static final String SPEC_TO_SPEC = "spec_to_spec";
	
	private static final String DIFF_REP_FILE = "diff_rep_file";
	private static final String DIFF_REP_FILE1 = "diff_rep_file1";
	private static final String DIFF_REP_FILE2 = "diff_rep_file2";
	private static final String CONST_VALUE_CONSTRAINT = "const_value_constraint";
	private static final String CONST_VALUE_CONSTRAINT1 = "const_value_constraint1";
	private static final String CONST_VALUE_CONSTRAINT2 = "const_value_constraint2";
	private static final String SEPARATOR_FILE = "separator_file";
	private static final String SEPARATOR1_FILE = "separator1_file";
	private static final String SEPARATOR2_FILE = "separator2_file";
	private static final String SPEC_NAME = "spec_name";
	private static final String SPEC1_NAME = "spec1_name";
	private static final String SPEC2_NAME = "spec2_name";
	
	private static final String COMBINED_ERR_PRE_TLA = "combined_err_pre_tla";
	private static final String COMBINED_ERR_POST_TLA = "combined_err_post_tla";
	private static final String SPEC1_SAT_SPEC2_CFG = "spec1_sat_spec2_cfg";
	private static final String SPEC2_SAT_SPEC1_CFG = "spec2_sat_spec1_cfg";
	
	private static final String DIFF_REP_STATES_EMPTY = "diff_rep_states_empty";
	private static final String DIFF_REP_STATES1_EMPTY = "diff_rep_states1_empty";
	private static final String DIFF_REP_STATES2_EMPTY = "diff_rep_states2_empty";
	private static final String SPEC_IS_SAFE = "spec_is_safe";
	private static final String SPEC1_IS_SAFE = "spec1_is_safe";
	private static final String SPEC2_IS_SAFE = "spec2_is_safe";
	private static final String TRUE = "true";
	private static final String FALSE = "false";

	private static final String SORTS_MAP_FILE = "sorts_map_file";
	private static final String SORTS_MAP1_FILE = "sorts_map_file1";
	private static final String SORTS_MAP2_FILE = "sorts_map_file2";
	
	private static final String DIFF_REP_STATE_FORMULA_ERROR = "diff_rep_state_formula_error";
	private static final String MISSING_TYPEOK = "missing_typeok";
	private static final String MISSING_BOTH_TYPEOKS = "missing_both_typeoks";
	
	private enum SpecScope {
		Spec, Spec1, Spec2
	}
	
	private static String keyForSpecScope(SpecScope scope, String key, String key1, String key2) {
		switch (scope) {
		case Spec:
			return key;
		case Spec1:
			return key1;
		case Spec2:
			return key2;
		}
		throw new RuntimeException("Invalid SpecScope provided");
	}
	
	
	/*
	 * We compute whether \eta(spec1,P) \subseteq \eta(spec2,P)
	 */
    public static void calc(String[] args) {
    	// TODO add functionality for compareSpecToEnvironment
    	Map<String,String> jsonOutput = new HashMap<>();
    	if (args.length == 3) {
    		compareSpecToProperty(args, jsonOutput);
    	}
    	else if (args.length == 5) {
    		compareSpecs(args, jsonOutput);
    	}
    	else {
    		System.out.println("usage: tlc-ian <output_loc> <spec1> <cfg1> [<spec2> <cfg2>]");
    	}
    	System.out.println(Utils.asJson(jsonOutput));
    	System.exit(0);
    }
    
    // M_err_rep: states that are in (M_err \cap P) but MAY leave P in one step
    private static void compareSpecToProperty(String[] args, Map<String,String> jsonOutput) {
    	final String outputLoc = args[0] + "/";
    	final String tla = args[1];
    	final String cfg = args[2];
    	
    	// initialize and run TLC
    	TLC tlc = new TLC();
    	TLC.runTLC(tla, cfg, tlc);

    	jsonOutput.put(COMPARISON_TYPE, SPEC_TO_PROPERTY);
    	jsonOutput.put(SPEC_NAME, tlc.getSpecName());
    	
    	// compute the representation for beh(P) - \eta(spec,P)
    	computePropertyDiffRep(tla, tlc, outputLoc, jsonOutput);
    }
    
    private static void compareSpecToEnvironment(String[] args, Map<String,String> jsonOutput) {
    	// TODO
    	// M_err_rep: states that are in (M_err \cap E) but MAY leave E in one step
    }
    
    private static void compareSpecs(String[] args, Map<String,String> jsonOutput) {
    	final String outputLoc = args[0] + "/";
    	final String tla1 = args[1];
    	final String cfg1 = args[2];
    	final String tla2 = args[3];
    	final String cfg2 = args[4];
    	assert(!tla1.equals(tla2));
    	
    	// initialize and run TLC
    	TLC tlc1 = new TLC();
    	TLC tlc2 = new TLC();
    	TLC.runTLC(tla1, cfg1, tlc1);
    	TLC.runTLC(tla2, cfg2, tlc2);
    	
    	jsonOutput.put(COMPARISON_TYPE, SPEC_TO_SPEC);
    	jsonOutput.put(SPEC1_NAME, tlc1.getSpecName());
    	jsonOutput.put(SPEC2_NAME, tlc2.getSpecName());
    	jsonOutput.put(SPEC1_IS_SAFE, tlc1.getKripke().isSafe() ? TRUE : FALSE);
    	jsonOutput.put(SPEC2_IS_SAFE, tlc2.getKripke().isSafe() ? TRUE : FALSE);
    	
    	// create err pre/post TLA+ specs
    	createErrPre(tlc1, tlc2, tla1, tla2, cfg1, cfg2, outputLoc, jsonOutput);
    	createErrPost(tlc1, tlc2, tla1, tla2, cfg1, cfg2, outputLoc, jsonOutput);
    	
    	// create the cfgs for comparing the pre/post specs
    	final String spec1SatSpec2Cfg = specSatConfig("Spec1", "Spec2", outputLoc);
    	final String spec2SatSpec1Cfg = specSatConfig("Spec2", "Spec1", outputLoc);
    	jsonOutput.put(SPEC1_SAT_SPEC2_CFG, spec1SatSpec2Cfg);
    	jsonOutput.put(SPEC2_SAT_SPEC1_CFG, spec2SatSpec1Cfg);
    	
    	// compute the representation for \eta(spec2,P) - \eta(spec1,P)
    	// and \eta(spec1,P) - \eta(spec2,P)
    	computeDiffRep(tlc1, tlc2, outputLoc, jsonOutput);
    }
    
    private static void computePropertyDiffRep(final String tlaFile, final TLC tlc, final String outputLoc, Map<String,String> jsonOutput) {
    	final String fileName = "safety_boundary_representation";
    	ExtKripke kripke = tlc.getKripke();
    	Set<TLCState> safetyBoundary = kripke.safetyBoundary();
    	Set<String> safetyBoundaryStrs = Utils.stateSetToStringSet(safetyBoundary);
    	writeDiffRepStatesToFile(safetyBoundaryStrs, fileName, outputLoc, SpecScope.Spec, jsonOutput);
    	createDiffStateRepFormula(safetyBoundaryStrs, tlaFile, tlc, tlc.getSpecName(), outputLoc, jsonOutput);
    	jsonOutput.put(SPEC_IS_SAFE, kripke.isSafe() ? TRUE : FALSE);
    }
    
    private static void computeDiffRep(final TLC tlc1, final TLC tlc2, final String outputLoc, Map<String,String> jsonOutput) {
    	ExtKripke errPre1 = tlc1.getKripke().createErrPre();
    	ExtKripke errPre2 = tlc2.getKripke().createErrPre();
    	ExtKripke errPost1 = tlc1.getKripke().createErrPost();
    	ExtKripke errPost2 = tlc2.getKripke().createErrPost();
    	
    	if (errPre1.isEmpty() && errPre2.isEmpty()) {
        	jsonOutput.put(SPEC1_IS_SAFE, TRUE);
        	jsonOutput.put(SPEC2_IS_SAFE, TRUE);
    		//System.out.println("Both specs are maximally robust.");
    	}
    	else if (errPre1.isEmpty()) {
        	jsonOutput.put(SPEC1_IS_SAFE, TRUE);
        	jsonOutput.put(SPEC2_IS_SAFE, FALSE);
    		//System.out.println("Spec 1 is maximally robust (M1_err is empty).");
    	}
    	else if (errPre2.isEmpty()) {
        	jsonOutput.put(SPEC1_IS_SAFE, FALSE);
        	jsonOutput.put(SPEC2_IS_SAFE, TRUE);
    		//System.out.println("Spec 2 is maximally robust (M2_err is empty).");
    	}
    	else {
    		// compute \eta1-\eta2 and \eta2-\eta1
    		final String spec1 = tlc1.getSpecName();
    		final String spec2 = tlc2.getSpecName();
        	final String diffRepStatesFileName1 = "diff_rep_" + spec1;
        	final String diffRepStatesFileName2 = "diff_rep_" + spec2;
    		computeDiffRepWrtOneSpec(errPre2, errPost2, errPre1, errPost1, tlc1, tlc2, diffRepStatesFileName1, spec1, outputLoc, SpecScope.Spec1, jsonOutput);
    		computeDiffRepWrtOneSpec(errPre1, errPost1, errPre2, errPost2, tlc2, tlc1, diffRepStatesFileName2, spec2, outputLoc, SpecScope.Spec2, jsonOutput);
    	}
    }

	// compute the diff rep, i.e. the states that represent \eta2 - \eta1
    private static void computeDiffRepWrtOneSpec(final ExtKripke errPre1, final ExtKripke errPost1, final ExtKripke errPre2, final ExtKripke errPost2,
    		final TLC tlc1, final TLC tlc2, final String diffRepStatesFileName, final String refSpec, final String outputLoc,
    		final SpecScope specScope, Map<String,String> jsonOutput) {
    	final String diffRepStateEmptyKey = keyForSpecScope(specScope, DIFF_REP_STATES_EMPTY, DIFF_REP_STATES1_EMPTY, DIFF_REP_STATES2_EMPTY);
    	Set<Pair<TLCState,Action>> diffRep = ExtKripke.union(
    			ExtKripke.behaviorDifferenceRepresentation(errPre1, errPre2),
    			ExtKripke.behaviorDifferenceRepresentation(errPost1, errPost2));
    	if (diffRep.size() > 0) {
        	// the two specs have overlapping error traces / state space so we compare them
        	Set<TLCState> diffRepStates = ExtKripke.projectFirst(diffRep);
        	Set<String> diffRepStateStrs = Utils.stateSetToStringSet(diffRepStates);
        	writeDiffRepStatesToFile(diffRepStateStrs, diffRepStatesFileName, outputLoc, specScope, jsonOutput);
        	createDiffStateRepFormula(diffRepStateStrs, tlc1, tlc2, refSpec, outputLoc, specScope, jsonOutput);
        	jsonOutput.put(diffRepStateEmptyKey, FALSE);
    	}
    	else {
    		//System.out.println("\\eta_2 - \\eta_1 = beh(M1_err) - beh(M2_err) = {}  (the diff rep is empty)");
        	jsonOutput.put(diffRepStateEmptyKey, TRUE);
    	}
    }
    
    private static void writeDiffRepStatesToFile(final Set<String> diffRepStateStrs, final String name, final String outputLoc,
    		final SpecScope specScope, Map<String,String> jsonOutput) {
    	final String diffRepFileNameKey = keyForSpecScope(specScope, DIFF_REP_FILE, DIFF_REP_FILE1, DIFF_REP_FILE2);
    	writeDiffRepStatesToFile(diffRepStateStrs, name, diffRepFileNameKey, outputLoc, jsonOutput);
    }
    
    private static void writeDiffRepStatesToFile(final Set<String> diffRepStateStrs, final String name, final String diffRepFileNameKey,
    		final String outputLoc, Map<String,String> jsonOutput) {
    	StringBuilder builder = new StringBuilder();
    	for (String diffState : diffRepStateStrs) {
    		builder.append(diffState).append("\n");
    	}
    	final String file = outputLoc + name + ".txt";
    	Utils.writeFile(file, builder.toString());
    	jsonOutput.put(diffRepFileNameKey, file);
    }
    
    private static void createDiffStateRepFormula(final Set<String> diffRepStateStrs, final String tlaFile, final TLC tlc, final String refSpec,
    		final String outputLoc, Map<String,String> jsonOutput) {
    	// a TypeOK is required to gather the info we need to create a sep.fol file
    	final String typeOKInv = "TypeOK";
    	final boolean hasTypeOK = tlc.hasInvariant(typeOKInv);
    	if (hasTypeOK) {
        	// compute the entire state space
        	final TLC tlcTypeOK = new TLC();
        	runTLCExtractStateSpace(tlaFile, tlc, outputLoc, tlcTypeOK);
        	createDiffStateRepFormula(diffRepStateStrs, tlcTypeOK, refSpec, outputLoc, SpecScope.Spec, jsonOutput);
    	}
    	else {
        	jsonOutput.put(DIFF_REP_STATE_FORMULA_ERROR, MISSING_TYPEOK);
    	}
    }
    
    private static void createDiffStateRepFormula(final Set<String> diffRepStateStrs, final TLC tlc1, final TLC tlc2, final String refSpec,
    		final String outputLoc, final SpecScope specScope, Map<String,String> jsonOutput) {
    	// a TypeOK is required to gather the info we need to create a sep.fol file
    	final String typeOKInv = "TypeOK";
    	final boolean bothHaveTypeOK = tlc1.hasInvariant(typeOKInv) && tlc2.hasInvariant(typeOKInv);
    	if (bothHaveTypeOK) {
        	// compute the entire state space
        	final TLC tlcTypeOK = new TLC();
        	runTLCExtractStateSpace(tlc1, tlc2, outputLoc, tlcTypeOK);
        	createDiffStateRepFormula(diffRepStateStrs, tlcTypeOK, refSpec, outputLoc, specScope, jsonOutput);
    	}
    	else {
        	jsonOutput.put(DIFF_REP_STATE_FORMULA_ERROR, MISSING_BOTH_TYPEOKS);
    	}
    }
    
    private static void createDiffStateRepFormula(final Set<String> posExamples, final TLC tlcTypeOK, final String refSpec,
    		final String outputLoc, final SpecScope specScope, Map<String,String> jsonOutput) {
    	final ExtKripke stateSpaceKripke = tlcTypeOK.getKripke();
    	final Set<TLCState> stateSpace = stateSpaceKripke.reach();
    	final Set<String> stateSpaceStrs = Utils.stateSetToStringSet(stateSpace);

    	// diffRepStateStrs is the set of positive examples
    	// notDiffStateStrs is the set of negative examples
    	final Set<String> negExamples = ExtKripke.setMinus(stateSpaceStrs, posExamples);
    	
    	// we can automatically extract types by looking at the states in stateSpace.
    	// there is no need to examine TypeOK
    	// TODO it would be a nice sanity check to make sure the vars in varTypes match those in tlc1 and tlc2
    	// TODO type domains should be mutually exclusive, we need to bail if they aren't
    	final Map<String, StateVarType> varTypes = StateVarType.determineVarTypes(stateSpaceStrs);
    	
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
    		final String constValueConstraintKey = keyForSpecScope(specScope, CONST_VALUE_CONSTRAINT, CONST_VALUE_CONSTRAINT1, CONST_VALUE_CONSTRAINT2);
    		final String constValueConstraint = buildConstValueConstraint(constValueVars, constValueValues, jsonOutput);
            jsonOutput.put(constValueConstraintKey, constValueConstraint);
    	}
    	if (nonConstValueVars.size() > 0) {
    		final String separatorFileKey = keyForSpecScope(specScope, SEPARATOR_FILE, SEPARATOR1_FILE, SEPARATOR2_FILE);
    		final String sortsMapFileKey = keyForSpecScope(specScope, SORTS_MAP_FILE, SORTS_MAP1_FILE, SORTS_MAP2_FILE);
        	final String separatorFile = buildAndWriteSeparatorFOL(posExamples, negExamples, varTypes, nonConstValueVars, nonConstValueTypes,
        			valueToConstantMap, refSpec, outputLoc);
        	final String sortsMapFile = writeSortsMap(nonConstValueTypes, refSpec, outputLoc);
            jsonOutput.put(separatorFileKey, separatorFile);
            jsonOutput.put(sortsMapFileKey, sortsMapFile);
    	}
    }
    
    private static String writeSortsMap(final Set<StateVarType> nonConstValueTypes, final String specName, final String outputLoc) {
    	List<String> mappings = new ArrayList<>();
    	for (StateVarType type : nonConstValueTypes) {
    		final String name = "\"" + type.getName() + "\"";
    		final String domain = "{" + String.join(",", type.getDomain()) + "}";
    		final String mapping = name + ":\"" + Utils.stringEscape(domain) + "\"";
    		mappings.add(mapping);
    	}
    	final String map = "{" + String.join(",", mappings) + "}";
    	
    	final String sortsMapFile = specName + "_sorts_map.json";
    	final String path = outputLoc + sortsMapFile;
    	Utils.writeFile(path, map);
        return path;
    }
    
    private static String buildAndWriteSeparatorFOL(final Set<String> posExamples, final Set<String> negExamples, final Map<String, StateVarType> varTypes,
    		final Set<String> nonConstValueVars, final Set<StateVarType> nonConstValueTypes, final Map<String,String> valueToConstantMap,
    		final String specName, final String outputLoc) {
    	Set<String> consts = new HashSet<>();
    	Set<String> modelElements = new HashSet<>();
    	Set<String> modelElementDefs = new HashSet<>();
    	for (StateVarType type : nonConstValueTypes) {
    		final String typeName = type.getName();
    		for (String e : type.getDomain()) {
    			assert(valueToConstantMap.containsKey(e));
    			final String elem = valueToConstantMap.get(e);
    	    	consts.add("(constant " + elem + " " + typeName + ")");
    	    	modelElements.add("(" + elem + "Const " + typeName + ")");
    	    	modelElementDefs.add("(= " + elem + " " + elem + "Const)");
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
    	
    	final String separatorFile = specName + ".fol";
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
    			StateVarType varType = varTypes.get(var);
    			nonConstValueVars.add(var);
    			nonConstValueTypes.add(varType);
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
        		final String val = valueToConstantMap.get(assg.second) + "Const";
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
	
    private static void createErrPre(final TLC tlc1, final TLC tlc2, final String tla1, final String tla2, final String cfg1, final String cfg2,
    		final String outputLoc, Map<String,String> jsonOutput) {
    	// collect state variables from each spec
    	Set<String> vars1 = new HashSet<String>();
    	Set<String> vars2 = new HashSet<String>();
    	
    	// create one err pre file for each spec, then combine them into a single one for comparison
    	final String tag = "ErrPre";
    	final String specName1 = createErrPre(tag, tlc1, tla1, cfg1, vars1, outputLoc, jsonOutput);
    	final String specName2 = createErrPre(tag, tlc2, tla2, cfg2, vars2, outputLoc, jsonOutput);
    	final String combineSpecName = combineSpec(tag, specName1, specName2, vars1, vars2, outputLoc);
        jsonOutput.put(COMBINED_ERR_PRE_TLA, combineSpecName);
    }
    
    private static String createErrPre(final String tag, final TLC tlc, final String tla, final String cfg, Set<String> vars,
    		final String outputLoc, Map<String,String> jsonOutput) {
    	ExtKripke kripke = tlc.getKripke();
    	ExtKripke errPreKripke = kripke.createErrPre();
    	final boolean strongFairness = true; // need SF in err pre
    	return kripkeToTLA(tag, tlc, errPreKripke, tla, cfg, outputLoc, strongFairness, vars);
    }
    
    private static void createErrPost(final TLC tlc1, final TLC tlc2, final String tla1, final String tla2, final String cfg1, final String cfg2,
    		final String outputLoc, Map<String,String> jsonOutput) {
    	// collect state variables from each spec
    	Set<String> vars1 = new HashSet<String>();
    	Set<String> vars2 = new HashSet<String>();
    	
    	// create one err pre file for each spec, then combine them into a single one for comparison
    	final String tag = "ErrPost";
    	final String specName1 = createErrPost(tag, tlc1, tla1, cfg1, vars1, outputLoc, jsonOutput);
    	final String specName2 = createErrPost(tag, tlc2, tla2, cfg2, vars2, outputLoc, jsonOutput);
    	final String combineSpecName = combineSpec(tag, specName1, specName2, vars1, vars2, outputLoc);
        jsonOutput.put(COMBINED_ERR_POST_TLA, combineSpecName);
    }
    
    private static String createErrPost(final String tag, final TLC tlc, final String tla, final String cfg, Set<String> vars,
    		final String outputLoc, Map<String,String> jsonOutput) {
    	ExtKripke kripke = tlc.getKripke();
    	ExtKripke errPostKripke = kripke.createErrPost();
    	final boolean strongFairness = false; // do not add SF to err post
    	return kripkeToTLA(tag, tlc, errPostKripke, tla, cfg, outputLoc, strongFairness, vars);
    }
    
    private static String specSatConfig(final String spec1, final String spec2, final String outputLoc) {
        StringBuilder builder = new StringBuilder();
        builder.append("SPECIFICATION ").append(spec1).append("\n");
        builder.append("PROPERTY ").append(spec2);
        final String file = outputLoc + spec1 + "Sat" + spec2 + ".cfg";
        Utils.writeFile(file, builder.toString());
        return file;
    }
    
    private static String combineSpec(final String tag, final String specName1, final String specName2, final Set<String> vars1, final Set<String> vars2, final String outputLoc) {
        final String specName = "Combined_" + tag;
        final String varsSeqName = "vars_" + tag;
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";
        
        ArrayList<String> varNameList1 = Utils.toArrayList(vars1);
        ArrayList<String> varNameList2 = Utils.toArrayList(vars2);
        
        vars1.addAll(vars2);
        ArrayList<String> combineVarNameList = Utils.toArrayList(vars1);
        
        final String varList = String.join(", ", combineVarNameList);
        final String varsDecl = "VARIABLES " + varList;
        
        final String spec1 = "S1 == INSTANCE " + specName1 + " WITH " + Utils.instanceWithList(varNameList1);
        final String spec2 = "S2 == INSTANCE " + specName2 + " WITH " + Utils.instanceWithList(varNameList2);
        final String spec1Def = "Spec1 == S1!Spec";
        final String spec2Def = "Spec2 == S2!Spec";

        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append(varsDecl).append("\n");
        builder.append("\n");
        builder.append(spec1).append("\n");
        builder.append("\n");
        builder.append(spec2).append("\n");
        builder.append("\n");
        builder.append(spec1Def).append("\n");
        builder.append(spec2Def).append("\n");
        builder.append(endModule).append("\n");
        builder.append("\n");
        
        final String name = outputLoc + specName + ".tla";
        Utils.writeFile(name, builder.toString());
        
        return name;
    }
    
    private static void runTLCExtractStateSpace(final String tlaFile, final TLC tlc, final String outputLoc, TLC tlcTypeOK) {
    	// no need to create a new TLA file since we've already checked (in the caller to this function)
    	// that there is a TypeOK in tlaFile
        final String cfgName = "JustTypeOK";
        final String cfgFile = stateSpaceConfig(cfgName, outputLoc);
    	TLC.runTLC(tlaFile, cfgFile, tlcTypeOK);
    }
    
    private static void runTLCExtractStateSpace(final TLC tlc1, final TLC tlc2, final String outputLoc, TLC tlcTypeOK) {
        final String specName = "CombinedTypeOK";
        final String tlaFile = stateSpaceTLA(specName, tlc1, tlc2, outputLoc);
        final String cfgFile = stateSpaceConfig(specName, outputLoc);
        TLC.runTLC(tlaFile, cfgFile, tlcTypeOK);
    }
    
    private static String stateSpaceTLA(final String specName, final TLC tlc, final String outputLoc) {
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";
        
        FastTool ft = (FastTool) tlc.tool;
        ArrayList<String> varNameList = Utils.toArrayList(ft.getVarNames());
        
        final String varList = String.join(", ", varNameList);
        final String varsDecl = "VARIABLES " + varList;
        
        final String specDef = "S1 == INSTANCE " + tlc.getSpecName() + " WITH " + Utils.instanceWithList(varNameList);
        final String typeOKDef = "TypeOK == S1!TypeOK";
        
        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append(varsDecl).append("\n");
        builder.append("\n");
        builder.append(specDef).append("\n");
        builder.append(typeOKDef).append("\n");
        builder.append(endModule).append("\n");
        builder.append("\n");
        
        final String file = outputLoc + specName + ".tla";
        Utils.writeFile(file, builder.toString());
        
        return file;
    }
    
    private static String stateSpaceTLA(final String specName, final TLC tlc1, final TLC tlc2, final String outputLoc) {
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";
        
        FastTool ft1 = (FastTool) tlc1.tool;
        FastTool ft2 = (FastTool) tlc2.tool;
        ArrayList<String> varNameList1 = Utils.toArrayList(ft1.getVarNames());
        ArrayList<String> varNameList2 = Utils.toArrayList(ft2.getVarNames());
        Set<String> combineVarNames = new HashSet<String>();
        combineVarNames.addAll(varNameList1);
        combineVarNames.addAll(varNameList2);
        
        final String varList = String.join(", ", combineVarNames);
        final String varsDecl = "VARIABLES " + varList;
        
        final String specName1 = tlc1.getSpecName();
        final String specName2 = tlc2.getSpecName();
        final String spec1 = "S1 == INSTANCE " + specName1 + " WITH " + Utils.instanceWithList(varNameList1);
        final String spec2 = "S2 == INSTANCE " + specName2 + " WITH " + Utils.instanceWithList(varNameList2);
        final String typeOKDef = "TypeOK == S1!TypeOK /\\ S2!TypeOK";
        
        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append(varsDecl).append("\n");
        builder.append("\n");
        builder.append(spec1).append("\n");
        builder.append(spec2).append("\n");
        builder.append(typeOKDef).append("\n");
        builder.append(endModule).append("\n");
        builder.append("\n");
        
        final String file = outputLoc + specName + ".tla";
        Utils.writeFile(file, builder.toString());
        
        return file;
    }
    
    private static String stateSpaceConfig(final String specName, final String outputLoc) {
        StringBuilder builder = new StringBuilder();
        builder.append("SPECIFICATION TypeOK");
        
        final String file = outputLoc + specName + ".cfg";
        Utils.writeFile(file, builder.toString());
        
        return file;
    }
    
    private static String kripkeToTLA(final String tag, final TLC tlc, final ExtKripke kripke,
    		final String tla, final String cfg, final String outputLoc, final boolean strongFairness, Set<String> vars) {
        FastTool ft = (FastTool) tlc.tool;
        
        final String specName = tlc.getSpecName() + "_" + tag;
        final String varsSeqName = "vars";
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";

        final List<String> moduleWhiteList =
        		Arrays.asList("Bags", "FiniteSets", "Functions", "Integers", "Json", "Naturals",
        				"NaturalsInduction", "RealTime", "Sequences", "SequencesExt", "TLC", "TLCExt");
        ArrayList<String> moduleNameList = Utils.filterArrayWhiteList(moduleWhiteList, ft.getModuleNames());
        ArrayList<String> varNameList = Utils.toArrayList(ft.getVarNames());
        vars.addAll(varNameList);

        final String moduleList = String.join(", ", moduleNameList);
        final String varList = String.join(", ", varNameList);
        final String modulesDecl = "EXTENDS " + moduleList;
        final String varsDecl = "VARIABLES " + varList;
        final String varsSeq = varsSeqName + " == <<" + varList + ">>";
        final String specFairness = fairnessConditionString(tla, tlc);

        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append(modulesDecl).append("\n");
        builder.append("\n");
        builder.append(varsDecl).append("\n");
        builder.append("\n");
        builder.append(varsSeq).append("\n");
        builder.append("\n");
        builder.append(kripke.toPartialTLASpec(varsSeqName, specFairness, strongFairness)).append("\n");
        builder.append(endModule).append("\n");
        builder.append("\n");

        final String fileName = specName + ".tla";
        final String file = outputLoc + fileName;
        Utils.writeFile(file, builder.toString());
        
        return specName;
    }
    
    private static String fairnessConditionString(final String tla, final TLC tlc) {
        Action[] fairnessConditions = tlc.tool.getTemporals();
        List<String> fairnessConditionStrs = new ArrayList<>();
        for (Action condition : fairnessConditions) {
        	final String condStr = Utils.extractSyntaxFromSource(tla, condition.getLocation());
        	fairnessConditionStrs.add(condStr);
        }
        return String.join(" /\\ ", fairnessConditionStrs);
    }
}
