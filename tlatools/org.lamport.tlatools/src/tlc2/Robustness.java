package tlc2;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.regex.Pattern;

import model.InJarFilenameToStream;
import model.ModelInJar;
import tlc2.tool.Action;
import tlc2.tool.ExtKripke;
import tlc2.tool.StateVarType;
import tlc2.tool.TLCState;
import tlc2.tool.ExtKripke.BoundaryType;
import tlc2.tool.ExtKripke.Pair;
import tlc2.tool.impl.FastTool;
import util.FileUtil;
import util.SimpleFilenameToStream;

public class Robustness {
    
    // thank you https://stackoverflow.com/questions/9882487/how-can-i-disable-system-out-for-speed-in-java
    private static final PrintStream SUPRESS_ALL_OUTPUT_PRINT_STREAM =
    		new java.io.PrintStream(new java.io.OutputStream() {
        	    @Override public void write(int b) {}
        	}) {
        	    @Override public void flush() {}
        	    @Override public void close() {}
        	    @Override public void write(int b) {}
        	    @Override public void write(byte[] b) {}
        	    @Override public void write(byte[] buf, int off, int len) {}
        	    @Override public void print(boolean b) {}
        	    @Override public void print(char c) {}
        	    @Override public void print(int i) {}
        	    @Override public void print(long l) {}
        	    @Override public void print(float f) {}
        	    @Override public void print(double d) {}
        	    @Override public void print(char[] s) {}
        	    @Override public void print(String s) {}
        	    @Override public void print(Object obj) {}
        	    @Override public void println() {}
        	    @Override public void println(boolean x) {}
        	    @Override public void println(char x) {}
        	    @Override public void println(int x) {}
        	    @Override public void println(long x) {}
        	    @Override public void println(float x) {}
        	    @Override public void println(double x) {}
        	    @Override public void println(char[] x) {}
        	    @Override public void println(String x) {}
        	    @Override public void println(Object x) {}
        	    @Override public java.io.PrintStream printf(String format, Object... args) { return this; }
        	    @Override public java.io.PrintStream printf(java.util.Locale l, String format, Object... args) { return this; }
        	    @Override public java.io.PrintStream format(String format, Object... args) { return this; }
        	    @Override public java.io.PrintStream format(java.util.Locale l, String format, Object... args) { return this; }
        	    @Override public java.io.PrintStream append(CharSequence csq) { return this; }
        	    @Override public java.io.PrintStream append(CharSequence csq, int start, int end) { return this; }
        	    @Override public java.io.PrintStream append(char c) { return this; }
        	};
        	
	private static final String COMPARISON_TYPE = "comparison_type";
	private static final String SPEC_TO_PROPERTY = "spec_to_property";
	private static final String SPEC_TO_SPEC = "spec_to_spec";
	
	private static final String SPEC_NAME = "spec_name";
	private static final String SPEC1_NAME = "spec1_name";
	private static final String SPEC2_NAME = "spec2_name";
	
	private static final String SPEC_IS_SAFE = "spec_is_safe";
	private static final String SPEC1_IS_SAFE = "spec1_is_safe";
	private static final String SPEC2_IS_SAFE = "spec2_is_safe";
	
	private static final String COMBINED_ERR_PRE_TLA = "combined_err_pre_tla";
	private static final String COMBINED_ERR_POST_TLA = "combined_err_post_tla";
	
	private static final String SPEC1_SAT_SPEC2_CFG = "spec1_sat_spec2_cfg";
	private static final String SPEC2_SAT_SPEC1_CFG = "spec2_sat_spec1_cfg";

	private static final String DIFF_REP_STATE_FORMULA_ERROR = "diff_rep_state_formula_error";
	private static final String MISSING_TYPEOK = "missing_typeok";
	private static final String MISSING_BOTH_TYPEOKS = "missing_both_typeoks";
	private static final String TYPE_OK = "TypeOK";
	private static final String ALL = "All";
	
	private static final String TRUE = "true";
	private static final String FALSE = "false";
	

	/*
	 * Main entry point
	 */
    public static void calc(String[] args) {
    	// TODO add functionality for compareSpecToEnvironment
    	Map<String,String> jsonStrs = new HashMap<>();
    	Map<String,List<String>> jsonLists = new HashMap<>();
    	if (args.length == 3) {
    		compareSpecToProperty(args, jsonStrs, jsonLists);
    	}
    	else if (args.length == 5) {
    		compareSpecs(args, jsonStrs, jsonLists);
    	}
    	else {
    		System.out.println("usage: tlc-ian <output_loc> <spec1> <cfg1> [<spec2> <cfg2>]");
    	}
    	System.out.println(Utils.asJson(jsonStrs, jsonLists));
    }
    
    // M_err_rep: states that are in (M_err \cap P) but MAY leave P in one step
    private static void compareSpecToProperty(String[] args, Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	final String outputLoc = args[0] + "/";
    	final String tla = args[1];
    	final String cfg = args[2];
    	
    	// initialize and run TLC
    	TLC tlc = new TLC();
    	TLC.runTLC(tla, cfg, tlc);

    	jsonStrs.put(COMPARISON_TYPE, SPEC_TO_PROPERTY);
    	jsonStrs.put(SPEC_NAME, tlc.getSpecName());
    	
    	// compute the representation for beh(P) - \eta(spec,P)
    	computePropertyDiffRep(tla, tlc, outputLoc, jsonStrs, jsonLists);
    }
    
    private static void compareSpecToEnvironment(String[] args, Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	// TODO
    	// M_err_rep: states that are in (M_err \cap E) but MAY leave E in one step
    }
    
    private static void compareSpecs(String[] args, Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
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
    	
    	jsonStrs.put(COMPARISON_TYPE, SPEC_TO_SPEC);
    	jsonStrs.put(SPEC1_NAME, tlc1.getSpecName());
    	jsonStrs.put(SPEC2_NAME, tlc2.getSpecName());
    	jsonStrs.put(SPEC1_IS_SAFE, tlc1.getKripke().isSafe() ? TRUE : FALSE);
    	jsonStrs.put(SPEC2_IS_SAFE, tlc2.getKripke().isSafe() ? TRUE : FALSE);
    	
    	// create err pre/post TLA+ specs
    	createErrPre(tlc1, tlc2, tla1, tla2, cfg1, cfg2, outputLoc, jsonStrs);
    	createErrPost(tlc1, tlc2, tla1, tla2, cfg1, cfg2, outputLoc, jsonStrs);
    	
    	// create the cfgs for comparing the pre/post specs
    	final String spec1SatSpec2Cfg = specSatConfig("Spec1", "Spec2", outputLoc);
    	final String spec2SatSpec1Cfg = specSatConfig("Spec2", "Spec1", outputLoc);
    	jsonStrs.put(SPEC1_SAT_SPEC2_CFG, spec1SatSpec2Cfg);
    	jsonStrs.put(SPEC2_SAT_SPEC1_CFG, spec2SatSpec1Cfg);
    	
    	// compute the representation for \eta(spec2,P) - \eta(spec1,P)
    	// and \eta(spec1,P) - \eta(spec2,P)
    	computeComparisonDiffRep(tlc1, tlc2, outputLoc, jsonStrs, jsonLists);
    }
    
    private static void computePropertyDiffRep(final String tlaFile, final TLC tlc, final String outputLoc, Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	final BoundaryType boundaryType = BoundaryType.safety;
    	final boolean groupByAction = true;
    	final ExtKripke kripke = tlc.getKripke();
    	final Map<String, Set<String>> boundariesByGroup = getBoundariesByGroup(kripke, boundaryType, groupByAction);

    	jsonStrs.put(SPEC_IS_SAFE, kripke.isSafe() ? TRUE : FALSE);
    	
    	// if the spec isn't safe (has 0 errors) then we compute the diff rep
    	if (!kripke.isSafe()) {
        	RobustDiffRep.SpecScope scope = RobustDiffRep.SpecScope.Spec;
        	RobustDiffRep diffRep = new RobustDiffRep(tlc.getSpecName(), scope, outputLoc, boundariesByGroup, jsonStrs, jsonLists);
    		diffRep.writeBoundariesByGroup();
        	
        	// create a formula for each safety boundary group. we do this by creating
        	// a FOL separator file per group and calculating a separating formula.
        	// this does require a TypeOK property in the spec though, since we need to
        	// calculate negative examples.
        	final boolean hasTypeOK = Utils.hasInvariant(tlc, TYPE_OK);
        	if (hasTypeOK) {
            	final TLC tlcTypeOK = new TLC();
            	runTLCExtractStateSpace(tlaFile, tlc, outputLoc, tlcTypeOK);
            	diffRep.writeBoundaryFOLSeparatorFileByGroup(tlcTypeOK);
        	}
        	else {
        		jsonStrs.put(DIFF_REP_STATE_FORMULA_ERROR, MISSING_TYPEOK);
        	}
    	}
    }
    
    private static void computeComparisonDiffRep(final TLC tlc1, final TLC tlc2, final String outputLoc, Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	final ExtKripke kripke1 = tlc1.getKripke();
    	final ExtKripke kripke2 = tlc2.getKripke();
    	final ExtKripke errPre1 = kripke1.createErrPre();
    	final ExtKripke errPre2 = kripke2.createErrPre();
    	final ExtKripke errPost1 = kripke1.createErrPost();
    	final ExtKripke errPost2 = kripke2.createErrPost();
    	
    	jsonStrs.put(SPEC1_IS_SAFE, kripke1.isSafe() ? TRUE : FALSE);
    	jsonStrs.put(SPEC2_IS_SAFE, kripke2.isSafe() ? TRUE : FALSE);
    	
    	// only calculate the diff rep if neither is safe
		// compute \eta1-\eta2 and \eta2-\eta1
    	if (!kripke1.isSafe() && !kripke2.isSafe()) {
        	// a TypeOK is required to gather the info we need to create a sep.fol file
        	final boolean bothHaveTypeOK = Utils.hasInvariant(tlc1, TYPE_OK) && Utils.hasInvariant(tlc2, TYPE_OK);
        	TLC tlcTypeOK = new TLC();
        	if (bothHaveTypeOK) {
            	// compute the entire state space
            	runTLCExtractStateSpace(tlc1, tlc2, outputLoc, tlcTypeOK);
        	} else {
        		jsonStrs.put(DIFF_REP_STATE_FORMULA_ERROR, MISSING_BOTH_TYPEOKS);
        	}
        	
        	computeComparisonDiffRepWrtOneSpec(errPre2, errPost2, errPre1, errPost1, tlc1, tlc2,
        			tlc1.getSpecName(), outputLoc, RobustDiffRep.SpecScope.Spec1, tlcTypeOK, bothHaveTypeOK, jsonStrs, jsonLists);
        	computeComparisonDiffRepWrtOneSpec(errPre1, errPost1, errPre2, errPost2, tlc2, tlc1,
        			tlc2.getSpecName(), outputLoc, RobustDiffRep.SpecScope.Spec2, tlcTypeOK, bothHaveTypeOK, jsonStrs, jsonLists);
    	}
    }

	// compute the diff rep, i.e. the states that represent \eta2 - \eta1
    private static void computeComparisonDiffRepWrtOneSpec(final ExtKripke errPre1, final ExtKripke errPost1, final ExtKripke errPre2, final ExtKripke errPost2,
    		final TLC tlc1, final TLC tlc2, final String refSpec, final String outputLoc, final RobustDiffRep.SpecScope specScope,
    		final TLC tlcTypeOK, final boolean writeSepFormulaFile, Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	// TODO allow behaviorDifferenceRepresentation() to calc the error rep too
    	final BoundaryType boundaryType = BoundaryType.safety;
    	final boolean groupByAction = true;
    	final Set<Pair<TLCState,Action>> diffRepSet = ExtKripke.union(
    			ExtKripke.behaviorDifferenceRepresentation(errPre1, errPre2),
    			ExtKripke.behaviorDifferenceRepresentation(errPost1, errPost2));
    	final Map<String, Set<String>> boundariesByGroup = groupTheDiffRep(diffRepSet, groupByAction);
    	RobustDiffRep diffRep = new RobustDiffRep(refSpec, specScope, outputLoc, boundariesByGroup, jsonStrs, jsonLists);
    	
    	// write the boundary groups to files
    	diffRep.writeBoundariesByGroup();
    	
    	if (writeSepFormulaFile) {
        	diffRep.writeBoundaryFOLSeparatorFileByGroup(tlcTypeOK);
    	}
    }
    
    private static Map<String, Set<String>> getBoundariesByGroup(final ExtKripke kripke, final BoundaryType boundaryType, final boolean groupByAction) {
    	if (groupByAction) {
    		if (boundaryType.equals(BoundaryType.safety)) {
    			return kripke.safetyBoundaryPerAction();
    		} else {
    			return kripke.errorBoundaryPerAction();
    		}
    	}
    	else {
    		if (boundaryType.equals(BoundaryType.safety)) {
    			Map<String, Set<String>> singleton = new HashMap<>();
    			singleton.put(ALL, Utils.stateSetToStringSet(kripke.safetyBoundary()));
    			return singleton;
    		} else {
    			Map<String, Set<String>> singleton = new HashMap<>();
    			singleton.put(ALL, Utils.stateSetToStringSet(kripke.errorBoundary()));
    			return singleton;
    		}
    	}
    }
    
    private static Map<String, Set<String>> groupTheDiffRep(final Set<Pair<TLCState,Action>> diffRepSet, final boolean groupByAction) {
    	if (groupByAction) {
    		Map<String, Set<String>> diffRepGroups = new HashMap<>();
    		for (Pair<TLCState,Action> diffRep : diffRepSet) {
    			final String group = diffRep.second.getName().toString();
    			final String state = Utils.normalizeStateString(diffRep.first.toString());
    			if (!diffRepGroups.containsKey(group)) {
    				diffRepGroups.put(group, new HashSet<>());
    			}
    			diffRepGroups.get(group).add(state);
    		}
    		return diffRepGroups;
    	}
    	else {
        	final Set<TLCState> diffRepStates = ExtKripke.projectFirst(diffRepSet);
			Map<String, Set<String>> singleton = new HashMap<>();
			singleton.put(ALL, Utils.stateSetToStringSet(diffRepStates));
			return singleton;
    	}
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
    
    private static String combineSpec(final String tag, final String specName1, final String specName2,
    		final Set<String> vars1, final Set<String> vars2, final String outputLoc) {
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
    
    private static String specSatConfig(final String spec1, final String spec2, final String outputLoc) {
        StringBuilder builder = new StringBuilder();
        builder.append("SPECIFICATION ").append(spec1).append("\n");
        builder.append("PROPERTY ").append(spec2);
        final String file = outputLoc + spec1 + "Sat" + spec2 + ".cfg";
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
}
