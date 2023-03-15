// an Extended Kripke Structure
// "extended" just means we keep track of some extra info

package tlc2.tool;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import tlc2.Utils;
import tlc2.Utils.Pair;

import java.lang.StringBuilder;


public class ExtKripke {
    
    private enum BoundaryType {
    	safety, error
    }
    
    private Set<String> initStates;
    private Set<String> allStates;
    private Set<String> badStates;
    private Set<Pair<String,String>> delta;
    private Map<Pair<String,String>, String> deltaActions;
    private Set<String> envStates;

    public ExtKripke() {
    	this.initStates = new HashSet<>();
        this.allStates = new HashSet<>();
        this.badStates = new HashSet<>();
        this.delta = new HashSet<>();
        this.deltaActions = new HashMap<>();
    	this.envStates = new HashSet<>();
    }

    public ExtKripke(final ExtKripke src) {
    	this.initStates = new HashSet<>(src.initStates);
    	this.allStates = new HashSet<>(src.allStates);
    	this.badStates = new HashSet<>(src.badStates);
    	this.delta = new HashSet<>(src.delta);
    	this.deltaActions = new HashMap<>(src.deltaActions);
    	this.envStates = new HashSet<>(src.envStates);
    }

    // assumes that the state space of srcClosed is more refined than the state space of srcM.
    // this assumption is generally valid because the closed system is composed of M, and hence
    // contains all state vars that are in M.
    public ExtKripke(final ExtKripke srcM, final ExtKripke srcClosed) {
    	this(srcM);
    	if (!srcClosed.badStates.isEmpty()) {
    		throw new RuntimeException("Closed system is not safe!");
    	}
    	if (!srcM.envStates.isEmpty()) {
    		throw new RuntimeException("M contains env states!");
    	}
    	
        // add env states. small optimization: we know that all env states are safe
    	final Set<String> srcMGoodStates = Utils.setMinus(srcM.allStates, srcM.badStates);
    	for (final String s : srcMGoodStates) {
    		if (refinedContainerContainsAbstractState(srcClosed.allStates, s)) {
    			this.envStates.add(s);
    		}
    	}
    }
    
    private static boolean refinedContainerContainsAbstractState(final Set<String> container, final String abstrState) {
    	for (final String refinedState : container) {
    		if (refinedImpliesAbstractState(refinedState, abstrState)) {
    			return true;
    		}
    	}
    	return false;
    }
    
    private static boolean refinedImpliesAbstractState(final String refinedState, final String abstrState) {
    	final Set<Pair<String,String>> refinedKvPairs = new HashSet<>(Utils.extractKeyValuePairsFromState(refinedState));
    	final Set<Pair<String,String>> abstrKvPairs = new HashSet<>(Utils.extractKeyValuePairsFromState(abstrState));
    	return refinedKvPairs.containsAll(abstrKvPairs);
    }
    
    // pre-processing

    // bad initial states are explicitly added (via addBadState()) in ModelChecker.java
    public void addInitState(TLCState s) {
    	final String sName = Utils.normalizeStateString(s.toString());
        allStates.add(sName);
        initStates.add(sName);
    }

    public void addGoodState(TLCState s) {
    	final String sName = Utils.normalizeStateString(s.toString());
        allStates.add(sName);
    }

    public void addBadState(TLCState s) {
    	final String sName = Utils.normalizeStateString(s.toString());
        allStates.add(sName);
        badStates.add(sName);
    }

    public void addTransition(Action act, TLCState src, TLCState dst) {
    	final String srcName = Utils.normalizeStateString(src.toString());
    	final String dstName = Utils.normalizeStateString(dst.toString());
    	final Pair<String,String> transition = new Pair<>(srcName, dstName);
    	
    	final String actName = act.getName().toString();
    	Utils.assertNotNull(actName, "TLC added null action name to an ExtKripke instance!");
    	delta.add(transition);
    	deltaActions.put(transition, actName);
    }
    
    
    // post-processing
    
    public boolean isEmpty() {
    	return this.allStates.isEmpty() || this.initStates.isEmpty();
    }

    public boolean isSafe() {
    	return this.badStates.isEmpty();
    }
    
    public Set<String> reach() {
    	return this.allStates;
    }
    
    public boolean isBadState(final String s) {
    	return this.badStates.contains(s);
    }
    
    public ExtKripke createErrPre() {
    	Set<String> errStates = notAlwaysNotPhiStates();
    	Set<Pair<String,String>> deltaErrSinks = createDeltaWithErrorSinks(badStates, delta);
    	Set<Pair<String,String>> deltaErrPre = filterDeltaByStates(errStates, deltaErrSinks);
    	// no way to add SF yet
    	ExtKripke errPre = new ExtKripke();
    	errPre.initStates = Utils.intersection(this.initStates, errStates);
    	errPre.allStates = errStates;
    	errPre.delta = deltaErrPre;
    	errPre.deltaActions = this.deltaActions;
    	return errPre;
    }
    
    public ExtKripke createErrPost() {
    	ExtKripke errPost = new ExtKripke();
    	errPost.initStates = errorBoundary();
    	errPost.allStates = this.allStates;
    	errPost.delta = this.delta;
    	errPost.deltaActions = this.deltaActions;
    	return errPost;
    }
    
    public String getStrNANPS() {
        StringBuilder builder = new StringBuilder();

        builder.append("NANPS\n");
        for (String s : this.notAlwaysNotPhiStates()) {
        	builder.append("  " + s + "\n");
        }

        return builder.toString();
    }
    
    
    public Set<String> safetyBoundary() {
    	return calculateBoundary(BoundaryType.safety);
    }
    
    public Set<String> robustSafetyBoundary() {
    	// the set of states that leave the env, but are guaranteed to be 1-step safe
    	final Set<String> nonEnvStates = Utils.setMinus(this.allStates, this.envStates);
    	return Utils.setMinus(calculateBoundary(BoundaryType.safety, nonEnvStates), calculateBoundary(BoundaryType.safety, this.badStates));
    }
    
    private Set<String> errorBoundary() {
    	return calculateBoundary(BoundaryType.error);
    }
    
    // returns a map of (action name) -> (safety boundary for the action)
    public Map<String, Set<String>> safetyBoundaryPerAction() {
    	return boundaryPerAction(safetyBoundary());
    }
    
    // runs under the assumption that: this.envStates \cap this.badStates = \emptyset
    // returns a map of (action name) -> (robust safety boundary for the action)
    public Map<String, Set<String>> robustSafetyBoundaryPerAction() {
    	// nonEnvStates = goodStates \cap envStates
    	// we have by assumption: envStates \subseteq goodStates
    	// so: badStates \subseteq nonEnvStates
    	final Set<String> nonEnvStates = Utils.setMinus(this.allStates, this.envStates);
    	final Set<String> goodNonEnvStates = Utils.setMinus(nonEnvStates, this.badStates);
    	final Set<String> envBoundaryStates = calculateBoundary(BoundaryType.safety, goodNonEnvStates);
    	Map<String, Set<String>> leaveEnv = boundaryPerAction(envBoundaryStates, goodNonEnvStates);
    	
    	// so far we have calculated (state,action) pairs such that there EXISTS a world in which the action
    	// safely leaves the environment. however, we want (state,action) pairs in which the action ALWAYS
    	// safely leaves the environment. we do this by removing any states at the safety boundary for the
    	// given action.
    	final Map<String, Set<String>> safetyBoundary = safetyBoundaryPerAction();
    	for (final String act : safetyBoundary.keySet()) {
    		if (leaveEnv.containsKey(act)) {
    			// remove any states that can lead to an error through this action in 1 step
    			final Set<String> robustSafetyBoundaryForAct = Utils.setMinus(leaveEnv.get(act), safetyBoundary.get(act));
    			if (robustSafetyBoundaryForAct.isEmpty()) {
    				leaveEnv.remove(act);
    			} else {
    				leaveEnv.put(act, robustSafetyBoundaryForAct);
    			}
    		}
    	}
    	return leaveEnv;
    }
    
    // returns a map of (action name) -> (error boundary for the action)
    public Map<String, Set<String>> errorBoundaryPerAction() {
    	return boundaryPerAction(errorBoundary());
    }
    

    private Set<String> calculateBoundary(BoundaryType boundaryType) {
    	return calculateBoundary(boundaryType, this.badStates);
    }
    
    // invariant: all states in frontier are safe (not in errorStates)
    private Set<String> calculateBoundary(final BoundaryType boundaryType, final Set<String> errorStates) {
    	Set<String> goodInitStates = Utils.setMinus(this.initStates, errorStates);
    	Set<String> explored = new HashSet<>(goodInitStates);
    	Set<String> frontier = new HashSet<>(goodInitStates);
    	Set<String> boundary = (boundaryType.equals(BoundaryType.safety)) ?
    			new HashSet<>() : Utils.intersection(this.initStates, errorStates);
    	
    	while (!frontier.isEmpty()) {
    		Set<String> addToFrontier = new HashSet<String>();
	    	for (String s : frontier) {
	    		explored.add(s);
	    		for (String t : this.succ(s)) {
	    			if (errorStates.contains(t)) {
	    				// the state which we add to the boundary depends on whether we're calculating:
	    				// the safety boundary or (else) the error boundary
	    				switch (boundaryType) {
	    				case safety:
	    					boundary.add(s);
	    					break;
	    				case error:
	    					boundary.add(t);
	    					break;
	    				}
	    			}
	    			else if (!explored.contains(t)) {
	    				addToFrontier.add(t);
	    			}
	    		}
	    	}
	    	frontier.addAll(addToFrontier);
	    	frontier.removeAll(explored);
    	}
    	return boundary;
    }
    
    private Map<String, Set<String>> boundaryPerAction(final Set<String> entireBoundary) {
    	return boundaryPerAction(entireBoundary, this.badStates);
    }
        
    private Map<String, Set<String>> boundaryPerAction(final Set<String> entireBoundary, final Set<String> errorStates) {
    	Map<String, Set<String>> groupedBoundaries = new HashMap<>();
    	for (String s : entireBoundary) {
			final String boundaryState = s;
    		for (String t : succ(s)) {
    			Pair<String,String> transition = new Pair<>(s,t);
    			if (this.delta.contains(transition) && errorStates.contains(t)) {
    				final String act = this.deltaActions.get(transition);
    				if (!groupedBoundaries.containsKey(act)) {
    					groupedBoundaries.put(act, new HashSet<>());
    				}
    				groupedBoundaries.get(act).add(boundaryState);
    			}
    		}
    	}
    	return groupedBoundaries;
    }
    
    private Set<String> succ(String s) {
    	Set<String> succStates = new HashSet<String>();
    	for (Pair<String,String> t : this.delta) {
    		if (s.equals(t.first)) {
    			succStates.add(t.second);
    		}
    	}
    	return succStates;
    }
    
    private Set<String> notAlwaysNotPhiStates() {
    	Set<String> states = new HashSet<String>();
    	Set<Pair<String,String>> inverseDelta = invertTransitionRelation(delta);
    	for (String errState : this.errorBoundary()) {
    		// perform a DFS (on inverse delta) from errState. add every state we find to "states"
    		// discoverDFS will mutate "states"
    		discoverDFS(errState, inverseDelta, states);
    	}
    	return states;
    }

    private static Set<Pair<String,String>> filterDeltaByStates(Set<String> states, Set<Pair<String,String>> delta) {
    	Set<Pair<String,String>> deltaFiltered = new HashSet<Pair<String,String>>();
    	for (Pair<String,String> t : delta) {
    		if (states.contains(t.first) && states.contains(t.second)) {
    			deltaFiltered.add(t);
    		}
    	}
    	return deltaFiltered;
    }
    
    private static Set<Pair<String,String>> createDeltaWithErrorSinks(Set<String> errStates, Set<Pair<String,String>> delta) {
    	Set<Pair<String,String>> deltaWithErrorSinks = new HashSet<Pair<String,String>>();
    	for (Pair<String,String> t : delta) {
    		if (!errStates.contains(t.first)) {
    			deltaWithErrorSinks.add(t);
    		}
    	}
    	return deltaWithErrorSinks;
    }
    
    private static Set<Pair<String,String>> invertTransitionRelation(Set<Pair<String,String>> d) {
    	Set<Pair<String,String>> inverse = new HashSet<Pair<String,String>>();
    	for (Pair<String,String> t : d) {
    		inverse.add(new Pair<String,String>(t.second, t.first));
    	}
    	return inverse;
    }
    
    private static void discoverDFS(String start, Set<Pair<String,String>> delta, Set<String> states) {
    	// base case
    	if (states.contains(start)) {
    		return;
    	}
    	
    	states.add(start);
    	for (Pair<String,String> t : delta) {
    		if (start.equals(t.first)) {
    			discoverDFS(t.second, delta, states);
    		}
    	}
    }
    
    // compute the representation for \eta(m2,P) - \eta(m1,P)
    // note: \eta(m2,P) - \eta(m1,P) = beh(m1_err) - beh(m2_err)
    // i.e. we find all erroneous behaviors of m1 that are NOT erroneous behaviors of m2
    public static Set<Pair<String,String>> behaviorDifferenceRepresentation(final ExtKripke m1, final ExtKripke m2, final ExtKripke refKripke) {
    	final Set<String> mutualReach = mutualReach(m1, m2);
    	final Set<Pair<String,String>> m1MinusM2Delta = Utils.setMinus(m1.delta, m2.delta);
    	final Set<Pair<String,String>> rep = new HashSet<>();
		for (final Pair<String,String> transition : m1MinusM2Delta) {
			final String s = transition.first;
			final String t = transition.second;
			if (mutualReach.contains(s) && refKripke.isBadState(t)) {
				// found an outgoing transition (of ONLY m1) from s to a bad state
				final String act = m1.deltaActions.get(transition);
				rep.add(new Pair<>(s, act));
			}
		}
    	return rep;
    }
    
    private static Set<String> mutualReach(final ExtKripke m1, final ExtKripke m2) {
    	Set<String> reach = new HashSet<String>();
    	Set<String> mutualInit = Utils.intersection(m1.initStates, m2.initStates);
    	Set<Pair<String,String>> mutualDelta = Utils.intersection(m1.delta, m2.delta);
    	for (String init : mutualInit) {
        	mutualReach(mutualDelta, init, reach);
    	}
    	return reach;
    }
    
    private static void mutualReach(final Set<Pair<String,String>> mutualDelta, final String init, Set<String> reach) {
    	reach.add(init);
    	for (Pair<String,String> t : mutualDelta) {
    		if (init.equals(t.first)) {
    			String succ = t.second;
    			if (!reach.contains(succ)) {
    				mutualReach(mutualDelta, succ, reach);
    			}
    		}
    	}
    }
    
    
    // print a TLA+ spec
    
    public String toPartialTLASpec(String varsSeqName, String specFairness, boolean strongFairness) {
    	StringBuilder builder = new StringBuilder();
    	
    	//String initOp = "Init_" + tag;
    	//String nextOp = "Next_" + tag;
    	//String specOp = "Spec_" + tag;
    	final String initOp = "Init";
    	final String nextOp = "Next";
    	final String specOp = "Spec";
    	
    	// Init operator
    	builder.append(initOp).append(" ==\n  ").append(initExpr());
    	builder.append("\n\n");
    	
    	// Next operator
    	builder.append(nextOp).append(" ==\n  ").append(nextExpr());
    	builder.append("\n\n");
    	
    	// Spec operator
    	builder.append(specOp).append(" == ")
    		.append(initOp).append(" /\\ [][")
    		.append(nextOp).append("]_").append(varsSeqName);
    	if (!specFairness.isEmpty() && !strongFairness) {
    		builder.append(" /\\ ").append(specFairness);
    	}
    	if (strongFairness) {
    		builder.append(" /\\ SF_").append(varsSeqName).append("(").append(nextOp).append(")");
    	}
    	
    	return builder.toString();
    }
    
    private String initExpr() {
    	if (this.initStates.isEmpty()) {
    		return "FALSE";
    	}
    	return "\\/ " + String.join("\n  \\/ ", statesToStringList(this.initStates));
    }

    private String nextExpr() {
    	ArrayList<String> strTransitions = new ArrayList<String>();
    	for (Pair<String,String> t : delta) {
    		String pre = t.first;
    		//String post = "(" + format(t.second.toString()) + ")'";
    		String post = primeVars(t.second);
    		String action = pre + " /\\ " + post;
    		strTransitions.add(action);
    	}
    	if (strTransitions.isEmpty()) {
    		return "FALSE";
    	}
    	return "\\/ " + String.join("\n  \\/ ", strTransitions);
    }
    
    private static String primeVars(String expr) {
    	String[] strs = expr.split("\\s*="); // matches any number of white space characters
    	return String.join("' =", strs);
    }
    
    private static ArrayList<String> statesToStringList(Set<String> set) {
    	ArrayList<String> arr = new ArrayList<String>();
    	for (String s : set) {
    		arr.add(s);
    	}
    	return arr;
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();

        builder.append("Init States\n");
        for (String s : initStates) {
        	builder.append("  " + s + "\n");
        }

        builder.append("All States\n");
        for (String s : allStates) {
        	builder.append("  " + s + "\n");
        }

        builder.append("Bad States\n");
        for (String s : badStates) {
        	builder.append("  " + s + "\n");
        }

        builder.append("Delta\n");
        for (Pair<String,String> transition : delta) {
        	String src = transition.first;
        	String dst = transition.second;
        	String act = deltaActions.get(transition);
        	Utils.assertNotNull(act, "Found null action!");
    		builder.append("  " + act + ": (" + src + ", " + dst + ")\n");
        }

        return builder.toString();
    }
}
