// an Extended Kripke Structure
// "extended" just means we keep track of some extra info

package tlc2.tool;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

import tlc2.Utils;
import tlc2.tool.ExtKripke.Pair;

import java.lang.StringBuilder;


public class ExtKripke {
    private Set<TLCState> initStates;
    private Set<TLCState> allStates;
    private Set<TLCState> badStates;
    private Set<Pair<TLCState,TLCState>> delta;
    private Map<Pair<TLCState,TLCState>, Action> deltaActions;
    private Set<TLCState> envStates;

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
    	final Set<TLCState> srcMGoodStates = setMinus(srcM.allStates, srcM.badStates);
    	for (final TLCState s : srcMGoodStates) {
    		if (refinedContainerContainsAbstractState(srcClosed.allStates, s)) {
    			this.envStates.add(s);
    		}
    	}
    }
    
    private static boolean refinedContainerContainsAbstractState(final Set<TLCState> container, final TLCState abstrState) {
    	for (final TLCState refinedState : container) {
    		if (refinedImpliesAbstractState(refinedState, abstrState)) {
    			return true;
    		}
    	}
    	return false;
    }
    
    private static boolean refinedImpliesAbstractState(final TLCState refinedState, final TLCState abstrState) {
    	final Set<Pair<String,String>> refinedKvPairs = new HashSet<>(Utils.extractKeyValuePairsFromState(refinedState));
    	final Set<Pair<String,String>> abstrKvPairs = new HashSet<>(Utils.extractKeyValuePairsFromState(abstrState));
    	return refinedKvPairs.containsAll(abstrKvPairs);
    }
    
    // pre-processing

    // bad initial states are explicitly added (via addBadState()) in ModelChecker.java
    public void addInitState(TLCState s) {
        allStates.add(s);
        initStates.add(s);
    }

    public void addGoodState(TLCState s) {
        allStates.add(s);
    }

    public void addBadState(TLCState s) {
        allStates.add(s);
        badStates.add(s);
    }

    public void addTransition(Action act, TLCState src, TLCState dst) {
    	Pair<TLCState,TLCState> transition = new Pair<TLCState,TLCState>(src, dst);
    	delta.add(transition);
    	deltaActions.put(transition, act);
    }
    
    
    // post-processing
    
    public boolean isEmpty() {
    	return this.allStates.isEmpty() || this.initStates.isEmpty();
    }

    public boolean isSafe() {
    	return this.badStates.isEmpty();
    }
    
    public Set<TLCState> reach() {
    	return this.allStates;
    }
    
    public ExtKripke createErrPre() {
    	Set<TLCState> errStates = notAlwaysNotPhiStates();
    	Set<Pair<TLCState,TLCState>> deltaErrSinks = createDeltaWithErrorSinks(badStates, delta);
    	Set<Pair<TLCState,TLCState>> deltaErrPre = filterDeltaByStates(errStates, deltaErrSinks);
    	// no way to add SF yet
    	ExtKripke errPre = new ExtKripke();
    	errPre.initStates = intersection(this.initStates, errStates);
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
        for (TLCState s : this.notAlwaysNotPhiStates()) {
        	builder.append("  " + format(s) + "\n");
        }

        return builder.toString();
    }


    public static <T> Set<T> union(Set<T> s1, Set<T> s2) {
    	Set<T> un = new HashSet<T>();
    	un.addAll(s1);
    	un.addAll(s2);
    	return un;
    }
    
    public static <T> Set<T> intersection(Set<T> s1, Set<T> s2) {
    	Set<T> inters = new HashSet<T>();
    	inters.addAll(s1);
    	inters.retainAll(s2);
    	return inters;
    }
    
    public static <T> Set<T> setMinus(Set<T> s1, Set<T> s2) {
    	Set<T> setmin = new HashSet<T>();
    	setmin.addAll(s1);
    	setmin.removeAll(s2);
    	return setmin;
    }
    
    public static <T> T singletonGetElement(Set<T> set) {
    	assert(set.size() == 1);
    	T elem = null;
    	for (T e : set) {
    		elem = e;
    	}
    	return elem;
    }
    
    public Set<TLCState> safetyBoundary() {
    	return calculateBoundary(BoundaryType.safety);
    }
    
    public Set<TLCState> robustSafetyBoundary() {
    	// the set of states that leave the env, but are guaranteed to be 1-step safe
    	final Set<TLCState> nonEnvStates = setMinus(this.allStates, this.envStates);
    	return setMinus(calculateBoundary(BoundaryType.safety, nonEnvStates), calculateBoundary(BoundaryType.safety, this.badStates));
    }
    
    private Set<TLCState> errorBoundary() {
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
    	final Set<TLCState> nonEnvStates = setMinus(this.allStates, this.envStates);
    	final Set<TLCState> goodNonEnvStates = setMinus(nonEnvStates, this.badStates);
    	final Set<TLCState> envBoundaryStates = calculateBoundary(BoundaryType.safety, nonEnvStates);
    	Map<String, Set<String>> leaveEnv = boundaryPerAction(envBoundaryStates, goodNonEnvStates);
    	
    	// so far we have calculated (state,action) pairs such that there EXISTS a world in which the action
    	// safely leaves the environment. however, we want (state,action) pairs in which the action ALWAYS
    	// safely leaves the environment. we do this by removing any states at the safety boundary for the
    	// given action.
    	final Map<String, Set<String>> safetyBoundary = safetyBoundaryPerAction();
    	Set<String> keysToRemove = new HashSet<>();
    	for (final String act : leaveEnv.keySet()) {
    		if (safetyBoundary.containsKey(act)) {
    			// remove any states that can lead to an error through this action in 1 step
    			final Set<String> robustSafetyBoundaryForAct = setMinus(leaveEnv.get(act), safetyBoundary.get(act));
    			if (robustSafetyBoundaryForAct.isEmpty()) {
    				keysToRemove.add(act);
    			} else {
    				leaveEnv.put(act, robustSafetyBoundaryForAct);
    			}
    		}
    	}
    	for (final String k : keysToRemove) {
    		leaveEnv.remove(k);
    	}
    	return leaveEnv;
    }
    
    // returns a map of (action name) -> (error boundary for the action)
    public Map<String, Set<String>> errorBoundaryPerAction() {
    	return boundaryPerAction(errorBoundary());
    }
    

    private Set<TLCState> calculateBoundary(BoundaryType boundaryType) {
    	return calculateBoundary(boundaryType, this.badStates);
    }
    
    // invariant: all states in frontier are safe (not in errorStates)
    private Set<TLCState> calculateBoundary(final BoundaryType boundaryType, final Set<TLCState> errorStates) {
    	Set<TLCState> goodInitStates = setMinus(this.initStates, errorStates);
    	Set<TLCState> explored = new HashSet<>(goodInitStates);
    	Set<TLCState> frontier = new HashSet<>(goodInitStates);
    	Set<TLCState> boundary = (boundaryType.equals(BoundaryType.safety)) ?
    			new HashSet<>() : intersection(this.initStates, errorStates);
    	
    	while (!frontier.isEmpty()) {
    		Set<TLCState> addToFrontier = new HashSet<TLCState>();
	    	for (TLCState s : frontier) {
	    		explored.add(s);
	    		for (TLCState t : this.succ(s)) {
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
    
    private Map<String, Set<String>> boundaryPerAction(final Set<TLCState> entireBoundary) {
    	return boundaryPerAction(entireBoundary, this.badStates);
    }
        
    private Map<String, Set<String>> boundaryPerAction(final Set<TLCState> entireBoundary, final Set<TLCState> errorStates) {
    	Map<String, Set<String>> groupedBoundaries = new HashMap<>();
    	for (TLCState s : entireBoundary) {
			final String boundaryState = Utils.normalizeStateString(s.toString());
    		for (TLCState t : succ(s)) {
    			Pair<TLCState,TLCState> transition = new Pair<>(s,t);
    			if (this.delta.contains(transition) && errorStates.contains(t)) {
    				final Action act = this.deltaActions.get(transition);
    				final String actName = act.getName().toString();
    				if (!groupedBoundaries.containsKey(actName)) {
    					groupedBoundaries.put(actName, new HashSet<>());
    				}
    				groupedBoundaries.get(actName).add(boundaryState);
    			}
    		}
    	}
    	return groupedBoundaries;
    }
    
    private Set<TLCState> succ(TLCState s) {
    	Set<TLCState> succStates = new HashSet<TLCState>();
    	for (Pair<TLCState,TLCState> t : this.delta) {
    		if (s.equals(t.first)) {
    			succStates.add(t.second);
    		}
    	}
    	return succStates;
    }
    
    private Set<TLCState> notAlwaysNotPhiStates() {
    	Set<TLCState> states = new HashSet<TLCState>();
    	Set<Pair<TLCState,TLCState>> inverseDelta = invertTransitionRelation(delta);
    	for (TLCState errState : this.errorBoundary()) {
    		// perform a DFS (on inverse delta) from errState. add every state we find to "states"
    		// discoverDFS will mutate "states"
    		discoverDFS(errState, inverseDelta, states);
    	}
    	return states;
    }

    private static Set<Pair<TLCState,TLCState>> filterDeltaByStates(Set<TLCState> states, Set<Pair<TLCState,TLCState>> delta) {
    	Set<Pair<TLCState,TLCState>> deltaFiltered = new HashSet<Pair<TLCState,TLCState>>();
    	for (Pair<TLCState,TLCState> t : delta) {
    		if (states.contains(t.first) && states.contains(t.second)) {
    			deltaFiltered.add(t);
    		}
    	}
    	return deltaFiltered;
    }
    
    private static Set<Pair<TLCState,TLCState>> createDeltaWithErrorSinks(Set<TLCState> errStates, Set<Pair<TLCState,TLCState>> delta) {
    	Set<Pair<TLCState,TLCState>> deltaWithErrorSinks = new HashSet<Pair<TLCState,TLCState>>();
    	for (Pair<TLCState,TLCState> t : delta) {
    		if (!errStates.contains(t.first)) {
    			deltaWithErrorSinks.add(t);
    		}
    	}
    	return deltaWithErrorSinks;
    }
    
    private static Set<Pair<TLCState,TLCState>> invertTransitionRelation(Set<Pair<TLCState,TLCState>> d) {
    	Set<Pair<TLCState,TLCState>> inverse = new HashSet<Pair<TLCState,TLCState>>();
    	for (Pair<TLCState,TLCState> t : d) {
    		inverse.add(new Pair<TLCState,TLCState>(t.second, t.first));
    	}
    	return inverse;
    }
    
    private static void discoverDFS(TLCState start, Set<Pair<TLCState,TLCState>> delta, Set<TLCState> states) {
    	// base case
    	if (states.contains(start)) {
    		return;
    	}
    	
    	states.add(start);
    	for (Pair<TLCState,TLCState> t : delta) {
    		if (start.equals(t.first)) {
    			discoverDFS(t.second, delta, states);
    		}
    	}
    }
    
    // compute the representation for \eta(m2,P) - \eta(m1,P)
    // note: \eta(m2,P) - \eta(m1,P) = beh(m1_err) - beh(m2_err)
    // i.e. we find all erroneous behaviors of m1 that are NOT erroneous behaviors of m2
    public static Set<Pair<TLCState,Action>> behaviorDifferenceRepresentation(final ExtKripke m1, final ExtKripke m2) {
    	final Set<TLCState> mutualReach = mutualReach(m1, m2);
    	final Set<Pair<TLCState,TLCState>> m1MinusM2Delta = setMinus(m1.delta, m2.delta);
    	final Set<Pair<TLCState,Action>> rep = new HashSet<Pair<TLCState,Action>>();
		for (Pair<TLCState,TLCState> t1 : m1MinusM2Delta) {
			TLCState s = t1.first;
			if (mutualReach.contains(s)) {
				// found an outgoing transition (of ONLY m1) from s
				final Action act = m1.deltaActions.get(t1);
				rep.add(new Pair<TLCState,Action>(s, act));
			}
		}
    	return rep;
    }
    
    private static Set<TLCState> mutualReach(final ExtKripke m1, final ExtKripke m2) {
    	Set<TLCState> reach = new HashSet<TLCState>();
    	Set<TLCState> mutualInit = intersection(m1.initStates, m2.initStates);
    	Set<Pair<TLCState,TLCState>> mutualDelta = intersection(m1.delta, m2.delta);
    	for (TLCState init : mutualInit) {
        	mutualReach(mutualDelta, init, reach);
    	}
    	return reach;
    }
    
    private static void mutualReach(final Set<Pair<TLCState,TLCState>> mutualDelta, final TLCState init, Set<TLCState> reach) {
    	reach.add(init);
    	for (Pair<TLCState,TLCState> t : mutualDelta) {
    		if (init.equals(t.first)) {
    			TLCState succ = t.second;
    			if (!reach.contains(succ)) {
    				mutualReach(mutualDelta, succ, reach);
    			}
    		}
    	}
    }
    
    
    
    // printing

    @Override
    public String toString() {
    	return printKS();
    }
    
    
    // print a TLA+ spec
    
    // TODO if the spec has fairness requirements we need to add them in
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
    	for (Pair<TLCState,TLCState> t : delta) {
    		String pre = format(t.first.toString());
    		//String post = "(" + format(t.second.toString()) + ")'";
    		String post = primeVars(format(t.second.toString()));
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
    
    public String toTLASpec(String moduleName) {
    	throw new RuntimeException("Not implemented!");
    	//StringBuilder builder = new StringBuilder();
    	//builder.append("--------------------------- MODULE ");
    	//builder.append(moduleName);
    	//builder.append(" ---------------------------\n");
    	//return builder.toString();
    }
    
    private static ArrayList<String> statesToStringList(Set<TLCState> set) {
    	ArrayList<String> arr = new ArrayList<String>();
    	for (TLCState s : set) {
    		arr.add(format(s.toString()));
    	}
    	return arr;
    }
    
    
    // code for printKS() below

    private Map<Action, ArrayList<TLCState>> createActionGuards() {
    	Map<Action, ArrayList<TLCState>> actionGuards = new HashMap<Action, ArrayList<TLCState>>();
    	
    	for (Action act : deltaActions.values()) {
    		actionGuards.put(act, new ArrayList<TLCState>());
    	}
    	
        for (TLCState src : allStates) {
            for (TLCState dst : badStates) {
            	Pair<TLCState,TLCState> unsafeTransition = new Pair<TLCState,TLCState>(src, dst);
            	if (delta.contains(unsafeTransition)) {
            		// found an "unsafe" transition
            		Action act = deltaActions.get(unsafeTransition);
            		actionGuards.get(act).add(src);
            	}
            }
        }
        return actionGuards;
    }
    
    private Set<Pair<String, String>> createActionGuardStrings(Map<Action, ArrayList<TLCState>> actionGuards) {
    	Set<Pair<String, String>> actionGuardStrings = new HashSet<Pair<String, String>>();
    	for (Map.Entry<Action, ArrayList<TLCState>> e : actionGuards.entrySet()) {
    		Action act = e.getKey();
    		StringBuilder builder = new StringBuilder();
    		for (TLCState s : e.getValue()) {
    			String guard = " /\\ ~(" + format(s.toString()) + ")";
    			builder.append(guard);
    		}
    		Pair<String,String> guardStringPair = new Pair<String,String>(act.getName().toString(), builder.toString());
    		actionGuardStrings.add(guardStringPair);
    	}
    	return actionGuardStrings;
    }
    
    private String createGuardedNext() {
    	Map<Action, ArrayList<TLCState>> actionGuards = createActionGuards();
    	Set<Pair<String, String>> actionGuardStrings = createActionGuardStrings(actionGuards);
    	
    	StringBuilder builder = new StringBuilder();
    	for (Pair<String, String> guardedActionPair : actionGuardStrings) {
    		String act = guardedActionPair.first;
    		String guardedAction = guardedActionPair.second;
    		builder.append(act).append("_Guarded == ");
    		builder.append(act).append(guardedAction).append("\n");
    	}
    	builder.append("Next ==\n");
    	for (Pair<String, String> guardedActionPair : actionGuardStrings) {
    		String act = guardedActionPair.first;
    		builder.append("  \\/ ").append(act).append("_Guarded").append("\n");
    	}
    	return builder.toString();
    }
    
    private String printKS() {
        StringBuilder builder = new StringBuilder();

        builder.append("Init States\n");
        for (TLCState s : initStates) {
        	builder.append("  " + format(s) + "\n");
        }

        builder.append("All States\n");
        for (TLCState s : allStates) {
        	builder.append("  " + format(s) + "\n");
        }

        builder.append("Bad States\n");
        for (TLCState s : badStates) {
        	builder.append("  " + format(s) + "\n");
        }

        builder.append("Delta\n");
        for (Pair<TLCState,TLCState> transition : delta) {
        	TLCState src = transition.first;
        	TLCState dst = transition.second;
        	Action act = deltaActions.get(transition);
        	if (act != null) {
        		builder.append("  " + act.getName() + ": (" + format(src.toString()) + ", " + format(dst.toString()) + ")\n");
        	}
        }
        
        //builder.append("\n");
        //builder.append("WA:\n");
        //builder.append(createGuardedNext());

        return builder.toString();
    }


    public static class Pair<A,B> {
        public A first;
        public B second;
        
        public Pair(A f, B s) {
        	first = f;
        	second = s;
        }
        
        @Override
        public int hashCode() {
        	return first.hashCode() + 5701 * second.hashCode();
        }
        
        @Override
        public boolean equals(Object other) {
        	if (other instanceof Pair<?,?>) {
        		Pair<?,?> p = (Pair<?,?>) other;
        		return this.first.equals(p.first) && this.second.equals(p.second);
        	}
        	return false;
        }
        
        @Override
        public String toString() {
        	return "Pair(" + first.toString() + ", " + second.toString() + ")";
        }
    }
    
    public static <A,B> Set<A> projectFirst(Set<Pair<A,B>> set) {
    	Set<A> proj = new HashSet<A>();
    	for (Pair<A,B> e : set) {
    		proj.add(e.first);
    	}
    	return proj;
    }
    
    private static String format(TLCState s) {
    	return format(s.toString());
    }
    
    private static String format(String s) {
    	return stripLeadingAnd(spaceAfterAnd(stripNewline(s))).trim();
    }

    private static String stripLeadingAnd(String s) {
		if (s.length() >= 2 && s.substring(0, 2).equals("/\\")) {
			return s.substring(2);
		}
		else {
			return s;
		}
	}
    
    private static String spaceAfterAnd(String s) {
    	ArrayList<String> conjuncts = new ArrayList<String>();
    	String[] raw = s.split(Pattern.quote("/\\"));
    	for (int i = 0; i < raw.length; ++i) {
    		String val = raw[i].trim();
    		if (!val.isEmpty()) {
    			conjuncts.add(val);
    		}
    	}
    	return String.join(" /\\ ", conjuncts);
	}
    
    private static String stripNewline(String s) {
		StringBuilder sNew = new StringBuilder();
		for (int i = s.length()-1; i >= 0; --i) {
			char c = s.charAt(i);
			if (c != '\n') {
				sNew.insert(0, c);
			}
		}
		return sNew.toString();
	}
    
    private enum BoundaryType {
    	safety, error
    }
}
