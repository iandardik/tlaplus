// an Extended Kripke Structure
// "extended" just means we keep track of some extra info

package tlc2.tool;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

import tlc2.TLC;
import tlc2.Utils;
import tlc2.tool.ExtKripke.Pair;

import java.lang.StringBuilder;


public class ExtKripke {
    private Set<TLCState> initStates = new HashSet<>();
    private Set<TLCState> allStates = new HashSet<>();
    private Set<TLCState> badStates = new HashSet<>();
    private Set<Pair<TLCState,TLCState>> delta = new HashSet<>();
    private Map<Pair<TLCState,TLCState>, Action> deltaActions = new HashMap<>();

    public ExtKripke() {}
    
    // pre-processing

    // bad initial states are explicitly added (via addBadState()) in ModelChecker.java
    public void addInitState(TLCState s) {
    	if (!(s instanceof TLCStateMut)) {
    		throw new RuntimeException("Invalid state added");
    	}
    	TLCState sk = new TLCStateKripke((TLCStateMut) s);
        allStates.add(sk);
        initStates.add(sk);
    }

    public void addGoodState(TLCState s) {
    	if (!(s instanceof TLCStateMut)) {
    		throw new RuntimeException("Invalid state added");
    	}
    	TLCState sk = new TLCStateKripke((TLCStateMut) s);
        allStates.add(sk);
    }

    public void addBadState(TLCState s) {
    	if (!(s instanceof TLCStateMut)) {
    		throw new RuntimeException("Invalid state added");
    	}
    	TLCState sk = new TLCStateKripke((TLCStateMut) s);
        allStates.add(sk);
        badStates.add(sk);
    }

    public void addTransition(Action act, TLCState src, TLCState dst) {
    	if (!(src instanceof TLCStateMut)) {
    		throw new RuntimeException("Invalid source state added");
    	}
    	if (!(dst instanceof TLCStateMut)) {
    		throw new RuntimeException("Invalid dest state added");
    	}
    	TLCState srck = new TLCStateKripke((TLCStateMut) src);
    	TLCState dstk = new TLCStateKripke((TLCStateMut) dst);
    	Pair<TLCState,TLCState> transition = new Pair<TLCState,TLCState>(srck, dstk);
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
    
    /*
    public static Set<TLCState> tlcStateIntersection(Set<TLCState> s1, Set<TLCState> s2) {
    	Map<String,TLCState> s1Map = new HashMap<>();
    	for (TLCState s : s1) {
    		s1Map.put(Utils.normalizeStateString(s.toString()), s);
    	}
    	Map<String,TLCState> s2Map = new HashMap<>();
    	for (TLCState s : s2) {
    		s2Map.put(Utils.normalizeStateString(s.toString()), s);
    	}
    	
    	Set<TLCState> inters = new HashSet<>();
    	for (String k : s1Map.keySet()) {
    		if (s2Map.containsKey(k)) {
    			TLCState state = s1Map.get(k);
    			inters.add(state);
    		}
    	}
    	for (String k : s2Map.keySet()) {
    		if (s1Map.containsKey(k)) {
    			TLCState state = s2Map.get(k);
    			inters.add(state);
    		}
    	}
    	return inters;
    }
    
    public static Set<Pair<TLCState,TLCState>> deltaIntersection(Set<Pair<TLCState,TLCState>> s1, Set<Pair<TLCState,TLCState>> s2) {
    	Map<String,Pair<TLCState,TLCState>> s1Map = new HashMap<>();
    	for (Pair<TLCState,TLCState> s : s1) {
    		s1Map.put(Utils.normalizeStateString(s.toString()), s);
    	}
    	Map<String,Pair<TLCState,TLCState>> s2Map = new HashMap<>();
    	for (Pair<TLCState,TLCState> s : s2) {
    		s2Map.put(Utils.normalizeStateString(s.toString()), s);
    	}
    	
    	Set<Pair<TLCState,TLCState>> inters = new HashSet<>();
    	for (String k : s1Map.keySet()) {
    		if (s2Map.containsKey(k)) {
    			Pair<TLCState,TLCState> state = s1Map.get(k);
    			inters.add(state);
    		}
    	}
    	for (String k : s2Map.keySet()) {
    		if (s1Map.containsKey(k)) {
    			Pair<TLCState,TLCState> state = s2Map.get(k);
    			inters.add(state);
    		}
    	}
    	return inters;
    }
    
    public static Set<Pair<TLCState,TLCState>> tlcStateSetMinus(Set<Pair<TLCState,TLCState>> s1, Set<Pair<TLCState,TLCState>> s2) {
    	Map<String,Pair<TLCState,TLCState>> s1Map = new HashMap<>();
    	for (Pair<TLCState,TLCState> s : s1) {
    		s1Map.put(Utils.normalizeStateString(s.toString()), s);
    	}
    	Map<String,Pair<TLCState,TLCState>> s2Map = new HashMap<>();
    	for (Pair<TLCState,TLCState> s : s2) {
    		s2Map.put(Utils.normalizeStateString(s.toString()), s);
    	}
    	
    	Set<Pair<TLCState,TLCState>> setm = new HashSet<>();
    	for (String k : s1Map.keySet()) {
    		if (!s2Map.containsKey(k)) {
    			Pair<TLCState,TLCState> state = s1Map.get(k);
    			setm.add(state);
    		}
    	}
    	return setm;
    }*/
    
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
    
    public Set<TLCState> errorBoundary() {
    	return calculateBoundary(BoundaryType.error);
    }
    
    // returns a map of (action name) -> (safety boundary for the action)
    public Map<String, Set<String>> safetyBoundaryPerAction() {
    	return boundaryPerAction(safetyBoundary());
    }
    
    // returns a map of (action name) -> (error boundary for the action)
    public Map<String, Set<String>> errorBoundaryPerAction() {
    	return boundaryPerAction(errorBoundary());
    }
    
    private Map<String, Set<String>> boundaryPerAction(final Set<TLCState> entireBoundary) {
    	Map<String, Set<String>> groupedBoundaries = new HashMap<>();
    	for (TLCState s : entireBoundary) {
			final String boundaryState = Utils.normalizeStateString(s.toString());
    		for (TLCState t : succ(s)) {
    			Pair<TLCState,TLCState> transition = new Pair<>(s,t);
    			if (this.delta.contains(transition) && this.badStates.contains(t)) {
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
    
    // invariant: all states in frontier are safe (not in this.badStates)
    private Set<TLCState> calculateBoundary(BoundaryType boundaryType) {
    	Set<TLCState> goodInitStates = setMinus(this.initStates, this.badStates);
    	Set<TLCState> explored = new HashSet<>(goodInitStates);
    	Set<TLCState> frontier = new HashSet<>(goodInitStates);
    	Set<TLCState> boundary = (boundaryType.equals(BoundaryType.safety)) ?
    			new HashSet<>() : intersection(this.initStates, this.badStates);
    	
    	while (!frontier.isEmpty()) {
    		Set<TLCState> addToFrontier = new HashSet<TLCState>();
	    	for (TLCState s : frontier) {
	    		explored.add(s);
	    		for (TLCState t : this.succ(s)) {
	    			if (this.badStates.contains(t)) {
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
    	System.out.println("m1 init:");
    	for (TLCState s : m1.initStates) {
    		System.out.println(s);
    		//System.out.println(s.getClass());
    	}
    	System.out.println("m2 init:");
    	for (TLCState s : m2.initStates) {
    		System.out.println(s);
    		//System.out.println(s.getClass());
    	}
    	System.out.println("m1 cap m2 init:");
    	for (TLCState s : intersection(m1.initStates, m2.initStates)) {
    		System.out.println(s);
    	}
    	System.out.println("m1 cup m2 init:");
    	for (TLCState s : union(m1.initStates, m2.initStates)) {
    		System.out.println(s);
    	}
    	
    	
    	
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
        	builder.append("  " + act.getName() + ": (" + format(src.toString()) + ", " + format(dst.toString()) + ")\n");
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
        	return this.first.toString() + "_" + this.second.toString();
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
    	return Utils.normalizeStateString(s);
    	//return stripLeadingAnd(spaceAfterAnd(stripNewline(s))).trim();
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
    
    public enum BoundaryType {
    	safety, error
    }
}
