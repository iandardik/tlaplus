// an Extended Kripke Structure
// "extended" just means we keep track of some extra info

package tlc2.tool;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;
import java.lang.StringBuilder;


public class ExtKripke {
    private Set<TLCState> initStates = new HashSet<TLCState>();
    private Set<TLCState> allStates = new HashSet<TLCState>();
    private Set<TLCState> badStates = new HashSet<TLCState>();
    private Set<Pair<TLCState,TLCState>> delta = new HashSet<Pair<TLCState,TLCState>>();
    private Map<Pair<TLCState,TLCState>, Action> deltaActions = new HashMap<Pair<TLCState,TLCState>, Action>();

    public ExtKripke() {}

    // TODO: right now we assume all init states are good, fix this
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

    @Override
    public String toString() {
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
        
        builder.append("\n");
        builder.append("WA:\n");
        builder.append(createGuardedNext());

        return builder.toString();
    }


    private class Pair<A,B> {
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
        		Pair p = (Pair) other;
        		return this.first.equals(p.first) && this.second.equals(p.second);
        	}
        	return false;
        }
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
}
