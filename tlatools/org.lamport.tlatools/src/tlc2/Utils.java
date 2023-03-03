package tlc2;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.regex.Pattern;

import tlc2.tool.Action;
import tlc2.tool.TLCState;
import tlc2.tool.ExtKripke.Pair;

public class Utils {

	private static final String QUOTE = "\"";
	private static final String COLON = ":";
	private static final String LSQBRACE = "[";
	private static final String RSQBRACE = "]";
    
	public static ArrayList<Pair<String,String>> extractKeyValuePairsFromState(String tlaState) {
    	ArrayList<Pair<String,String>> kvPairs = new ArrayList<>();
    	String[] conjuncts = tlaState.split(Pattern.quote("/\\"));
    	for (int i = 0; i < conjuncts.length; ++i) {
    		final String tlaConjunct = conjuncts[i];
    		final Pair<String,String> kvPair = extractKeyValuePairFromAssignment(tlaConjunct);
    		kvPairs.add(kvPair);
    	}
    	return kvPairs;
    }
    
    public static Pair<String, String> extractKeyValuePairFromAssignment(String assg) {
    	String[] kvp = assg.split("=");
		assert(kvp.length == 2);
		final String key = kvp[0].trim();
		final String val = kvp[1].trim();
		return new Pair<>(key,val);
    }
    
    public static Set<String> stateSetToStringSet(Set<TLCState> src) {
    	Set<String> dst = new HashSet<String>();
    	for (TLCState s : src) {
    		final String state = normalizeStateString(s.toString());
    		dst.add(state);
    	}
    	return dst;
    }
    
    public static String normalizeStateString(String s) {
		//String[] conjuncts = s.replace('\n', ' ').trim().split(Pattern.quote("\\s*/\\\\s*"));
    	String[] conjuncts = s.split(Pattern.quote("\n"));
    	for (int i = 0; i < conjuncts.length; ++i) {
    		final String orig = conjuncts[i];
    		conjuncts[i] = orig.replaceAll(Pattern.quote("/\\"), "").trim();
    	}
		Arrays.sort(conjuncts);
		return String.join(" /\\ ", conjuncts);
	}
    
    public static boolean hasInvariant(final TLC tlc, final String inv) {
    	for (Action i : tlc.tool.getInvariants()) {
    		final String name = i.getName().toString();
    		if (inv.equals(name)) {
    			return true;
    		}
    	}
    	return false;
    }
    
    public static String instanceWithList(ArrayList<String> vars) {
    	ArrayList<String> varArrowList = new ArrayList<String>();
    	for (String var : vars) {
    		final String arrow = var + " <- " + var;
    		varArrowList.add(arrow);
    	}
    	return String.join(", ", varArrowList);
    }

    public static <T> ArrayList<T> toArrayList(Set<T> src) {
    	ArrayList<T> dst = new ArrayList<T>();
    	for (T s : src) {
    		dst.add(s);
    	}
    	return dst;
    }

    public static <T> ArrayList<T> toArrayList(T[] src) {
    	ArrayList<T> dst = new ArrayList<T>();
    	for (int i = 0; i < src.length; ++i) {
    		dst.add(src[i]);
    	}
    	return dst;
    }
    
    public static ArrayList<String> filterArrayBlackList(String filter, String[] arr) {
    	ArrayList<String> filtered = new ArrayList<String>();
    	for (int i = 0; i < arr.length; ++i) {
    		String e = arr[i];
    		if (!filter.equals(e)) {
    			filtered.add(e);
    		}
    	}
    	return filtered;
    }
    
    public static ArrayList<String> filterArrayWhiteList(List<String> filter, String[] arr) {
    	ArrayList<String> filtered = new ArrayList<String>();
    	for (int i = 0; i < arr.length; ++i) {
    		String e = arr[i];
    		if (filter.contains(e)) {
    			filtered.add(e);
    		}
    	}
    	return filtered;
    }
    
    public static int findFirstLineOfSpec(ArrayList<String> lines) {
    	for (int i = 0; i < lines.size(); ++i) {
    		String line = lines.get(i);
    		if (line.length() >= 3 && line.substring(0,3).equals("---")) {
    			return i;
    		}
    	}
    	throw new RuntimeException("Unable to find the last line in the TLA+ spec!");
    }
    
    public static int findLastLineOfSpec(ArrayList<String> lines) {
    	for (int i = lines.size()-1; i >= 0; --i) {
    		String line = lines.get(i);
    		if (line.length() >= 3 && line.substring(0,3).equals("===")) {
    			return i;
    		}
    	}
    	throw new RuntimeException("Unable to find the last line in the TLA+ spec!");
    }
    
    public static void printStringArr(ArrayList<String> arr) {
    	for (String s : arr) {
    		System.out.println(s);
    	}
    }
    
    // thanks https://stackoverflow.com/questions/2406121/how-do-i-escape-a-string-in-java
    public static String stringEscape(String s){
	  return s.replace("\\", "\\\\")
	          .replace("\t", "\\t")
	          .replace("\b", "\\b")
	          .replace("\n", "\\n")
	          .replace("\r", "\\r")
	          .replace("\f", "\\f")
	          .replace("\'", "\\'")
	          .replace("\"", "\\\"");
	}
    
    public static String extractSyntaxFromSource(final String tla, final String loc) {
    	String[] parts = loc.replaceAll(",", "").split(" ");
    	int startLine = -1;
    	int startCol = -1;
    	int endLine = -1;
    	int endCol = -1;
    	for (int i = 0; i < parts.length-1; ++i) {
    		final String part = parts[i];
			final String strLineOrColNum = parts[i+1];
    		if (part.equals("line") && startLine < 0) {
    			startLine = Integer.parseInt(strLineOrColNum) - 1;
    		}
    		else if (part.equals("line") && startLine >= 0) {
    			endLine = Integer.parseInt(strLineOrColNum) - 1;
    		}
    		else if (part.equals("col") && startCol < 0) {
    			startCol = Integer.parseInt(strLineOrColNum) - 1;
    		}
    		else if (part.equals("col") && startCol >= 0) {
    			endCol = Integer.parseInt(strLineOrColNum);
    		}
    	}
    	assert(startLine >= 0);
    	assert(startCol >= 0);
    	assert(endLine >= 0);
    	assert(endCol >= 0);
    	assert(startLine <= endLine);

    	ArrayList<String> tlaSource = fileContents(tla);
    	// single line extraction
    	if (startLine == endLine) {
    		final String line = tlaSource.get(startLine);
    		final String syntax = line.substring(startCol, endCol);
    		return syntax;
    	}
    	// multi-line extraction
    	else {
        	StringBuilder builder = new StringBuilder();
        	for (int i = startLine; i <= endLine; ++i) {
        		final String line = tlaSource.get(i);
        		if (i == startLine) {
        			builder.append(line.substring(startCol));
        		}
        		else if (i == endLine) {
        			builder.append(" ").append(line.substring(0, endCol));
        		}
        		else {
        			builder.append(" ").append(line);
        		}
        	}
        	return builder.toString();
    	}
    }
    
    public static void writeFile(String file, String contents) {
    	try {
    		BufferedWriter writer = new BufferedWriter(new FileWriter(file));
    	    writer.write(contents);
    	    writer.close();
    	}
    	catch (IOException e) {
    		throw new RuntimeException("Failed to write to file: " + file + "!");
    	}
    }
    
    public static ArrayList<String> fileContents(String loc) {
    	ArrayList<String> lines = new ArrayList<String>();
    	try {
	      Scanner scan = new Scanner(new File(loc));
	      while (scan.hasNextLine()) {
	        lines.add(scan.nextLine());
	      }
	      scan.close();
	    } catch (FileNotFoundException e) {
	      System.out.println("The file " + loc + " does not exist!");
	      e.printStackTrace();
	    }
    	return lines;
    }
    
    public static String asJson(Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	final String strs = asJsonStrs(jsonStrs);
    	final String lists = asJsonLists(jsonLists);
    	if (strs.isEmpty() && lists.isEmpty()) {
    		return "{}";
    	}
    	else if (strs.isEmpty()) {
        	return "{" + lists + "}";
    	}
    	else if (lists.isEmpty()) {
        	return "{" + strs + "}";
    	}
    	else {
        	return "{" + strs + "," + lists + "}";
    	}
    }
	
    private static String asJsonStrs(Map<String,String> output) {
    	List<String> fields = new ArrayList<>();
    	for (String key : output.keySet()) {
    		final String value = output.get(key);
        	StringBuilder builder = new StringBuilder();
    		builder.append(QUOTE).append(key).append(QUOTE).append(COLON)
    			.append(QUOTE).append(value).append(QUOTE);
    		fields.add(builder.toString());
    	}
    	final String fieldsStr = String.join(",", fields);
    	return fieldsStr;
    	//return "{" + fieldsStr + "}";
    }
    
    private static String asJsonLists(Map<String,List<String>> output) {
    	List<String> fields = new ArrayList<>();
    	for (String key : output.keySet()) {
    		final List<String> value = output.get(key);
    		final String flatValue = "\"" + String.join("\",\"", value) + "\"";
        	StringBuilder builder = new StringBuilder();
    		builder.append(QUOTE).append(key).append(QUOTE).append(COLON)
    			.append(LSQBRACE).append(flatValue).append(RSQBRACE);
    		fields.add(builder.toString());
    	}
    	final String fieldsStr = String.join(",", fields);
    	return fieldsStr;
    	//return "{" + fieldsStr + "}";
    }
}
