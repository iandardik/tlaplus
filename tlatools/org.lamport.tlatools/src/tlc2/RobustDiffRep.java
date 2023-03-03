package tlc2;

import java.util.Map;
import java.util.Set;


public class RobustDiffRep {
	private static final String DIFF_REP_FILE = "diff_rep_file";
	private static final String DIFF_REP_FILE1 = "diff_rep_file1";
	private static final String DIFF_REP_FILE2 = "diff_rep_file2";
	
	public enum SpecScope {
		Spec, Spec1, Spec2
	}
	
	public static String keyForSpecScope(SpecScope scope, String key, String key1, String key2) {
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
	
	
	private final String specName;
	private final SpecScope specScope;
	private final String outputLocation;
	private final Set<String> safetyBoundary;
	private Map<String, String> jsonStrs;
	
	public RobustDiffRep(String specName, SpecScope scope, String outputLoc, Set<String> safetyBoundary, Map<String,String> jsonStrs) {
		this.specName = specName;
		this.specScope = scope;
		this.safetyBoundary = safetyBoundary;
		this.outputLocation = outputLoc;
		this.jsonStrs = jsonStrs;
	}
	
	public void writeBoundary(final String fileName) {
    	final String diffRepFileNameKey = keyForSpecScope(specScope, DIFF_REP_FILE, DIFF_REP_FILE1, DIFF_REP_FILE2);
    	StringBuilder builder = new StringBuilder();
    	for (String diffState : this.safetyBoundary) {
    		builder.append(diffState).append("\n");
    	}
    	final String file = this.outputLocation + fileName + ".txt";
    	Utils.writeFile(file, builder.toString());
    	this.jsonStrs.put(diffRepFileNameKey, file);
	}
	
	public void writeBoundaryFOLSeparatorFile() {
		
	}
}
