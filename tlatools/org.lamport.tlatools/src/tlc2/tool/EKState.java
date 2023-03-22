package tlc2.tool;

// ExtKripkeState
public class EKState {
	private final String rawTlcStr;
	
	public EKState(final String rawTlcStr) {
		this.rawTlcStr = rawTlcStr;
	}
	
	@Override
	public boolean equals(Object o) {
		if (o instanceof EKState) {
			final EKState other = (EKState) o;
			return this.rawTlcStr.equals(other.rawTlcStr);
		}
		return false;
	}
	
	@Override
	public int hashCode() {
		return this.rawTlcStr.hashCode();
	}
	
	@Override
	public String toString() {
		return this.rawTlcStr;
	}
}
