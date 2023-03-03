package tlc2.tool;

import tlc2.Utils;

public class TLCStateKripke extends TLCStateMut {
	public TLCStateKripke(TLCStateMut other) {
		super(other.values);
	}
	
	@Override
	public int hashCode() {
		return Utils.normalizeStateString(this.toString()).hashCode();
	}
	
	@Override
	public boolean equals(Object other) {
		if (other instanceof TLCStateKripke) {
			TLCStateKripke o = (TLCStateKripke) other;
			return Utils.normalizeStateString(this.toString()).equals(Utils.normalizeStateString(o.toString()));
		}
		return false;
	}
}
