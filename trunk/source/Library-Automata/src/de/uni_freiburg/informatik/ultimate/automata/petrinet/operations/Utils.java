package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;

public final class Utils {

	private Utils() {
	};

	/*
	 * Properly generate a String for a Petri Transition
	 */
	public static <LETTER, PLACE> String transitionToString(final Transition<LETTER, PLACE> trans) {
		String res = "{";
		res += "{";
		for (final var pre : trans.getPredecessors()) {
			res += " " + pre.toString() + " ";
		}
		res += "} " + trans.getSymbol() + " {";
		for (final var suc : trans.getSuccessors()) {
			res += " " + suc.toString() + " ";
		}
		res += "}}";
		return res;
	}
}
