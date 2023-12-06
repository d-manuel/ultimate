package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public final class Utils<L> {

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

	// prints a Petri net to console in apt format
	private String petriToApt(final IPetriNet<L, IPredicate> abstraction) {
		final StringBuilder res = new StringBuilder();

		final String placePattern = "(\\d+?)#.*";
		final String labelPattern = "\\[(\\d+?)\\].*";

		res.append(".name \"output-net \"\n");
		res.append(".type LPN\n");
		res.append(".places \n");
		for (final var place : abstraction.getPlaces()) {
			final String newPlace = place.toString().replaceAll(placePattern, "$1");
			res.append(newPlace + "\n");
		}
		final StringBuilder transitions = new StringBuilder(".transitions\n");
		final StringBuilder flows = new StringBuilder(".flows \n");
		int i = 0;
		for (final var trans : abstraction.getTransitions()) {
			final String name = "t" + i;
			final String label = trans.getSymbol().toString().replaceAll(labelPattern, "$1");
			transitions.append(name + "[label=\"" + label + "\"]" + "\n");
			flows.append(name + ": {");
			// flows.append(trans.getPredecessors().toString().replaceAll(placePattern, "$1"));
			for (final var pred : trans.getPredecessors()) {
				flows.append(pred.toString().replaceAll(placePattern, "$1"));
				flows.append(",");
			}
			flows.deleteCharAt(flows.length() - 1);
			flows.append("} -> {");
			// flows.append(trans.getSuccessors().toString().replaceAll(placePattern, "$1"));
			for (final var succ : trans.getSuccessors()) {
				flows.append(succ.toString().replaceAll(placePattern, "$1"));
				flows.append(",");
			}
			flows.deleteCharAt(flows.length() - 1);
			flows.append("} \n");
			i++;
		}
		res.append(transitions);
		res.append(flows);

		res.append(".initial_marking {");
		// res.append(abstraction.getInitialPlaces().toString().replaceAll(placePattern, "$1"));
		for (final var initPlace : abstraction.getInitialPlaces()) {
			final String initPlaceString = initPlace.toString();
			final String toReplace = initPlace.toString().replaceAll(placePattern, "$1,");
			res.append(initPlace.toString().replaceAll(placePattern, "$1"));
			res.append(",");
		}
		res.deleteCharAt(res.length() - 1);
		res.append("}");

		return res.toString();
	}

}