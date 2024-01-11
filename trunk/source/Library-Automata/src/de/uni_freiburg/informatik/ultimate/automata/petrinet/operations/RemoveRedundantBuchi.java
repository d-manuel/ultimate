/*
 * Copyright (C) 2023-2024 Manuel Dienert
 * Copyright (C) 2009-2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/*
 * Merge places with the Same pre- and postset
 */
public class RemoveRedundantBuchi<LETTER, PLACE> extends GeneralOperation<LETTER, PLACE, IStateFactory<PLACE>> {

	private final IPetriNet<LETTER, PLACE> mOperand;
	// private Collection<Condition<LETTER, PLACE>> mAcceptingConditions;
	private final BoundedPetriNet<LETTER, PLACE> mResult;
	private final Map<PLACE, PLACE> mReplacement = new HashMap<>();

	public RemoveRedundantBuchi(final AutomataLibraryServices services, final IPetriNet<LETTER, PLACE> operand) {
		super(services);
		mOperand = operand;

		printStartMessage();
		mResult = new BoundedPetriNet<>(mServices, mOperand.getAlphabet(), false);
		computeRedudantPlaces();
		updatePetriNet();
		printExitMessage();
	}

	/**
	 * Compute places that have the same pre and postset transitions and merge them into single places
	 */
	private void computeRedudantPlaces() {
		for (final var trans : mOperand.getTransitions()) {
			final Set<PLACE> candidates = trans.getSuccessors();

			for (final PLACE candidate : candidates) {
				if (mReplacement.containsKey(candidates)) {
					continue;
				}
				final Set<Transition<LETTER, PLACE>> preset = mOperand.getPredecessors(candidate);
				final Set<Transition<LETTER, PLACE>> postset = mOperand.getSuccessors(candidate);

				final Set<PLACE> replacements =
						candidates.stream().filter(place -> mOperand.getPredecessors(place).equals(preset)
								&& mOperand.getSuccessors(place).equals(postset)).collect(Collectors.toSet());
				replacements.forEach(x -> mReplacement.put(x, candidate)); // also maps candidate to itself!

				mResult.addPlace(candidate, mOperand.getInitialPlaces().contains(candidate),
						replacements.stream().anyMatch(mOperand::isAccepting));
			}
		}
	}

	private PLACE getReplacementPlace(final PLACE place) {
		return mReplacement.getOrDefault(place, place);
	}

	// create the new Petri net with reduced places
	private void updatePetriNet() {
		// Add remaining places needed here
		mOperand.getPlaces().stream().filter(place -> !mReplacement.values().contains(place)).forEach(place -> mResult
				.addPlace(place, mOperand.getInitialPlaces().contains(place), mOperand.isAccepting(place)));
		// TODO eigentlich nur initial palces, sonst wäre die transiton unnötig nochmal anschauen wie in
		// RemoveRedundantFlow war.
		// -> ich mach das jetzt einfach mal in getReplacmeentPlace fürs erste.
		// nein geht nicht, da wir immer erst places, dann transitions hinzufügen müssen!

		// Add transitions
		for (final var trans : mOperand.getTransitions()) {
			final var preds = trans.getPredecessors().stream().map(p -> getReplacementPlace(p)).distinct()
					.collect(Collectors.toSet());
			final var succs = trans.getSuccessors().stream().map(p -> getReplacementPlace(p)).distinct()
					.collect(Collectors.toSet());
			mResult.addTransition(trans.getSymbol(), ImmutableSet.of(preds), ImmutableSet.of(succs));
		}
	}

	@Override
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

	@Override
	public String exitMessage() {
		// return "Finished " + this.getClass().getSimpleName() + ", result has " + mResult.sizeInformation();
		return "Finished";
	}
}
