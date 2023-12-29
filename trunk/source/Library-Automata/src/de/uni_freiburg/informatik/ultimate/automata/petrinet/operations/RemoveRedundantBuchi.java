/*
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
import java.util.HashSet;
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

/**
 */
// public class RemoveRedundantBuchi<LETTER, PLACE, CRSF extends IStateFactory<PLACE> &
// IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
// extends UnaryNetOperation<LETTER, PLACE, CRSF> {
public class RemoveRedundantBuchi<LETTER, PLACE> extends GeneralOperation<LETTER, PLACE, IStateFactory<PLACE>> {

	private final IPetriNet<LETTER, PLACE> mOperand;
	// private Collection<Condition<LETTER, PLACE>> mAcceptingConditions;
	// private final BoundedPetriNet<LETTER, PLACE> mResult;
	// private final Map<Set<PLACE>, PLACE> mReplacement = new HashMap<>();
	private final Map<PLACE, PLACE> mReplacement = new HashMap<>();
	private boolean mResult;

	public RemoveRedundantBuchi(final AutomataLibraryServices services, final IPetriNet<LETTER, PLACE> operand) {
		super(services);
		mOperand = operand;

		printStartMessage();
		removeRedundantPlaces();
		updatePetriNet(operand);
		printExitMessage();
	}

	private boolean removeRedundantPlaces() {
		Set<PLACE> checked = new HashSet<>();
		for (final var trans : mOperand.getTransitions()) {
			final Set<PLACE> postset = trans.getSuccessors();
			for (final PLACE place : postset) {
				if (checked.contains(place)) {
					continue;
				}
				checked.add(place);
				final Set<Transition<LETTER, PLACE>> preset = mOperand.getPredecessors(place);
				final Set<PLACE> replacements = postset.stream()// .filter(candidate -> candidate != place)
						.filter(candidate -> mOperand.getPredecessors(candidate).equals(preset))
						.collect(Collectors.toSet());
				replacements.forEach(x -> mReplacement.put(x, place));
				// mReplacement.put(replacements, place);
				if (replacements.size() > 1) {
					mResult = true;
					return true;
				}

			}
		}
		checked = new HashSet<>();
		for (final var trans : mOperand.getTransitions()) {
			final Set<PLACE> preset = trans.getPredecessors();
			for (final PLACE place : preset) {
				if (checked.contains(place)) {
					continue;
				}
				checked.add(place);
				final Set<Transition<LETTER, PLACE>> postset = mOperand.getSuccessors(place);
				final Set<PLACE> replacements = preset.stream()// .filter(candidate -> candidate != place)
						.filter(candidate -> mOperand.getSuccessors(candidate).equals(postset))
						.collect(Collectors.toSet());

				replacements.forEach(x -> mReplacement.put(x, place));
				// mReplacement.put(replacements, place);
				if (replacements.size() > 1) {
					mResult = true;
					return true;
				}
			}
		}
		return false;
	}

	// create the new Petri net with reduced number of places
	// TODO maybe into CopySubnet class
	private IPetriNet<LETTER, PLACE> updatePetriNet(final IPetriNet<LETTER, PLACE> operand) {
		final BoundedPetriNet<LETTER, PLACE> res = new BoundedPetriNet<>(mServices, mOperand.getAlphabet(), false);
		// Add places
		// TODO maybe directly use a separate list. or directly add them after they have been checked!! or keept this
		// copying isolated. don't know yet.
		mReplacement.values().stream().forEach(place -> res.addPlace(place, true, true));// TODO make this correct

		// Add transitions...
		for (final var trans : mOperand.getTransitions()) {
			final var preds = trans.getPredecessors().stream().map(p -> mReplacement.get(p)).distinct()
					.collect(Collectors.toSet());
			final var succs =
					trans.getSuccessors().stream().map(p -> mReplacement.get(p)).distinct().collect(Collectors.toSet());
			res.addTransition(trans.getSymbol(), ImmutableSet.of(preds), ImmutableSet.of(succs));
		}
		return res;
	}

	private boolean timeout() {
		return !mServices.getProgressAwareTimer().continueProcessing();
	}

	@Override
	// public BoundedPetriNet<LETTER, PLACE> getResult() {
	public Boolean getResult() {
		mLogger.info(mResult);
		return mResult;
	}

	// @Override
	// protected IPetriNet<LETTER, PLACE> getOperand() {
	// return mOperand;
	// }

	// @Override
	// public boolean checkResult(final CRSF stateFactory) throws AutomataLibraryException {
	// mLogger.warn("checkResult not implemented-");
	// return true;
	// }

	@Override
	public String exitMessage() {
		// return "Finished " + this.getClass().getSimpleName() + ", result has " + mResult.sizeInformation();
		return "Finished";
	}
}
