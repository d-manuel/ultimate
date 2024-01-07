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

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
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
 * Removes places from a Petri net with an empty postset. In Büchi-Petri nets those places
 * will never contribute to an accepting run. If the removal leads to transitions with an
 * empty postset, we remove those as well.
 */
public class BackwardRemoveSinkPlaces<LETTER, PLACE> extends GeneralOperation<LETTER, PLACE, IStateFactory<PLACE>> {

	private final IPetriNet<LETTER, PLACE> mOperand;
	private final BoundedPetriNet<LETTER, PLACE> mResult;
	private final Set<Transition<LETTER, PLACE>> mTransToRemove = new HashSet<>();
	private final Set<PLACE> mPlacesToRemove = new HashSet<>();

	public BackwardRemoveSinkPlaces(final AutomataLibraryServices services, final IPetriNet<LETTER, PLACE> operand) {
		super(services);
		mOperand = operand;

		printStartMessage();
		mResult = new BoundedPetriNet<>(mServices, mOperand.getAlphabet(), false);
		compute();
		if (!mTransToRemove.isEmpty()) {
			mLogger.warn("we actually found a sink place");
		}
		updatePetriNet();
		printExitMessage();
	}

	private void compute() {
		final Queue<PLACE> placesToCheck = new LinkedList<PLACE>();
		placesToCheck.addAll(mOperand.getPlaces());
		while (!placesToCheck.isEmpty()) {
			final PLACE place = placesToCheck.remove();
			if (isSinkPlace(place)) {
				mPlacesToRemove.add(place);
				final var emptyTransCandidates = mOperand.getPredecessors(place);
				emptyTransCandidates.stream().filter(t -> !mTransToRemove.contains(t)).filter(t -> isSinkTransition(t))
						.forEach(t -> {
							mTransToRemove.add(t);
							placesToCheck.addAll(t.getPredecessors());
						});
			}
		}
	}

	private boolean isSinkPlace(final PLACE place) {
		// A place is sink place if it has no successor transitions
		final Set<Transition<LETTER, PLACE>> succs = mOperand.getSuccessors(place);
		// All succ transitions (if there even are any) are removable
		return succs.stream().allMatch(mTransToRemove::contains);
	}

	private boolean isSinkTransition(final Transition<LETTER, PLACE> trans) {
		final Set<PLACE> succs = trans.getSuccessors();
		// all succ places (if there even are any) are removable
		return succs.stream().allMatch(mPlacesToRemove::contains);
	}

	private void updatePetriNet() {
		// Add places that are still needed
		mOperand.getPlaces().stream().filter(p -> !mPlacesToRemove.contains(p))
				.forEach(p -> mResult.addPlace(p, mOperand.getInitialPlaces().contains(p), mOperand.isAccepting(p)));
		// Add transitions
		for (final var trans : mOperand.getTransitions()) {
			if (mTransToRemove.contains(trans)) {
				continue;
			}
			final var preds = trans.getPredecessors().stream().filter(p -> !mPlacesToRemove.contains(p))
					.collect(Collectors.toSet());
			final var succs = trans.getSuccessors().stream().filter(p -> !mPlacesToRemove.contains(p))
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
