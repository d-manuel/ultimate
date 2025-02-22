/*
 * Copyright (C) 2023-2024 Manuel Dienert
 * Copyright (C) 2023-2024 University of Freiburg
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
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Creates intersection of a Büchi-Petri net and a goal trapped Büchi automaton
 *
 * @param <LETTER>
 * @param <PLACE>
 *
 * @author Manuel Dienert
 */
public class BuchiIntersectGoalTrapped<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {
	private final IPetriNet<LETTER, PLACE> mPetriNet;
	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomaton;
	private final IBlackWhiteStateFactory<PLACE> mLabeledBuchiPlaceFactory;
	private final Map<PLACE, PLACE> mInputQGetQ1 = new HashMap<>();
	private final Map<PLACE, PLACE> mInputQGetQ2 = new HashMap<>();
	private final Map<PLACE, PLACE> mInputQ2GetQ = new HashMap<>();

	private final BoundedPetriNet<LETTER, PLACE> mIntersectionNet;

	public BuchiIntersectGoalTrapped(final AutomataLibraryServices services,
			final IBlackWhiteStateFactory<PLACE> factory, final IPetriNet<LETTER, PLACE> petriNet,
			final INestedWordAutomaton<LETTER, PLACE> buchiAutomaton) {
		super(services);
		mPetriNet = petriNet;
		mBuchiAutomaton = buchiAutomaton;
		mLogger.info(startMessage());
		if (buchiAutomaton.getInitialStates().size() != 1) {
			throw new IllegalArgumentException("Buchi with multiple initial states not supported.");
		}
		mLabeledBuchiPlaceFactory = factory;
		mIntersectionNet = new BoundedPetriNet<>(services, petriNet.getAlphabet(), false);

		constructIntersection();

		mLogger.info(exitMessage());
	}

	// Check if a Büchi Automaton is an Goal Trapped
	public static <LETTER, PLACE> boolean isGoalTrapped(final INestedWordAutomaton<LETTER, PLACE> buchiAutomaton) {
		for (final var x : buchiAutomaton.getFinalStates()) {
			for (final var y : buchiAutomaton.internalSuccessors(x)) {
				if (!buchiAutomaton.getFinalStates().contains(y.getSucc())) {
					return false;
				}
			}
		}
		return true;
	}

	private final void constructIntersection() {
		addPlaces();
		addTransitions();
	}

	private final void addPlaces() {
		addPetriPlaces();
		addBuchiPlaces();
	}

	private final void addPetriPlaces() {
		final Stream<PLACE> places = mPetriNet.getPlaces().stream();
		places.forEach(place -> mIntersectionNet.addPlace(place, mPetriNet.getInitialPlaces().contains(place), false));
	}

	private final void addBuchiPlaces() {
		final Set<PLACE> states = mBuchiAutomaton.getStates();
		for (final PLACE state : states) {
			final PLACE qi1 = mLabeledBuchiPlaceFactory.getWhiteContent(state);
			mIntersectionNet.addPlace(qi1, mBuchiAutomaton.isInitial(state), false);
			mInputQGetQ1.put(state, qi1);
			if (mBuchiAutomaton.getFinalStates().contains(state)) {
				final PLACE qi2 = mLabeledBuchiPlaceFactory.getBlackContent(state);
				mIntersectionNet.addPlace(qi2, false, mBuchiAutomaton.isFinal(state));
				mInputQGetQ2.put(state, qi2);
				mInputQ2GetQ.put(qi2, state);
			}
		}
	}

	private final void addTransitions() {
		for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
			for (final PLACE buchiPlace : mBuchiAutomaton.getStates()) {
				final boolean isGoalPlace = mBuchiAutomaton.getFinalStates().contains(buchiPlace);
				for (final OutgoingInternalTransition<LETTER, PLACE> buchiTransition : mBuchiAutomaton
						.internalSuccessors(buchiPlace, petriTransition.getSymbol())) {
					if (isGoalPlace) {
						syncToGoalTransition(petriTransition, buchiTransition, buchiPlace);
					} else {
						syncToStemTransition(petriTransition, buchiTransition, buchiPlace);
					}
				}
			}
		}
	}

	private final void syncToStemTransition(final Transition<LETTER, PLACE> petriTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiTransition, final PLACE buchiPredecessor) {
		final LETTER label = petriTransition.getSymbol();

		final Set<PLACE> predecessors = new HashSet<>(petriTransition.getPredecessors()); // F1
		predecessors.add(mInputQGetQ1.get(buchiPredecessor)); // F3
		final Set<PLACE> successors = new HashSet<>(petriTransition.getSuccessors()); // F2
		successors.add(mInputQGetQ1.get(buchiTransition.getSucc())); // F4

		final var trans_1 =
				mIntersectionNet.addTransition(label, ImmutableSet.of(predecessors), ImmutableSet.of(successors));
	}

	private final void syncToGoalTransition(final Transition<LETTER, PLACE> petriTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiTransition, final PLACE buchiPredecessor) {

		final Stream<PLACE> places = petriTransition.getSuccessors().stream();
		// check if petriTrans fires into accepting place (so the P_acceptnace
		// condition).
		final boolean petriTransAccepting = places.anyMatch(place -> mPetriNet.getAcceptingPlaces().contains(place));
		final LETTER label = petriTransition.getSymbol();

		// successor is equal between both transitions because we do not need to
		// consider the acceptance
		// condition of the Büchi automaton
		final Set<PLACE> successors = new HashSet<>(petriTransition.getSuccessors()); // F2
		successors.add(petriTransAccepting ? mInputQGetQ2.get(buchiTransition.getSucc())
				: mInputQGetQ1.get(buchiTransition.getSucc())); // F6 or F7

		final Set<PLACE> predecessors1 = new HashSet<>(petriTransition.getPredecessors()); // F1
		final Set<PLACE> predecessors2 = new HashSet<>(petriTransition.getPredecessors()); // F1
		predecessors1.add(mInputQGetQ1.get(buchiPredecessor)); // F5 i=1
		predecessors2.add(mInputQGetQ2.get(buchiPredecessor)); // F5 i=2
		final var trans_1 =
				mIntersectionNet.addTransition(label, ImmutableSet.of(predecessors1), ImmutableSet.of(successors));
		final var trans_2 =
				mIntersectionNet.addTransition(label, ImmutableSet.of(predecessors2), ImmutableSet.of(successors));
	}

	@Override
	public String startMessage() {
		return "Starting Intersection with goal trap optimization";
	}

	@Override
	public String exitMessage() {
		return "Exiting Intersection with goal trap optimization";
	}

	@Override
	public IPetriNet<LETTER, PLACE> getResult() {
		return mIntersectionNet;
	}
}
