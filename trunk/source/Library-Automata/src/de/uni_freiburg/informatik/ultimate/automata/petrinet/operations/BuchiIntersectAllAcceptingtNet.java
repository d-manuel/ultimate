package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;
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

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Creates intersection of a Büchi-Petri net with only accepting states and a Büchi automat
 *
 * @param <LETTER>
 * @param <PLACE>
 *
 * @author Manuel Dienert
 */
public class BuchiIntersectAllAcceptingtNet<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {
	private final IPetriNet<LETTER, PLACE> mPetriNet;
	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomaton;

	private final BoundedPetriNet<LETTER, PLACE> mIntersectionNet;

	public BuchiIntersectAllAcceptingtNet(final AutomataLibraryServices services,
			final IPetriNet<LETTER, PLACE> petriNet, final INestedWordAutomaton<LETTER, PLACE> buchiAutomaton) {
		super(services);
		mPetriNet = petriNet;
		mBuchiAutomaton = buchiAutomaton;
		mLogger.info(startMessage());
		if (buchiAutomaton.getInitialStates().size() != 1) {
			throw new IllegalArgumentException("Buchi with multiple initial states not supported.");
		}

		mIntersectionNet = new BoundedPetriNet<>(services, petriNet.getAlphabet(), false);

		constructIntersection();

		mLogger.info(exitMessage());
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
		for (final PLACE place : mPetriNet.getPlaces()) {
			mIntersectionNet.addPlace(place, mPetriNet.getInitialPlaces().contains(place), false);
		}
	}

	private final void addBuchiPlaces() {
		for (final PLACE state : mBuchiAutomaton.getStates()) {
			mIntersectionNet.addPlace(state, mBuchiAutomaton.isInitial(state), mBuchiAutomaton.isFinal(state));
		}
	}

	private final void addTransitions() {
		for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
			final LETTER label = petriTransition.getSymbol();
			for (final PLACE buchiPlace : mBuchiAutomaton.getStates()) {
				for (final OutgoingInternalTransition<LETTER, PLACE> buchiTransition : mBuchiAutomaton
						.internalSuccessors(buchiPlace, label)) {

					final Set<PLACE> predecessors = new HashSet<>(petriTransition.getPredecessors());
					predecessors.add(buchiPlace);
					final Set<PLACE> successors = new HashSet<>(petriTransition.getSuccessors());
					successors.add(buchiTransition.getSucc());

					final var trans1 = mIntersectionNet.addTransition(label, ImmutableSet.of(predecessors),
							ImmutableSet.of(successors));
					mLogger.debug("Added transition " + Utils.transitionToString(trans1));
				}
			}
		}
	}

	@Override
	public String startMessage() {
		return "Starting Intersection with all accepting Petri Net";
	}

	@Override
	public String exitMessage() {
		return "Exiting Intersection with all accepting Petri Net";
	}

	@Override
	public IPetriNet<LETTER, PLACE> getResult() {
		return mIntersectionNet;
	}
}
