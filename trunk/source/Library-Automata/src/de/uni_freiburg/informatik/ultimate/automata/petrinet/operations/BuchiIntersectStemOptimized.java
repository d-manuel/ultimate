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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.AutomatonSccComputation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Creates intersection of Buchi Petri net and buchi automata with stem optimization
 *
 * @param <LETTER>
 * @param <PLACE>
 *
 * @author Manuel Dienert
 */
public class BuchiIntersectStemOptimized<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {
	private final BoundedPetriNet<LETTER, PLACE> mPetriNet;
	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomaton;
	private final IBlackWhiteStateFactory<PLACE> mLabeledBuchiPlaceFactory;
	private final Map<PLACE, PLACE> mInputQGetQ1 = new HashMap<>();
	private final Map<PLACE, PLACE> mInputQGetQ2 = new HashMap<>();
	private final Map<PLACE, PLACE> mInputQ2GetQ = new HashMap<>();

	private final BoundedPetriNet<LETTER, PLACE> mIntersectionNet;

	private final Set<PLACE> mAcceptingSccPlaces = new HashSet<PLACE>();

	public BuchiIntersectStemOptimized(final AutomataLibraryServices services,
			final IBlackWhiteStateFactory<PLACE> factory, final BoundedPetriNet<LETTER, PLACE> petriNet,
			final INestedWordAutomaton<LETTER, PLACE> buchiAutomata) throws AutomataOperationCanceledException {
		super(services);
		mPetriNet = petriNet;
		mBuchiAutomaton = buchiAutomata;

		mLogger.info(startMessage());
		if (buchiAutomata.getInitialStates().size() != 1) {
			throw new IllegalArgumentException("Buchi with multiple initial states not supported.");
		}
		mLabeledBuchiPlaceFactory = factory;
		mIntersectionNet = new BoundedPetriNet<>(services, petriNet.getAlphabet(), false);

		computeAcceptingSccs();

		constructIntersection();

		mLogger.info(exitMessage());
	}

	private void computeAcceptingSccs() throws AutomataOperationCanceledException {
		final NestedWordAutomatonReachableStates<LETTER, PLACE> buchiAutomatonReachable =
				new RemoveUnreachable<>(mServices, mBuchiAutomaton).getResult();
		final AutomatonSccComputation<LETTER, PLACE> sccComp = new AutomatonSccComputation<>(mServices,
				buchiAutomatonReachable, mBuchiAutomaton.getStates(), mBuchiAutomaton.getStates());
		final Collection<StronglyConnectedComponent<PLACE>> sccs = sccComp.getBalls();
		for (final StronglyConnectedComponent<PLACE> scc : sccs) {
			final boolean containsAccepting = scc.getNodes().stream().anyMatch(buchiAutomatonReachable::isFinal);
			if (containsAccepting) {
				scc.getNodes().stream().forEach(mAcceptingSccPlaces::add);
			}
		}

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
		places.forEach(place -> mIntersectionNet.addPlace(place, mPetriNet.isInitial(place), false));
	}

	private final void addBuchiPlaces() {
		for (final PLACE state : mBuchiAutomaton.getStates()) {
			final PLACE qi1 = mLabeledBuchiPlaceFactory.getWhiteContent(state);
			mIntersectionNet.addPlace(qi1, mBuchiAutomaton.isInitial(state), false);
			mInputQGetQ1.put(state, qi1);
			mLogger.info("added Buchi Place" + qi1);
			if (mAcceptingSccPlaces.contains(state)) {
				final PLACE qi2 = mLabeledBuchiPlaceFactory.getBlackContent(state);
				mIntersectionNet.addPlace(qi2, false, mBuchiAutomaton.isFinal(state));
				mLogger.info("added Buchi Place" + qi2);
				mInputQGetQ2.put(state, qi2);
				mInputQ2GetQ.put(qi2, state);
			}
		}
	}

	private final void addTransitions() {
		for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
			for (final PLACE buchiPlace : mBuchiAutomaton.getStates()) {
				final boolean isGoalPlace = mAcceptingSccPlaces.contains(buchiPlace);
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

		final Set<PLACE> predecessors = new HashSet<>(petriTransition.getPredecessors());
		predecessors.add(mInputQGetQ1.get(buchiPredecessor));
		final Set<PLACE> successors = new HashSet<>(petriTransition.getSuccessors());
		successors.add(mInputQGetQ1.get(buchiTransition.getSucc()));

		final var trans_1 =
				mIntersectionNet.addTransition(label, ImmutableSet.of(predecessors), ImmutableSet.of(successors));
		mLogger.info("Added stem transition " + Utils.transitionToString(trans_1));
	}

	private final void syncToGoalTransition(final Transition<LETTER, PLACE> petriTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiTransition, final PLACE buchiPredecessor) {

		final LETTER label = petriTransition.getSymbol();
		final boolean petriSuccAccepting = petriTransition.getSuccessors().stream().anyMatch(mPetriNet::isAccepting);
		final boolean buchiPredAccepting = mBuchiAutomaton.isFinal(buchiPredecessor);

		// Transiton 1 index 1 to X
		final Set<PLACE> predecessors1 = new HashSet<>(petriTransition.getPredecessors()); // TODO is it adding petri
																							// succs
		predecessors1.add(mInputQGetQ1.get(buchiPredecessor));
		final Set<PLACE> successors1 = new HashSet<>(petriTransition.getSuccessors());
		successors1.add((petriSuccAccepting) ? mInputQGetQ2.get(buchiTransition.getSucc())
				: mInputQGetQ1.get(buchiTransition.getSucc()));

		// Transition 2 index 2 to Y
		final Set<PLACE> predecessors2 = new HashSet<>(petriTransition.getPredecessors());
		predecessors2.add(mInputQGetQ2.get(buchiPredecessor));
		final Set<PLACE> successors2 = new HashSet<>(petriTransition.getSuccessors());
		successors2.add((buchiPredAccepting) ? mInputQGetQ1.get(buchiTransition.getSucc())
				: mInputQGetQ2.get(buchiTransition.getSucc()));

		final var trans_1 =
				mIntersectionNet.addTransition(label, ImmutableSet.of(predecessors1), ImmutableSet.of(successors1));
		mLogger.info("Added goal transition " + Utils.transitionToString(trans_1));
		final var trans_2 =
				mIntersectionNet.addTransition(label, ImmutableSet.of(predecessors2), ImmutableSet.of(successors2));
		mLogger.info("Added goal transition " + Utils.transitionToString(trans_2));
	}

	@Override
	public String startMessage() {
		return "Starting Basic Intersection";
	}

	@Override
	public String exitMessage() {
		return "Exiting Basic Intersection";
	}

	@Override
	public IPetriNet<LETTER, PLACE> getResult() {
		return mIntersectionNet;
	}
}