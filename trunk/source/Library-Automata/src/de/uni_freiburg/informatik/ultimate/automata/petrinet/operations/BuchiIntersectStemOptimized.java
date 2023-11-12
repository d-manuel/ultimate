package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;
/*
 * Copyright (C) 2022-2023 Daniel Küchler (kuechlerdaniel33@gmail.com)
 * Copyright (C) 2022-2023 University of Freiburg
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
 * @author Daniel Küchler (kuechlerdaniel33@gmail.com)
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

		mLogger.info(exitMessage());
	}

	// TODO Remove
	@Override
	public Object getResult() {
		return null;
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

		final boolean petriSuccAccepting = petriTransition.getSuccessors().stream().noneMatch(mPetriNet::isAccepting);
		// check if petriTrans fires into accepting place (so the P_acceptnace
		// condition).
		// TODO could also compute this already one layer above and pass it as an argument.

		final boolean buchiPredAccepting = mBuchiAutomaton.isFinal(buchiPredecessor);

		// successor is equal between both transitions because we do not need to
		// consider the acceptance
		// condition of the Büchi automaton
		// but we need to go to only one places if the successor is nonaccepting.

		// we can only go to the qi2 if we go to an accepting state in q_i
		// TODO improve
		final boolean buchiSuccAccepting = mBuchiAutomaton.getFinalStates().contains(buchiTransition.getSucc());
		final Set<PLACE> successors = new HashSet<>(petriTransition.getSuccessors()); // F2
		successors.add((petriSuccAccepting && buchiSuccAccepting) ? mInputQGetQ2.get(buchiTransition.getSucc())
				: mInputQGetQ1.get(buchiTransition.getSucc())); // F6 or F7

		final Set<PLACE> predecessors1 = new HashSet<>(petriTransition.getPredecessors()); // F1
		final Set<PLACE> predecessors2 = new HashSet<>(petriTransition.getPredecessors()); // F1
		predecessors1.add(mInputQGetQ1.get(buchiPredecessor)); // F5 i=1
		predecessors2.add(mInputQGetQ2.get(buchiPredecessor)); // F5 i=2
		final var trans_1 =
				mIntersectionNet.addTransition(label, ImmutableSet.of(predecessors1), ImmutableSet.of(successors));
		mLogger.info("Added goal transition " + Utils.transitionToString(trans_1));
		final var trans_2 =
				mIntersectionNet.addTransition(label, ImmutableSet.of(predecessors2), ImmutableSet.of(successors));
		mLogger.info("Added goal transition " + Utils.transitionToString(trans_2));
	}

	// private final void constructOptimizedIntersectionNet() {
	// addPlacesToIntersectionNet();
	// addOptimizedTransitions();
	//
	// }
	//
	// private final void constructIntersectionNet() {
	// addPlacesToIntersectionNet();
	// addTransitionsToIntersectionNet();
	// }// -------------------------------------------
	//
	// private boolean isSelfLoopOptimizable(final LETTER label) {
	// for (final PLACE state : mBuchiAutomata.getStates()) {
	// if (!isSelfLoop(state, label)) {
	// return false;
	// }
	// }
	// return true;
	// }
	//
	// // returns true if the place as at least one transition with label 'label' that
	// // forms a self loop
	// private boolean isSelfLoop(final PLACE state, final LETTER label) {
	// for (final OutgoingInternalTransition<LETTER, PLACE> succ : mBuchiAutomata.internalSuccessors(state, label)) {
	// if (succ.getSucc().equals(state)) {
	// return true;
	// }
	// }
	// return false;
	// }
	//
	// private final void addOptimizedTransitions() {
	// for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
	// mLogger.info("current petri trans: %s", petriTransition);
	// final Set<PLACE> pPreset = petriTransition.getPredecessors();
	// final Set<PLACE> pPostset = petriTransition.getSuccessors();
	// final LETTER pLabel = petriTransition.getSymbol();
	//
	// final boolean isSelfLoopOptimizable = isSelfLoopOptimizable(pLabel);
	// if (isSelfLoopOptimizable) {
	// mLogger.warn(String.format(" \"%s\" is %s optimizble", pLabel, isSelfLoopOptimizable ? "" : "not"));
	// addNondeterministicTransition(pLabel, pPreset, pPostset);
	//
	// // create 1-2 transitions create optimized state one transitions
	//
	// // TODO check correctness again of this condition
	// final boolean succAccepting = petriTransition.getSuccessors().stream()
	// .anyMatch(t -> mPetriNet.getAcceptingPlaces().contains(t));
	//
	// addOptimizedStateOneTransitions(pLabel, pPreset, pPostset, succAccepting);
	// addOptimizedStateTwoTransitions(pLabel, pPreset, pPostset);
	// } else { // not selfloop optimizable
	// // old (base) intersection algo
	// for (final PLACE buchiPlace : mBuchiAutomata.getStates()) {
	// for (final OutgoingInternalTransition<LETTER, PLACE> buchiTransition : mBuchiAutomata
	// .internalSuccessors(buchiPlace, petriTransition.getSymbol())) {
	// addStateOneAndTwoTransition(petriTransition, buchiTransition, buchiPlace);
	// }
	// }
	// }
	// }
	// }
	//
	// private final void addNondeterministicTransition(final LETTER label, final Set<PLACE> pPreset,
	// final Set<PLACE> pPostset) {
	// mIntersectionNet.addTransition(label, ImmutableSet.of(pPreset), ImmutableSet.of(pPostset));
	// mLogger.debug("adding nondeterministic transition for label %s with preset; %s ; postset: %s", label, pPreset,
	// pPostset);
	// }
	//
	// private void addOptimizedStateTwoTransitions(final LETTER label, final Set<PLACE> preset,
	// final Set<PLACE> postset) {
	// for (final PLACE bPlace : mBuchiAutomata.getStates()) {
	// for (final OutgoingInternalTransition<LETTER, PLACE> bTransition : mBuchiAutomata.internalSuccessors(bPlace,
	// label)) {
	// final Set<PLACE> intersectionPredecessors = new HashSet<>(preset);
	// intersectionPredecessors.add(mInputQGetQ2.get(bPlace));
	//
	// final Set<PLACE> intersectionSuccessors = new HashSet<>(postset);
	// final boolean bAccepting = mBuchiAutomata.getFinalStates().contains(bTransition.getSucc());
	// final boolean isSelfLoop = bTransition.getSucc().equals(bPlace);
	// if (bAccepting && isSelfLoop) {
	// intersectionSuccessors.add(mInputQGetQ1.get(bTransition.getSucc()));
	// } else if (!bAccepting && isSelfLoop) {
	// continue;
	// } else if (bAccepting && !isSelfLoop) {
	// intersectionSuccessors.add(mInputQGetQ1.get(bTransition.getSucc()));
	// } else if (!bAccepting && !isSelfLoop) {
	// intersectionSuccessors.add(mInputQGetQ1.get(bTransition.getSucc()));
	// }
	// mIntersectionNet.addTransition(label, ImmutableSet.of(intersectionPredecessors),
	// ImmutableSet.of(intersectionSuccessors));
	// }
	// }
	//
	// }
	//
	// private void addOptimizedStateOneTransitions(final LETTER label, final Set<PLACE> preset, final Set<PLACE>
	// postset,
	// final boolean succAccepting) {
	// for (final PLACE bPlace : mBuchiAutomata.getStates()) {
	//
	// // WRONG: Minimization
	// // TODO DELETE OR CORRECT
	// // check if bPlace as incoming transition from an accepting state or is initial. otherwise it can never get
	// // a token in the intersection
	// // if (!mBuchiAutomata.isInitial(bPlace)) {
	// // boolean predAccepting = false;
	// // for (var predTrans : mBuchiAutomata.internalPredecessors(bPlace)) {
	// // if (mBuchiAutomata.isFinal(predTrans.getPred())) {
	// // predAccepting = true;
	// // break;
	// // }
	// // }
	// // if (!predAccepting)
	// // return;
	// // }
	//
	// for (final OutgoingInternalTransition<LETTER, PLACE> bTransition : mBuchiAutomata.internalSuccessors(bPlace,
	// label)) {
	// final Set<PLACE> intersectionPredecessors = new HashSet<>(preset);
	// intersectionPredecessors.add(mInputQGetQ1.get(bPlace));
	//
	// final boolean isSelfLoop = bTransition.getSucc().equals(bPlace);
	// final Set<PLACE> intersectionSuccessors = new HashSet<>(postset);
	// if (succAccepting && isSelfLoop) {
	// intersectionSuccessors.add(mInputQGetQ2.get(bTransition.getSucc()));
	// } else if (succAccepting && !isSelfLoop) {
	// intersectionSuccessors.add(mInputQGetQ1.get(bTransition.getSucc()));
	// } else if (!succAccepting && isSelfLoop) {
	// continue;
	// } else if (!succAccepting && !isSelfLoop) {
	// intersectionSuccessors.add(mInputQGetQ1.get(bTransition.getSucc()));
	// }
	//
	// mIntersectionNet.addTransition(label, ImmutableSet.of(intersectionPredecessors),
	// ImmutableSet.of(intersectionSuccessors));
	// }
	// }
	// }
	// // -------------------------------------------
	//
	// private final void addPlacesToIntersectionNet() {
	// addOriginalPetriPlaces();
	// addOriginalBuchiPlaces();
	// }
	//
	// private final void addOriginalPetriPlaces() {
	// for (final PLACE place : mPetriNet.getPlaces()) {
	// mIntersectionNet.addPlace(place, mPetriNet.getInitialPlaces().contains(place), false);
	// }
	// }
	//
	// private final void addOriginalBuchiPlaces() {
	// for (final PLACE place : mBuchiAutomata.getStates()) {
	// final PLACE stateOnePlace = mLabeledBuchiPlaceFactory.getWhiteContent(place);
	// final PLACE stateTwoPlace = mLabeledBuchiPlaceFactory.getBlackContent(place);
	// mIntersectionNet.addPlace(stateOnePlace, mBuchiAutomata.isInitial(place), false);
	// mIntersectionNet.addPlace(stateTwoPlace, false, mBuchiAutomata.isFinal(place));
	// mInputQGetQ1.put(place, stateOnePlace);
	// mInputQGetQ2.put(place, stateTwoPlace);
	// mInputQ2GetQ.put(stateTwoPlace, place);
	// }
	// }
	//
	// private final void addTransitionsToIntersectionNet() {
	// for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
	// for (final PLACE buchiPlace : mBuchiAutomata.getStates()) {
	// for (final OutgoingInternalTransition<LETTER, PLACE> buchiTransition : mBuchiAutomata
	// .internalSuccessors(buchiPlace, petriTransition.getSymbol())) {
	// addStateOneAndTwoTransition(petriTransition, buchiTransition, buchiPlace);
	// }
	// }
	// }
	// }
	//
	// private final void addStateOneAndTwoTransition(final Transition<LETTER, PLACE> petriTransition,
	// final OutgoingInternalTransition<LETTER, PLACE> buchiTransition, final PLACE buchiPredecessor) {
	// Set<PLACE> predecessorSet = getTransitionPredecessors(petriTransition, buchiPredecessor, true);
	// Set<PLACE> successorSet = getTransitionSuccessors(petriTransition, buchiTransition, predecessorSet, true);
	// mIntersectionNet.addTransition(petriTransition.getSymbol(), ImmutableSet.of(predecessorSet),
	// ImmutableSet.of(successorSet));
	// predecessorSet = getTransitionPredecessors(petriTransition, buchiPredecessor, false);
	// successorSet = getTransitionSuccessors(petriTransition, buchiTransition, predecessorSet, false);
	// mIntersectionNet.addTransition(petriTransition.getSymbol(), ImmutableSet.of(predecessorSet),
	// ImmutableSet.of(successorSet));
	// }
	//
	// private final Set<PLACE> getTransitionPredecessors(final Transition<LETTER, PLACE> petriTransition,
	// final PLACE buchiPredecessor, final boolean mBuildingStateOneTransition) {
	// final Set<PLACE> predecessorSet = new HashSet<>(petriTransition.getPredecessors());
	// if (mBuildingStateOneTransition) {
	// predecessorSet.add(mInputQGetQ1.get(buchiPredecessor));
	// } else {
	// predecessorSet.add(mInputQGetQ2.get(buchiPredecessor));
	// }
	//
	// return predecessorSet;
	// }
	//
	// private final Set<PLACE> getTransitionSuccessors(final Transition<LETTER, PLACE> petriTransition,
	// final OutgoingInternalTransition<LETTER, PLACE> buchiTransition, final Set<PLACE> predecessorSet,
	// final boolean mBuildingStateOneTransition) {
	// final Set<PLACE> successorSet = new HashSet<>(petriTransition.getSuccessors());
	// if (mBuildingStateOneTransition) {
	// successorSet.add(getQSuccesorForStateOneTransition(petriTransition, buchiTransition));
	// } else {
	// successorSet.add(getQSuccesorForStateTwoTransition(predecessorSet, buchiTransition));
	// }
	//
	// return successorSet;
	// }
	//
	// private PLACE getQSuccesorForStateOneTransition(final Transition<LETTER, PLACE> petriTransition,
	// final OutgoingInternalTransition<LETTER, PLACE> buchiTransition) {
	// for (final PLACE place : petriTransition.getSuccessors()) {
	// if (mPetriNet.getAcceptingPlaces().contains(place)) {
	// return mInputQGetQ2.get(buchiTransition.getSucc());
	// }
	// }
	// return mInputQGetQ1.get(buchiTransition.getSucc());
	// }
	//
	// private PLACE getQSuccesorForStateTwoTransition(final Set<PLACE> predecessorSet,
	// final OutgoingInternalTransition<LETTER, PLACE> buchiTransition) {
	// for (final PLACE place : predecessorSet) {
	// if (mInputQ2GetQ.containsKey(place) && mBuchiAutomata.getFinalStates().contains(mInputQ2GetQ.get(place))) {
	// return mInputQGetQ1.get(buchiTransition.getSucc());
	// }
	// }
	// return mInputQGetQ2.get(buchiTransition.getSucc());
	// }
	//
	// @Override
	// public String startMessage() {
	// return "Starting Basic Intersection";
	// }
	//
	// @Override
	// public String exitMessage() {
	// return "Exiting Basic Intersection";
	// }
	//
	// @Override
	// public IPetriNet<LETTER, PLACE> getResult() {
	// return mIntersectionNet;
	// }

	// TODO should the check be in this class on in the parent class?
	// /**
	// *
	// */
	// @SuppressWarnings("unchecked")
	// @Override
	// public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
	// throws AutomataLibraryException {
	// final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> operandAsNwa = (new BuchiPetriNet2FiniteAutomaton<>(
	// mServices, stateFactory, (IBlackWhiteStateFactory<PLACE>) stateFactory, mPetriNet)).getResult();
	// final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> resultAsNwa = (new BuchiPetriNet2FiniteAutomaton<>(
	// mServices, stateFactory, (IBlackWhiteStateFactory<PLACE>) stateFactory, mIntersectionNet)).getResult();
	//
	// final NestedWordAutomatonReachableStates<LETTER, PLACE> automatonIntersection = new
	// de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersect<>(
	// mServices, (IBuchiIntersectStateFactory<PLACE>) stateFactory, operandAsNwa, mBuchiAutomata).getResult();
	//
	// final IsIncludedBuchi<LETTER, PLACE> isSubset = new IsIncludedBuchi<>(mServices,
	// (INwaInclusionStateFactory<PLACE>) stateFactory, resultAsNwa, automatonIntersection);
	// if (!isSubset.getResult()) {
	// final NestedLassoWord<LETTER> ctx = isSubset.getCounterexample().getNestedLassoWord();
	// final ILogger logger = mServices.getLoggingService().getLogger(PetriNetUtils.class);
	// logger.error("Intersection recognizes incorrect word : " + ctx);
	//
	// }
	// final IsIncludedBuchi<LETTER, PLACE> isSuperset = new IsIncludedBuchi<>(mServices,
	// (INwaInclusionStateFactory<PLACE>) stateFactory, automatonIntersection, resultAsNwa);
	// if (!isSuperset.getResult()) {
	// final NestedLassoWord<LETTER> ctx = isSuperset.getCounterexample().getNestedLassoWord();
	// final ILogger logger = mServices.getLoggingService().getLogger(PetriNetUtils.class);
	// logger.error("Intersection not recognizing word of correct intersection : " + ctx);
	// }
	// return isSubset.getResult() && isSuperset.getResult();
	// }
}
