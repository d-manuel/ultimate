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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsIncludedBuchi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.PetriNetUtils;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Creates intersection of Buchi Petri net and buchi automata with or without self loop optimization.
 *
 * @param <LETTER>
 * @param <PLACE>
 *
 * @author Daniel Küchler (kuechlerdaniel33@gmail.com)
 * @author Manuel Dienert
 */
public class BuchiIntersectDefault<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {
	private final IPetriNet<LETTER, PLACE> mPetriNet;
	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomata;
	private final IBlackWhiteStateFactory<PLACE> mLabeledBuchiPlaceFactory;
	private final Map<PLACE, PLACE> mInputQGetQ1 = new HashMap<>();
	private final Map<PLACE, PLACE> mInputQGetQ2 = new HashMap<>();
	private final Map<PLACE, PLACE> mInputQ2GetQ = new HashMap<>();

	private BoundedPetriNet<LETTER, PLACE> mIntersectionNet;

	public BuchiIntersectDefault(final AutomataLibraryServices services, final IBlackWhiteStateFactory<PLACE> factory,
			final IPetriNet<LETTER, PLACE> petriNet, final INestedWordAutomaton<LETTER, PLACE> buchiAutomata, 
			boolean doSelfLoopOptimization) {
		super(services);
		mPetriNet = petriNet;
		mBuchiAutomata = buchiAutomata;

		mLogger.info(startMessage());
		if (buchiAutomata.getInitialStates().size() != 1) {
			throw new IllegalArgumentException("Buchi with multiple initial states not supported.");
		}
		mLabeledBuchiPlaceFactory = factory;
		mIntersectionNet = new BoundedPetriNet<>(services, petriNet.getAlphabet(), false);

		if (doSelfLoopOptimization) {
			constructOptimizedIntersectionNet();
		} else {
			constructIntersectionNet();
		}
		
			
//		mLogger.info(exitMessage());
	}
	private final void constructOptimizedIntersectionNet(){
		addPlacesToIntersectionNet();
		addOptimizedTransitions();
		
	}

	private final void constructIntersectionNet() {
		addPlacesToIntersectionNet();
		addTransitionsToIntersectionNet();
	}// -------------------------------------------

	private boolean isSelfLoopOptimizable(LETTER label) {
		for (final PLACE state : mBuchiAutomata.getStates()) {
			if (!isSelfLoop(state, label))
				return false;
		}
		return true;
	}

	// returns true if the place as at least one transition with label 'label' that
	// forms a self loop
	private boolean isSelfLoop(PLACE state, LETTER label) {
		for (OutgoingInternalTransition<LETTER, PLACE> succ : mBuchiAutomata.internalSuccessors(state, label)) {
			if (succ.getSucc().equals(state)) {
				return true;
			}
		}
		return false;
	}

	private final void addOptimizedTransitions() {
		for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
			mLogger.info("current petri trans: %s", petriTransition);
			Set<PLACE> pPreset = petriTransition.getPredecessors();
			Set<PLACE> pPostset = petriTransition.getSuccessors();
			LETTER pLabel = petriTransition.getSymbol();

			boolean isSelfLoopOptimizable = isSelfLoopOptimizable(pLabel);
			if (isSelfLoopOptimizable) {
				mLogger.warn(String.format(" \"%s\" is %s optimizble", pLabel, isSelfLoopOptimizable ? "" : "not"));
				addNondeterministicTransition(pLabel, pPreset, pPostset);

				// create 1-2 transitions create optimized state one transitions

				// TODO check correctness again of this condition
				boolean succAccepting = petriTransition.getSuccessors().stream()
						.anyMatch(t -> mPetriNet.getAcceptingPlaces().contains(t));
				
				addOptimizedStateOneTransitions(pLabel, pPreset, pPostset, succAccepting);
				addOptimizedStateTwoTransitions(pLabel, pPreset, pPostset);
			} else { // not selfloop optimizable
				// old (base) intersection algo
				for (final PLACE buchiPlace : mBuchiAutomata.getStates()) {
					for (final OutgoingInternalTransition<LETTER, PLACE> buchiTransition : mBuchiAutomata
							.internalSuccessors(buchiPlace, petriTransition.getSymbol())) {
						addStateOneAndTwoTransition(petriTransition, buchiTransition, buchiPlace);
					}
				}
			}
		}
	}

	private final void addNondeterministicTransition(LETTER label, Set<PLACE> pPreset, Set<PLACE> pPostset) {
		mIntersectionNet.addTransition(label, ImmutableSet.of(pPreset), ImmutableSet.of(pPostset));
		mLogger.debug("adding nondeterministic transition for label %s with preset; %s ; postset: %s", label, pPreset,
				pPostset);
	}

	private void addOptimizedStateTwoTransitions(LETTER label, Set<PLACE> preset, Set<PLACE> postset) {
		for (final PLACE bPlace : mBuchiAutomata.getStates()) {
			for (final OutgoingInternalTransition<LETTER, PLACE> bTransition : mBuchiAutomata.internalSuccessors(bPlace,
					label)) {
				final Set<PLACE> intersectionPredecessors = new HashSet<>(preset);
				intersectionPredecessors.add(mInputQGetQ2.get(bPlace));

				final Set<PLACE> intersectionSuccessors = new HashSet<>(postset); 
				boolean bAccepting = mBuchiAutomata.getFinalStates().contains(bTransition.getSucc());
				boolean isSelfLoop = bTransition.getSucc().equals(bPlace);
				if (bAccepting && isSelfLoop)
					intersectionSuccessors.add(mInputQGetQ1.get(bTransition.getSucc()));
				else if (!bAccepting && isSelfLoop)
					continue;
				else if (bAccepting && !isSelfLoop)
					intersectionSuccessors.add(mInputQGetQ1.get(bTransition.getSucc()));
				else if (!bAccepting && !isSelfLoop)
					intersectionSuccessors.add(mInputQGetQ1.get(bTransition.getSucc()));
				mIntersectionNet.addTransition(label, ImmutableSet.of(intersectionPredecessors),
						ImmutableSet.of(intersectionSuccessors));
			}
		}

	}

	private void addOptimizedStateOneTransitions(LETTER label, Set<PLACE> preset, Set<PLACE> postset,
			boolean succAccepting) {
		for (final PLACE bPlace : mBuchiAutomata.getStates()) {

			// WRONG: Minimization
			// TODO DELETE OR CORRECT
			// check if bPlace as incoming transition from an accepting state or is initial. otherwise it can never get a token in the intersection
//			if (!mBuchiAutomata.isInitial(bPlace)) {
//				boolean predAccepting = false;
//				for (var predTrans : mBuchiAutomata.internalPredecessors(bPlace)) {
//					if (mBuchiAutomata.isFinal(predTrans.getPred())) {
//						predAccepting = true;
//						break;
//					}
//				}
//				if (!predAccepting)
//					return;
//			}
				
			for (final OutgoingInternalTransition<LETTER, PLACE> bTransition : mBuchiAutomata.internalSuccessors(bPlace,
					label)) {
				final Set<PLACE> intersectionPredecessors = new HashSet<>(preset);
				intersectionPredecessors.add(mInputQGetQ1.get(bPlace));

				boolean isSelfLoop = bTransition.getSucc().equals(bPlace);
				final Set<PLACE> intersectionSuccessors = new HashSet<>(postset);
				if (succAccepting && isSelfLoop)
					intersectionSuccessors.add(mInputQGetQ2.get(bTransition.getSucc()));
				else if (succAccepting && !isSelfLoop)
					intersectionSuccessors.add(mInputQGetQ1.get(bTransition.getSucc()));
				else if (!succAccepting && isSelfLoop)
					continue;
				else if (!succAccepting && !isSelfLoop)
					intersectionSuccessors.add(mInputQGetQ1.get(bTransition.getSucc()));

				mIntersectionNet.addTransition(label, ImmutableSet.of(intersectionPredecessors),
						ImmutableSet.of(intersectionSuccessors));
			}
		}
	};
	// -------------------------------------------


	private final void addPlacesToIntersectionNet() {
		addOriginalPetriPlaces();
		addOriginalBuchiPlaces();
	}

	private final void addOriginalPetriPlaces() {
		for (final PLACE place : mPetriNet.getPlaces()) {
			mIntersectionNet.addPlace(place, mPetriNet.getInitialPlaces().contains(place), false);
		}
	}

	private final void addOriginalBuchiPlaces() {
		for (final PLACE place : mBuchiAutomata.getStates()) {
			final PLACE stateOnePlace = mLabeledBuchiPlaceFactory.getWhiteContent(place);
			final PLACE stateTwoPlace = mLabeledBuchiPlaceFactory.getBlackContent(place);
			mIntersectionNet.addPlace(stateOnePlace, mBuchiAutomata.isInitial(place), false);
			mIntersectionNet.addPlace(stateTwoPlace, false, mBuchiAutomata.isFinal(place));
			mInputQGetQ1.put(place, stateOnePlace);
			mInputQGetQ2.put(place, stateTwoPlace);
			mInputQ2GetQ.put(stateTwoPlace, place);
		}
	}

	private final void addTransitionsToIntersectionNet() {
		for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
			for (final PLACE buchiPlace : mBuchiAutomata.getStates()) {
				for (final OutgoingInternalTransition<LETTER, PLACE> buchiTransition : mBuchiAutomata
						.internalSuccessors(buchiPlace, petriTransition.getSymbol())) {
					addStateOneAndTwoTransition(petriTransition, buchiTransition, buchiPlace);
				}
			}
		}
	}

	private final void addStateOneAndTwoTransition(final Transition<LETTER, PLACE> petriTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiTransition, final PLACE buchiPredecessor) {
		Set<PLACE> predecessorSet = getTransitionPredecessors(petriTransition, buchiPredecessor, true);
		Set<PLACE> successorSet = getTransitionSuccessors(petriTransition, buchiTransition, predecessorSet, true);
		mIntersectionNet.addTransition(petriTransition.getSymbol(), ImmutableSet.of(predecessorSet),
				ImmutableSet.of(successorSet));
		predecessorSet = getTransitionPredecessors(petriTransition, buchiPredecessor, false);
		successorSet = getTransitionSuccessors(petriTransition, buchiTransition, predecessorSet, false);
		mIntersectionNet.addTransition(petriTransition.getSymbol(), ImmutableSet.of(predecessorSet),
				ImmutableSet.of(successorSet));
	}

	private final Set<PLACE> getTransitionPredecessors(final Transition<LETTER, PLACE> petriTransition,
			final PLACE buchiPredecessor, final boolean mBuildingStateOneTransition) {
		final Set<PLACE> predecessorSet = new HashSet<>(petriTransition.getPredecessors());
		if (mBuildingStateOneTransition) {
			predecessorSet.add(mInputQGetQ1.get(buchiPredecessor));
		} else {
			predecessorSet.add(mInputQGetQ2.get(buchiPredecessor));
		}

		return predecessorSet;
	}

	private final Set<PLACE> getTransitionSuccessors(final Transition<LETTER, PLACE> petriTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiTransition, final Set<PLACE> predecessorSet,
			final boolean mBuildingStateOneTransition) {
		final Set<PLACE> successorSet = new HashSet<>(petriTransition.getSuccessors());
		if (mBuildingStateOneTransition) {
			successorSet.add(getQSuccesorForStateOneTransition(petriTransition, buchiTransition));
		} else {
			successorSet.add(getQSuccesorForStateTwoTransition(predecessorSet, buchiTransition));
		}

		return successorSet;
	}

	private PLACE getQSuccesorForStateOneTransition(final Transition<LETTER, PLACE> petriTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiTransition) {
		for (final PLACE place : petriTransition.getSuccessors()) {
			if (mPetriNet.getAcceptingPlaces().contains(place)) {
				return mInputQGetQ2.get(buchiTransition.getSucc());
			}
		}
		return mInputQGetQ1.get(buchiTransition.getSucc());
	}

	private PLACE getQSuccesorForStateTwoTransition(final Set<PLACE> predecessorSet,
			final OutgoingInternalTransition<LETTER, PLACE> buchiTransition) {
		for (final PLACE place : predecessorSet) {
			if (mInputQ2GetQ.containsKey(place) && mBuchiAutomata.getFinalStates().contains(mInputQ2GetQ.get(place))) {
				return mInputQGetQ1.get(buchiTransition.getSucc());
			}
		}
		return mInputQGetQ2.get(buchiTransition.getSucc());
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

	// TODO should the check be in this class on in the parent class? 
//	/**
//	 *
//	 */
//	@SuppressWarnings("unchecked")
//	@Override
//	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
//			throws AutomataLibraryException {
//		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> operandAsNwa = (new BuchiPetriNet2FiniteAutomaton<>(
//				mServices, stateFactory, (IBlackWhiteStateFactory<PLACE>) stateFactory, mPetriNet)).getResult();
//		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> resultAsNwa = (new BuchiPetriNet2FiniteAutomaton<>(
//				mServices, stateFactory, (IBlackWhiteStateFactory<PLACE>) stateFactory, mIntersectionNet)).getResult();
//
//		final NestedWordAutomatonReachableStates<LETTER, PLACE> automatonIntersection = new de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersect<>(
//				mServices, (IBuchiIntersectStateFactory<PLACE>) stateFactory, operandAsNwa, mBuchiAutomata).getResult();
//
//		final IsIncludedBuchi<LETTER, PLACE> isSubset = new IsIncludedBuchi<>(mServices,
//				(INwaInclusionStateFactory<PLACE>) stateFactory, resultAsNwa, automatonIntersection);
//		if (!isSubset.getResult()) {
//			final NestedLassoWord<LETTER> ctx = isSubset.getCounterexample().getNestedLassoWord();
//			final ILogger logger = mServices.getLoggingService().getLogger(PetriNetUtils.class);
//			logger.error("Intersection recognizes incorrect word : " + ctx);
//
//		}
//		final IsIncludedBuchi<LETTER, PLACE> isSuperset = new IsIncludedBuchi<>(mServices,
//				(INwaInclusionStateFactory<PLACE>) stateFactory, automatonIntersection, resultAsNwa);
//		if (!isSuperset.getResult()) {
//			final NestedLassoWord<LETTER> ctx = isSuperset.getCounterexample().getNestedLassoWord();
//			final ILogger logger = mServices.getLoggingService().getLogger(PetriNetUtils.class);
//			logger.error("Intersection not recognizing word of correct intersection : " + ctx);
//		}
//		return isSubset.getResult() && isSuperset.getResult();
//	}
}
