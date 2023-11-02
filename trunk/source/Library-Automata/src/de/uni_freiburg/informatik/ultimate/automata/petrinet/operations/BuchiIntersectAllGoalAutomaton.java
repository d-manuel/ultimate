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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriPlaceFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Creates intersection of a Büchi-Petri net and a goal trapped Büchi automaton
 *
 * @param <LETTER>
 * @param <PLACE>
 *
 * @author Manuel Dienert
 */
public class BuchiIntersectAllGoalAutomaton<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {
	private final IPetriNet<LETTER, PLACE> mPetriNet;
	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomata;

	private BoundedPetriNet<LETTER, PLACE> mIntersectionNet;

	public BuchiIntersectAllGoalAutomaton(final AutomataLibraryServices services,
			final IPetriNet<LETTER, PLACE> petriNet, final INestedWordAutomaton<LETTER, PLACE> buchiAutomata) {
		super(services);
		mPetriNet = petriNet;
		mBuchiAutomata = buchiAutomata;
		mLogger.info(startMessage());
		if (buchiAutomata.getInitialStates().size() != 1) {
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
			mIntersectionNet.addPlace(place, mPetriNet.getInitialPlaces().contains(place), mPetriNet.isAccepting(place));
		}
	}

	private final void addBuchiPlaces() {
		for (final PLACE state : mBuchiAutomata.getStates()) {
			mIntersectionNet.addPlace(state, mBuchiAutomata.isInitial(state), false);

		}
	}

	private final void addTransitions() {
		for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
			LETTER label = petriTransition.getSymbol();
			for (final PLACE buchiPlace : mBuchiAutomata.getStates()) {
				for (final OutgoingInternalTransition<LETTER, PLACE> buchiTransition : mBuchiAutomata
						.internalSuccessors(buchiPlace,label )) {

					Set<PLACE> predecessors = new HashSet<>(petriTransition.getPredecessors());
					predecessors.add(buchiPlace);
					Set<PLACE> successors = new HashSet<>(petriTransition.getSuccessors());
					successors.add(buchiTransition.getSucc());

					var trans1 = mIntersectionNet.addTransition(label, ImmutableSet.of(predecessors), ImmutableSet.of(successors));
					mLogger.info("Added transition " + transitionToString(trans1));
				}
			}
		}
	}
//------------------------------
	// for debugging
	private String transitionToString(Transition<LETTER, PLACE> trans) {
		String res = "{";
		res += "{";
		for (var pre : trans.getPredecessors()) {
			res += " " + pre.toString() + " ";
		}
		res += "} " + trans.getSymbol() + " {";
		for (var suc : trans.getSuccessors()) {
			res += " " + suc.toString() + " ";
		}
		res += "}}";
		return res;
	}
//------------------------------


	@Override
	public String startMessage() {
		return "Starting Intersection with all goal automaton";
	}

	@Override
	public String exitMessage() {
		return "Exiting Intersection with all goal automaton";
	}

	@Override
	public IPetriNet<LETTER, PLACE> getResult() {
		return mIntersectionNet;
	}

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
