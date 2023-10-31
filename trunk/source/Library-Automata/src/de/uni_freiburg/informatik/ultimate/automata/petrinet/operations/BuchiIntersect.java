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
  * Abstract class for the intersection of a  Büchi-Petri Net and a Büchi automaton.
  *
  * @param <LETTER>
  * @param <PLACE>
  *
  * @author Daniel Küchler (kuechlerdaniel33@gmail.com)
  * @author Manuel Dienert 
  */
 public class BuchiIntersect<LETTER, PLACE>
 		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {
 	private final IPetriNet<LETTER, PLACE> mPetriNet;
 	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomata;
 	private final IBlackWhiteStateFactory<PLACE> mLabeledBuchiPlaceFactory;
 	private final Map<PLACE, PLACE> mInputQGetQ1 = new HashMap<>();
 	private final Map<PLACE, PLACE> mInputQGetQ2 = new HashMap<>();
 	private final Map<PLACE, PLACE> mInputQ2GetQ = new HashMap<>();

 	private BoundedPetriNet<LETTER, PLACE> mIntersectionNet;

// 	private boolean REMOVE_DEAD_OPTIMIZATION = false;
 	private final boolean GOAL_TRAP_OPTIMIZATION = false;
 	private final boolean ALL_GOAL_AUTOMATON_OPTIMIZATION= false;
// 	private final boolean ALL_ACCEPTING_NET_OPTIMIZATION = true;
 	private final boolean SELF_LOOP_OPTIMIZATION = false;

 	public BuchiIntersect(final AutomataLibraryServices services, final IBlackWhiteStateFactory<PLACE> factory,
 			final IPetriNet<LETTER, PLACE> petriNet, final INestedWordAutomaton<LETTER, PLACE> buchiAutomata) {
 		super(services);
 		mPetriNet = petriNet;
 		mBuchiAutomata = buchiAutomata;
 		mLogger.info(startMessage());
 		if (buchiAutomata.getInitialStates().size() != 1) {
 			throw new IllegalArgumentException("Buchi with multiple initial states not supported.");
 		}
 		mLabeledBuchiPlaceFactory = factory;
 		mIntersectionNet = new BoundedPetriNet<>(services, petriNet.getAlphabet(), false);

 		
 		if (GOAL_TRAP_OPTIMIZATION && isGoalTrapped()){
 			final BuchiIntersectGoalTrapped<LETTER, PLACE> intersection = 
 					new BuchiIntersectGoalTrapped<>(mServices, mLabeledBuchiPlaceFactory, mPetriNet, mBuchiAutomata);
 			// TODO why type casting here necessary?
 			mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
 		} else if (ALL_GOAL_AUTOMATON_OPTIMIZATION && isAllGoalAutomaton()) {
 			final BuchiIntersectAllGoalAutomaton<LETTER, PLACE> intersection = 
 					new BuchiIntersectAllGoalAutomaton<>(services, factory, petriNet, buchiAutomata);
 			mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
// 		} else if (ALL_ACCEPTING_NET_OPTIMIZATION && isAllAcceptingNet()) {
// 			final BuchiIntersectAllAcceptingtNet<LETTER, PLACE> intersection = 
// 					new BuchiIntersectAllAcceptingtNet<>(services, factory, petriNet, buchiAutomata);
// 			mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
 		} else if (SELF_LOOP_OPTIMIZATION) {
 			final BuchiIntersectDefault<LETTER, PLACE> intersection = 
 					new BuchiIntersectDefault<>(services, factory, petriNet, buchiAutomata, SELF_LOOP_OPTIMIZATION);
 			mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
 		} else { 
 			final BuchiIntersectDefault<LETTER, PLACE> intersection = 
 				new BuchiIntersectDefault<>(services, factory, petriNet, buchiAutomata, false);
 			mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
 		}

 		mLogger.info(exitMessage());
 	}
 	// -------------------------------------------
 	private boolean isAllGoalAutomaton() {
 		for (var state : mBuchiAutomata.getStates()) {
 			if (!mBuchiAutomata.getFinalStates().contains(state)) {
 				return false;
 			}
 		}
 		return true;
 	}
 	private boolean isAllAcceptingNet() { 
 		for (var place : mPetriNet.getPlaces()) {
 			if (!mPetriNet.isAccepting(place)) {
 				return false;
 			}
 		}
 		return true;
 	}
 	private boolean isGoalTrapped() {
		for (var x  : mBuchiAutomata.getFinalStates()) {
			for (var y : mBuchiAutomata.internalSuccessors(x)) {
				if (!mBuchiAutomata.getFinalStates().contains(y.getSucc()))
					return false;
			}
		}
		return true;
	}

 	@Override
 	public String startMessage() {
 		return "Starting Intersection";
 	}

 	@Override
 	public String exitMessage() {
 		return "Exiting Intersection";
 	}

 	@Override
 	public IPetriNet<LETTER, PLACE> getResult() {
 		return mIntersectionNet;
 	}

 	/**
 	 *
 	 */
 	@SuppressWarnings("unchecked")
 	@Override
 	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
 			throws AutomataLibraryException {
 		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> operandAsNwa = (new BuchiPetriNet2FiniteAutomaton<>(
 				mServices, stateFactory, (IBlackWhiteStateFactory<PLACE>) stateFactory, mPetriNet)).getResult();
 		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> resultAsNwa = (new BuchiPetriNet2FiniteAutomaton<>(
 				mServices, stateFactory, (IBlackWhiteStateFactory<PLACE>) stateFactory, mIntersectionNet)).getResult();

 		final NestedWordAutomatonReachableStates<LETTER, PLACE> automatonIntersection = new de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersect<>(
 				mServices, (IBuchiIntersectStateFactory<PLACE>) stateFactory, operandAsNwa, mBuchiAutomata).getResult();

 		final IsIncludedBuchi<LETTER, PLACE> isSubset = new IsIncludedBuchi<>(mServices,
 				(INwaInclusionStateFactory<PLACE>) stateFactory, resultAsNwa, automatonIntersection);
 		if (!isSubset.getResult()) {
 			final NestedLassoWord<LETTER> ctx = isSubset.getCounterexample().getNestedLassoWord();
 			final ILogger logger = mServices.getLoggingService().getLogger(PetriNetUtils.class);
 			logger.error("Intersection recognizes incorrect word : " + ctx);

 		}
 		final IsIncludedBuchi<LETTER, PLACE> isSuperset = new IsIncludedBuchi<>(mServices,
 				(INwaInclusionStateFactory<PLACE>) stateFactory, automatonIntersection, resultAsNwa);
 		if (!isSuperset.getResult()) {
 			final NestedLassoWord<LETTER> ctx = isSuperset.getCounterexample().getNestedLassoWord();
 			final ILogger logger = mServices.getLoggingService().getLogger(PetriNetUtils.class);
 			logger.error("Intersection not recognizing word of correct intersection : " + ctx);
 		}
 		return isSubset.getResult() && isSuperset.getResult();
 	}
 }
