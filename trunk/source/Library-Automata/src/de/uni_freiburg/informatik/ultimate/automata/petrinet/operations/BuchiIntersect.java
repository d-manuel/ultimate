package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;
/*
 * Copyright (C) 2022-2023 Daniel Küchler (kuechlerdaniel33@gmail.com)
 * Copyright (C) 2022-2023 University of Freiburg
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
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.AutomatonSccComputation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiWeakComp;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsIncludedBuchi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.PetriNetUtils;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Abstract class for the intersection of a Büchi-Petri Net and a Büchi automaton.
 *
 * @param <LETTER>
 * @param <PLACE>
 *
 * @author Daniel Küchler (kuechlerdaniel33@gmail.com)
 * @author Manuel Dienert
 */
public class BuchiIntersect<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {

	// private boolean REMOVE_DEAD_OPTIMIZATION = false;
	private static final boolean ALL_GOAL_AUTOMATON_OPTIMIZATION = false;
	private static final boolean INHERENTLY_ALL_GOAL_AUTOMATON_OPTIMIZATION = true;
	private static final boolean ALL_ACCEPTING_NET_OPTIMIZATION = false;
	private static final boolean STEM_OPTIMIZATION = true;
	private static final boolean SELF_LOOP_OPTIMIZATION = false;
	private static final boolean WEAK_AUTOMATON_OPTIMIZATION = false;
	private static final boolean GOAL_TRAP_OPTIMIZATION = false;

	private final IPetriNet<LETTER, PLACE> mPetriNet;
	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomaton;
	private final IBlackWhiteStateFactory<PLACE> mLabeledBuchiPlaceFactory;
	private final AutomataLibraryServices mServices;

	private BoundedPetriNet<LETTER, PLACE> mIntersectionNet;

	public BuchiIntersect(final AutomataLibraryServices services, final IBlackWhiteStateFactory<PLACE> factory,
			final IPetriNet<LETTER, PLACE> petriNet, final INestedWordAutomaton<LETTER, PLACE> buchiAutomata)
			throws AutomataOperationCanceledException {
		super(services);
		mPetriNet = petriNet;
		mBuchiAutomaton = buchiAutomata;
		mServices = services;
		mLogger.info(startMessage());
		if (buchiAutomata.getInitialStates().size() != 1) {
			throw new IllegalArgumentException("Buchi with multiple initial states not supported.");
		}
		mLabeledBuchiPlaceFactory = factory;
		mIntersectionNet = new BoundedPetriNet<>(services, petriNet.getAlphabet(), false);

		executeIntersection();

		mLogger.info(exitMessage());
	}

	@SuppressWarnings("unused")
	private void executeIntersection() throws AutomataOperationCanceledException {
		if (ALL_ACCEPTING_NET_OPTIMIZATION && isAllAcceptingNet(mPetriNet)) {
			final BuchiIntersectAllAcceptingtNet<LETTER, PLACE> intersection =
					new BuchiIntersectAllAcceptingtNet<>(mServices, mPetriNet, mBuchiAutomaton);
			mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
			return;
			// } else if (WEAK_AUTOMATON_OPTIMIZATION && isWeakAutomaton(mServices,mBuchiAutomata)) {
		} else if (WEAK_AUTOMATON_OPTIMIZATION) {
		}
		if (GOAL_TRAP_OPTIMIZATION && isGoalTrapped()) {
			final BuchiIntersectGoalTrapped<LETTER, PLACE> intersection =
					new BuchiIntersectGoalTrapped<>(mServices, mLabeledBuchiPlaceFactory, mPetriNet, mBuchiAutomaton);
			mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
			return;
		}
		if (ALL_GOAL_AUTOMATON_OPTIMIZATION && isAllGoalAutomaton(mBuchiAutomaton)) {
			final BuchiIntersectAllGoalAutomaton<LETTER, PLACE> intersection =
					new BuchiIntersectAllGoalAutomaton<>(mServices, mPetriNet, mBuchiAutomaton);
			mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
			return;
		}
		if (INHERENTLY_ALL_GOAL_AUTOMATON_OPTIMIZATION && isInherentlyAllGoalAutomaton(mServices, mBuchiAutomaton)) {
			// apart from checking a different condition we can create the same intersection as with allGoal automata!!!
			final BuchiIntersectAllGoalAutomaton<LETTER, PLACE> intersection =
					new BuchiIntersectAllGoalAutomaton<>(mServices, mPetriNet, mBuchiAutomaton);
			mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
			return;
		}
		if (WEAK_AUTOMATON_OPTIMIZATION) {
			// we need a NestedWordAutomatonReachableStates for this
			try {
				final NestedWordAutomatonReachableStates<LETTER, PLACE> buchiAutomatonReachable =
						new RemoveUnreachable<>(mServices, mBuchiAutomaton).getResult();

				final BuchiWeakComp<LETTER, PLACE> buchiWeakComp =
						new BuchiWeakComp<>(mServices, mLabeledBuchiPlaceFactory, mPetriNet, buchiAutomatonReachable);

				if (buchiWeakComp.isWeak()) {
					final BuchiIntersectWeakAutomaton<LETTER, PLACE> intersection =
							new BuchiIntersectWeakAutomaton<LETTER, PLACE>(mServices, mLabeledBuchiPlaceFactory,
									mPetriNet, mBuchiAutomaton, buchiWeakComp.getResult());

					mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
					return;
				}

			} catch (final AutomataOperationCanceledException e) {
				e.printStackTrace();
				return;
			}
		} else if (SELF_LOOP_OPTIMIZATION) {
		}
		if (SELF_LOOP_OPTIMIZATION) {
			final BuchiIntersectDefault<LETTER, PLACE> intersection = new BuchiIntersectDefault<>(mServices,
					mLabeledBuchiPlaceFactory, mPetriNet, mBuchiAutomaton, SELF_LOOP_OPTIMIZATION);
			mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
			return;
		}
		if (STEM_OPTIMIZATION) {
			final BuchiIntersectStemOptimized<LETTER, PLACE> intersection = new BuchiIntersectStemOptimized<>(mServices,
					mLabeledBuchiPlaceFactory, (BoundedPetriNet<LETTER, PLACE>) mPetriNet, mBuchiAutomaton);
			mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
			return;
		}
		final BuchiIntersectDefault<LETTER, PLACE> intersection =
				new BuchiIntersectDefault<>(mServices, mLabeledBuchiPlaceFactory, mPetriNet, mBuchiAutomaton, false);
		mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
	}

	// -------------------------------------------

	public static <LETTER, PLACE> boolean isAllGoalAutomaton(final INestedWordAutomaton<LETTER, PLACE> buchiAutomaton) {
		final Stream<PLACE> states = buchiAutomaton.getStates().stream();
		return states.allMatch(state -> buchiAutomaton.getFinalStates().contains(state));
	}

	public static <LETTER, PLACE> boolean isAllAcceptingNet(final IPetriNet<LETTER, PLACE> petriNet) {
		final Stream<Transition<LETTER, PLACE>> transitions = petriNet.getTransitions().stream();
		return transitions.allMatch(trans -> trans.getSuccessors().stream().anyMatch(petriNet::isAccepting));
	}

	public boolean isGoalTrapped() {
		for (final var x : mBuchiAutomaton.getFinalStates()) {
			for (final var y : mBuchiAutomaton.internalSuccessors(x)) {
				if (!mBuchiAutomaton.getFinalStates().contains(y.getSucc())) {
					return false;
				}
			}
		}
		return true;
	}

	public static <LETTER, PLACE> boolean isInherentlyAllGoalAutomaton(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, PLACE> buchiAutomaton) {
		try {
			final NestedWordAutomatonReachableStates<LETTER, PLACE> mBuchiAutomatonAccepting =
					new RemoveUnreachable<>(services, buchiAutomaton).getResult();
			final AutomatonSccComputation<LETTER, PLACE> sccComp =
					new AutomatonSccComputation<>(services, mBuchiAutomatonAccepting,
							mBuchiAutomatonAccepting.getStates(), mBuchiAutomatonAccepting.getStates());
			final Collection<StronglyConnectedComponent<PLACE>> sccs = sccComp.getBalls();
			final BuchiWeakComp<LETTER, PLACE> weakComp =
					new BuchiWeakComp<>(services, null, null, mBuchiAutomatonAccepting);
			return sccs.stream().allMatch(weakComp::isWeakenizable);

		} catch (final AutomataOperationCanceledException e) {
			e.printStackTrace();
			return false;
		}
	}

	public static <LETTER, PLACE> boolean isWeakAutomaton(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, PLACE> buchiAutomaton) {
		try {
			final NestedWordAutomatonReachableStates<LETTER, PLACE> mBuchiAutomatonAccepting =
					new RemoveUnreachable<>(services, buchiAutomaton).getResult();
			final AutomatonSccComputation<LETTER, PLACE> sccComp =
					new AutomatonSccComputation<>(services, mBuchiAutomatonAccepting,
							mBuchiAutomatonAccepting.getStates(), mBuchiAutomatonAccepting.getStates());
			// Collection<StronglyConnectedComponent<PLACE>> sccs = sccComp.getBalls();
			final Stream<StronglyConnectedComponent<PLACE>> sccsStream = sccComp.getBalls().stream();
			final Set<StronglyConnectedComponent<PLACE>> sccs = new HashSet<>();
			sccsStream.forEach(sccs::add);
			for (final var scc : sccs) {
				final boolean isAcceptingSCC = scc.getNodes().stream()
						.allMatch(node -> mBuchiAutomatonAccepting.getFinalStates().contains(node));
				final boolean isNonAcceptingScc = scc.getNodes().stream()
						.allMatch(node -> !mBuchiAutomatonAccepting.getFinalStates().contains(node));
				if (!isAcceptingSCC && !isNonAcceptingScc) {// accepting SCC has nonaccepting cycle or nonaccepting SCC
															// has an accepting state.
					return false;
				}
			}
		} catch (final AutomataOperationCanceledException e) {
			e.printStackTrace();
			return false;
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
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> operandAsNwa =
				(new BuchiPetriNet2FiniteAutomaton<>(mServices, stateFactory,
						(IBlackWhiteStateFactory<PLACE>) stateFactory, mPetriNet)).getResult();
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> resultAsNwa =
				(new BuchiPetriNet2FiniteAutomaton<>(mServices, stateFactory,
						(IBlackWhiteStateFactory<PLACE>) stateFactory, mIntersectionNet)).getResult();

		final NestedWordAutomatonReachableStates<LETTER, PLACE> automatonIntersection =
				new de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersect<>(mServices,
						(IBuchiIntersectStateFactory<PLACE>) stateFactory, operandAsNwa, mBuchiAutomaton).getResult();

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
