/*
 * Copyright (C) 2022-2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiIntersectAllAcceptingtNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiIntersectLooperOptimized;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiIntersectLazy;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiIntersectUsingSccs;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiPetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.DifferencePairwiseOnDemand;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;

/**
 * Cegar loop that uses Büchi-Petri-Nets
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Daniel Küchler (kuechlerdaniel33@gmail.com)
 * @author Manuel Dienert
 *
 * @param <L>
 */
public class BuchiPetriNetCegarLoop<L extends IIcfgTransition<?>>
		extends AbstractBuchiCegarLoop<L, IPetriNet<L, IPredicate>> {
	// private static final boolean USE_AUTOMATON_FOR_EMPTINESS = false;

	private final Marking2MLPredicate mMarking2MLPredicate;
	private final PredicateFactoryRefinement mStateFactoryForRefinement;

	final boolean mUseBuchiPetriOptimizations;
	final boolean mUseAutomatonForEmptiness;

	// Flags for the Buchi Intersection
	private static final boolean ALL_ACCEPTING_NET_OPTIMIZATION = true;
	private static final boolean SCC_OPTIMIZATION = true;

	boolean USE_LAZY_INTERSECTION = false;

	public BuchiPetriNetCegarLoop(final IIcfg<?> icfg, final RankVarConstructor rankVarConstructor,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final IPetriNet<L, IPredicate> initialAbstraction,
			final PredicateFactoryRefinement stateFactoryForRefinement,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		super(icfg, rankVarConstructor, predicateFactory, taPrefs, services, transitionClazz, initialAbstraction,
				benchmarkGenerator);
		mMarking2MLPredicate = new Marking2MLPredicate(predicateFactory);
		mStateFactoryForRefinement = stateFactoryForRefinement;

		final IPreferenceProvider baPref = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mUseBuchiPetriOptimizations =
				baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_USE_BUCHI_PETRI_OPTIMIZATIONS);
		mUseAutomatonForEmptiness =
				baPref.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_AUTOMATA_FOR_BUCHI_PETRI_EMTPTINESS);
	}

	protected boolean isAbstractionEmpty(final IPetriNet<L, IPredicate> abstraction) throws AutomataLibraryException {
		if (mUseAutomatonForEmptiness) {
			mLogger.info("use automaton for emptiness check");
			final var automaton = new BuchiPetriNet2FiniteAutomaton<>(new AutomataLibraryServices(mServices),
					mStateFactoryForRefinement, mStateFactoryForRefinement, abstraction).getResult();
			// mStateFactoryForRefinement, mStateFactoryForRefinement, abstraction).getResult();
			final var result = new de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty<>(
					new AutomataLibraryServices(mServices), automaton);
			if (result.getResult()) {
				return true;
			}
			mCounterexample = result.getAcceptingNestedLassoRun();
			return false;
		}
		final var isempty = new BuchiIsEmpty<>(new AutomataLibraryServices(mServices), abstraction, mPref.eventOrder(),
				mPref.cutOffRequiresSameTransition(), true);
		final PetriNetLassoRun<L, IPredicate> run = isempty.getRun();
		if (run == null) {
			return true;
		}
		mCounterexample =
				new NestedLassoRun<>(constructNestedLassoRun(run.getStem()), constructNestedLassoRun(run.getLoop()));
		return false;
	}

	// overloadedLazy<L, IPredicate> buchiIntersectLazy) {
	// final PetriNetLassoRun<L, IPredicate> run = buchiIntersectLazy.getRun();
	// if (run == null) {
	// return true;
	// }
	// mCounterexample =
	// new NestedLassoRun<>(constructNestedLassoRun(run.getStem()), constructNestedLassoRun(run.getLoop()));
	// return false;
	// }

	private NestedRun<L, IPredicate> constructNestedLassoRun(final PetriNetRun<L, IPredicate> run) {
		return new NestedRun<>(NestedWord.nestedWord(run.getWord()), run.getStateSequence().stream()
				.map(mMarking2MLPredicate::markingToPredicate).collect(Collectors.toList()));
	}

	@Override
	protected IPetriNet<L, IPredicate> refineFinite(final IPetriNet<L, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException {
		try {
			return new Difference<>(new AutomataLibraryServices(mServices), mDefaultStateFactory, abstraction,
					new NestedWordAutomatonReachableStates<>(new AutomataLibraryServices(mServices),
							interpolantAutomaton)).getResult();
//			return new DifferencePairwiseOnDemand<>(new AutomataLibraryServices(mServices), abstraction,
//					interpolantAutomaton).getResult();
		} catch (AutomataOperationCanceledException | PetriNetNot1SafeException e) {
			throw new AutomataLibraryException(getClass(), e.toString());
		}
	}

	@Override
	protected IPetriNet<L, IPredicate> refineBuchi(final IPetriNet<L, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException {
		final IStateDeterminizer<L, IPredicate> stateDeterminizer =
				new PowersetDeterminizer<>(interpolantAutomaton, mUseDoubleDeckers, mDefaultStateFactory);
		final BuchiComplementFKV<L, IPredicate> complNwa = new BuchiComplementFKV<>(
				new AutomataLibraryServices(mServices), mDefaultStateFactory, interpolantAutomaton, stateDeterminizer);
		mBenchmarkGenerator.reportHighestRank(complNwa.getHighestRank());

		if (USE_LAZY_INTERSECTION) {
			final BuchiIntersectLazy<L, IPredicate> intersection = new BuchiIntersectLazy<>(
					new AutomataLibraryServices(mServices), mDefaultStateFactory, abstraction, complNwa.getResult());

			return intersection.getResult();
		}
		if(mUseBuchiPetriOptimizations) {
			if (ALL_ACCEPTING_NET_OPTIMIZATION && mIteration == 1
					&& BuchiIntersectAllAcceptingtNet.isAllAcceptingNet(abstraction)) {
				final BuchiIntersectAllAcceptingtNet<L, IPredicate> intersection =
						new BuchiIntersectAllAcceptingtNet<>(new AutomataLibraryServices(mServices), abstraction, complNwa.getResult());
				return intersection.getResult();
			}

			if (SCC_OPTIMIZATION) {
				final BuchiIntersectUsingSccs<L, IPredicate> intersection =
						new BuchiIntersectUsingSccs<>(new AutomataLibraryServices(mServices),
				mDefaultStateFactory, abstraction, complNwa.getResult());
				return intersection.getResult();
			}
//		if (ALL_GOAL_AUTOMATON_OPTIMIZATION && BuchiIntersectAllGoalAutomaton.isAllGoalAutomaton(mBuchiAutomaton)) {
//				final BuchiIntersectAllGoalAutomaton<LETTER, PLACE> intersection =
//						new BuchiIntersectAllGoalAutomaton<>(mServices, mPetriNet, mBuchiAutomaton);
//				mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
//				return;
//			}
//			if (INHERENTLY_ALL_GOAL_AUTOMATON_OPTIMIZATION
//					&& BuchiIntersectAllGoalAutomaton.isInherentlyAllGoalAutomaton(mServices, mBuchiAutomaton)) {
//				// apart from checking a different condition we can create the same intersection as with allGoal
//				// automata!!!
//				final BuchiIntersectAllGoalAutomaton<LETTER, PLACE> intersection =
//						new BuchiIntersectAllGoalAutomaton<>(mServices, mPetriNet, mBuchiAutomaton);
//				mIntersectionNet = (BoundedPetriNet<LETTER, PLACE>) intersection.getResult();
//				return;
//			}
		}
//		final BuchiIntersectDefault<L, IPredicate> intersection =
//				new BuchiIntersectDefault<L, IPredicate>(new AutomataLibraryServices(mServices),
//				mDefaultStateFactory, abstraction, complNwa.getResult(), false);
//		return intersection.getResult();
		final BuchiIntersect<L, IPredicate> intersection =
				new BuchiIntersect<L, IPredicate>(new AutomataLibraryServices(mServices),
				mDefaultStateFactory, abstraction, complNwa.getResult());
		return intersection.getResult();

	}

	@Override
	protected IPetriNet<L, IPredicate> reduceAbstractionSize(final IPetriNet<L, IPredicate> abstraction,
			final Minimization automataMinimization) throws AutomataOperationCanceledException {

		// return new BackwardRemoveSinkPlaces<>(new AutomataLibraryServices(mServices), abstraction).getResult();
		// return new RemoveRedundantBuchi<>(new AutomataLibraryServices(mServices), abstraction).getResult();
		return abstraction;
	}
}