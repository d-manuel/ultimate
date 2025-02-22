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

package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Subclass of {@PetriNetUnfolder} which implements the lasso-word search of a Buchi-Petri-Net during its Unfolding.
 * Algorithm(s) based on "Omega-Petri-Nets for termination analysis" thesis.
 *
 * @param <LETTER>
 * @param <PLACE>
 *
 * @author Daniel Küchler (kuechlerdaniel33@gmail.com)
 */
public class PetriNetUnfolderBuchi<LETTER, PLACE>
		extends PetriNetUnfolderBase<LETTER, PLACE, PetriNetLassoRun<LETTER, PLACE>> {

	private Events2PetriNetLassoRunBuchi<LETTER, PLACE> mEvents2PetriNetLassoRunBuchi;

	public PetriNetUnfolderBuchi(final AutomataLibraryServices services,
			final IPetriNetSuccessorProvider<LETTER, PLACE> operand, final EventOrderEnum order,
			final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);
	}

	@Override
	protected boolean checkInitialPlaces() {
		return false;
	}

	@Override
	protected PetriNetLassoRun<LETTER, PLACE> constructInitialRun() throws PetriNetNot1SafeException {
		return null;
	}

	@Override
	protected boolean addAndCheck(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {
		mUnfolding.addEvent(event);

		if (!event.isCutoffEvent()) {
			return false;
		}

		/**
		 * Special case of a lassoword appearing in a local configuration where its cutoff event has the
		 * Unfolding-stem-event as companion event, and thus needs special handling.
		 */
		if (event.getCompanion().getTransition() == null) {
			final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
			configLoopEvents.addAll(event.getLocalConfiguration().getSortedConfiguration(mUnfolding.getOrder()));
			if (checkIfLassoConfigurationAccepted(configLoopEvents, new ArrayList<>())) {
				return true;
			}
		}

		/**
		 * Searches for lasso-words which are fully contained in a local configuration of the Unfolding.
		 */
		if (event.getLocalConfiguration().contains(event.getCompanion())) {
			final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
			final List<Event<LETTER, PLACE>> configStemEvents = new ArrayList<>();
			for (final Event<LETTER, PLACE> configEvent : event.getLocalConfiguration()
					.getSortedConfiguration(mUnfolding.getOrder())) {
				if (configEvent != event.getCompanion()
						&& configEvent.getLocalConfiguration().contains(event.getCompanion())) {
					configLoopEvents.add(configEvent);
				} else {
					configStemEvents.add(configEvent);
				}
			}

			if (checkIfLassoConfigurationAccepted(configLoopEvents, configStemEvents)) {
				return true;
			}

		}

		/**
		 * Searches for lasso-words which are NOT fully contained in a local configuration and instead in a "partial
		 * configuration". An example of such a word would be c(fehg)^w contained in the Buchi-Petri-Net in
		 * "PartialConfigurationThesis.ats". Such words cannot be found in a local configuration (depending on the
		 * Unfolding algorithm of course).
		 *
		 * The rough algorithm to find such words in the Unfolding below is that we "backtrack" starting from a
		 * cutoff-event and if we encounter companion events during backtracking we jump to their respective
		 * cutoff-event(s). If, through this backtracking, we encounter the starting cutoff event again, we have found a
		 * partial configuration that builds a lasso-word.
		 */
		// Using a stack for the backtrack search which behaves like a tree-search (one companion event might have
		// multiple respective cutoff events, creating multiple branches of search).
		final ArrayDeque<Pair<List<Event<LETTER, PLACE>>, Event<LETTER, PLACE>>> worklist = new ArrayDeque<>();
		worklist.add(new Pair<>(new ArrayList<>(), event));
		final Set<Event<LETTER, PLACE>> seenEvents = new HashSet<>();
		while (!worklist.isEmpty()) {
			final Pair<List<Event<LETTER, PLACE>>, Event<LETTER, PLACE>> currentBranch = worklist.pop();
			final List<Event<LETTER, PLACE>> localConfigEvents =
					currentBranch.getSecond().getLocalConfiguration().getSortedConfiguration(mUnfolding.getOrder());
			Collections.reverse(localConfigEvents);

			final Optional<Event<LETTER, PLACE>> optionalFirstBackwardCompanion =
					localConfigEvents.stream().filter(e -> e.isCompanion()).findFirst();
			if (!optionalFirstBackwardCompanion.isPresent()) {
				continue;
			}
			final Event<LETTER, PLACE> firstBackwardCompanion = optionalFirstBackwardCompanion.get();

			// Collecting events we pass through until the first companion event, because they will build the loop of
			// the lasso-word.
			final var backwardsTraceEvents =
					localConfigEvents.stream().takeWhile(e -> !e.isCompanion()).collect(Collectors.toList());
			currentBranch.getFirst().addAll(backwardsTraceEvents);

			// Done Found lasso word. Ringschluss erfolgt.
			if (firstBackwardCompanion.getCutoffEventsThisIsCompanionTo().contains(event)) {
				Collections.reverse(currentBranch.getFirst());
				final List<Event<LETTER, PLACE>> configLoopEvents = currentBranch.getFirst();
				final List<Event<LETTER, PLACE>> configStemEvents =
						event.getLocalConfiguration().getSortedConfiguration(mUnfolding.getOrder());

				if (checkIfLassoConfigurationAccepted(configLoopEvents, configStemEvents)) {
					return true;
				}
			}
			// Need to continue to find for a loop (Ringschluss).thus new backwards branching
			// New backtrack-tree-path found through another companion event.

			firstBackwardCompanion.getCutoffEventsThisIsCompanionTo().stream().filter(e -> !seenEvents.contains(e))
					.forEach(e -> {
						seenEvents.add(e);
						worklist.add(new Pair<>(new ArrayList<>(currentBranch.getFirst()), e));
					});
		}
		return false;
	}

	private final boolean checkIfLassoConfigurationAccepted(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart) {
		mEvents2PetriNetLassoRunBuchi = new Events2PetriNetLassoRunBuchi<>(configLoopPart, configStemPart, mUnfolding);
		return mEvents2PetriNetLassoRunBuchi.isAccepted();
	}

	@Override
	protected PetriNetLassoRun<LETTER, PLACE> constructRun(final Event<LETTER, PLACE> event)
			throws PetriNetNot1SafeException {
		return mEvents2PetriNetLassoRunBuchi.constructLassoRun();
	}

	@Override
	protected boolean checkRun(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory,
			final PetriNetLassoRun<LETTER, PLACE> run)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		// TODO: Not implemented yet
		return true;
	}
}
