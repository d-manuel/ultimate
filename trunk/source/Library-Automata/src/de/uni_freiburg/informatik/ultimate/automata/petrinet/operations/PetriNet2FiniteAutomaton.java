/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Given a Petri net, this class constructs a finite automaton that recognizes the same language.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbols type
 * @param <PLACE>
 *            place content type
 */
public final class PetriNet2FiniteAutomaton<LETTER, PLACE>
		extends UnaryNetOperation<LETTER, PLACE, IStateFactory<PLACE>> {
	private final IPetriNetTransitionProvider<LETTER, PLACE> mOperand;
	private final NestedWordAutomaton<LETTER, PLACE> mResult;
	private final Predicate<Marking<PLACE>> mIsKnownDeadEnd;

	/**
	 * List of markings for which
	 * <ul>
	 * <li>there has already been a state constructed
	 * <li>outgoing transitions of this state have not yet been constructed.
	 * </ul>
	 */
	private final List<Marking<PLACE>> mWorklist = new LinkedList<>();
	/**
	 * Maps a marking to the automaton state that represents this marking.
	 */
	private final Map<Marking<PLACE>, PLACE> mMarking2State = new HashMap<>();
	private final IPetriNet2FiniteAutomatonStateFactory<PLACE> mContentFactory;

	public PetriNet2FiniteAutomaton(final AutomataLibraryServices services,
			final IPetriNet2FiniteAutomatonStateFactory<PLACE> factory,
			final IPetriNetTransitionProvider<LETTER, PLACE> operand)
			throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		this(services, factory, operand, null);
	}

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param factory
	 *            content factory
	 * @param operand
	 *            operand Petri net
	 * @param isKnownDeadEnd
	 *            Function that can be used to identify dead ends. Construction does not continue from dead ends.
	 * @throws PetriNetNot1SafeException
	 * @throws AutomataOperationCanceledException
	 */
	public PetriNet2FiniteAutomaton(final AutomataLibraryServices services,
			final IPetriNet2FiniteAutomatonStateFactory<PLACE> factory,
			final IPetriNetTransitionProvider<LETTER, PLACE> operand, final Predicate<Marking<PLACE>> isKnownDeadEnd)
			throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mIsKnownDeadEnd = isKnownDeadEnd;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mContentFactory = factory;
		final Set<LETTER> alphabet = new HashSet<>(operand.getAlphabet());
		final VpAlphabet<LETTER> vpAlphabet =
				new VpAlphabet<>(alphabet, Collections.emptySet(), Collections.emptySet());
		mResult = new NestedWordAutomaton<>(mServices, vpAlphabet, factory);
		getState(new Marking<>(ImmutableSet.of(operand.getInitialPlaces())), true);
		while (!mWorklist.isEmpty()) {
			final Marking<PLACE> marking = mWorklist.remove(0);
			constructOutgoingTransitions(marking);
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				final RunningTaskInfo rti = new RunningTaskInfo(getClass(),
						"constructing automaton for Petri net that has " + mOperand.sizeInformation()
								+ ". Already constructed " + mMarking2State.size() + " states. Currently "
								+ mWorklist.size() + " states in worklist.");
				throw new AutomataOperationCanceledException(rti);
			}
		}

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mResult.sizeInformation();
	}

	/**
	 * Returns the automaton state that represents marking. If this state is not yet constructed, construct it and
	 * enqueue the marking. If it has to be constructed it is an initial state iff isInitial is true.
	 */
	private PLACE getState(final Marking<PLACE> marking, final boolean isInitial) {
		if (isKnownDeadEnd(marking)) {
			return null;
		}

		PLACE state = mMarking2State.get(marking);
		if (state == null) {
			final boolean isFinal = mOperand.isAccepting(marking);
			state = mContentFactory.getContentOnPetriNet2FiniteAutomaton(marking);
			mResult.addState(isInitial, isFinal, state);
			mMarking2State.put(marking, state);
			mWorklist.add(marking);
		}
		return state;
	}

	/**
	 * Given a marking. Get the state that represents the marking. Add all possible outgoing automaton transitions to
	 * state. Construct (and enqueue to worklist) successor states if necessary.
	 *
	 * @throws PetriNetNot1SafeException
	 */
	private void constructOutgoingTransitions(final Marking<PLACE> marking) throws PetriNetNot1SafeException {
		final PLACE state = getState(marking, false);
		assert state != null : "Dead-end marking should never be on worklist";

		final Set<Transition<LETTER, PLACE>> outgoing = getOutgoingNetTransitions(marking);
		for (final Transition<LETTER, PLACE> transition : outgoing) {
			if (marking.isTransitionEnabled(transition)) {
				final Marking<PLACE> succMarking = marking.fireTransition(transition);
				final PLACE succState = getState(succMarking, false);
				if (succState != null) {
					mResult.addInternalTransition(state, transition.getSymbol(), succState);
				}
			}
		}
	}

	private Set<Transition<LETTER, PLACE>> getOutgoingNetTransitions(final Marking<PLACE> marking) {
		final Set<Transition<LETTER, PLACE>> transitions = new HashSet<>();
		for (final PLACE place : marking) {
			transitions.addAll(mOperand.getSuccessors(place));
		}
		return transitions;
	}

	private boolean isKnownDeadEnd(final Marking<PLACE> state) {
		if (mIsKnownDeadEnd == null) {
			return false;
		}
		return mIsKnownDeadEnd.test(state);
	}

	@Override
	protected IPetriNetTransitionProvider<LETTER, PLACE> getOperand() {
		return mOperand;
	}

	@Override
	public INestedWordAutomaton<LETTER, PLACE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<PLACE> stateFactory) throws AutomataLibraryException {
		return true;
	}
}
