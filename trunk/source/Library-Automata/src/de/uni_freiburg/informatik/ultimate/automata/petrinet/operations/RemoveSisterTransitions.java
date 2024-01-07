/*
 * Copyright (C) 2023-2024 Manuel Dienert
 * Copyright (C) 2009-2023 University of Freiburg
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

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Remove transitions with equal pre- and postset places
 */
public class RemoveSisterTransitions<LETTER, PLACE> extends GeneralOperation<LETTER, PLACE, IStateFactory<PLACE>> {

	private final IPetriNet<LETTER, PLACE> mOperand;
	private final Set<Transition<LETTER, PLACE>> mTransToRemove = new HashSet<>();
	private final BoundedPetriNet<LETTER, PLACE> mResult;

	public RemoveSisterTransitions(final AutomataLibraryServices services, final IPetriNet<LETTER, PLACE> operand) {
		super(services);
		mOperand = operand;

		printStartMessage();
		mResult = new BoundedPetriNet<>(mServices, mOperand.getAlphabet(), false);
		computeRedudantTrans();
		updatePetriNet();
		printExitMessage();
	}

	private void computeRedudantTrans() {
		for (final var trans : mOperand.getTransitions()) {
			final var candidates = trans.getSuccessors().stream().flatMap(p -> mOperand.getPredecessors(p).stream());
			final Set<Transition<LETTER, PLACE>> sisters =
					candidates.filter(t -> !t.equals(trans) && t.getPredecessors().equals(trans.getPredecessors())
							&& t.getSuccessors().equals(trans.getSuccessors())
							&& t.getSuccessors().equals(trans.getSymbol())).collect(Collectors.toSet());
			sisters.forEach(mTransToRemove::add);
		}
	}

	private void updatePetriNet() {
		// Add places
		mOperand.getPlaces().stream()
				.forEach(p -> mResult.addPlace(p, mOperand.getInitialPlaces().contains(p), mOperand.isAccepting(p)));

		// Add transitions
		for (final var trans : mOperand.getTransitions()) {
			// skip adding the redundant transitions
			if (mTransToRemove.contains(trans)) {
				continue;
			}
			final var preds = trans.getPredecessors();
			final var succs = trans.getSuccessors();
			mResult.addTransition(trans.getSymbol(), ImmutableSet.of(preds), ImmutableSet.of(succs));
		}
	}

	@Override
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

	@Override
	public String exitMessage() {
		// return "Finished " + this.getClass().getSimpleName() + ", result has " + mResult.sizeInformation();
		return "Finished";
	}
}
