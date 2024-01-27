package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;
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
import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.AutomatonSccComputation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Determines if a automaton is weak. And it makes inherently weak automata weak. TODO Update It supplies Accepting SCC
 * places.
 *
 * @param <LETTER>
 * @param <PLACE>
 *
 * @author Manuel Dienert
 */
public class BuchiWeakComp<LETTER, PLACE> extends GeneralOperation<LETTER, PLACE, IStateFactory<PLACE>> {

	private final AutomataLibraryServices mServices;
	private final NestedWordAutomatonReachableStates<LETTER, PLACE> mBuchiAutomatonReachable;
	private Collection<StronglyConnectedComponent<PLACE>> mSccs;
	// private Set<StronglyConnectedComponent<PLACE>> mAcceptingSccs;
	// private Set<StronglyConnectedComponent<PLACE>> mNonAcceptingSccs;
	// private Set<StronglyConnectedComponent<PLACE>> mMixedSccs;
	private final Set<PLACE> mAcceptingSccPlaces = new HashSet<PLACE>();
	private boolean isWeak;

	public BuchiWeakComp(final AutomataLibraryServices services, final IBlackWhiteStateFactory<PLACE> factory,
			final IPetriNet<LETTER, PLACE> petriNet,
			final NestedWordAutomatonReachableStates<LETTER, PLACE> buchiAutomatonReachable) {
		super(services);
		this.mServices = services;
		this.mBuchiAutomatonReachable = buchiAutomatonReachable;

		compute();
	}

	private void compute() {
		final AutomatonSccComputation<LETTER, PLACE> sccComp = new AutomatonSccComputation<>(mServices,
				mBuchiAutomatonReachable, mBuchiAutomatonReachable.getStates(), mBuchiAutomatonReachable.getStates());
		this.mSccs = sccComp.getBalls();
		// Each SCC either needs to be nonaccepting (no accepting states), accepting (only accepting states) or
		// weakenizable (no cycles with only nonaccepting states)
		for (final var scc : mSccs) {
			final boolean isAcceptingSCC =
					scc.getNodes().stream().allMatch(node -> mBuchiAutomatonReachable.getFinalStates().contains(node));
			if (isAcceptingSCC) {
				scc.getNodes().stream().forEach(state -> mAcceptingSccPlaces.add(state));
				// mAcceptingSccs.add(scc);
				continue;
			}
			final boolean isNonAcceptingSCC =
					scc.getNodes().stream().allMatch(node -> !mBuchiAutomatonReachable.getFinalStates().contains(node));
			if (isNonAcceptingSCC) {
				// mNonAcceptingSccs.add(scc);
				continue;
			}
			// (!isAcceptingSCC && !isNonAcceptingSCC)
			// mMixedSccs.add(scc);
			if (isWeakenizable(scc)) {
				scc.getNodes().stream().forEach(state -> mAcceptingSccPlaces.add(state));
			} else {
				this.isWeak = false;
				return;
				// return false;
			}

		}
		// return true;
		this.isWeak = true;
		return;
	}

	// returns true if it weakenizable, false if not
	/**
	 *
	 * @param scc
	 *            A {@link StronglyConnectedComponent} of the Büchi automaton
	 * @return True for weakenizable SCCs. So Sccs without nonaccepting loops.
	 */
	public boolean isWeakenizable(final StronglyConnectedComponent<PLACE> scc) {
		final Set<PLACE> nodes = scc.getNodes();
		for (final PLACE node : nodes) {
			if (mBuchiAutomatonReachable.isFinal(node)) {
				continue;
			}
			final Stack<PLACE> stack = new Stack<PLACE>();
			stack.push(node);
			if (DFS(stack) == false) {
				return false;
			}
		}
		return true;
	}

	// Helper Function for the isWeakenizable method
	// Check for non-accepting cycles.
	private boolean DFS(final Stack<PLACE> stack) {
		final PLACE currentPlace = stack.peek();
		for (final var succTrans : mBuchiAutomatonReachable.internalSuccessors(currentPlace)) {
			final PLACE neighbor = succTrans.getSucc();
			if (mBuchiAutomatonReachable.isFinal(neighbor)) {
				// We only look for nona- ccepting cycles. If we encounter an accepting state all subsequently
				// discovered
				// loops would have an accepting place
				continue;
			}
			if (stack.contains(neighbor)) {
				return false; // TODO; we found an nonaccepting loop. SCC is not weakenizable.
			}
			stack.push(neighbor);
			if (DFS(stack) == false) {
				return false;
			}
		}
		stack.pop();// backtrack
		return true;
	}

	public boolean isWeak() {
		return isWeak;
	}

	@Override
	public Set<PLACE> getResult() {
		return mAcceptingSccPlaces;
	}
}