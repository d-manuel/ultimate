package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Class foor a lazy intersection of a Büchi-Petri Net and a Büchi automaton.
 *
 * @param <LETTER>
 * @param <PLACE>
 *
 * @author Manuel Dienert
 */
public class BuchiIntersectLazy<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {

	private final BoundedPetriNet<LETTER, PLACE> mPetriNet;
	// private final IPetriNet<LETTER, PLACE> mPetriNet;
	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomaton;
	private final IBlackWhiteStateFactory<PLACE> mLabeledBuchiPlaceFactory;
	private final AutomataLibraryServices mServices;
	private final Map<PLACE, PLACE> mInputQGetQ1 = new HashMap<>();
	private final Map<PLACE, PLACE> mInputQGetQ2 = new HashMap<>();

	private final BoundedPetriNet<LETTER, PLACE> mIntersectionNet;

	public BuchiIntersectLazy(final AutomataLibraryServices services, final IBlackWhiteStateFactory<PLACE> factory,
			final IPetriNet<LETTER, PLACE> petriNet, final INestedWordAutomaton<LETTER, PLACE> buchiAutomaton)
			throws PetriNetNot1SafeException {
		super(services);
		mPetriNet = (BoundedPetriNet<LETTER, PLACE>) petriNet;
		mBuchiAutomaton = buchiAutomaton;
		mServices = services;
		mLogger.info(startMessage());
		if (buchiAutomaton.getInitialStates().size() != 1) {
			throw new IllegalArgumentException("Buchi with multiple initial states not supported.");
		}
		mLabeledBuchiPlaceFactory = factory;
		mIntersectionNet = new BoundedPetriNet<>(services, petriNet.getAlphabet(), false);
		run();

		mLogger.info(exitMessage());
	}

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
		for (final PLACE place : mBuchiAutomaton.getStates()) {
			final PLACE stateOnePlace = mLabeledBuchiPlaceFactory.getWhiteContent(place);
			final PLACE stateTwoPlace = mLabeledBuchiPlaceFactory.getBlackContent(place);
			mIntersectionNet.addPlace(stateOnePlace, mBuchiAutomaton.isInitial(place), false);
			mIntersectionNet.addPlace(stateTwoPlace, false, mBuchiAutomaton.isFinal(place));
			mInputQGetQ1.put(place, stateOnePlace);
			mInputQGetQ2.put(place, stateTwoPlace);
		}
	}

	private void run() throws PetriNetNot1SafeException {
		// ------------------------------
		// Add all possible places for now
		addPlacesToIntersectionNet();
		// ------------------------------

		// starting node
		final var initialMarking = new Marking<>(ImmutableSet.of(mPetriNet.getInitialPlaces()));
		final var initialState = mBuchiAutomaton.getInitialStates().iterator().next();
		final Node initialNode = new Node(initialMarking, initialState, Index.ONE);

		// List of already processed (expanded) nodes
		final Queue<Node> expanded = new LinkedList<>();
		// List of nodes needed to process next
		// final Queue<Node> worklist = new LinkedList<>();
		final Stack<Node> worklist = new Stack<>();
		worklist.add(initialNode);

		while (!worklist.isEmpty()) {
			// fetch node
			final Node currentNode = worklist.pop();

			if (expanded.contains(currentNode)) {
				continue;
			}
			expanded.add(currentNode);
			final List<Node> succs = getSuccessorNodes(currentNode);
			worklist.addAll(succs);
			for (final Node succNode : succs) {
				// Add transitions
				final ImmutableSet<PLACE> predecessors =
						ImmutableSet.of(concatPlaces(currentNode.mMarking, getBuchiState(currentNode)));
				final ImmutableSet<PLACE> successors =
						ImmutableSet.of(concatPlaces(succNode.mMarking, getBuchiState(succNode)));

				mIntersectionNet.addTransition(succNode.getLetter(), predecessors, successors);
			}
		}
		return;
	}

	Set<PLACE> concatPlaces(final Marking<PLACE> petriPlaces, final PLACE buchiState) {
		return Stream.concat(petriPlaces.stream(), Stream.of(buchiState)).collect(Collectors.toSet());
	}

	PLACE getBuchiState(final Node succNode) {
		return succNode.mIndex == Index.ONE ? mInputQGetQ1.get(succNode.mState) : mInputQGetQ2.get(succNode.mState);
	}

	private List<Node> getSuccessorNodes(final Node node) throws PetriNetNot1SafeException {
		final var candidatePetriSuccs = node.mMarking.stream().flatMap(p -> mPetriNet.getSuccessors(p).stream());
		final Set<Transition<LETTER, PLACE>> enabledPetriSuccs =
				candidatePetriSuccs.filter(node.mMarking::isTransitionEnabled).collect(Collectors.toSet());

		final List<OutgoingInternalTransition<LETTER, PLACE>> enabledBuchiSuccs = new ArrayList<>();

		mBuchiAutomaton.internalSuccessors(node.mState).forEach(enabledBuchiSuccs::add);

		final List<Node> res = new LinkedList<>();

		for (final var buchiSucc : enabledBuchiSuccs) {
			for (final var petriSucc : enabledPetriSuccs) {
				if (buchiSucc.getLetter().equals(petriSucc.getSymbol())) {
					final Marking<PLACE> succMarking = node.mMarking.fireTransition(petriSucc);
					final var nextBuchiState = buchiSucc.getSucc();
					final Index index = determineIndex(node.mIndex, mPetriNet.isAccepting(succMarking),
							mBuchiAutomaton.isFinal(node.mState));
					res.add(new Node(succMarking, nextBuchiState, index, buchiSucc.getLetter()));
				}
			}
		}
		return res;
	}

	private static Index determineIndex(final Index index, final boolean petriSuccAccepting,
			final boolean buchiPredAccepting) {
		if (index == Index.ONE) {
			return petriSuccAccepting ? Index.TWO : Index.ONE;
		}
		assert index == Index.TWO;
		return buchiPredAccepting ? Index.ONE : Index.TWO;
	}

	@Override
	public String startMessage() {
		return "Starting  Lazy Intersection";
	}

	@Override
	public String exitMessage() {
		return "Exiting Lazy Intersection";
	}

	@Override
	public IPetriNet<LETTER, PLACE> getResult() {
		return mIntersectionNet;
	}

	// need for inner class
	enum Index {
		ONE, TWO
	}

	// class representing a node in the expansion tree
	private class Node {
		Marking<PLACE> mMarking;
		PLACE mState;
		Index mIndex;

		// TODO maybe improve
		// a letter how we arrived at this node. Letters don't append for multiple incoming transitions. And it is not
		// considered for equality. We abstract away from it.
		private LETTER mLetter;

		Node(final Marking<PLACE> marking, final PLACE state, final Index index, final LETTER letter) {
			mMarking = marking;
			mState = state;
			mIndex = index;
			mLetter = letter;
		}

		Node(final Marking<PLACE> marking, final PLACE state, final Index index) {
			this(marking, state, index, null);
		}

		Node(final Marking<PLACE> marking, final PLACE state, final int index) {
			this(marking, state, index == 1 ? Index.ONE : Index.TWO);
			assert (index == 1 || index == 2);
		}

		LETTER getLetter() {
			assert (mLetter != null);
			return mLetter;
		}

		@Override
		public String toString() {
			return "(" + mMarking + ", " + mState + ", " + mIndex + ")";
		}

		@Override
		public boolean equals(final Object obj) {
			if (obj == this) {
				return true;
			}
			if (!(obj instanceof BuchiIntersectLazy.Node)) {
				return false;
			}
			// Important: Letter is not considered for equality! It is only used for carrying the information how one
			// reached this node.
			final Node node = (Node) obj;
			final boolean b1 = mMarking.equals(node.mMarking);
			final boolean b2 = mIndex == node.mIndex;
			final boolean b3 = mState.equals(node.mState);
			return b1 && b2 && b3;
		}
	}

	/**
	 *
	 */
	// @SuppressWarnings("unchecked")
	// @Override
	// public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
	// throws AutomataLibraryException {
	// final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> operandAsNwa =
	// (new BuchiPetriNet2FiniteAutomaton<>(mServices, stateFactory,
	// (IBlackWhiteStateFactory<PLACE>) stateFactory, mPetriNet)).getResult();
	// final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> resultAsNwa =
	// (new BuchiPetriNet2FiniteAutomaton<>(mServices, stateFactory,
	// (IBlackWhiteStateFactory<PLACE>) stateFactory, mIntersectionNet)).getResult();
	//
	// final NestedWordAutomatonReachableStates<LETTER, PLACE> automatonIntersection =
	// new de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersect<>(mServices,
	// (IBuchiIntersectStateFactory<PLACE>) stateFactory, operandAsNwa, mBuchiAutomaton).getResult();
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
