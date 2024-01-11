package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
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

	private final List<Node> visited = new LinkedList<>();

	private final BoundedPetriNet<LETTER, PLACE> mIntersectionNet;

	PetriNetLassoRun<LETTER, PLACE> mAcceptingRun;

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

		final Node root = new Node(initialMarking, initialState, Index.ONE);

		final Stack<Node> currentRun = new Stack<>();
		currentRun.add(root);

		run_helper(root, currentRun);
	}

	void run_helper(final Node node, final Stack<Node> currentRun) throws PetriNetNot1SafeException {
		// void run_helper(final Node node) throws PetriNetNot1SafeException {
		if (visited.contains(node)) {
			return;
		}
		visited.add(node);
		// generate successors on the fly
		final List<Node> succs = getSuccessorNodes(node);
		mLogger.info("Current Node:");
		mLogger.info(node);
		mLogger.info("Succs");
		mLogger.info(succs);
		for (final Node succ : succs) {

			final Transition<LETTER, PLACE> newTransition = addSuccessorTransition(node, succ);
			succ.mNewPetriPredecessor = newTransition;

			if (currentRun.contains(succ) && isLassoAccepting(currentRun, succ)) {
				mLogger.info("found accepting run");
				mLogger.info(currentRun);
				mLogger.info(succ);
				mAcceptingRun = nodeLassoToPetriLasso(currentRun, succ);
				mLogger.info("");
			}

			// TODO is this a pointer? do i need to actually create a new list?
			final Stack<Node> newRun = (Stack<Node>) currentRun.clone();
			newRun.push(succ);

			run_helper(succ, newRun);
		}

	}

	Set<PLACE> concatPlaces(final Set<PLACE> petriPlaces, final PLACE buchiState) {
		return Stream.concat(petriPlaces.stream(), Stream.of(buchiState)).collect(Collectors.toSet());
	}

	PLACE getBuchiState(final Node succNode) {
		return succNode.mIndex == Index.ONE ? mInputQGetQ1.get(succNode.mState) : mInputQGetQ2.get(succNode.mState);
	}

	// Adds a transition to the intersection net.
	Transition<LETTER, PLACE> addSuccessorTransition(final Node srcNode, final Node succNode) {
		// TODO source node nur für buchiState? Kann ich den nicht auch besser übergeben?
		// Add transitions

		final Set<PLACE> petriPreset = succNode.mOldPetriPredecessor.getPredecessors();
		final Set<PLACE> petriPostset = succNode.mOldPetriPredecessor.getSuccessors();
		final LETTER label = succNode.mOldPetriPredecessor.getSymbol();
		final ImmutableSet<PLACE> predecessors = ImmutableSet.of(concatPlaces(petriPreset, getBuchiState(srcNode)));
		final ImmutableSet<PLACE> successors = ImmutableSet.of(concatPlaces(petriPostset, getBuchiState(succNode)));

		return mIntersectionNet.addTransition(label, predecessors, successors);
	}

	private List<Node> getSuccessorNodes(final Node srcNode) throws PetriNetNot1SafeException {
		final var candidatePetriSuccs = srcNode.mMarking.stream().flatMap(p -> mPetriNet.getSuccessors(p).stream());
		final Set<Transition<LETTER, PLACE>> enabledPetriSuccs =
				candidatePetriSuccs.filter(srcNode.mMarking::isTransitionEnabled).collect(Collectors.toSet());

		final List<OutgoingInternalTransition<LETTER, PLACE>> enabledBuchiSuccs = new ArrayList<>();

		mBuchiAutomaton.internalSuccessors(srcNode.mState).forEach(enabledBuchiSuccs::add);

		final List<Node> res = new LinkedList<>();

		for (final var buchiTrans : enabledBuchiSuccs) {
			for (final var petriTrans : enabledPetriSuccs) {
				if (buchiTrans.getLetter().equals(petriTrans.getSymbol())) {

					final Marking<PLACE> succMarking = srcNode.mMarking.fireTransition(petriTrans);
					final var succBuchiState = buchiTrans.getSucc();
					final boolean isPetriSuccAccepting =
							petriTrans.getSuccessors().stream().anyMatch(mPetriNet::isAccepting);
					final Index succIndex = determineIndex(srcNode.mIndex, isPetriSuccAccepting,
							mBuchiAutomaton.isFinal(srcNode.mState));
					res.add(new Node(succMarking, succBuchiState, succIndex, petriTrans));
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

		// a transition how we arrive at this node in the minuend petri net. Letters don't append for multiple incoming
		// transitions. And it is not considered for equality. We a abstract away from it.
		Transition<LETTER, PLACE> mOldPetriPredecessor;

		// Transition of the resulting intersection net.Stored to reconstruct runs!
		// Maybe setter and getter for it
		Transition<LETTER, PLACE> mNewPetriPredecessor;

		Node(final Marking<PLACE> marking, final PLACE state, final Index index,
				final Transition<LETTER, PLACE> predecessor) {
			mMarking = marking;
			mState = state;
			mIndex = index;
			mOldPetriPredecessor = predecessor;

		}

		Node(final Marking<PLACE> marking, final PLACE state, final Index index) {
			this(marking, state, index, null);
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

			// Important: The incoming transition is not considered for equality! It is only used for carrying the
			// information how one reached this node.
			final Node node = (Node) obj;
			final boolean b1 = mMarking.equals(node.mMarking);
			final boolean b2 = mIndex == node.mIndex;
			final boolean b3 = mState.equals(node.mState);
			return b1 && b2 && b3;
		}

		@Override
		public int hashCode() {
			return super.hashCode();
		}
	}

	// TODO better way to represent a lasso.
	// TODO maybe already create it one step earlier
	boolean isLassoAccepting(final List<Node> lassoRun, final Node hondanode) {
		final int fromIndex = lassoRun.indexOf(hondanode);
		final int toIndex = lassoRun.size();
		final List<Node> loop = lassoRun.subList(fromIndex, toIndex);
		// TODO maybe seperate function. or maybe do everything with proper states instead of nodes, then we only have
		// the intersecteionNet cointains it as an accepting state instead of everything with loops and so.
		final boolean loopContainsAcceptingPlace =
				loop.stream().anyMatch(node -> node.mIndex == Index.TWO && mBuchiAutomaton.isFinal(node.mState));
		return loopContainsAcceptingPlace;
	}

	private PetriNetLassoRun<LETTER, PLACE> nodeLassoToPetriLasso(final Stack<Node> lassoRun, final Node hondanode) {
		final int hondaIndex = lassoRun.indexOf(hondanode);
		// TODO hondanode has to be part of both??
		final List<Node> stem = lassoRun.subList(0, hondaIndex + 1);
		final List<Node> loop = lassoRun.subList(hondaIndex, lassoRun.size());
		return new PetriNetLassoRun<>(runOfNodesToPetriNetRun(stem), runOfNodesToPetriNetRun(loop));
	}

	private PetriNetRun<LETTER, PLACE> runOfNodesToPetriNetRun(final List<Node> runOfNodes) {
		final List<Marking<PLACE>> sequenceOfMarkings = new LinkedList<>();
		// TODO there has to be a better solution for appending (iteratively creating) the word!
		Word<LETTER> word = new Word<LETTER>();
		// List<LETTER> labels = new LinkedList<>();
		final List<Transition<LETTER, PLACE>> transitions = new LinkedList<>();

		boolean firstIteration = true;

		for (final Node node : runOfNodes) {
			// To the marking resulting form the original Petri net subtrahend suubnet, we also need to add the buchi
			// state
			sequenceOfMarkings
					.add(new Marking<>(ImmutableSet.of(concatPlaces(node.mMarking.getPlaces(), getBuchiState(node)))));

			final Transition<LETTER, PLACE> predecessorTransition = node.mNewPetriPredecessor;

			// given that the root node can have no predecessor, we need to check for null pointers.
			if (!firstIteration) {
				word = word.concatenate(new Word<>(predecessorTransition.getSymbol()));
				transitions.add(predecessorTransition);
			}
			firstIteration = false;
		}

		// final Word<LETTER> word = new Word<LETTER>(labels.toArray(new LETTER[0]));

		return new PetriNetRun<>(sequenceOfMarkings, word, transitions);
	}

	public PetriNetLassoRun<LETTER, PLACE> getRun() {
		return mAcceptingRun;
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
