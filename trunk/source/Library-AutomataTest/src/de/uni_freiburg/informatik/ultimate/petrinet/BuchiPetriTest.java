package de.uni_freiburg.informatik.ultimate.petrinet;

import java.util.Collection;
import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.AutomatonSccComputation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.GetAcceptedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.LassoExtractor;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiIntersectUsingSccs;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiPetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveDead;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveDeadBuchi;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.ConsoleLogger;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

// Test Class for Büchi Petri Nets
public class BuchiPetriTest {
	private AutomataLibraryServices mServices;
	private ILogger mLogger;
	private StringFactory sFactory;

	@Before
	public void setUp() {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
		mServices = new AutomataLibraryServices(services);
		mLogger = new ConsoleLogger(LogLevel.DEBUG);
		sFactory = new StringFactory();
	}

	// @Test
	public void test1() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d", "e");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, true);
		petriNet.addPlace("p6", false, false);
		petriNet.addPlace("p7", false, false);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3", "p4")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2", "p3", "p4")), ImmutableSet.of(Set.of("p5", "p6")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p4")));

		petriNet.addTransition("e", ImmutableSet.of(Set.of("p6", "p5")), ImmutableSet.of(Set.of("p7")));

		final IPetriNet<String, String> abstraction = petriNet;

		checkEmptinessCorrect(abstraction, false);

		// reduceAbstraction(abstraction);
	}

	// @Test
	public void test2() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, true);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", true, false);
		petriNet.addPlace("p5", false, false);
		petriNet.addPlace("p6", false, false);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p2", "p3")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p4", "p5")), ImmutableSet.of(Set.of("p3", "p6")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p1")));

		final IPetriNet<String, String> abstraction = petriNet;

		checkEmptinessCorrect(abstraction, true);
	}

	// @Test
	public void test3() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b", "c");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", false, true);
		petriNet.addPlace("p2", true, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", true, false);
		petriNet.addPlace("p5", true, false);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p1")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1", "p2", "p4")),
				ImmutableSet.of(Set.of("p2", "p3", "p5")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p4")));

		final IPetriNet<String, String> abstraction = petriNet;

		checkEmptinessCorrect(abstraction, false);
	}

	// @Test
	public void test4() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, true);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p2", "p3")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p4")));

		final IPetriNet<String, String> abstraction = petriNet;

		checkEmptinessCorrect(abstraction, false);

		// reduceAbstraction(petriNet);

	}

	// @Test
	public void test5() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, true);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", true, false);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p2", "p5")), ImmutableSet.of(Set.of("p3", "p4")));
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p1")));
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p5")));

		final IPetriNet<String, String> abstraction = petriNet;

		checkEmptinessCorrect(abstraction, false);

		reduceAbstraction(petriNet);

	}

	// @Test
	public void testLassoWord() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d", "e");
		final var buchiAutomaton = new NestedWordAutomaton<>(mServices, new VpAlphabet<>(alphabet), sFactory);

		buchiAutomaton.addState(true, false, "q1");
		buchiAutomaton.addState(false, false, "q2");
		buchiAutomaton.addState(false, false, "qx");
		buchiAutomaton.addState(false, false, "q3");
		buchiAutomaton.addState(false, true, "q4");
		buchiAutomaton.addInternalTransition("q1", "a", "q2");
		buchiAutomaton.addInternalTransition("q2", "b", "qx");
		buchiAutomaton.addInternalTransition("qx", "b", "q2");
		buchiAutomaton.addInternalTransition("q2", "c", "q3");
		buchiAutomaton.addInternalTransition("q3", "d", "q4");
		buchiAutomaton.addInternalTransition("q4", "e", "q3");

		final var lasso = new GetAcceptedLassoWord<>(mServices, buchiAutomaton);
		// mLogger.info(lasso.getResult());
		final var extractor = new LassoExtractor<>(mServices, buchiAutomaton);
		mLogger.info("all lassos:");
		mLogger.info(extractor.getResult());

		// final NestedWord stem = NestedWord.nestedWord(new Word<>("a", "b", "b", "c", "d"));
		// final NestedWord loop = NestedWord.nestedWord(new Word<>("e", "d"));
		final NestedWord stem = NestedWord.nestedWord(new Word<>("a", "c"));
		final NestedWord loop = NestedWord.nestedWord(new Word<>("d", "e", "d"));
		final NestedLassoWord lassoWord = new NestedLassoWord<>(stem, loop);
		final var buchiAccepts = new BuchiAccepts<String, String>(mServices, buchiAutomaton, lassoWord);
		mLogger.info("does buchiAutomaton accept this lassoword?");
		mLogger.info(buchiAccepts.getResult());

	}

	public void understandingSccs() throws AutomataOperationCanceledException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d", "e");
		final var buchiAutomaton = new NestedWordAutomaton<>(mServices, new VpAlphabet<>(alphabet), sFactory);

		buchiAutomaton.addState(true, false, "q1");
		buchiAutomaton.addState(false, false, "q2");
		buchiAutomaton.addState(false, false, "q3");
		buchiAutomaton.addInternalTransition("q1", "a", "q2");
		buchiAutomaton.addInternalTransition("q2", "a", "q3");
		buchiAutomaton.addInternalTransition("q3", "a", "q1");
		buchiAutomaton.addInternalTransition("q1", "a", "q3");

		final NestedWordAutomatonReachableStates<String, String> mBuchiAutomatonAccepting =
				new RemoveUnreachable<>(mServices, buchiAutomaton).getResult();
		final AutomatonSccComputation<String, String> sccComp = new AutomatonSccComputation<>(mServices,
				mBuchiAutomatonAccepting, mBuchiAutomatonAccepting.getStates(), mBuchiAutomatonAccepting.getStates());
		final Collection<StronglyConnectedComponent<String>> sccs = sccComp.getBalls();
		mLogger.info(sccs);

	}

	// @Test
	public void understandingUnfolding() throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		// final Set<String> alphabet = Set.of("a", "b", "c", "d", "e", "f", "g", "h");
		final Set<String> alphabet = Set.of("a", "b", "c", "d", "e", "x");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);
		// Example from Kuechler BA.
		// petriNet.addPlace("p1", true, false);
		// petriNet.addPlace("p2", false, false);
		// petriNet.addPlace("p3", false, true);
		// petriNet.addPlace("p4", false, false);
		// petriNet.addPlace("p5", false, false);
		// petriNet.addPlace("p6", false, false);
		// petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		// petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p3")));
		// petriNet.addTransition("c", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p4")));
		// petriNet.addTransition("d", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p5")));
		// petriNet.addTransition("e", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p6")));
		// petriNet.addTransition("f", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p3")));
		// petriNet.addTransition("g", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p4")));
		// petriNet.addTransition("h", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p5")));
		// Example with two branch cross-branch
		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, true);
		petriNet.addPlace("p4", false, false);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p3")));
		petriNet.addTransition("x", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p3")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p3")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("e", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p2")));

		final var buchiIsEmpty = new BuchiIsEmpty<>(mServices, petriNet, EventOrderEnum.ERV, false, true);
		mLogger.info(buchiIsEmpty.getResult());
		final var run = buchiIsEmpty.getRun();

	}

	// @Test
	public void testingUnfolding() throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d", "e", "f", "g", "h", "i", "j");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);

		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", true, false);
		petriNet.addPlace("p3", true, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, false);
		petriNet.addPlace("p6", false, false);
		petriNet.addPlace("p7", false, false);
		petriNet.addPlace("p8", false, false);
		petriNet.addPlace("p9", false, false);
		petriNet.addPlace("p10", false, false);
		petriNet.addPlace("p11", false, false);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p6")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p7")));
		petriNet.addTransition("e", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p8")));
		petriNet.addTransition("f", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p9")));
		petriNet.addTransition("g", ImmutableSet.of(Set.of("p7")), ImmutableSet.of(Set.of("p8")));
		petriNet.addTransition("h", ImmutableSet.of(Set.of("p8")), ImmutableSet.of(Set.of("p10")));
		petriNet.addTransition("i", ImmutableSet.of(Set.of("p9")), ImmutableSet.of(Set.of("p10")));
		petriNet.addTransition("j", ImmutableSet.of(Set.of("p10")), ImmutableSet.of(Set.of("p4")));

		final var buchiIsEmpty = new BuchiIsEmpty<>(mServices, petriNet, EventOrderEnum.KMM, false, true);
		// final var isEmpty = new IsEmpty<>(mServices, petriNet);
		// final var finitePrefix = new FinitePrefix<>(mServices, petriNet);
		final var unfolding = new PetriNetUnfolder<>(mServices, petriNet, EventOrderEnum.DBO, false, false);
		mLogger.warn(buchiIsEmpty.getResult());
		final var run = buchiIsEmpty.getRun();

	}

	// @Test
	public void testingUnfolding2() throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d", "e", "f", "g");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);

		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", true, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, false);
		petriNet.addPlace("p6", false, false);
		petriNet.addPlace("p7", false, false);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p3")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("d", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p6")));
		petriNet.addTransition("e", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p7")));
		petriNet.addTransition("f", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("g", ImmutableSet.of(Set.of("p7")), ImmutableSet.of(Set.of("p6")));

		final var buchiIsEmpty = new BuchiIsEmpty<>(mServices, petriNet, EventOrderEnum.ERV, false, true);
		// final var isEmpty = new IsEmpty<>(mServices, petriNet);
		// final var finitePrefix = new FinitePrefix<>(mServices, petriNet);
		mLogger.warn(buchiIsEmpty.getResult());
		final var run = buchiIsEmpty.getRun();
		// final var unfolding = new PetriNetUnfolder<>(mServices, petriNet, EventOrderEnum.ERV, false, false);

	}

	// @Test
	public void testingUnfolding3() throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final Set<String> alphabet = Set.of("a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "x", "y", "z");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);

		petriNet.addPlace("p1", false, false);
		petriNet.addPlace("p2", false, false);
		petriNet.addPlace("p3", false, false);
		petriNet.addPlace("p4", false, false);
		petriNet.addPlace("p5", false, false);
		petriNet.addPlace("p6", false, false);
		petriNet.addPlace("p7", false, false);
		petriNet.addPlace("p8", false, false);
		petriNet.addPlace("p9", false, false);
		petriNet.addPlace("p10", false, true);
		petriNet.addPlace("p11", true, false);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p4")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p5")));
		petriNet.addTransition("c", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p6")));

		petriNet.addTransition("d", ImmutableSet.of(Set.of("p4")), ImmutableSet.of(Set.of("p7")));
		petriNet.addTransition("e", ImmutableSet.of(Set.of("p5")), ImmutableSet.of(Set.of("p8")));
		petriNet.addTransition("f", ImmutableSet.of(Set.of("p6")), ImmutableSet.of(Set.of("p9")));

		petriNet.addTransition("g", ImmutableSet.of(Set.of("p7")), ImmutableSet.of(Set.of("p8")));
		petriNet.addTransition("h", ImmutableSet.of(Set.of("p8")), ImmutableSet.of(Set.of("p10")));
		petriNet.addTransition("i", ImmutableSet.of(Set.of("p9")), ImmutableSet.of(Set.of("p10")));

		petriNet.addTransition("j", ImmutableSet.of(Set.of("p10")), ImmutableSet.of(Set.of("p4")));

		petriNet.addTransition("x", ImmutableSet.of(Set.of("p11")), ImmutableSet.of(Set.of("p1")));
		petriNet.addTransition("y", ImmutableSet.of(Set.of("p11")), ImmutableSet.of(Set.of("p2")));
		petriNet.addTransition("z", ImmutableSet.of(Set.of("p11")), ImmutableSet.of(Set.of("p3")));

		final var buchiIsEmpty = new BuchiIsEmpty<>(mServices, petriNet, EventOrderEnum.ERV, false, true);
		// final var isEmpty = new IsEmpty<>(mServices, petriNet);
		// final var finitePrefix = new FinitePrefix<>(mServices, petriNet);
		mLogger.warn(buchiIsEmpty.getResult());
		final var run = buchiIsEmpty.getRun();
		// final var unfolding = new PetriNetUnfolder<>(mServices, petriNet, EventOrderEnum.DBO, false, false);

	}

	// @Test
	public void deterministicConversion() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);

		petriNet.addPlace("p1", true, false);
		petriNet.addPlace("p2", false, true);
		petriNet.addPlace("p3", false, false);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p2", "p3")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p3")), ImmutableSet.of(Set.of("p3")));

		final var buchiPetriIsEmpty = new BuchiIsEmpty<>(mServices, petriNet, EventOrderEnum.ERV, false, true);
		assert (buchiPetriIsEmpty.getResult() == true);
		final var convertedA = new BuchiPetriNet2FiniteAutomaton<>(mServices, sFactory, petriNet).getResult();
		final var buchiIsEmpty =
				new de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty<>(mServices, convertedA);
		assert (buchiIsEmpty.getResult() == true);
		mLogger.info(convertedA);
	}

	@Test
	public void testStemOptmization() throws AutomataLibraryException {
		final Set<String> alphabet = Set.of("a", "b");
		final BoundedPetriNet<String, String> petriNet = new BoundedPetriNet<>(mServices, alphabet, false);

		petriNet.addPlace("p1", true, true);
		petriNet.addPlace("p2", true, false);
		petriNet.addTransition("a", ImmutableSet.of(Set.of("p1")), ImmutableSet.of(Set.of("p1")));
		petriNet.addTransition("b", ImmutableSet.of(Set.of("p2")), ImmutableSet.of(Set.of("p2")));

		final var buchiAutomaton = new NestedWordAutomaton<>(mServices, new VpAlphabet<>(alphabet), sFactory);
		buchiAutomaton.addState(true, true, "q1");
		buchiAutomaton.addState(false, false, "q2");
		buchiAutomaton.addState(false, false, "q3");
		buchiAutomaton.addInternalTransition("q1", "a", "q2");
		buchiAutomaton.addInternalTransition("q2", "b", "q1");
		buchiAutomaton.addInternalTransition("q2", "b", "q3");

		final var intersection =
				new BuchiIntersectUsingSccs<>(mServices, sFactory, petriNet, buchiAutomaton).getResult();
		mLogger.info(intersection);

	}

	private void checkEmptinessCorrect(final IPetriNet<String, String> abstraction, final boolean expectedEmpty)
			throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		// Check Emptiness by Conversion to BüchiAutomaton
		final var automaton =
				(new BuchiPetriNet2FiniteAutomaton<>(mServices, sFactory, sFactory, abstraction)).getResult();
		final var result =
				new de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty<>(mServices, automaton);

		// Emptiness via PetriNet Unfolding Check

		final var result2 = new de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BuchiIsEmpty<>(
				mServices, abstraction);

		// Assert both return the correct result
		final boolean nwaB = result.getResult();
		final boolean netB = result2.getResult();
		assert (nwaB == netB && nwaB == expectedEmpty);
		// print the counter examples
		if (nwaB == netB && nwaB == false) {

			final NestedLassoRun<String, String> run = result.getAcceptingNestedLassoRun();

			final PetriNetLassoRun<String, String> run2 = result2.getRun();

			mLogger.info(run);
			mLogger.info(run2.getStem());
			mLogger.info(run2.getLoop());
		}
	}

	private void reduceAbstraction(final IPetriNet<String, String> petriNet)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		// final var t = new RemoveUnreachable<>(mServices, petriNet);
		// final var s = new RemoveDead<>(mServices, petriNet);
		final var r = new RemoveDeadBuchi<>(mServices, petriNet, null).getResult();
		final var q = new RemoveDead<>(mServices, petriNet);
		mLogger.info("end");
		// mLogger.info(s);
	}
}