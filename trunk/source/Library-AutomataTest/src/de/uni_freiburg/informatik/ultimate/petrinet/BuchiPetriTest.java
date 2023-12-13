package de.uni_freiburg.informatik.ultimate.petrinet;

import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiPetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveDead;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveDeadBuchi;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.ConsoleLogger;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

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

	@Test
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

	@Test
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

	@Test
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

	@Test
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

	@Test
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