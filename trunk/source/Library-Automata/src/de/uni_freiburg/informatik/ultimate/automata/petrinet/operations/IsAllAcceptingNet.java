package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class IsAllAcceptingNet<LETTER, PLACE> extends GeneralOperation<LETTER, PLACE, IStateFactory<PLACE>> {
	BoundedPetriNet<LETTER, PLACE> mPetriNet;
	private final boolean mIsAllAccepting;

	public IsAllAcceptingNet(final AutomataLibraryServices services, final BoundedPetriNet<LETTER, PLACE> petriNet) {
		super(services);
		mPetriNet = petriNet;
		mIsAllAccepting = isAllAcceptingNet(petriNet);
	}

	public static <LETTER, PLACE> boolean isAllAcceptingNet(final IPetriNet<LETTER, PLACE> petriNet) {
		final Stream<Transition<LETTER, PLACE>> transitions = petriNet.getTransitions().stream();
		return transitions.allMatch(trans -> trans.getSuccessors().stream().anyMatch(petriNet::isAccepting));
	}

	@Override
	public Boolean getResult() {
		return mIsAllAccepting;
	}
}
