package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.Collection;
import java.util.HashSet;
import java.util.Optional;
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

public class BuchiWeakComp<LETTER,PLACE>
 extends GeneralOperation<LETTER, PLACE, IStateFactory<PLACE>>{
	
	private final AutomataLibraryServices mServices;
	private  NestedWordAutomatonReachableStates<LETTER, PLACE> mBuchiAutomatonReachable;
	private Collection<StronglyConnectedComponent<PLACE>> mSccs;
//	private Set<StronglyConnectedComponent<PLACE>> mAcceptingSccs;
//	private Set<StronglyConnectedComponent<PLACE>> mNonAcceptingSccs;
//	private Set<StronglyConnectedComponent<PLACE>> mMixedSccs;
	private Set<PLACE> mAcceptingSccPlaces = new HashSet<PLACE>();
	private boolean isWeak;
	
	public BuchiWeakComp( final AutomataLibraryServices services, final IBlackWhiteStateFactory<PLACE> factory,
			final IPetriNet<LETTER, PLACE> petriNet, NestedWordAutomatonReachableStates<LETTER, PLACE> buchiAutomatonReachable){
		super(services);
		this.mServices = services;
		this.mBuchiAutomatonReachable = buchiAutomatonReachable;
		
		compute();
	}
	
	private void compute() {
		AutomatonSccComputation<LETTER, PLACE> sccComp =  
				new AutomatonSccComputation<>(mServices, mBuchiAutomatonReachable, mBuchiAutomatonReachable.getStates(), 
						mBuchiAutomatonReachable.getStates());
		this.mSccs =  sccComp.getBalls();
		// Each SCC either needs to be nonaccepting (no accepting states), accepting (only accepting states) or weakenizable (no cycles with only nonaccepting states)
		for (var scc : mSccs) {
			boolean isAcceptingSCC = 
					scc.getNodes().stream().allMatch(node -> mBuchiAutomatonReachable.getFinalStates().contains(node));
			if (isAcceptingSCC) { 
				scc.getNodes().stream().forEach(state -> mAcceptingSccPlaces.add(state));
//				mAcceptingSccs.add(scc);
				continue;
				}
			boolean isNonAcceptingSCC = 
					scc.getNodes().stream().allMatch(node -> !mBuchiAutomatonReachable.getFinalStates().contains(node));
			if (isNonAcceptingSCC) { 
//				mNonAcceptingSccs.add(scc);
				continue; 
			}
//			 (!isAcceptingSCC && !isNonAcceptingSCC) 
//				mMixedSccs.add(scc);
			if (isWeakenizable(scc)) {
				scc.getNodes().stream().forEach(state -> mAcceptingSccPlaces.add(state));
			}else {
				this.isWeak = false;
				return;
//				return false;
			}

		}
//		return true;
		this.isWeak = true;
		return;
	}
	// returns true if it weakenizable, false if not
	/**
	 * 
	 * @param scc 
	 * 		A {@link StronglyConnectedComponent} of the Büchi automaton
	 * @return
	 * 		True for weakenizable SCCs. So Sccs without nonaccepting loops.
	 */
	private boolean isWeakenizable(StronglyConnectedComponent<PLACE> scc) {
		Set<PLACE> nodes = scc.getNodes();
		for (PLACE node : nodes) {
			if (mBuchiAutomatonReachable.isFinal(node))
				continue;
			Stack<PLACE> stack = new Stack<PLACE>();
			stack.push(node);
			if (DFS(stack) == false) {
				return false;
			};
		}
		return true;
	}
	
	// Helper Function for the isWeakenizable method
	private boolean DFS(Stack<PLACE> stack) {
		PLACE currentPlace = stack.peek();
		for (var succTrans : mBuchiAutomatonReachable.internalSuccessors(currentPlace)){
			PLACE neighbor = succTrans.getSucc();
			if (mBuchiAutomatonReachable.isFinal(neighbor)) {
//				We only look for nonaccepting cycles. If we encounter an accepting state all subsequently discovered loops 
//				would have an accepting place
				continue; 
			}
			if (stack.contains(neighbor)) {
				return false; // TODO; we found an nonaccepting loop. SCC is not weakenizable.
			}
			else {
				stack.push(neighbor);
				if (DFS(stack) == false) {
					return false;
				};
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