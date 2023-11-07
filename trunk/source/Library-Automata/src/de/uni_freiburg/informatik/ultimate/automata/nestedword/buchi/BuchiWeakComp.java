package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

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

public class BuchiWeakComp<LETTER,PLACE>
 extends GeneralOperation<LETTER, PLACE, IStateFactory<PLACE>>{
	
	private final AutomataLibraryServices mServices;
	private  NestedWordAutomatonReachableStates<LETTER, PLACE> mBuchiAutomatonReachable;
	private Collection<StronglyConnectedComponent<PLACE>> mSccs;
//	private Set<StronglyConnectedComponent<PLACE>> mAcceptingSccs;
//	private Set<StronglyConnectedComponent<PLACE>> mNonAcceptingSccs;
//	private Set<StronglyConnectedComponent<PLACE>> mMixedSccs;
	private Set<PLACE> mAcceptingSccPlaces;
	private boolean isWeak;
	
	public BuchiWeakComp( final AutomataLibraryServices services, final IBlackWhiteStateFactory<PLACE> factory,
			final IPetriNet<LETTER, PLACE> petriNet, NestedWordAutomatonReachableStates<LETTER, PLACE> buchiAutomatonReachable){
		super(services);
		this.mServices = services;
		this.mBuchiAutomatonReachable = buchiAutomatonReachable;
		
		compute();
	}
	
	private boolean compute() {
		AutomatonSccComputation<LETTER, PLACE> sccComp =  
				new AutomatonSccComputation<>(mServices, mBuchiAutomatonReachable, mBuchiAutomatonReachable.getStates(), 
						mBuchiAutomatonReachable.getStates());
		this.mSccs =  sccComp.getBalls();
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
			if (!isAcceptingSCC && !isNonAcceptingSCC) {
//				mMixedSccs.add(scc);
				if (weakenize(scc) == false) 
					return false;
			}
		}
		return true;
	}
	private boolean weakenize(StronglyConnectedComponent<PLACE> scc) {
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
	
	// returns true if it weakenizable, false if not
	// TODO also automatically weanizes the SCC
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

	@Override
	public Object getResult() {
		// TODO Auto-generated method stub
		return null;
	}
}