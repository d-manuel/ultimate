/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NwaOutgoingLetterAndTransitionAdapter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.NumberOfTransitions;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementNcsbStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Buchi Complementation based on the following paper: <br>
 * 2016TACAS - Blahoudek,Heizmann,Schewe,Strejček,Tsai - Complementing
 * Semi-deterministic Büchi Automata <br>
 * The "lazy S optimization" is explained in the following paper <br>
 * 2018PLDI - Chen,Heizmann,Lengál,Li,Tsai,Turrini,Zhang - Advanced
 * automata-based algorithms for program termination checking <br>
 * This algorithm is only sound for semi-deterministic Büchi automata.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER> letter type
 * @param <STATE>  state type
 */
public final class BuchiComplementNCSB<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mResult;
	private final boolean mCompareResultToLazy3Algorithm = false;


	public BuchiComplementNCSB(final AutomataLibraryServices services,
			final IBuchiComplementNcsbStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final boolean lazySOptimization) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		final BuchiComplementNCSBNwa<LETTER, STATE> onDemandComplement =
				new BuchiComplementNCSBNwa<>(mServices, stateFactory, operand, lazySOptimization);
		final NwaOutgoingLetterAndTransitionAdapter<LETTER, STATE> complemented =
				new NwaOutgoingLetterAndTransitionAdapter<>(onDemandComplement);
		mResult = new NestedWordAutomatonReachableStates<>(mServices, complemented);
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	public BuchiComplementNCSB(final AutomataLibraryServices services,
			final IBuchiComplementNcsbStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, false);
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Operand " + mOperand.sizeInformation() + " Result "
				+ mResult.sizeInformation();
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Start testing correctness of " + getOperationName());
		}
		boolean correct = true;
		if (mCompareResultToLazy3Algorithm) {
			final NestedWordAutomatonReachableStates<LETTER, STATE> lazy3 = new BuchiComplementNCSBLazy3<LETTER, STATE>(mServices,
					(IBuchiComplementNcsbStateFactory<STATE>) stateFactory, mOperand).getResult();
			final int numberOfTransitionsLazy3 = new NumberOfTransitions<>(mServices, lazy3).getResult();
			final int numberOfTransitionsResult = new NumberOfTransitions<>(mServices, getResult()).getResult();
			correct &= (lazy3.size() == mResult.size());
			if (!correct) {
				throw new AssertionError(String.format(
						"Inconsistent number of states. Input: %s states, output: %s states, %s transitions, lazy3: %s states, %s transitions",
						mOperand.size(), mResult.size(), numberOfTransitionsResult, lazy3.size(),
						numberOfTransitionsLazy3));
			}
			correct &= (new NumberOfTransitions<>(mServices, lazy3).getResult().equals(new NumberOfTransitions<>(mServices, getResult()).getResult()));
			if (!correct) {
				throw new AssertionError(String.format(
						"Inconsistent number of transitions. Input: %s states, output: %s states, %s transitions, lazy3: %s states, %s transitions",
						mOperand.size(), mResult.size(), numberOfTransitionsResult, lazy3.size(),
						numberOfTransitionsLazy3));
			}
		}

		final boolean underApproximationOfComplement = false;
		final List<NestedLassoWord<LETTER>> lassoWords = new ArrayList<>();
		final BuchiIsEmpty<LETTER, STATE> operandEmptiness = new BuchiIsEmpty<>(mServices, mOperand);
		final boolean operandEmpty = operandEmptiness.getResult();
		if (!operandEmpty) {
			lassoWords.add(operandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		final BuchiIsEmpty<LETTER, STATE> resultEmptiness = new BuchiIsEmpty<>(mServices, mResult);
		final boolean resultEmpty = resultEmptiness.getResult();
		if (!resultEmpty) {
			lassoWords.add(resultEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		correct &= !(operandEmpty && resultEmpty);
		assert correct;
		/*
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, mResult.size()));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, mResult.size()));
		*/
		for (int i = 0; i < 11; ++i) {
			lassoWords.add(NestedWordAutomataUtils.getRandomNestedLassoWord(mResult, 1, i));
			lassoWords.add(NestedWordAutomataUtils.getRandomNestedLassoWord(mResult, 2, i));
		}
		lassoWords.addAll((new LassoExtractor<>(mServices, mOperand)).getResult());
		lassoWords.addAll((new LassoExtractor<>(mServices, mResult)).getResult());

		for (final NestedLassoWord<LETTER> nlw : lassoWords) {
			boolean thistime = checkAcceptance(nlw, mOperand, underApproximationOfComplement);
			if (!thistime) {
				thistime = checkAcceptance(nlw, mOperand, underApproximationOfComplement);
			}
			correct &= thistime;
			assert correct;
		}



		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, getOperationName() + "Failed",
					"language is different", mOperand, mResult);
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
		return correct;
	}

	private boolean checkAcceptance(final NestedLassoWord<LETTER> nlw,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand, final boolean underApproximationOfComplement)
			throws AutomataLibraryException {
		final boolean op = (new BuchiAccepts<>(mServices, operand, nlw)).getResult();
		final boolean res = (new BuchiAccepts<>(mServices, mResult, nlw)).getResult();
		boolean correct;
		if (underApproximationOfComplement) {
			correct = !res || op;
		} else {
			correct = op ^ res;
		}
		return correct;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public NestedWordAutomatonReachableStates<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics result = new AutomataOperationStatistics();

		final int inputSize = getOperand().size();
		final int outputSize = getResult().size();

		result.addKeyValuePair(StatisticsType.STATES_INPUT, inputSize);
		result.addKeyValuePair(StatisticsType.STATES_OUTPUT, outputSize);

		final int outputTransitions = new NumberOfTransitions<>(mServices, getResult()).getResult();
		result.addKeyValuePair(StatisticsType.TRANSITIONS_OUTPUT, outputTransitions);

		return result;
	}
}
