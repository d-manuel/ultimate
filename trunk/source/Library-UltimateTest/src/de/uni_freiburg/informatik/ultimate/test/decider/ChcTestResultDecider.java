/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE UnitTest Library.
 *
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.decider;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.SMTLibExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.IOverallResultEvaluator;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.ChcOverallResult;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.ChcOverallResultEvaluator;

public class ChcTestResultDecider extends ThreeTierTestResultDecider<ChcOverallResult> {

	public ChcTestResultDecider(final UltimateRunDefinition ultimateRunDefinition,
			final boolean unknownIsJUnitSuccess) {
		super(ultimateRunDefinition, unknownIsJUnitSuccess);
	}

	@Override
	public SMTLibExpectedResultFinder<ChcOverallResult> constructExpectedResultFinder() {
		return new SMTLibExpectedResultFinder<>(ChcOverallResult.UNKNOWN, ChcOverallResult.SAT,
				ChcOverallResult.UNSAT);
	}

	@Override
	public ChcOverallResultEvaluator constructUltimateResultEvaluation() {
		return new ChcOverallResultEvaluator();
	}

	@Override
	public ChcTestResultEvaluation constructTestResultEvaluation() {
		return new ChcTestResultEvaluation();
	}

	public class ChcTestResultEvaluation implements ITestResultEvaluation<ChcOverallResult> {

		private TestResult mTestResult;
		private String mCategory;
		private String mMessage;

		@Override
		public void evaluateTestResult(final IExpectedResultFinder<ChcOverallResult> expectedResultEvaluation,
				final IOverallResultEvaluator<ChcOverallResult> overallResultDeterminer) {
			final ChcOverallResult expectedResult = expectedResultEvaluation.getExpectedResult();
			final ChcOverallResult actualResult = overallResultDeterminer.getOverallResult();

			if (expectedResult == ChcOverallResult.UNKNOWN) {
				mCategory = "expected result unknown";
				mMessage = "expected: " + expectedResult + " actual: " + actualResult;
				mTestResult = TestResult.UNKNOWN;
			}

			if (expectedResult == actualResult) {
				mCategory = "precise match of results (and results are not both UNKOWN).";
				mMessage = "both results are " + expectedResult;
				mTestResult = TestResult.SUCCESS;
				return;
			}

			mCategory = "results don't match";
			mMessage = "expected: " + expectedResult + " actual: " + actualResult;
			mTestResult = TestResult.FAIL;
		}

		@Override
		public void evaluateTestResult(final IExpectedResultFinder<ChcOverallResult> expectedResultEvaluation,
				final Throwable e) {
			final ChcOverallResult expectedResult = expectedResultEvaluation.getExpectedResult();

			mCategory = "threw an exception";
			mMessage = "expected: " + expectedResult + " actual: threw an exception";
			mTestResult = TestResult.FAIL;
		}

		@Override
		public TestResult getTestResult() {
			return mTestResult;
		}

		@Override
		public String getTestResultCategory() {
			return mCategory;
		}

		@Override
		public String getTestResultMessage() {
			return mMessage;
		}

	}
}
