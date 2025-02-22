/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Test Library.
 *
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Test Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.svcomp;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SvcompTestResultDeciderNoOverflow;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 *
 */
public class Svcomp17AutomizerOverflowTestSuite extends AbstractSvcompTestSuite {
	
	@Override
	protected ITestResultDecider getTestResultDecider(final UltimateRunDefinition urd) {
		return new SvcompTestResultDeciderNoOverflow(urd, false);
	}
	
	@Override
	protected long getTimeout() {
		// Timeout for each test case in milliseconds
		return 120 * 1000;
	}
	
	@Override
	protected int getFilesPerCategory() {
		// -1 or value larger than 0
		return -1;
	}
	
	@Override
	protected List<SvcompTestDefinition> getTestDefinitions() {
		final List<SvcompTestDefinition> rtr = new ArrayList<>();
		//@formatter:off

		// available sets:
//		Overflows-BitVectors.set
//		Overflows-Other.set	
		//@formatter:on
		
		rtr.addAll(getForAll("Overflows-BitVectors", 9999));
		rtr.addAll(getForAll("Overflows-Other", 9999));
		return rtr;
	}
	
	private List<SvcompTestDefinition> getForAll(final String set, final int limit) {
		return getForAll(set, getTimeout(), limit);
	}
	
	private List<SvcompTestDefinition> getForAll(final String set) {
		return getForAll(set, getTimeout(), getFilesPerCategory());
	}
	
	private List<SvcompTestDefinition> getForAll(final String set, final long timeout, final int limit) {
		final List<SvcompTestDefinition> rtr = new ArrayList<>();
		rtr.add(getTestDefinitionFromExamples(set, "AutomizerC.xml", "svcomp2017/automizer/svcomp-Overflow-32bit-Automizer_Default.epf",
				timeout, limit));
		rtr.add(getTestDefinitionFromExamples(set, "AutomizerC.xml", "svcomp2017/automizer/svcomp-Overflow-64bit-Automizer_Default.epf",
				timeout, limit));
		return rtr;
	}
}
