/**
 *  SimpleDFS.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XlteqC;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Implements Simple Depth First Search .
 * 
 * @author Krzysztof Kuchcinski
 * @version 4.1
 */

public class SplitSearch {

	int failCount = 0;

	boolean trace = false;

	/**
	 * Store used in search
	 */
	Store store;

	/**
	 * Defines variables to be printed when solution is found
	 */
	IntVar[] variablesToReport;

	/**
	 * It represents current depth of store used in search.
	 */
	int depth = 0;

	/**
	 * It represents the cost value of currently best solution for FloatVar cost.
	 */
	public int costValue = IntDomain.MaxInt;

	/**
	 * It represents the cost variable.
	 */
	public IntVar costVariable = null;

	public SplitSearch(Store s) {
		store = s;
	}

	/**
	 * This function is called recursively to assign variables one by one.
	 */
	public boolean label(IntVar[] vars) {

		if (trace) {
			for (int i = 0; i < vars.length; i++)
				System.out.print(vars[i] + " ");
			System.out.println();
		}

		ChoicePoint choice = null;
		boolean consistent;

		// Instead of imposing constraint just restrict bounds
		// -1 since costValue is the cost of last solution
		if (costVariable != null) {
			try {
				if (costVariable.min() <= costValue - 1)
					costVariable.domain.in(store.level, costVariable, costVariable.min(), costValue - 1);
				else
					return false;
			} catch (FailException f) {
				return false;
			}
		}

		consistent = store.consistency();

		if (!consistent) {
			// Failed leaf of the search tree
			failCount++;
			return false;
		} else { // consistent
			if (vars.length == 0) {
				// solution found; no more variables to label
				// update cost if minimization
				if (costVariable != null)
					costValue = costVariable.min();

				reportSolution();

				return costVariable == null; // true is satisfiability search and false if minimization
			}

			choice = new ChoicePoint(vars);

			levelUp();

			store.impose(choice.cnstraint);

			// choice point imposed.

			consistent = label(choice.searchVariables);

			if (consistent) {
				levelDown();
				return true;
			} else {
				// failCount++;
				restoreLevel();

				store.impose(new Not(choice.cnstraint));

				// negated choice point imposed.

				consistent = label(vars);

				levelDown();

				if (consistent) {
					return true;
				} else {
					failCount++;
					return false;
				}
			}
		}
	}

	void levelDown() {
		store.removeLevel(depth);
		store.setLevel(--depth);
	}

	void levelUp() {
		store.setLevel(++depth);
	}

	void restoreLevel() {
		store.removeLevel(depth);
		store.setLevel(store.level);
	}

	public void reportSolution() {
		if (costVariable != null)
			System.out.println("Cost is " + costVariable);

		for (int i = 0; i < variablesToReport.length; i++)
			System.out.print(variablesToReport[i] + " ");
		System.out.println("\n---------------");
	}

	public void setVariablesToReport(IntVar[] v) {
		variablesToReport = v;
	}

	public void setCostVariable(IntVar v) {
		costVariable = v;
	}

	public class ChoicePoint {

		static final int smallestValue = 0, splitLT = 1, splitGT = 2;
		static final int InputOrder = 0, FirstFail = 1;

		int selection = InputOrder;
		int algo = splitLT;

		IntVar crnt;
		IntVar[] searchVariables;
		PrimitiveConstraint cnstraint;
		int val;

		public ChoicePoint(IntVar[] vars) {
			crnt = selectVariable(vars); // ChoicePoint makeChoice(IntVar[] vars)
			searchVariables = vars;
			val = selectValue(crnt, vars);
			//System.out.println(""  + vars[0]);
		
			cnstraint = getConstraint(crnt);
//			System.out.println("crnt: " + crnt + ", val: " + val);
//			System.out.println("searchVariables: " + searchVariables[0] + searchVariables[1] + searchVariables[2]);
		}

//		public IntVar[] getSearchVariables() {
//			return searchVariables;
//		}

		/**
		 * example variable selection; input order
		 */
		IntVar selectVariable(IntVar[] vars) {
			//System.out.println("select: " + vars[0] + vars[1] + vars[2]);
			if (selection == FirstFail) {
				IntVar first = vars[0];
				int cost = first.max() - first.min();
				for (int i = 1; i < vars.length; i++) {
					IntVar second = vars[i];
					int newCost = second.max() - second.min();
					if (newCost < cost) {
						first = second;
						cost = newCost;
					}
				}
				return first;
			}
			return vars[0]; //inputorder
		}

		/**
		 * example value selection; indomain_min
		 * @param vars 
		 */
		int selectValue(IntVar var, IntVar[] vars) {
			int tempVal = 0;
			if (algo == splitLT || algo == splitGT) {
				tempVal = (var.min() + var.max()) / 2;if(algo==splitGT&&var.max() - var.min() == 1){tempVal = var.max();}
				
				if (var.min() == var.max()) {
					System.out.println("delete " + var);
					vars = delete(vars, var);
					searchVariables = vars;
				}
			} else { //smallestValue
				tempVal = var.min();
				//System.out.println("delete");
				vars = delete(vars, var);
				searchVariables = vars;
				//System.out.println("" + vars[0]);
			}
			//System.out.println("" + tempVal);
			return tempVal;
			
		}

		/**
		 * example constraint assigning a selected value
		 */
		public PrimitiveConstraint getConstraint(IntVar var) {
			switch (algo) {
			case 1:
				return new XlteqC(var, val);
			case 2:
				System.out.println("" + var + val);
				return new XgteqC(var, val);
			default:
				//System.out.println("var = " + var + ", val = " + val);
				return new XeqC(var, val);
			}
		}

		public IntVar[] delete(IntVar[] vars, IntVar var) {
			IntVar[] temp = new IntVar[vars.length - 1];
			int n = 0;
			for (int m = 0; m < vars.length; m++) {
				if (vars[m] != var) {
					temp[n] = vars[m];
					n++;
				}
			}
			return temp;
		}
	}
}
