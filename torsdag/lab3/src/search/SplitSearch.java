package search;

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
	int nodeCount = 0;

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
		nodeCount++;

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
				failCount++;
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

		static final int SmallestValue = 0, SplitLT = 1, SplitGT = 2;
		static final int InputOrder = 0, FirstFail = 1;

		int selection = FirstFail;
		int algo = SplitLT;

		IntVar crnt;
		IntVar[] searchVariables;
		PrimitiveConstraint cnstraint;
		int val;

		public ChoicePoint(IntVar[] vars) {
			crnt = selectVariable(vars); // ChoicePoint makeChoice(IntVar[] vars)
			searchVariables = vars;
			val = selectValue(crnt, vars);
		
			cnstraint = getConstraint(crnt);
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
			if (algo == SplitLT) {
				tempVal = (var.min() + var.max()) / 2;
				if (var.min() == var.max()) {
					vars = delete(vars, var);
					searchVariables = vars;
				}
			} else if (algo == SplitGT) {
				int t = var.min() + var.max();
				tempVal = (t%2 == 0 ? t/2 : (t+1)/2);
				if (var.min() == var.max()) {
					vars = delete(vars, var);
					searchVariables = vars;
				}
			} else { //smallestValue
				tempVal = var.min();
				vars = delete(vars, var);
				searchVariables = vars;
			}
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
				//System.out.println("" + var + val);
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