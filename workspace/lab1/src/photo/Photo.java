package photo;

import java.util.ArrayList;

import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Distance;
import org.jacop.constraints.IfThenElse;
import org.jacop.constraints.Max;
import org.jacop.constraints.Or;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMax;
import org.jacop.search.IndomainMin;
import org.jacop.search.LargestDomain;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.jacop.set.core.SetVar;
import org.jacop.set.search.IndomainSetMin;
import org.jacop.set.search.MinGlbCard;

import search.SimpleDFS;

public class Photo {

	Store store;

	public static void main(String[] args) {
		Photo p = new Photo();
		p.model();
	}

	public void model() {
		store = new Store();

		/*
		 * int n = 9; int n_prefs = 17; int[][] prefs = { { 1, 3 }, { 1, 5 }, { 1, 8 },
		 * { 2, 5 }, { 2, 9 }, { 3, 4 }, { 3, 5 }, { 4, 1 }, { 4, 5 }, { 5, 6 }, { 5, 1
		 * }, { 6, 1 }, { 6, 9 }, { 7, 3 }, { 7, 8 }, { 8, 9 }, { 8, 7 } };
		 */

		/*
		 * int n = 11; int n_prefs = 20; int[][] prefs = { { 1, 3 }, { 1, 5 }, { 2, 5 },
		 * { 2, 8 }, { 2, 9 }, { 3, 4 }, { 3, 5 }, { 4, 1 }, { 4, 5 }, { 4, 6 }, { 5, 1
		 * }, { 6, 1 }, { 6, 9 }, { 7, 3 }, { 7, 5 }, { 8, 9 }, { 8, 7 }, { 8, 10 }, {
		 * 9, 11 }, { 10, 11 } };
		 */

		int n = 15;
		int n_prefs = 20;
		int[][] prefs = { { 1, 3 }, { 1, 5 }, { 2, 5 }, { 2, 8 }, { 2, 9 }, { 3, 4 }, { 3, 5 }, { 4, 1 }, { 4, 15 },
				{ 4, 13 }, { 5, 1 }, { 6, 10 }, { 6, 9 }, { 7, 3 }, { 7, 5 }, { 8, 9 }, { 8, 7 }, { 8, 14 }, { 9, 13 },
				{ 10, 11 } };

		IntVar[] position = new IntVar[n];
		for (int i = 0; i < n; i++) {
			position[i] = new IntVar(store, "person " + (i + 1) + " is at ", 1, n);
		}

		store.impose(new Alldifferent(position));

		IntVar[] distance = new IntVar[n_prefs];
		for (int i = 0; i < n_prefs; i++) {
			int[] pref = prefs[i];
			int a = pref[0]; // person id
			int b = pref[1]; // person id
			distance[i] = new IntVar(store, "distance between " + a + " -> " + b, 1, n - 1);
			Constraint c = new Distance(position[a - 1], position[b - 1], distance[i]);
			store.impose(c);
		}

		// IntVar unit = new IntVar(store,1,1);
		// IntVar zero = new IntVar(store,0,0);
		IntVar[] fulfilled = new IntVar[n_prefs];
		for (int i = 0; i < n_prefs; i++) {
			fulfilled[i] = new IntVar(store, "fulfillment of pref " + (i + 1), 0, 1);
			PrimitiveConstraint c1 = new XeqC(distance[i], 1);
			PrimitiveConstraint c2 = new XeqC(fulfilled[i], 1);
			PrimitiveConstraint c3 = new XeqC(fulfilled[i], 0);
			Constraint c = new IfThenElse(c1, c2, c3);
			store.impose(c);
		}

		IntVar utilityA = new IntVar(store, 0, n_prefs);
		Constraint c = new SumInt(fulfilled, "==", utilityA);
		store.impose(c);

		IntVar costA = new IntVar(store, -n_prefs, 0);
		store.impose(new XplusYeqC(utilityA, costA, 0));

		IntVar costB = new IntVar(store, 1, n - 1);
		store.impose(new Max(distance, costB));

		SelectChoicePoint<IntVar> select = new SimpleSelect<IntVar>(position, new SmallestDomain<IntVar>(),
				new IndomainMin<IntVar>());
		Search<IntVar> label = new DepthFirstSearch<IntVar>();
		// System.out.println("starting search");
		boolean result = label.labeling(store, select, costB);

		System.out.println("Det funkar fortfarande!");
		System.out.println(result);

	}

}
