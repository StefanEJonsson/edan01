package schedule;


import java.util.LinkedList;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.Max;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.constraints.Cumulative;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;

public class Scheduler2 {

	public int del_add = 1;
	public int del_mul = 2;

	public int number_add = 1;
	public int number_mul = 2;
	public int n = 28;

	public int[] last = { 27, 28 };

	public int[] add = { 9, 10, 11, 12, 13, 14, 19, 20, 25, 26, 27, 28 };

	public int[] mul = { 1, 2, 3, 4, 5, 6, 7, 8, 15, 16, 17, 18, 21, 22, 23, 24 };

	public int[][] dependencies = { { 9 }, { 9 }, { 10 }, { 10 }, { 11 }, { 11 }, { 12 }, { 12 }, { 27 }, { 28 },
			{ 13 }, { 14 }, { 16, 17 }, { 15, 18 }, { 19 }, { 19 }, { 20 }, { 20 }, { 22, 23 }, { 21, 24 }, { 25 },
			{ 25 }, { 26 }, { 26 }, { 27 }, { 28 }, {}, {}, };

	Store store;

	public static void main(String[] args) {
		Scheduler2 p = new Scheduler2();
		p.model();
	}

	public void model() {
		System.out.println("Test");
		store = new Store();
		
		LinkedList<IntVar> ar = new LinkedList();
		
		final int MAXINT = del_add*add.length + del_mul * mul.length + 1;
		
		IntVar[] start = new IntVar[n];
		IntVar[] duration = new IntVar[n];
		
		IntVar[] addResourceUse = new IntVar[n];
		IntVar[] mulResourceUse = new IntVar[n];
		
		for (int i = 0; i < n; i++) {
			start[i] = new IntVar(store, "start" + (i+1), 0, MAXINT);
			ar.add(start[i]);
		}
		
		IntVar one = new IntVar (store, "one", 1, 1);
		IntVar zero = new IntVar (store, "zero", 0, 0);
		
		ar.add(one);
		ar.add(zero);
		
		
		IntVar aDuration = new IntVar (store, "addDuration", del_add, del_add);
		ar.add(aDuration);
		for (int i = 0; i < add.length; i++) {
			duration[add[i]-1] = aDuration;
			 
			addResourceUse[add[i]-1] = one;
			mulResourceUse[add[i]-1] = zero;
		}
		
		IntVar mDuration = new IntVar (store, "mulDuration", del_mul, del_mul);
		ar.add(mDuration);
		for (int i = 0; i < mul.length; i++) {
			duration[mul[i]-1] = mDuration;
			
			addResourceUse[mul[i]-1] = zero;
			mulResourceUse[mul[i]-1] = one;
		}
		
		for (int i = 0; i < n; i++) {
			IntVar localEnd = new IntVar (store, "end" + i, 0, MAXINT);
			for (int j_ = 0; j_ < dependencies[i].length; j_++) {
				int j = dependencies[i][j_]-1;
				ar.add(localEnd);
				Constraint t = new XplusYeqZ (start[i], duration[i], localEnd);
				Constraint eventAfterEvent = new XlteqY (localEnd, start[j]);
				
				store.impose(eventAfterEvent);
				store.impose(t);
			}
		}
		
		IntVar nbrAddJ = new IntVar(store, "nbrAddJ", number_add, number_add);
		ar.add(nbrAddJ);
		IntVar nbrMulJ = new IntVar(store, "nbrMulJ", number_mul, number_mul);
		ar.add(nbrMulJ);
		
		Constraint addersPlacement = new Cumulative (start, duration, addResourceUse, nbrAddJ);
		Constraint multipPlacement = new Cumulative (start, duration, mulResourceUse, nbrMulJ);
		
		store.impose(addersPlacement);
		store.impose(multipPlacement);
		
		
		IntVar[] yAdd = new IntVar[n];
		IntVar[] yMul = new IntVar[n];
		
		for (int i = 0; i < add.length; i++) {
			yAdd[add[i]-1] = new IntVar (store, "yAdd" + i, 1, number_add);
			ar.add(yAdd[add[i]-1]);
			yMul[add[i]-1] = zero;
		}
		
		for (int i = 0; i < mul.length; i++) {
			yMul[mul[i]-1] = new IntVar (store, "yMul" + i, 1, number_mul);
			ar.add(yMul[mul[i]-1]);
			yAdd[mul[i]-1] = zero;
		}
		
		store.impose(new Diffn(start, yAdd, duration, addResourceUse));
		store.impose(new Diffn(start, yMul, duration, mulResourceUse));
		
		
		
		IntVar[] ends = new IntVar[last.length];
		
		for (int i = 0; i < ends.length; i++) {
			IntVar localEnd = new IntVar (store, "localLastEnd" + i, 0, MAXINT);
			ar.add(localEnd);
			Constraint eventAfterEvent = new XplusYeqZ (start[last[i]-1], duration[last[i]-1], localEnd);
			ends[i] = localEnd;
			
			store.impose(eventAfterEvent);
		}
		
		IntVar cost = new IntVar(store, "total time", 0, MAXINT);
		ar.add(cost);

		store.impose(new Max(ends, cost));

		IntVar[] vars = new IntVar[ar.size()];
		for (int i = 0; i < vars.length; i++) {
			vars[i] = ar.get(i);
		}
		
		SelectChoicePoint<IntVar> select = new SimpleSelect<IntVar>(vars, new SmallestDomain<IntVar>(),
				new IndomainMin<IntVar>());
		Search<IntVar> label = new DepthFirstSearch<IntVar>();
		boolean result = label.labeling(store, select, cost);
		System.out.println(result);

	}

}
