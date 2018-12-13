package schedule;


import org.jacop.constraints.Constraint;
import org.jacop.constraints.Max;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;

public class Schedule {

public int del_add = 1;
public int del_mul = 2;

public int number_add = 2;
public int number_mul = 4;
public int n = 28;

public int[] last = {27,28};

public int[] add = {9,10,11,12,13,14,19,20,25,26,27,28};

public int[] mul = {1,2,3,4,5,6,7,8,15,16,17,18,21,22,23,24};

public int[][] dependencies = {
{9},
{9},
{10},
{10},
{11},
{11},
{12},
{12},
{27},
{28},
{13},
{14},
{16,17},
{15,18},
{19},
{19},
{20},
{20},
{22,23},
{21,24},
{25},
{25},
{26},
{26},
{27},
{28},
{},
{},
};
	
	
	Store store;
		
	public static void main(String[] args) {
		Schedule p = new Schedule();
		p.model();
	}

	public void model() {
		store = new Store();

		IntVar[] vars = new IntVar[2*n];
		
		IntVar[][] rects = new IntVar[n][];
		
		for(int i = 0; i < n; i++) {
			IntVar x = new IntVar(store,"time"+i, 0, 1000000000);
			IntVar y;
			IntVar dx;
			if(contains(add,i)) {
				y = new IntVar(store,"addr"+i,0,number_add-1);
				dx = new IntVar(store,"delay",del_add,del_add);
			} else {
				y = new IntVar(store,"mulr"+i,number_add,number_add+number_mul-1);
				dx = new IntVar(store,"delay",del_mul,del_mul);
			}
			
			IntVar dy = new IntVar(store,"height",1,1);
			rects[i] = new IntVar[4];
			rects[i][0] = x;
			rects[i][1] = y;
			rects[i][2] = dx;
			rects[i][3] = dy;
			vars[i*2 + 0] = x;
			vars[i*2 + 1] = y;
			//vars[i*4 + 2] = dx;
			//vars[i*4 + 3] = dy;
		}
		
		Constraint diffn = new Diffn(rects);
		
		store.impose(diffn);
		
		IntVar[] end = new IntVar[n]; 
		
		int maxEnd = add.length*del_add + mul.length*del_mul;
		
		for(int i = 0; i < n; i++) {
			end[i] = new IntVar(store,"end " + i,0,maxEnd);
			store.impose(new XplusYeqZ(rects[i][0],rects[i][2],end[i]));	
		}
		
		for(int i = 0; i < dependencies.length; i++) {
			for(int j_ = 0; j_ < dependencies[i].length; j_++) {
				int j = dependencies[i][j_] - 1;
				//operation i must occur before operation j
				store.impose(new XlteqY(end[i],rects[j][0]));
			}
		}
		
		IntVar cost = new IntVar(store,"total time",0,maxEnd);
		
		store.impose(new Max(end,cost));
		
		SelectChoicePoint<IntVar> select = 
				new SimpleSelect<IntVar>(vars, new SmallestDomain<IntVar>(),
				new IndomainMin<IntVar>());
		Search<IntVar> label = new DepthFirstSearch<IntVar>();
		boolean result = label.labeling(store, select, cost);
		System.out.println(result);

	}
	
	private boolean contains(int[] list, int elem) {
		for(int i = 0; i < list.length; i++) {
			if(list[i] == elem) return true;
		}
		return false;
	}

}
