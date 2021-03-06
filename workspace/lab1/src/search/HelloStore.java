package search;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

public class HelloStore {
	public static void main (String[] args) {
		Store store = new Store();
		IntVar x = new IntVar(store,"x",1,100);
		IntVar y = new IntVar(store,"y",1,100);
		
		IntVar xTimes3 = new IntVar(store,"x*3",3,300);
		IntVar three = new IntVar(store,"three",3,3);
		
		Constraint mul = new XmulYeqZ(x,three,xTimes3);
		
		Constraint equation = new XplusYeqC(xTimes3,y,5);
		
		store.impose(mul);
		store.impose(equation);
		
		SimpleDFS dfs = new SimpleDFS(store);
		
		IntVar[] vars = {x,y,xTimes3,three};
		dfs.setVariablesToReport(vars);
		dfs.trace = true;
		dfs.label(vars);
		
	}
}
