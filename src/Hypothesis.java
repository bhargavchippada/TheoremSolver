import java.util.HashSet;


public class Hypothesis {
	String expression;
	String lhs;
	String rhs;
	int how; //0 means hypothesis, 1 means result of modus ponens, 2 means result of axiom
	int ruleno = -1; // contains rule number in case of axiom
	String Ei; // contains(1) A		or		(2)		rule(ruleno)
	String Ej; // contains(1) A->B		or	(2)			A
	HashSet<Integer> appliedrules = new HashSet<Integer>();
	
	@Override
	public boolean equals(Object obj) {
		return expression.equals(((Hypothesis)obj).expression);
	}
	
	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		return expression.hashCode();
	}
}
