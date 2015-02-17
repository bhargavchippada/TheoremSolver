import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;


public class RuleApplier {
	String rule; 
	String rule_lhs;
	String rule_rhs;
	int ruleno;
	HashMap<Character, String> variables = new HashMap<Character, String>(); 
	
	public RuleApplier(String r, int rno) {
		Hypothesis temp_hyp = Utils.expandHypothesis(Utils.expandAll(r));
		rule = temp_hyp.expression;
		rule_lhs = temp_hyp.lhs;
		rule_rhs = temp_hyp.rhs;
		ruleno = rno;
		Utils.println(rule_lhs+" : "+rule_rhs);
	}
	
	ArrayList<Hypothesis> checkRule(Hypothesis hyp){
		ArrayList<Hypothesis> newhypos = new ArrayList<Hypothesis>();
		Hypothesis hyp1 = applyRule(hyp.lhs, hyp.rhs, rule, hyp.expression);
		Hypothesis hyp2 = applyRule(hyp.expression, "", rule_lhs, hyp.expression);
		if(hyp1!=null) {
			Utils.printHypothesis(hyp1);
			newhypos.add(hyp1);
			
			Hypothesis hypo = ThmParser.makeHypothesis(hyp.lhs, 2, ruleno, Utils.rules.get(ruleno),hyp.expression);
			Utils.printHypothesis(hypo);
			newhypos.add(hypo);
		}
		if(hyp2!=null) {
			Utils.printHypothesis(hyp2);
			newhypos.add(hyp2);
		}
		return newhypos;
	}
	
	Hypothesis applyRule(String hyp, String hyp_rhs, String ruleexp, String hyp_exp){
		Hypothesis hypo;
		int lhsrulepos = 0;
		int lenlhsrule = ruleexp.length();
		int lenhyp = hyp.length();
		int pos = 0;
		do {
			//Utils.println(lhsrulepos+" "+pos);
			//Utils.println(ruleexp.charAt(lhsrulepos)+"");
			char rulechar = ruleexp.charAt(lhsrulepos);
			if(("()->F").contains(rulechar+"")){
				if(hyp.charAt(pos) == rulechar){
					//matching
					lhsrulepos++;
					pos++;
				}else{
					break;
				}
			}else if(("->").contains(hyp.charAt(pos)+"")){
				break;
			}else{
				int count = 0;
				char c;
				int posend=pos;
				boolean b = true;
				while(posend<lenhyp){
					c = hyp.charAt(posend);
					//Utils.println(c+"");
					if(c == '(') count++; 
					else if(c==')') count--;
					
					if(count<0) {
						b=false;
						break;
					}else if(count==0){
						// found the expression
						String exp = variables.get(rulechar);
						if(exp==null){
							variables.put(rulechar, hyp.substring(pos, posend+1));
							lhsrulepos++;
							pos=posend+1;
						}else{
							if(exp.equals(hyp.substring(pos, posend+1))){
								//valid
								lhsrulepos++;
								pos=posend+1;
							}else{
								b=false;
								break;
							}
						}
						break;
					}
					posend++;
				}
				if(!b) break;
			}
		} while (pos!=lenhyp && lhsrulepos!=lenlhsrule);
		
		if(lhsrulepos == lenlhsrule && pos == lenhyp){
			//this is the end of rule
			//Utils.println("Found "+hyp_rhs.length());
			if(hyp_rhs.length()==0) {
				//Utils.println("Found 1");
				hypo = transformHypothesis(hyp,0, pos);
				if(hypo==null) return null;
				hypo.how=2;
				hypo.ruleno=ruleno;
				hypo.Ei=Utils.rules.get(ruleno);
				hypo.Ej=hyp_exp;
			}else {
				//Utils.println("Found 2");
				hypo = ThmParser.makeHypothesis(hyp_rhs, 2, ruleno, Utils.rules.get(ruleno),hyp_exp);
			}
			return hypo;
			
		}else{
			//hypothesis ended before satisfying the rule
			//rule ended before hypothesis finished
			//Utils.println("Missed");
		}
		variables.clear();
		return null;
	}
	
	Hypothesis transformHypothesis(String hyp, int hyp_pos, int hyp_end){
		/*
		Iterator it = variables.entrySet().iterator();
		Utils.println(rule+"Rule matches: "+hyp_pos);
	    while (it.hasNext()) {
	        Map.Entry pairs = (Map.Entry)it.next();
	        Utils.println((Character)pairs.getKey()+" : "+(String)pairs.getValue());
	    }
	    */
	    
	    String rhs = rule_rhs;
	    int pos = 0;
	    char c;
	    String newrhs = "";
	    while(pos!=rhs.length()){
	    	c = rhs.charAt(pos);
	    	if(("()->F").contains(c+"")){
	    		newrhs+=c+"";
	    	}else{
	    		String t = variables.get(c);
	    		if(t!=null) newrhs+=t;
	    		else return null;
	    	}
	    	pos++;
	    }
	    
	    //Utils.println(newrhs);
	    if(newrhs.length()!=1 && !(hyp_pos==0 && hyp_end==hyp.length())){
	    	newrhs = "("+newrhs+")";
	    }
	    String newhyp = hyp.substring(0,hyp_pos)+newrhs+hyp.substring(hyp_end);
	    //Utils.println(newhyp);
	    Hypothesis newhypo = Utils.expandHypothesis(newhyp);
	    variables.clear();
	    return newhypo;
	}
	
	public static boolean is_axiom_1(Hypothesis h){
		/* A->(B->A) */	
		String lhs = h.lhs;
		String rhs = h.rhs;
		if(rhs.equals("")) return false;
		Hypothesis temp_hyp = Utils.expandHypothesis(rhs);
		
		if(temp_hyp.rhs.equals(lhs)) return true;
		else return false;	
	}
	
	public static boolean is_axiom_2(Hypothesis h){
		/* (A->(B->C))->((A->B)->(A->C)) */
		String lhs1 = h.lhs;
		String rhs1 = h.rhs;
		if(rhs1.equals("")) return false;
		
		Hypothesis temp_hyp_l1 = Utils.expandHypothesis(lhs1);
		Hypothesis temp_hyp_r1 = Utils.expandHypothesis(rhs1);
		
		String a = temp_hyp_l1.lhs;
		String btoc = temp_hyp_l1.rhs;
		if(btoc.equals("")) return false;
		Hypothesis temp_hyp_btoc = Utils.expandHypothesis(btoc);
		String b = temp_hyp_btoc.lhs;
		String c = temp_hyp_btoc.rhs;
		if(c.equals("")) return false;
		
		String atob = temp_hyp_r1.lhs;
		String atoc = temp_hyp_r1.rhs;
		if (atoc.equals("")) return false;
		
		Hypothesis temp_hyp_atob = Utils.expandHypothesis(atob);
		Hypothesis temp_hyp_atoc = Utils.expandHypothesis(atoc);
		
		String a2 = temp_hyp_atob.lhs;
		String b2 = temp_hyp_atob.rhs;
		String a3 = temp_hyp_atoc.lhs;
		String c2 = temp_hyp_atoc.rhs;
		
		if(b2.equals("") || c2.equals("")) return false;
		if (a.equals(a2) && a.equals(a3) && b.equals(b2) && c.equals(c2)) return true;
		else return false;
	}
	
	public static boolean is_axiom_3(Hypothesis h){
		/* ((A->F)->F)->A */
		String l = h.lhs;
		String r = h.rhs;
		if(r.equals("")) return false;
		
		Hypothesis temp_hyp_l = Utils.expandHypothesis(l);
		String atoF = temp_hyp_l.lhs;
		String f = temp_hyp_l.rhs;
		if (!f.equals("F"))return false;
		Hypothesis temp_hyp_atoF = Utils.expandHypothesis(atoF);
		String a = temp_hyp_atoF.lhs;
		f = temp_hyp_atoF.rhs;
		if (!f.equals("F"))return false;
		if(a.equals(r)) return true;
		else return false;
	}
	
	public static boolean is_axiom_4(Hypothesis h){
		/* A->((A->F)->F) */
		String l = h.lhs;
		String r = h.rhs;
		if(r.equals("")) return false;
		
		Hypothesis temp_hyp_r = Utils.expandHypothesis(r);
		String atoF = temp_hyp_r.lhs;
		String f = temp_hyp_r.rhs;
		if (!f.equals("F"))return false;
		Hypothesis temp_hyp_atoF = Utils.expandHypothesis(atoF);
		String a = temp_hyp_atoF.lhs;
		f = temp_hyp_atoF.rhs;
		if (!f.equals("F"))return false;
		if(a.equals(l)) return true;
		else return false;
	}
	
	
	public static void main(String[] args){
		ThmParser thmp = new ThmParser();
		RuleApplier rapp = new RuleApplier("(A->B)->(~B->~A)",0);
		rapp.checkRule(Utils.expandHypothesis("p->q"));
	}
	
}
