import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;


public class Utils {
	
	public static ArrayList<String> rules = new ArrayList<String>();
	public static ArrayList<RuleApplier> ruleappliers = new ArrayList<RuleApplier>();
	
	public static void println(String s){
		System.out.println(s);
	}
	
	public static void print(String s){
		System.out.print(s);
	}
	
	public static void printRules(){
		for(int i=0; i<rules.size();i++){
			System.out.println(i+": "+ruleappliers.get(i).rule);
		}
	}
	
	public static String expression(String lhs, String rhs){
		if(rhs.length()==0) return lhs; 
		
		String lhs1, rhs1;
		if(lhs.length()!=1) lhs1="("+lhs+")";
		else lhs1=lhs;
		if(rhs.length()!=1) rhs1="("+rhs+")";
		else rhs1=rhs;
		return lhs1+"->"+rhs1;
	}

	public static String removeUnwantedBrac(String s){
		int count = 0;
		char c;
		int pos = 0;
		if(s.length()==1) return s;
		
		while(pos!=s.length()){
			c = s.charAt(pos);
			if(c == '(') count++; 
			else if(c==')') count--;
			else if(c=='-' && count==0){
				// divide it up into lhs and rhs
				String lhs, rhs;
				if(s.charAt(0)=='('){
					// lhs has brackets to itself
					lhs = s.substring(1,pos-1);
				}else{
					lhs = s.substring(0,pos);
				}
				
				if(s.charAt(pos+2)=='('){
					//rhs has brackets to itself
					rhs = s.substring(pos+3,s.length()-1);
				}else{
					rhs = s.substring(pos+2);
				}
				lhs = removeUnwantedBrac(lhs);
				rhs = removeUnwantedBrac(rhs);
				return Utils.expression(lhs, rhs);
			}
			pos++;
		}
		//the expression is like this: (p->q)
		return removeUnwantedBrac(s.substring(1, s.length()-1));
	}
	
	public static String expandNot(String thm){
		int notpos = 0;
		//searching for ~
		while(notpos!=thm.length()){
			if(thm.charAt(notpos)=='~'){
				break;
			}
			notpos++;
		}
		if(notpos==thm.length()) return thm; // no more ~
		int count = 0;
		char c;
		int pos=notpos+1;
		while(pos<thm.length()){
			c = thm.charAt(pos);
			if(c == '(') count++; 
			else if(c==')') count--;
			
			if(count==0){
				// found the expression
				String newthm = thm.substring(0,notpos)+"("+thm.substring(notpos+1,pos+1)+"->F)"+thm.substring(pos+1);
				return expandNot(newthm);
			}
			pos++;
		}
		
		return thm;
	}
	
	public static String expandAnd(String thm){
		int andpos = 0;
		//searching for ~
		while(andpos!=thm.length()){
			if(thm.charAt(andpos)=='&'){
				break;
			}
			andpos++;
		}
		if(andpos==thm.length()) return thm; // no more &
		int count = 0;
		char c;
		int rhspos=andpos+1;
		String rhs="";
		while(rhspos<thm.length()){
			c = thm.charAt(rhspos);
			if(c == '(') count++; 
			else if(c==')') count--;
			
			if(count==0){
				// found rhs expression
				rhs = "("+thm.substring(andpos+1,rhspos+1)+"->F)";
				//Utils.println(rhs);
				break;
			}
			rhspos++;
		}
		
		count = 0;
		int lhspos=andpos-1;
		String lhs="";
		while(lhspos>-1){
			c = thm.charAt(lhspos);
			if(c == '(') count++; 
			else if(c==')') count--;
			
			if(count==0){
				// found lhs expression
				lhs = thm.substring(lhspos,andpos);
				//Utils.println(lhs);
				break;
			}
			lhspos--;
		}
		if((lhspos-1)>=0 && thm.charAt(lhspos-1)=='(' && thm.charAt(rhspos+1)==')'){
			lhspos--;
			rhspos++;
		}
		String newthm = thm.substring(0,lhspos)+"(("+lhs+"->"+rhs+")->F)"+thm.substring(rhspos+1);
		return expandAnd(newthm);
		
	}
	
	public static String expandOr(String thm){
		int orpos = 0;
		//searching for ~
		while(orpos!=thm.length()){
			if(thm.charAt(orpos)=='|'){
				break;
			}
			orpos++;
		}
		if(orpos==thm.length()) return thm; // no more &
		int count = 0;
		char c;
		int rhspos=orpos+1;
		String rhs="";
		while(rhspos<thm.length()){
			c = thm.charAt(rhspos);
			if(c == '(') count++; 
			else if(c==')') count--;
			
			if(count==0){
				// found rhs expression
				rhs = thm.substring(orpos+1,rhspos+1);
				//Utils.println(rhs);
				break;
			}
			rhspos++;
		}
		
		count = 0;
		int lhspos=orpos-1;
		String lhs="";
		while(lhspos>-1){
			c = thm.charAt(lhspos);
			if(c == '(') count++; 
			else if(c==')') count--;
			
			if(count==0){
				// found lhs expression
				lhs = "("+thm.substring(lhspos,orpos)+"->F)";
				//Utils.println(lhs);
				break;
			}
			lhspos--;
		}
		if((lhspos-1)>=0 && thm.charAt(lhspos-1)=='(' && thm.charAt(rhspos+1)==')'){
			lhspos--;
			rhspos++;
		}
		String newthm = thm.substring(0,lhspos)+"("+lhs+"->"+rhs+")"+thm.substring(rhspos+1);
		return expandOr(newthm);
		
	}
	
	public static String expandAll(String thm){
		return removeUnwantedBrac(expandOr(expandAnd(expandNot(thm.replaceAll("\\s+","")))));
	}
	
	public static Hypothesis expandHypothesis(String hyp){
		int count = 0;
		char c;
		int pos = 0;
		
		Hypothesis newhypo = new Hypothesis();
		
		if(hyp.length()==1){
			String exp = hyp.charAt(0)+"";
			newhypo.expression = exp;
			newhypo.lhs = exp;
			newhypo.rhs = "";
			return newhypo;
		}
		
		while(pos!=hyp.length()){
			c = hyp.charAt(pos);
			if(c == '(') count++; 
			else if(c==')') count--;
			else if(c=='-' && count==0){
				// divide it up into lhs and rhs
				String lhs, rhs;
				if(hyp.charAt(0)=='('){
					// lhs has brackets to itself
					lhs = hyp.substring(1,pos-1);
				}else{
					lhs = hyp.substring(0,pos);
				}
				
				if(hyp.charAt(pos+2)=='('){
					//rhs has brackets to itself
					rhs = hyp.substring(pos+3,hyp.length()-1);
				}else{
					rhs = hyp.substring(pos+2);
				}
				
				//System.out.println("expand Hypothesis lhs: "+lhs+"   rhs: "+rhs);
				newhypo.lhs = lhs;
				newhypo.rhs = rhs;
				newhypo.expression = Utils.expression(lhs, rhs);
				return newhypo;
			}
			pos++;
		}
		//the expression is like this: (p->q)
		return expandHypothesis(hyp.substring(1, hyp.length()-1));
	}

	public static void printThmParser(ThmParser thmp){
		Iterator it = thmp.hypothesis.entrySet().iterator();
		Utils.println("Hypothesis: ");
	    while (it.hasNext()) {
	        Map.Entry pairs = (Map.Entry)it.next();
	        Hypothesis hyp = (Hypothesis) pairs.getValue();
	        Utils.println(pairs.getKey() + " " + hyp.expression+" lhs: "+hyp.lhs+" rhs: "+hyp.rhs);
	    }
	    
	    it = thmp.lhs_hypo.entrySet().iterator();
	    Utils.println("LHS: ");
	    while (it.hasNext()) {
	        Map.Entry pairs = (Map.Entry)it.next();
	        HashSet<String> rhs_set = (HashSet<String>) pairs.getValue();
	        Utils.print(pairs.getKey()+" : ");
	        Iterator sit = rhs_set.iterator();
	        while (sit.hasNext()) {
	        	Utils.print((String) sit.next()+" , ");
	        }
	        Utils.print("\n");
	    }
	    
	    it = thmp.rhs_hypo.entrySet().iterator();
	    Utils.println("RHS: ");
	    while (it.hasNext()) {
	        Map.Entry pairs = (Map.Entry)it.next();
	        HashSet<String> lhs_set = (HashSet<String>) pairs.getValue();
	        Utils.print(pairs.getKey()+" : ");
	        Iterator sit = lhs_set.iterator();
	        while (sit.hasNext()) {
	        	Utils.print((String) sit.next()+" , ");
	        }
	        Utils.print("\n");
	    }
	    
	    it = thmp.charsinhypo.iterator();
	    Utils.println("Distinct Chars: ");
	    while (it.hasNext()) {
	    	String ch = (String) it.next();
	        Utils.print(ch+", ");
	    }
	    Utils.print("\n");
	}

	public static void printHypothesis(Hypothesis hyp){
		String footer="";
		if(hyp.how==0) footer = "	Basic Hypothesis";
		else if(hyp.how==1) {
			footer = "	Modus Ponen ( "+hyp.Ei+" on "+hyp.Ej+" )";
		}else if(hyp.how==2) {
			footer = "	rule: "+hyp.ruleno+"	Axiom/Theorem ( "+hyp.Ei+" on "+hyp.Ej+" )";
		}
		
		Utils.println(hyp.expression+", lhs: "+hyp.lhs+", rhs: "+hyp.rhs+footer);
	}

	public static HashSet<String> distinctChars(String s){
		HashSet<String> chars = new HashSet<String>();
		chars.add("F");
		int pos = 0;
		char c;
		while(pos!=s.length()){
			c = s.charAt(pos);
			if(!("()->~&|").contains(c+"")){
				chars.add(c+"");
			}
			pos++;
		}
		return chars;
	}

}
