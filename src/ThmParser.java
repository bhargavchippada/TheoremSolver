import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Scanner;



public class ThmParser {
	
	HashMap<String, Hypothesis> hypothesis = new HashMap<String,Hypothesis>();
	HashMap<String,HashSet<String> > lhs_hypo = new HashMap<String,HashSet<String> >();
	HashMap<String,HashSet<String> > rhs_hypo = new HashMap<String,HashSet<String> >();
	
	HashMap<String,HashSet<Hypothesis> > new_lhs_hypo = new HashMap<String,HashSet<Hypothesis> >();
	// the above is for the sake of modus ponens computation, to avoid redundant comparisons
	
	HashSet<String> charsinhypo = new HashSet<String>();
	
	public ThmParser() {
		Utils.rules.add("A->(B->A)"); //axiom 0
		Utils.ruleappliers.add(new RuleApplier("A->(B->A)",0));
		Utils.rules.add("(A->(B->C))->((A->B)->(A->C))"); //axiom 1
		Utils.ruleappliers.add(new RuleApplier("(A->(B->C))->((A->B)->(A->C))",1));
		Utils.rules.add("((A->F)->F)->A"); //axiom 2
		Utils.ruleappliers.add(new RuleApplier("((A->F)->F)->A",2));
		Utils.rules.add("A->((A->F)->F)"); //axiom 3
		Utils.ruleappliers.add(new RuleApplier("A->((A->F)->F)",3));
		
		Utils.rules.add("(A->B)->(~B->~A)"); //axiom 4
		Utils.ruleappliers.add(new RuleApplier("(A->B)->(~B->~A)",4));
		Utils.rules.add("(~B->~A)->(A->B)"); //axiom 5
		Utils.ruleappliers.add(new RuleApplier("(~B->~A)->(A->B)",5));
		Utils.rules.add("(~B->A)->(~A->B)"); //axiom 6
		Utils.ruleappliers.add(new RuleApplier("(~B->A)->(~A->B)",6));
		Utils.rules.add("(B->~A)->(A->~B)"); //axiom 7
		Utils.ruleappliers.add(new RuleApplier("(B->~A)->(A->~B)",7));
		Utils.rules.add("~(A&B)->(~A|~B)"); //axiom 8
		Utils.ruleappliers.add(new RuleApplier("~(A&B)->(~A|~B)",8));
		Utils.rules.add("~(A|B)->(~A&~B)"); //axiom 9
		Utils.ruleappliers.add(new RuleApplier("~(A|B)->(~A&~B)",9));
		
	}
	
	void rhstolhs(String thm){
		int count = 0;
		char c;
		int pos = 0;
		
		if(thm.length()==1){
			//Utils.println(thm.charAt(0)+"");
			if(thm.charAt(0)=='F') return;
			else{
				rhstolhs("("+thm.charAt(0)+"->F)->F");
				return;
			}
		}
		
		while(pos!=thm.length()){
			c = thm.charAt(pos);
			if(c == '(') count++; 
			else if(c==')') count--;
			else if(c=='-' && count==0){
				// divide it up into lhs and rhs
				String lhs, rhs;
				if(thm.charAt(0)=='('){
					// lhs has brackets to itself
					lhs = thm.substring(1,pos-1);
				}else{
					lhs = thm.substring(0,pos);
				}
				
				if(thm.charAt(pos+2)=='('){
					//rhs has brackets to itself
					rhs = thm.substring(pos+3,thm.length()-1);
				}else{
					rhs = thm.substring(pos+2);
				}
				//lhs = removeUnwantedBrac(lhs);
				//rhs = removeUnwantedBrac(rhs);
				
				//Utils.println("lhs: "+lhs+"   rhs: "+rhs);
				Hypothesis temp_hypo = makeHypothesis(lhs, 0, -1, null, null);
				insertNewHypoMPDirty(temp_hypo);
				
				rhstolhs(rhs);
				return;
			}
			pos++;
		}
		//the expression is like this: (p->q)
		rhstolhs(thm.substring(1, thm.length()-1));
	}
	
	public static Hypothesis makeHypothesis(String hyp, int how, int ruleno, String Ei, String Ej){
		if(hyp.length()==0) return null;
		Hypothesis newhypo = Utils.expandHypothesis(hyp);
		newhypo.how = how;
		newhypo.ruleno = ruleno;
		newhypo.Ei = Ei;
		newhypo.Ej = Ej;
		return newhypo;
	}
	
	boolean insertHypothesis(Hypothesis newhypo){
		String expression = newhypo.expression;
		
		if(newhypo==null) return false;
		else if(expression.length()==0) return false;
		
		if(hypothesis.containsKey(expression)) {
			//Utils.println("Existing hypo: "+expression); 
			return false;
		}
		
		
		String lhs = newhypo.lhs;
		String rhs = newhypo.rhs;
		
		hypothesis.put(expression,newhypo);
		Utils.println("Adding hypo "+expression);
		
		HashSet<String> rhs_set = lhs_hypo.get(lhs);
		if(rhs_set == null){
			rhs_set = new HashSet<String>();
			rhs_set.add(rhs);
			lhs_hypo.put(lhs, rhs_set);
		}else{
			rhs_set.add(rhs);
		}

		HashSet<String> lhs_set = rhs_hypo.get(rhs);
		if(lhs_set == null){
			lhs_set = new HashSet<String>();
			lhs_set.add(lhs);
			rhs_hypo.put(rhs, lhs_set);
		}else{
			lhs_set.add(lhs);
		}
		
		return true;
	}
	
	boolean insertNewHypoMPDirty(Hypothesis newhypo){
		boolean in_hypo = insertHypothesis(newhypo);
		
		if(in_hypo) {
			//Utils.println("Add New hypo: "+newhypo.expression);
			HashSet<Hypothesis> hypo_set = (HashSet<Hypothesis>) new_lhs_hypo.get(newhypo.lhs);
			if(hypo_set==null){
				hypo_set = new HashSet<Hypothesis>();
				hypo_set.add(newhypo);
				new_lhs_hypo.put(newhypo.lhs, hypo_set);
			}else{
				hypo_set.add(newhypo);
			}
		}else{
			//Utils.println("Existing hypo: "+newhypo.expression);
		}
		
		return in_hypo;
	}
	
	void modusponens(){
		//Utils.println("Size of new_lhs_hypo: "+new_lhs_hypo.size());
		HashMap<String,HashSet<Hypothesis> > temp_lhs_hypo = new HashMap<String,HashSet<Hypothesis> >();
		HashSet<Hypothesis> new_hypos = new HashSet<Hypothesis>();
		
		//Utils.println("hypothesis list");
		Iterator it = hypothesis.entrySet().iterator();
	    while (it.hasNext()) {
	        Map.Entry pairs = (Map.Entry)it.next();
	        String A = (String)pairs.getKey();
	        //Utils.println("hypothesis A : "+A);
	        HashSet<Hypothesis> A_B = new_lhs_hypo.get(A);
	        if(A_B == null) {
	        	//Utils.println("No match");
	        	continue;
	        	}
	        else{
	        	//Utils.println("Matched: "+A_B.size());
	        	Iterator bit = A_B.iterator();
	        	while (bit.hasNext()) {
	    	        Hypothesis A_B_hypo = (Hypothesis)bit.next();
		        	Hypothesis mp_hypo = makeHypothesis(A_B_hypo.rhs, 1, -1, A, A_B_hypo.expression);
		        	if(mp_hypo!=null) {
		        		new_hypos.add(mp_hypo);
			        	if(hypothesis.containsKey(mp_hypo.expression)) {
			        		//Utils.println("Existing MP result: "+A_B_hypo.rhs+" on "+A+" and "+A_B_hypo.expression);
			        		//already existing
				        }else{// new hypothesis has resulted
				        	//Utils.println("New MP result: "+A_B_hypo.rhs+" on "+A+" and "+A_B_hypo.expression);
				        }
		        	}else{
		        		//Utils.println("MP Not Valid: "+A_B_hypo.rhs+" on "+A+" and "+A_B_hypo.expression);
		        	}
		        }
	        }
	    }
	    
	    //Utils.println("new hypothesis list");
	    it = new_lhs_hypo.entrySet().iterator();
	    while (it.hasNext()) {
	        Map.Entry pairs = (Map.Entry)it.next();
	        HashSet<Hypothesis> hypos = (HashSet<Hypothesis>) pairs.getValue();
	        Iterator<Hypothesis> Ait = hypos.iterator();
	        while(Ait.hasNext()){
	        	String A = ((Hypothesis)Ait.next()).expression;
	        	//Utils.println("hypothesis A : "+A);
	        	HashSet<String> B_set = lhs_hypo.get(A);
	        	if(B_set == null){
	        		//Utils.println("No match");
	        		continue;
	        		}
	        	else{
	        		//Utils.println("Matched: "+B_set.size());
	        		Iterator Bit = B_set.iterator();
		        	while(Bit.hasNext()){
		        		String B_str = (String) Bit.next();
		        		String A_B_exp = Utils.expression(A, B_str);
		        		Hypothesis mp_hypo = makeHypothesis(B_str, 1, -1, A, A_B_exp);
		        		if(mp_hypo!=null) {
			        		new_hypos.add(mp_hypo);
				        	if(hypothesis.containsKey(mp_hypo.expression)) {
				        		//Utils.println("Existing MP result: "+B_str+" on "+A+" and "+A_B_exp);
				        		//already existing
					        }else{// new hypothesis has resulted
					        	//Utils.println("New MP result: "+B_str+" on "+A+" and "+A_B_exp);
					        }
			        	}else{
			        		//Utils.println("MP Not Valid: "+B_str+" on "+A+" and "+A_B_exp);
			        	}
		        	}
	        	}
	        	
	        }
	    }
	    
	    //Utils.println("Size of new_hypos: "+new_hypos.size());
	    
	    Iterator<Hypothesis> hit = new_hypos.iterator();
	    while(hit.hasNext()){
	    	Hypothesis mp_hypo = hit.next();
	    	boolean b = insertHypothesis(mp_hypo);
	    	if(b){
	    		HashSet<Hypothesis> temp_hypos = temp_lhs_hypo.get(mp_hypo.lhs);
	        	if(temp_hypos == null){
	        		temp_hypos = new HashSet<Hypothesis>();
	        		temp_hypos.add(mp_hypo);
	        		temp_lhs_hypo.put(mp_hypo.lhs, temp_hypos);
	        	}else{
	        		temp_hypos.add(mp_hypo);
	        	}
	        	//Utils.printHypothesis(mp_hypo);
	    	}
	    }
	    

	    //Utils.println("Size of temp_lhs_hypo: "+temp_lhs_hypo.size());
	    
	    new_lhs_hypo.clear();
	    new_lhs_hypo = temp_lhs_hypo;
	    if(new_lhs_hypo.size()!=0) modusponens();
	}
	
	void axiom1(HashSet<String> A, HashSet<String> B){
		Iterator<String> it_A = A.iterator();
		Utils.println("Axiom 1 on single non-terminals : ");
		HashSet<Hypothesis> new_hypos = new HashSet<Hypothesis>();
		while(it_A.hasNext()){
			String sA = it_A.next();
			Iterator<String> it_B = B.iterator();
			while(it_B.hasNext()){
				String sB = it_B.next();
				String rhs = Utils.expression(sB, sA);
				String hyp = Utils.expression(sA, rhs);
				Hypothesis axiom1_hypo = makeHypothesis(hyp, 2, 1, Utils.rules.get(0), (sA+" & "+sB));
				axiom1_hypo.appliedrules.add(0);
				new_hypos.add(axiom1_hypo);
			}
		}
	    
	    Iterator<Hypothesis> hit = new_hypos.iterator();
	    while(hit.hasNext()){
	    	Hypothesis mp_hypo = hit.next();
	    	insertNewHypoMPDirty(mp_hypo);
	    }
	    
	    Utils.println("modus ponens: ");
		modusponens();
	    
	    if(checkF()) {
			proofPath("F");
			return;
		}
	}
	
	boolean checkF(){
		return hypothesis.containsKey("F");
	}
	
	void proofPath(String h){
		Hypothesis hyp = hypothesis.get(h);
		if(hyp.how==0) Utils.printHypothesis(hyp);
		else if(hyp.how==1){
			proofPath(hyp.Ei);
			proofPath(hyp.Ej);
			Utils.printHypothesis(hyp);
		}else if(hyp.how==2){
			proofPath(hyp.Ej);
			Utils.printHypothesis(hyp);
		}
	}

	
	void runParser(String hyp){
		charsinhypo = Utils.distinctChars(hyp);
		Utils.println("rhstolhs: ");
		rhstolhs(Utils.expandAll(hyp));
		int i = 1;
		while(true){
			i=1;
			int itr = 0;
			while(i!=0 && itr < 1){
				i=0;
				Utils.println("modus ponens: ");
				modusponens();
				int h1=hypothesis.size();
				
				
				for(int rulenum=0; rulenum<Utils.rules.size();rulenum++){
					
					Utils.println("Applying rule "+rulenum+" "+Utils.ruleappliers.get(rulenum).rule+" : ");
					HashSet<Hypothesis> new_hypos = new HashSet<Hypothesis>();
					Iterator it = hypothesis.entrySet().iterator();
				    while (it.hasNext()) {
				        Map.Entry pairs = (Map.Entry)it.next();
				        String exp = (String)pairs.getKey();
				        Hypothesis hypo = (Hypothesis)pairs.getValue();
				        if(hypo.appliedrules.contains(rulenum)) continue;
				        else {
				        	System.out.println("on : "+exp);
				        	hypo.appliedrules.add(rulenum);
				        }
				        ArrayList<Hypothesis> hypos = Utils.ruleappliers.get(rulenum).checkRule(hypo);
				        for(int x = 0; x< hypos.size(); x++){
				        	new_hypos.add(hypos.get(x));
				        }
				    }
				    
				    Iterator<Hypothesis> hit = new_hypos.iterator();
				    while(hit.hasNext()){
				    	Hypothesis mp_hypo = hit.next();
				    	insertNewHypoMPDirty(mp_hypo);
				    }
				    
				    Utils.println("modus ponens: ");
					modusponens();
				    
				    if(checkF()) {
						proofPath("F");
						return;
					}
				}
			    
			    int h2 = hypothesis.size();
			    if(h1!=h2) {i=1; itr++;}
			    if(checkF()) {
					proofPath("F");
					return;
				}
			}
			
			while(true){
				System.out.print("hint : ");
				Utils.printRules();
				Scanner sc = new Scanner(System.in);
				String inp = sc.nextLine();
				
				int newrulenum;
				
				if(inp.equals("continue")) break;
				else if(inp.equals("axiom1")) {
					axiom1(charsinhypo, charsinhypo);
					continue;
				}else if(inp.equals("rule")){
					System.out.print("rule number : ");
					Scanner scnum = new Scanner(System.in);
					String inpnum = scnum.nextLine();
					newrulenum = Integer.parseInt(inpnum);
				}else{
					newrulenum = Utils.rules.size();
					Utils.rules.add(inp);
					Utils.ruleappliers.add(new RuleApplier(inp, newrulenum));
				}
				
				Utils.println("");
				
				Utils.println("modus ponens: ");
				modusponens();
					
				Utils.println("Applying rule "+newrulenum+" "+Utils.ruleappliers.get(newrulenum).rule+" : ");
				HashSet<Hypothesis> new_hypos = new HashSet<Hypothesis>();
				Iterator it = hypothesis.entrySet().iterator();
			    while (it.hasNext()) {
			        Map.Entry pairs = (Map.Entry)it.next();
			        String exp = (String)pairs.getKey();
			        Hypothesis hypo = (Hypothesis)pairs.getValue();
			        if(hypo.appliedrules.contains(newrulenum)) continue;
			        else {
			        	System.out.println("on : "+exp);
			        	hypo.appliedrules.add(newrulenum);
			        }
			        ArrayList<Hypothesis> hypos = (Utils.ruleappliers.get(newrulenum)).checkRule(hypo);
			        for(int x = 0; x< hypos.size(); x++){
			        	new_hypos.add(hypos.get(x));
			        }
			    }
			    
			    Iterator<Hypothesis> hit = new_hypos.iterator();
			    while(hit.hasNext()){
			    	Hypothesis mp_hypo = hit.next();
			    	insertNewHypoMPDirty(mp_hypo);
			    }
			    
			    Utils.println("modus ponens: ");
				modusponens();
			    
			    if(checkF()) {
					proofPath("F");
					return;
			    }
			}
						
		}
	}
	
	
	public static void main(String[] args){
		long startTime = System.currentTimeMillis();
		ThmParser thmp = new ThmParser();
		String EXAMPLE_TEST="(p&q)->(p|q)";//"((p->q)->((r->s)->t))->((u->((r->s)->t))->((p->u)->(s->t)))";
		Utils.println(EXAMPLE_TEST);
		//EXAMPLE_TEST.replaceAll("\\s+","");
		//thmp.lhs_rhs(EXAMPLE_TEST);
		//System.out.println(Utils.expandAll(EXAMPLE_TEST));
		//thmp.rhstolhs(Utils.expandAll(EXAMPLE_TEST));
		thmp.runParser(EXAMPLE_TEST);
		/*
		Utils.printThmParser(thmp);
		Utils.println("F Found: "+thmp.checkF());
		thmp.modusponens();
		Utils.printThmParser(thmp);
		Utils.println("F Found: "+thmp.checkF());
		thmp.axiom1(thmp.charsinhypo, thmp.charsinhypo);
		thmp.modusponens();
		Utils.println("F Found: "+thmp.checkF());
		//thmp.proofPath("F");
		 * 
		 */
		long stopTime = System.currentTimeMillis();
	    long elapsedTime = stopTime - startTime;
	    System.out.println(elapsedTime+"ms");
	}
}
