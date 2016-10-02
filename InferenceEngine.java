
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Stack;

public class InferenceEngine {
	
	private Map<String , List<Facts>> facts = new HashMap<String, List<Facts>>();
	
	private Map<String , List<Rules>> rules = new HashMap<String, List<Rules>>();
 
	public static void main(String[] args) throws NumberFormatException, IOException {
		BufferedWriter bw = null;
		try {
			File outputFile = new File("output.txt");
			if(!outputFile.exists()){
				outputFile.createNewFile();
			}
			
			FileWriter frw = new FileWriter(outputFile);
			bw = new BufferedWriter(frw);
			
			String inputFile = args[0];
			InferenceEngine  i1 = new InferenceEngine ();
			File file = new File(inputFile);
			FileReader fr = new FileReader(file);
			BufferedReader br = new BufferedReader(fr);
			int queries = Integer.parseInt(br.readLine());
			List<String> queriesList = new ArrayList<String>();
			
			for(int i=0;i<queries;i++){
				queriesList.add(br.readLine());
			}
			
			i1.MakeKB(br);
			
			for(String str : queriesList){
				boolean value = false;
				try{
					value = i1.MakeInference(str);
				} catch (Exception e) {
					value = false;
				}
				if(value == false) {
					bw.write("FALSE");
				} else {
					bw.write("TRUE");
				}
				bw.newLine();
				//System.out.println(str+" "+value);
			}
		} catch (Exception e) {
			System.out.println("Some error!!!" + e.getMessage());
		} finally {
			bw.close();
		}
	}

	private boolean MakeInference(String query) throws Exception {
		boolean isNegative = false;
		String literal = query.substring(0, query.indexOf("("));
		
		String[] constants = query.substring(query.indexOf("(")+1,query.indexOf(")")).split(",");
		
		boolean value = false;
		Predicate predicate = new Predicate();
		Stack<Predicate> stack = new Stack<Predicate>();
		predicate.setLiteral(literal);
		predicate.setArguments(constants);
		predicate.setValue(!isNegative);
		stack.push(predicate);
		
		int status = checkKnowLedgeBase(stack, null, 2, null);
		if(status == 0){
			value  = true;
		} 
		
		Facts f1 = new Facts();
		f1.setLiteral(literal);
		f1.setConstants(constants);
		if(isNegative) { 
			f1.setValue(!value);
		} else {
			f1.setValue(value);
		}
		
		if(status == 0) {
			if(facts.containsKey(literal)){
				facts.get(literal).add(f1);
			} else{
				List<Facts> list= new ArrayList<Facts>();
				list.add(f1);
				facts.put(literal, list);
			}
		}
		return value;
	}

	private int checkKnowLedgeBase(Stack<Predicate> stack, Map<String,List<String[]>> literallsUsed, int resultFinal, Map<Predicate, Map<String,List<String[]>>> literallsStackRelation) throws Exception {
		
		int finalResult = 2;
		try{
			if(stack.empty()){
				return finalResult;
			}
			Predicate predicate = stack.pop();
			/*System.out.print(predicate.getLiteral()+"          ");
			for(int i=0;i<predicate.getArguments().length;i++)
			{
				System.out.print(predicate.getArguments()[i]+" , ");
			}
			System.out.print("              ");
			if(literallsUsed!=null){
				for(Entry<String,List<String[]>> entry : literallsUsed.entrySet()) 	{
					System.out.print("key:-"+entry.getKey()+" Value:- ");
					for(String[] list : entry.getValue()){
						for(String str : list){
							System.out.print(str+" , ");
						}
						System.out.print(" Value:- ");
					}
				}
				System.out.print("            ");
			} else {
				System.out.print("          no");
			}
			System.out.println();
			*/if(facts.containsKey(predicate.getLiteral())){
				int status = CheckFacts(predicate.getLiteral(), predicate.getArguments());
				if(status == 0 && predicate.isValue()){
					return 0;
				} else if(status == 1 && !predicate.isValue()){
					return 0;
				}
				if(stack.isEmpty()) {
					if(status == 0 && !predicate.isValue()){
						return 1;
					} else if(status == 1 && predicate.isValue()){
						return 1;
					}
				}
				List<Facts> factList = getMatchingFactList(predicate.getLiteral(), predicate.getArguments());
				if(factList != null) {
					for(Facts fact : factList){
						if(predicate.isValue() && fact.isValue() || !predicate.isValue() && !fact.isValue()){
							Map<String , String> ConstantsToverify = unificationMapBackword(predicate.getArguments(), fact.getConstants());
							Stack<Predicate> stack1 = makeCloneOfStack(stack, literallsStackRelation);
							stack1 = doUnificationOfStack(stack1, ConstantsToverify);
							if(stack1.isEmpty()){
								return 0;
							}
							while(!stack1.empty()) {
								int result = checkKnowLedgeBase(stack1, literallsStackRelation.get(stack1.peek()), resultFinal, literallsStackRelation);
								if(stack1.empty() && result == 0) {
									finalResult = result;
									stack.clear();
									return finalResult;
								} else if(result == 0) {
									continue;
								} else if (result == 2){
									break;
								}
							}
						}
					}
				}
			}
			
			List<Rules> listRules = rules.get(predicate.getLiteral());
			if(listRules == null){
				return 2;
			}
			
			if(literallsUsed==null){
				literallsUsed = new HashMap<String,List<String[]>>();
			}
			if(checkConstants(predicate.getArguments())){
				if(literallsUsed.containsKey(predicate.getLiteral())){
					List<String[]> listOfConstants = literallsUsed.get(predicate.getLiteral());
					if(doesPredicateAllreadyUsed(predicate, listOfConstants)){
						return 2;
					} else {
						String[] litUsed = predicate.getArguments().clone();
						listOfConstants.add(litUsed);
					}
					
				} else {
					List<String[]> listOfConstants = new ArrayList<>();
					String[] litUsed = predicate.getArguments().clone();
					listOfConstants.add(litUsed);
					literallsUsed.put(predicate.getLiteral(), listOfConstants);
				}
			}
			
			
			
			for(Rules rule : listRules){
				if(resultFinal!=2){
					break;
				}
				Map<String , String> ConstantsToverify = unificationMap(predicate.getArguments(), rule.getRightArguments());
				if(ConstantsToverify == null){
					continue;
				} else {
					Stack<Predicate> stack1 = makeCloneOfStack(stack, literallsStackRelation);
					List<Predicate> predicateList = rule.getPredicatesList();
					for(int i=predicateList.size()-1;i>=0;i--) {
						Predicate leftPredicate = doUnificationWithClone(predicateList.get(i), ConstantsToverify);
						Map<String,List<String[]>> litUsed = getLiteralsUsedCopy(literallsUsed);
						if(literallsStackRelation==null) {
							literallsStackRelation = new HashMap<>();
							literallsStackRelation.put(leftPredicate, litUsed);
						} else {
							literallsStackRelation.put(leftPredicate, litUsed);
						}
						stack1.push(leftPredicate);
					}
					stack1 = doUnificationOfStack(stack1, ConstantsToverify);
					while(!stack1.empty()) {
						int result = checkKnowLedgeBase(stack1, literallsStackRelation.get(stack1.peek()), resultFinal, literallsStackRelation);
						if(result == 2 || result == 1) {
							break;
						} else if(stack1.empty() && result == 0 && rule.isValue() && predicate.isValue()){
							finalResult = result;
							stack.clear();
							return finalResult;
						} else if(stack1.empty() && result == 0 && !rule.isValue() && !predicate.isValue()){
							finalResult = result;
							stack.clear();
							return finalResult;
						}else if(stack1.empty() && result == 0){
							stack.clear();
							break;
						}
					}
					
				}
			}
			literallsUsed.remove(predicate.getLiteral());
		}  catch (StackOverflowError r) {
			return 2;
		} catch (Exception r) {
			return 2;
		}
		return finalResult;
	}

	private Map<String, List<String[]>> getLiteralsUsedCopy(Map<String, List<String[]>> literallsUsed) {
		Map<String, List<String[]>> copy = new HashMap<>();
		for(Entry<String, List<String[]>> entry : literallsUsed.entrySet()) {
			List<String[]> copyList = new ArrayList<>();
			for(String[] listInside : entry.getValue()){
				copyList.add(listInside.clone());
			}
			copy.put(entry.getKey(), copyList);
		}
		return copy;
	}

	private boolean doesPredicateAllreadyUsed(Predicate predicate, List<String[]> listOfConstants) {
		String[] argumentslist = predicate.getArguments();
		for(String[] list : listOfConstants){
			boolean flag = false;
			for(int i=0;i<list.length;i++){
				if(!list[i].equals(argumentslist[i])) {
					flag = true;
					break;
				}
			}
			if(!flag){
				return true;
			}
		}
		return false;
	}

	private boolean checkConstants(String[] arguments) {
		for(int i=0;i<arguments.length;i++){
			if(CheckvariableFromString(arguments[i])){
				return false;
			}
		}
		return true;
	}

	@SuppressWarnings("unchecked")
	private Stack<Predicate> makeCloneOfStack(Stack<Predicate> stack, Map<Predicate, Map<String,List<String[]>>> literallsStackRelation) throws CloneNotSupportedException {
		Stack<Predicate> tempStack1 = new Stack<>();
		Stack<Predicate> tempStack = new Stack<>();
		Stack<Predicate> stack1 = (Stack<Predicate>) stack.clone();
		while(!stack1.empty()) {
			Map<String,List<String[]>> argUsedList = literallsStackRelation.get(stack1.peek());
			literallsStackRelation.remove(stack1.peek());
			Predicate predicate = (Predicate) stack1.pop().clone();
			tempStack1.push(predicate);
			literallsStackRelation.put(predicate, argUsedList);
		}
		while(!tempStack1.empty()) {
			tempStack.push(tempStack1.pop());
		}
		return tempStack;
	}

	private Predicate doUnificationWithClone(Predicate predicate, Map<String, String> constantsToverify) throws CloneNotSupportedException {
		Predicate leftPredicate = (Predicate) predicate.clone();
		String[] argumentList = leftPredicate.getArguments();
		for(int i =0;i<argumentList.length;i++){
			if(constantsToverify.containsKey(argumentList[i])){
					argumentList[i] = constantsToverify.get(argumentList[i]);
			}
		}
		return leftPredicate;
	}

	private Map<String, String> unificationMapBackword(String[] arguments, String[] rightArguments) {
		Map<String , String> ConstantsToverify = new HashMap<String, String>();
		for(int i=0;i<arguments.length;i++){
			if(CheckvariableFromString(arguments[i]) || CheckvariableFromString(rightArguments[i])){
				ConstantsToverify.put(arguments[i], rightArguments[i]);
			} else if(arguments[i].equals(rightArguments[i])){
				ConstantsToverify.put(arguments[i], rightArguments[i]);
			} else {
				return null;
			}
		}
		return ConstantsToverify;
	}

	private Stack<Predicate> doUnificationOfStack(Stack<Predicate> stack1, Map<String, String> constantsToverify) throws CloneNotSupportedException {
		Stack<Predicate> tempStack = new Stack<>();
		while(!stack1.empty()) {
			Predicate predicate = doUnification(stack1.pop(), constantsToverify);
			tempStack.push(predicate);
		}
		while(!tempStack.empty()) {
			stack1.push(tempStack.pop());
		}
		return stack1;
	}

	private List<Facts> getMatchingFactList(String literal, String[] arguments) {
		List<Facts> listofFacts = facts.get(literal);
		List<Facts> listofFactsToBeSend = new ArrayList<Facts>();
		if(listofFacts==null || listofFacts.isEmpty()){
			return null;
		} else {
			for(Facts fact : listofFacts){
				String[] factArguments = fact.getConstants();
				Map<String, String> similarityChkMap = new HashMap<String, String>();
				boolean flag = true;
				for(int i=0; i<factArguments.length; i++){
					if(!CheckvariableFromString(arguments[i]) && !arguments[i].equals(factArguments[i])){
						flag = false;
						break;
					} else if (CheckvariableFromString(arguments[i])) {
						if(similarityChkMap.containsKey(arguments[i])){
							if(!factArguments[i].equals(similarityChkMap.get(arguments[i]))){
								flag = false;
								break;
							}
						} else {
							similarityChkMap.put(arguments[i] , factArguments[i]);
						}
					}
				}
				if(flag) {
					listofFactsToBeSend.add(fact);
				}
			}
		}
		return listofFactsToBeSend;
	}

	private Predicate doUnification(Predicate leftPredicate, Map<String, String> constantsToverify) throws CloneNotSupportedException {
		String[] argumentList = leftPredicate.getArguments();
		for(int i =0;i<argumentList.length;i++){
			if(constantsToverify.containsKey(argumentList[i])){
				argumentList[i] = constantsToverify.get(argumentList[i]);
			}
		}
		return leftPredicate;
	}

	private Map<String, String> unificationMap(String[] arguments, String[] rightArguments) {
		Map<String , String> ConstantsToverify = new HashMap<String, String>();
		for(int i=0;i<arguments.length;i++){
			if(CheckvariableFromString(arguments[i]) || CheckvariableFromString(rightArguments[i])){
				if(CheckvariableFromString(arguments[i]) && !CheckvariableFromString(rightArguments[i])){
					if(ConstantsToverify.containsKey(arguments[i])) {
						if(!ConstantsToverify.get(arguments[i]).equals(rightArguments[i])) {
							return null;
						}
					} else {
						ConstantsToverify.put(arguments[i], rightArguments[i]);
					}
				} else if (!CheckvariableFromString(arguments[i]) && CheckvariableFromString(rightArguments[i])) {
					if(ConstantsToverify.containsKey(rightArguments[i])) {
						if(!ConstantsToverify.get(rightArguments[i]).equals(arguments[i])) {
							return null;
						}
					} else {
						ConstantsToverify.put(rightArguments[i], arguments[i]);
					}
				} else if (CheckvariableFromString(arguments[i]) && CheckvariableFromString(rightArguments[i])){
					if(ConstantsToverify.containsKey(arguments[i]) && !ConstantsToverify.containsKey(rightArguments[i])) {
						ConstantsToverify.put(rightArguments[i], ConstantsToverify.get(arguments[i]));
					} else if(ConstantsToverify.containsKey(arguments[i]) && ConstantsToverify.containsKey(rightArguments[i])) {
						if(!ConstantsToverify.get(arguments[i]).equals(ConstantsToverify.get(rightArguments[i]))){
							return null;
						}
					} else if(ConstantsToverify.containsKey(rightArguments[i]) && !ConstantsToverify.containsKey(arguments[i])) {
						ConstantsToverify.put(arguments[i], ConstantsToverify.get(rightArguments[i]));
					} else {
						ConstantsToverify.put(rightArguments[i], arguments[i]);
					}
				}
			} else if(arguments[i].equals(rightArguments[i])){
				
			} else {
				return null;
			}
		}
		return ConstantsToverify;
	}

		
	private boolean CheckvariableFromString(String argument) {
		if(argument.length()==1 && argument.equals(argument.toLowerCase())){
			return true;
		} else if(argument.startsWith("#") && argument.endsWith("#")){
			return true;
		}
		return false;
	}

	private int CheckFacts(String literal, String[] listConstants) {
		
		List<Facts> listFacts= facts.get(literal);
		for(Facts fact : listFacts){
			if(chechConstants(fact.getConstants() , listConstants)){
				if(fact.isValue()){
					return 0;
				} else{
					return 1;
				}
			}
		}
		
		return 2;
	}

	private boolean chechConstants(String[] constants, String[] listConstants) {
		for(int i=0;i<constants.length;i++){
			if(!constants[i].equals(listConstants[i])){
				return false;
			}
		}
		return true;
	}

	private void MakeKB(BufferedReader br) throws NumberFormatException, IOException {
		int clauses = Integer.parseInt(br.readLine());
		int counter = 1;
		for(int i=0;i<clauses;i++){
			String clause = br.readLine();
			if(clause.contains("=>")){
				Rules r1 = new Rules();
				String[] array = clause.split("=>");
				String str = array[array.length-1];
				str = str.trim();
				String literal = str.substring(0, str.indexOf("("));
				r1.setValue(true);
				r1.setRightLiteral(literal);
				List<Predicate> predicatesList = getPredicates(array[0].trim() , counter);
				r1.setPredicatesList(predicatesList);
				String[] rightArgumentList = getArgumentList(str, counter);
				r1.setRightArguments(rightArgumentList);
				if(rules.containsKey(literal)){
					rules.get(literal).add(r1);
				} else{
					List<Rules> list= new ArrayList<Rules>();
					list.add(r1);
					rules.put(literal, list);
				}
				counter++;
			} else {
				String literal = "";
				boolean value = false;
				Facts f1 = new Facts();
				clause = clause.trim();
				literal = clause.substring(0, clause.indexOf("("));
				value= true;
				String[] constants = clause.substring(clause.indexOf("(")+1,clause.indexOf(")")).split(",");
				for(int j=0;j<constants.length;j++){
					constants[j] = constants[j].trim();
				}
				f1.setConstants(constants);
				f1.setLiteral(literal);
				f1.setValue(value);
				if(facts.containsKey(literal)){
					facts.get(literal).add(f1);
				} else{
					List<Facts> list= new ArrayList<Facts>();
					list.add(f1);
					facts.put(literal, list );
				}
			}
		}
	}
	
	private String[] getArgumentList(String str, int counter) {
		String[] strArray = str.substring(str.indexOf("(")+1,str.indexOf(")")).split(",");
		String[] arguments = new String[strArray.length];
		int count = 0;
		for(String st : strArray){
			if(CheckvariableFromString(st.trim())){
				arguments[count]="#"+st+counter+"#";
			} else {
				arguments[count]=st.trim();
			}
			count++;
		}
		return arguments;
	}

	private List<Predicate> getPredicates(String string, int counter) {
		List<Predicate> predicatesList = new ArrayList<Predicate>();
		String[] predicatesArray = string.split("\\^");
		for(String str : predicatesArray){
			str = str.trim();
			Predicate p1 = new Predicate();
			boolean value = false;
			String literal = str.substring(0, str.indexOf("("));
			value= true;
			p1.setLiteral(literal);
			p1.setValue(value);
			String[] predicateArgumentList = getArgumentList(str, counter);
			p1.setArguments(predicateArgumentList);
			predicatesList.add(p1);
		}
		return predicatesList;
	}

	private class Facts{
		private String literal;
		private boolean value;
		private String[] constants;
		public String getLiteral() {
			return literal;
		}
		public void setLiteral(String literal) {
			this.literal = literal;
		}
		public boolean isValue() {
			return value;
		}
		public void setValue(boolean value) {
			this.value = value;
		}
		public String[] getConstants() {
			return constants;
		}
		public void setConstants(String[] constants) {
			this.constants = constants;
		}
	}
	
	
	private class Rules{
		private String rightLiteral;
		private boolean value;
		private String[] rightArguments;
		private List<Predicate> predicatesList;
		public String getRightLiteral() {
			return rightLiteral;
		}
		public void setRightLiteral(String rightLiteral) {
			this.rightLiteral = rightLiteral;
		}
		public boolean isValue() {
			return value;
		}
		public void setValue(boolean value) {
			this.value = value;
		}
		public String[] getRightArguments() {
			return rightArguments;
		}
		public void setRightArguments(String[] rightArguments) {
			this.rightArguments = rightArguments;
		}
		public List<Predicate> getPredicatesList() {
			return predicatesList;
		}
		public void setPredicatesList(List<Predicate> predicatesList) {
			this.predicatesList = predicatesList;
		}
	}
	
	private class Predicate implements Cloneable{
		private String literal;
		private boolean value;
		private String[] arguments;
		public String getLiteral() {
			return literal;
		}
		public void setLiteral(String literal) {
			this.literal = literal;
		}
		public boolean isValue() {
			return value;
		}
		public void setValue(boolean value) {
			this.value = value;
		}
		public String[] getArguments() {
			return arguments;
		}
		public void setArguments(String[] arguments) {
			this.arguments = arguments;
		}
		
		protected Object clone() throws CloneNotSupportedException {
			Predicate clone=(Predicate)super.clone();
			clone.setArguments(clone.getArguments().clone());
		    return clone;
		 }
	}
}


