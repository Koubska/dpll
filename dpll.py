import sys
from copy import copy as cp


class dpll : 

	def __init__(self):
		self.trail = list() # Global Stack of assignments
		self.numVars = 0 # Global amount of Variables
		self.numClauses = 0 #Global amount of Clauses
		self.clausesToCheck = [] #(clauseNumber, LiteralWhy) used for BCP
		self.heuristic = dict() 
		self.clauses = dict()
		self.watchlist = dict()
		self.clauseWatching = dict()

	def solve(self, file) :
		self.trail.clear()
		self.parse_dimacs(file)
		self.dpll()

	def parse_dimacs(self, file):
		curClauseNumber = 0
		with open(file, 'r') as input_file:
			for line in input_file:
				if line[0] == 'c':
					continue
				if line[0] == 'p' :
					continue
				literals = list(map(int, line.split()))
				assert literals[-1] == 0
				literals = literals[:-1]
				for lit in literals : 
					var_name = abs(lit)
					(total, diff) = self.heuristic.get(var_name, (0,0))
					if lit > 0 : #positive lit
						self.heuristic.update({var_name : (total+1, diff+1)})
					else : #negative lit
						self.heuristic.update({var_name : (total+1, diff-1)})
				curClauseNumber += 1 	
				self.clauses[curClauseNumber] = literals
			self.numVars = len(self.heuristic)
			self.numClauses = curClauseNumber+1
			#sort dict by amount of variable occurence and make it a list for better iteration 
			self.heuristic = [(k, self.heuristic[k]) for k in sorted(self.heuristic, key=self.heuristic.get, reverse=True)]


#bool DPLL(CNF_Formula φ)
#trail.clear(); //trail is a global stack of assignments
#if (!BCP()) then return UNSAT
#	while (true) 
#		if (!decide()) then return SAT;
#		while (!BCP())
#			if (!backtrack()) then return UNSAT;
#}

	def dpll(self) : 
		self.trail.clear()
		self.initWatchlist()
		if not self.BCP() : 
			sys.exit(20)
		while True : 
			if not self.decide() :
				sys.exit(10)
			while not self.BCP() : 
				if not self.backtrack() : 
					sys.exit(20)

	def initWatchlist(self) : 
		#Init dict for +- vars
		for i in range(1,self.numVars) : 
			self.watchlist[i] = []
			self.watchlist[-i] = []

		for i in range(1, self.numClauses) :
			clause = self.clauses[i]
			if len(clause) == 1 : 
				pass
			else : 
				temp0 = self.watchlist.pop(clause[0], [])
				temp0.append(i)
				temp1 = self.watchlist.pop(clause[1], [])
				temp1.append(i)
				self.watchlist[clause[0]] = temp0
				self.watchlist[clause[1]] = temp1
				self.clauseWatching[i] = [clause[0], clause[1]]
				
				


	#bool BCP() { //more advanced implementation: return false as soon as an unsatisfied clause is detected
	#	while (there is a unit clause implying that a variable x must be set to a value v )
	#		trail.push(x , v , true);
	#	if (there is an unsatisfied clause) then return false;
	#	return true;
	#}

	def BCP(self) : 
		#start = time()
		if len(self.trail) == 0 : 
			#check for direct unit clauses (clauses of length 1)
			for clause in self.clauses.values() : 
				if len(clause) == 1 : 
					#print("Found Unit" + str(clause)) 
					lit = clause[0]
					if lit > 0 : #positve lit -> assign true 1
						self.trail.append((abs(lit), 1, True))
					else : #negative lit -> assign false 0
						self.trail.append((abs(lit), 0 , True))
					self.clausesToCheck += (self.watchlist[-1*lit], lit)	 
		else : 
			#we only need to check the last made assignment
			(name, val, fixed) = self.trail[-1]
			if val == 1 : #postitive assignment, check clauses with negative occurence
				self.clausesToCheck += [(cur, -name) for cur in self.watchlist[-name]]
			else : #negative assignment, check clauses with positive occurence
				self.clausesToCheck += [(cur, name) for cur in self.watchlist[name]]

		while len(self.clausesToCheck) > 0  : 
			Case1 = False 
			Case2 = False 
			(clauseNumber, literalWhy) = self.clausesToCheck.pop()
			clause = self.clauses[clauseNumber]
			#print("Checking LiteralWhy: " + str(literalWhy) + "   Clause : " + str(clause)+ "  ClauseNumber : " + str(clauseNumber) + " isWatching : " + str(self.clauseWatching[clauseNumber]))
			otherWatchedLiteralList = cp(self.clauseWatching[clauseNumber])
			otherWatchedLiteralList.remove(literalWhy)
			otherWatchedLiteral = otherWatchedLiteralList[0]
			#if other watched literal is True, do nothing as no conflict CASE 1
			for (name, value, fixed) in self.trail : 
				if name == abs(otherWatchedLiteral) : #other watched literal is assigned
					if (otherWatchedLiteral < 0 and value == 0) or (otherWatchedLiteral > 0 and value == 1) : 
						#No Conflict do nothing as current Clause is satisfied
						Case1 = True
						break

			if not Case1 :  #CASE 2 
				#If other unwatched Literal is not false, change the watched literal 
				for lit in clause :
					found = False
					if abs(lit) == abs(otherWatchedLiteral) or abs(lit) == abs(literalWhy) : #current lit is beeing watched
						continue 
					elif Case2 : 
						break

					for (name, value, fixed) in self.trail : 
						if name == abs(lit) : #found assigned lit in clause
							found = True
							if (value == 1 and lit > 0) or (value == 0 and lit < 0) : #clause is satisfied
								#found true unwatched literal -> update the watchlist
								Case2 = True
								self.removeFromWatchlist(literalWhy, clauseNumber)
								self.removeClauseWatching(literalWhy, clauseNumber)
								self.appendToWatchlist(lit, clauseNumber)
								self.appendClauseWatching(lit, clauseNumber)
							break
	
					if not found : 
						#current lit is not assigned -> make it the new watched literal 
						Case2 =  True 
						found = True
						self.removeFromWatchlist(literalWhy, clauseNumber)
						self.removeClauseWatching(literalWhy, clauseNumber)
						self.appendToWatchlist(lit, clauseNumber)
						self.appendClauseWatching(lit, clauseNumber)
						#print("Current lit : " + str(lit) + " is not assigned")
						#print("Clause is now watching : " + str(self.clauseWatching[clauseNumber]))
						break
						
			if not (Case1 or Case2) : 
				#Look at other watched Literal
				for (name, value, fixed) in self.trail :	
					if name == abs(otherWatchedLiteral) : 
						#Is set Found Confict
						#print("Conflict because of " +str(otherWatchedLiteral))
						self.clausesToCheck = []
						return False 
				#Not set so Propagate	
				if otherWatchedLiteral > 0: 
					#Positive occurence in clause 
					self.trail.append((otherWatchedLiteral, 1, True))
					self.clausesToCheck += [(cur, -otherWatchedLiteral) for cur in self.watchlist[-otherWatchedLiteral]]
				else : 
					self.trail.append((abs(otherWatchedLiteral), 0, True))
					self.clausesToCheck += [(cur, abs(otherWatchedLiteral)) for cur in self.watchlist[abs(otherWatchedLiteral)]]
		return True


	def appendToWatchlist(self, literal, clauseNumber) : 
		temp = self.watchlist[literal]
		temp.append(clauseNumber)
		self.watchlist[literal] = temp
	
	def removeFromWatchlist(self, literal, clauseNumber) :
		temp = self.watchlist[literal]
		temp.remove(clauseNumber)
		self.watchlist[literal] = temp

	def appendClauseWatching(self, literal, clauseNumber) :
		temp = self.clauseWatching[clauseNumber] 
		temp.append(literal)
		self.clauseWatching[clauseNumber] = temp

	def removeClauseWatching(self, literal, clauseNumber) :
		temp = self.clauseWatching[clauseNumber] 
		temp.remove(literal)
		self.clauseWatching[clauseNumber] = temp


	#bool decide() {
	#if (all variables are assigned)
	#	return false;
	#choose unassigned variable x ;
	#choose value v ∈ {0, 1};
	#trail.push(x , v , false);
	#return true

# ------- DECIDE WITHOUT HEURISTICS ----------
#	def decide(self, clauses) : 
#		#check if all variables are assigned
#		unknownVars = cp(list(self.setVars))
#		for assignment in self.trail : 
#			(x,v, f) = assignment 
#			if x in unknownVars : 
#				unknownVars.remove(x)
#			if len(unknownVars) == 0 : #there are no unassigned Variables 
#				return False
#		self.trail.append((unknownVars[0], 0, False))
#		return True

	def decide(self) : 
		if len(self.trail) == self.numVars : #nothing to decide
			return False
		else : #choose unused variable with most occurences
			#iterate over heuristic list 
			trail_names = [t[0] for t in self.trail]
			for (name, (_, diff)) in self.heuristic : 
				if name in trail_names: 
					pass
				else : 
					if diff > 0 :  #more positive occurences
						self.trail.append((name, 1, False))
					else : #more negative occurences
						self.trail.append((name, 0, False))
		
					#print("Decided : " + str(self.trail[-1]))
					return True
		return False #Shouldnt get here


	#bool backtrack() 
	#while (true)
	#	if (trail.empty())
	# 		return false
	#	else	
	# 		(x,v,b)=trail.pop()
	#		if (!b) 
	#			trail.push(x , ¬v , true)
	#			return true
	def backtrack(self) :
		while True : 
			if len(self.trail) == 0 : #Nothing to undo
				return False 
			else : 
				(x,v,b) = self.trail.pop() #backtrack until the last unfixed variable 
				if b == False : 
					self.trail.append((x,int(1-v),True)) #reverse the last decision
					return True


def main() : 
	solver = dpll()
	solver.solve(sys.argv[1])
main()