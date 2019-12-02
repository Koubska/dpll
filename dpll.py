import sys
from copy import copy as cp


class dpll : 

	def __init__(self):
		self.trail = list() # Global Stack of assignments
		self.numVars = 0 # Global amount of Variables
		self.numClauses = 0 # Global amount of Clauses
		self.heuristic = dict() #{name :  (total, diff)}

	def solve(self, file) :
		self.trail.clear()
		clauses = self.parse_dimacs(file)
		self.dpll(clauses)

	def parse_dimacs(self, file):
		clauses = []
		with open(file, 'r') as input_file:
			for line in input_file:
				if line[0] == 'c':
					continue
				if line[0] == 'p' : #get numVars and numClauses 
					temp = line.split(" ")
					tempint = [int(x) for x in temp[2:]]
					#self.numVars = tempint[0]
					self.numClauses = tempint[1]
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
				clauses.append(literals)
			self.numVars = len(self.heuristic)
			#sort dict by amount of variable occurence and make it a list for better iteration 
			self.heuristic = [(k, self.heuristic[k]) for k in sorted(self.heuristic, key=self.heuristic.get, reverse=True)]
		return clauses


#bool DPLL(CNF_Formula φ)
#trail.clear(); //trail is a global stack of assignments
#if (!BCP()) then return UNSAT
#	while (true) 
#		if (!decide()) then return SAT;
#		while (!BCP())
#			if (!backtrack()) then return UNSAT;
#}
	def dpll(self, clauses) : 
		if not self.BCP(clauses) : 
			print("unsat")
			sys.exit(20)
		while True : 
			if not self.decide(clauses) :
				print("sat")
				sys.exit(10)
			while not self.BCP(clauses) : 
				if not self.backtrack(clauses) : 
					print("unsat")
					sys.exit(20)

	#bool BCP() { //more advanced implementation: return false as soon as an unsatisfied clause is detected
	#	while (there is a unit clause implying that a variable x must be set to a value v )
	#		trail.push(x , v , true);
	#	if (there is an unsatisfied clause) then return false;
	#	return true;
	#}

	def BCP(self, clauses) :
		for clause in clauses : # check for unit and unsatisfiable clauses : 
			satisfiable = False 
			copy = cp(clause)
			for (name, value, fixed) in reversed(self.trail) : #Iterate over given assignments
				if not fixed : 
					pass #not fixed variables not usefull for Propagation
				if value == 0 : #current variable is assigned to false 
					if (-1 * name) in clause : 
						satisfiable = True 
						copy.remove(-1 * name)
						pass
					elif name in clause : 
						copy.remove(name) 
				elif value == 1 : #current variable is assigned to true 
					if (-1 * name) in clause :
						#print("Copy : " + str(copy) + "  Name : " + str(-1 * name))
						copy.remove(-1 * name)	
					if name in clause : 
						satisfiable = True 
						copy.remove(name)
						pass
			if len(copy) == 0 and satisfiable == False :
				return False
			elif len(copy) == 1 and satisfiable == False : #Found unit Clause
				if copy[0] < 0 : 
					self.trail.append((abs(copy[0]), 0, True)) 
					#self.heuristic.pop(abs(copy[0]), None)
				else : 
					self.trail.append((abs(copy[0]), 1, True)) 
					#self.heuristic.pop(abs(copy[0]), None)
				
		return True


	#bool decide() {
	#if (all variables are assigned)
	#	return false;
	#choose unassigned variable x ;
	#choose value v ∈ {0, 1};
	#trail.push(x , v , false);
	#return true

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

	def decide(self, clauses) : 
		if len(self.trail) == self.numVars : 
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
	def backtrack(self, clauses) :
		while True : 
			if len(self.trail) == 0 : 
				return False 
			else : 
				(x,v,b) = self.trail.pop() #backtrack until the last unfixed variable 
				if b == False : 
					self.trail.append((x,int(1-v),True))
					return True


def main() : 
	solver = dpll()
	solver.solve(sys.argv[1])
main()