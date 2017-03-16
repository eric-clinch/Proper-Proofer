import copy, time

from tkinter import *

#taken from http://www.cs.cmu.edu/~112/notes/notes-graphics.html
def rgbString(red, green, blue):
    return "#%02x%02x%02x" % (red, green, blue)

class Struct(object): pass

class Proof(object):
	def __init__(self, statement, reasons, assumptionCancellation = None):
		self.statement = statement
		#reasons will either be a Proof object, a list of Proof objects, or
		#a string. If the reason is a single Proof object, we will want to make
		#it into a list of the single proof. Otherwise, leave it alone
		self.reasons = [reasons] if(isinstance(reasons,Proof)) else reasons
		self.assumptionCancellation = assumptionCancellation

	def __repr__(self):
		return self.statement

	def draw(self, canvas, x, y):
		drawProof(canvas, proof, x, y)

	def __eq__(self, other):
		if(not isinstance(other, Proof)): return False
		return (replaceConnectives(self.statement) == replaceConnectives(other.statement)
			 and self.reasons == other.reasons)

	def __hash__(self):
		return hash((replaceConnectives(self.statement), tuple(self.reasons), self.assumptionCancellation))

def replaceConnectives(s):
	s = s.replace("\u2227", "&")
	s = s.replace("\u2228", "|")
	s = s.replace("\u2192", ">")
	s = s.replace("\u00AC", "~")
	s = s.replace("\u22A5", "!")
	return s

def replaceTermsWithConnectives(s):
	s = s.replace("\\and", "\u2227")
	s = s.replace("\or", "\u2228")
	s = s.replace("\\to", "\u2192")
	s = s.replace("\implies", "\u2192")
	s = s.replace("\\not", "\u00AC")
	s = s.replace("\\false", "\u22A5")
	s = s.replace("\contradiction", "\u22A5")
	return s


###############################################################################
####	THE PROOFING SYSTEM
###############################################################################

def matchingParenthesis(s, i):
	if(s[i] != "("): return None

	parenthesisDepth = 0
	iDepth = None
	for j in range(len(s)):
		if(j == i): iDepth = parenthesisDepth
		if(s[j] == "("): parenthesisDepth += 1
		elif(s[j] == ")"): parenthesisDepth -= 1

		if(iDepth != None and parenthesisDepth == iDepth): return j

	return None

#removes unnecessary parantheses around the given string
def removeParenthesis(s):
	if(s == ""): return s
	#check that the first character is a parethesis,
	#and that its matching parenthesis is at the end of the string
	if(s[0] == "(" and matchingParenthesis(s, 0) + 1 == len(s)):
		s = s[1:-1]
	return s

#returns the outermost connective of the given conjecture, along with the
#propositions that it connects
def outerConnective(sentence):
	if(len(sentence) == 0): return None
	#look for implication, from right to left
	parenthesesDepth = 0
	for i in range(len(sentence) - 1, -1, -1):
		if(parenthesesDepth == 0 and sentence[i] == ">"): 
			prop1 = removeParenthesis(sentence[:i])
			prop2 = removeParenthesis(sentence[i+1:])
			return (">", prop1, prop2)
		elif(sentence[i] == '('): parenthesesDepth += 1
		elif(sentence[i] == ')'): parenthesesDepth -= 1

	#look for conjunction or disjunction, from left to right
	parenthesesDepth = 0
	for i in range(len(sentence)):
		if(parenthesesDepth==0 and (sentence[i] == "|" or sentence[i] == "&")):
			prop1 = removeParenthesis(sentence[:i])
			prop2 = removeParenthesis(sentence[i+1:])
			return (sentence[i], prop1, prop2)
		elif(sentence[i] == '('): parenthesesDepth += 1
		elif(sentence[i] == ')'): parenthesesDepth -= 1

	#check for negation
	if(sentence[0] == "~"):
		return ("~", '', removeParenthesis(sentence[1:]))

	return None

#looks for a proof of the given implication
def implicationIntroduction(conjecture, antecedent, consequent, have):
	have.numberAssumptions += 1
	newHave = copy.deepcopy(have)
	newHave.assumed = newHave.assumed.union({antecedent})
	newHave.assumptionNums[antecedent] = newHave.numberAssumptions
	proof = prove(consequent, newHave)
	if(proof != None):
		return Proof(conjecture, proof, newHave.assumptionNums[antecedent])
	have.numberAssumptions -= 1
	return None

#given an implication, looks for a proof of the antecendent. If it finds a proof
#of the antecedent, it returns a proof of the consequent
def implicationElimination(implication, antecedent, consequent, have):
	#the implication should be a truth if we are using it
	proofOfImplication = proveFromTruths(implication, have)
	proofOfAntecedent = weakProve(antecedent, have)
	if(proofOfAntecedent != None):
		reasons = [proofOfImplication, proofOfAntecedent]
		return Proof(consequent, reasons)

#looks for a proof of the given conjunction
def andIntroduction(conjecture, prop1, prop2, have):
	#look for a proof of the first part of the conjunction
	proof1 = weakProve(prop1,have)
	if(proof1 == None): return None
	#look for a proof of the second part of the conjunction
	proof2 = weakProve(prop2,have)
	if(proof2 == None): return None
	#if you have a proof of both parts of the conjunction, return the proof of
	#the conjunction
	reasons = [proof1, proof2]
	return Proof(conjecture, reasons)

#given a conjunction that we know is true, return a proof of both parts of the
#conjunction
def andElimination(truth, prop1, prop2, have):
	proofOfTruth = proveFromTruths(truth,have)
	proof1 = Proof(prop1, proofOfTruth)
	proof2 = Proof(prop2, proofOfTruth)
	return (proof1, proof2)

def orIntroduction(conjecture, prop1, prop2, have):
	proof1 = weakProve(prop1, have) #look for a proof of prop1
	if(proof1 != None): return Proof(conjecture, proof1)
	proof2 = weakProve(prop2, have)
	if(proof2 != None): return Proof(conjecture, proof2)
	return None

#looks for a proof of the 
def orElimHelper(antecedent, consequent, have):
	newHave = copy.deepcopy(have)
	newHave.assumed = newHave.assumed.union({antecedent})
	newHave.assumptionNums[antecedent] = have.numberAssumptions
	proof = prove(consequent, newHave)
	if(proof != None): return proof
	return None

def orElimination(conjecture, truth, prop1, prop2,have):
	proofOfTruth = proveFromTruths(truth,have)
	have.numberAssumptions += 1
	proof1 = orElimHelper(prop1,conjecture,have)
	proof2 = orElimHelper(prop2,conjecture,have)
	if(proof1 == None or proof2 == None): 
		have.numberAssumptions -= 1
		return None
	reasons = [proofOfTruth, proof1, proof2]
	return Proof(conjecture, reasons, have.numberAssumptions)

def notIntroduction(conjecture, prop, have):
	have.numberAssumptions += 1
	newHave = copy.deepcopy(have)
	newHave.assumed = newHave.assumed.union({prop})
	newHave.assumptionNums[prop] = newHave.numberAssumptions
	proof = prove("!", newHave)
	if(proof != None):
		return Proof(conjecture, proof, newHave.assumptionNums[prop])
	have.numberAssumptions -= 1
	return None

#Looks for the outermost connective in the statement and looks for a proof
#of the statement
def connectionIntroduction(conjecture, have):
	breakDown = outerConnective(conjecture)
	if(breakDown == None): return None
	connective = breakDown[0]
	prop1 = breakDown[1]
	prop2 = breakDown[2]
	if(connective == ">"): 
		return implicationIntroduction(conjecture,prop1,prop2,have)
	elif(connective == "&"):
		return andIntroduction(conjecture,prop1,prop2,have)
	elif(connective == "|"):
		return orIntroduction(conjecture,prop1,prop2,have)
	elif(connective == "~"):
		return notIntroduction(conjecture,prop2,have)

def showMore(conjecture, truth, have):
	breakDown = outerConnective(truth)
	if(breakDown == None): return None
	connective = breakDown[0]
	prop1 = breakDown[1]
	prop2 = breakDown[2]
	proofs = None
	if(connective == ">"):
		proofs = (implicationElimination(truth,prop1,prop2,have),)
	elif(connective == "&"):
		proofs = andElimination(truth,prop1,prop2,have)
	elif(connective == "|"):
		proofs = (orElimination(conjecture, truth, prop1, prop2, have),)
	if(proofs == (None,) or proofs == None): return None
	provedStatements = set()
	statementProofs = dict()
	for proof in proofs:
		provedStatements.add(proof.statement)
		statementProofs[proof.statement] = proof
	return (provedStatements, statementProofs)

def proveByContradiction(conjecture, have):
	negation = "~(" + conjecture + ")"
	if (negation in have.assumed): return None
	have.numberAssumptions += 1
	newHave = copy.deepcopy(have)
	newHave.assumed = newHave.assumed.union({negation})
	newHave.assumptionNums[negation] = have.numberAssumptions
	proof = prove("!", newHave)
	if(proof == None):
		have.numberAssumptions -= 1
		return None
	return Proof(conjecture, proof, newHave.assumptionNums[negation])

def prove(conjecture, have):
	haveCopy = copy.deepcopy(have)
	proof = None
	queue = [have]
	while (proof == None and len(queue) > 0):
		currentHave = queue.pop(0)
		currentState = (conjecture,tuple(currentHave.given),
			tuple(currentHave.assumed),tuple(currentHave.shown))
		if (currentState in have.states): continue
		have.states.add(currentState)
		proof = weakProve(conjecture, currentHave)
		if(proof != None): return proof
		truths = currentHave.given.union(
					currentHave.assumed.union(currentHave.shown))
		for truth in truths:
			newHave = copy.deepcopy(currentHave)
			show = showMore(conjecture, truth, currentHave)
			if(show == None): continue
			#add what we have shown to the set of things we have shown
			newHave.shown = newHave.shown.union(show[0])
			#add the proofs of what we have shown to the dictionary of proofs
			newHave.shownProofs = {**newHave.shownProofs, **show[1]}
			queue += [newHave]
	if(proof == None and have.proofByContradiction and conjecture != "!"):
		have = haveCopy
		proof = proveByContradiction(conjecture, have)
	return proof

def proveContradiction(have):
	truths = have.given.union(have.assumed.union(have.shown))
	for truth in truths:
		if (truth[0] == "~"):
			negation = truth[1:]
			negation = removeParenthesis(negation)
			proofOfTruth = proveFromTruths(truth,have)
			proofOfNegation = prove(negation, have)
			if(proofOfNegation == None): continue
			reasons = [proofOfTruth, proofOfNegation]
			return Proof("!", reasons)
	return None

def lookForContradiction(have):
	truths = have.given.union(have.assumed.union(have.shown))
	for truth in truths:
		if (truth[0] == "~"):
			negation = truth[1:]
			negation = removeParenthesis(negation)
			if(negation in truths):
				proofOfTruth = proveFromTruths(truth, have)
				proofOfNegation = proveFromTruths(negation, have)
				reasons = [proofOfTruth, proofOfNegation]
				return Proof("!", reasons)

def proveFromTruths(conjecture, have):
	if (conjecture in have.given): return Proof(conjecture, "given")
	if (conjecture in have.assumed): 
		return Proof(conjecture, "assumed"+str(have.assumptionNums[conjecture]))
	if (conjecture in have.shown): return have.shownProofs[conjecture]
	print("ERROR")#if this function is ran, conjecture should already be proved

def weakProve(conjecture, have):
	if (conjecture == "!"): return proveContradiction(have)
	if (conjecture in have.given): return Proof(conjecture, "given")
	if (conjecture in have.assumed): 
		return Proof(conjecture, "assumed"+str(have.assumptionNums[conjecture]))
	if (conjecture in have.shown):
		return have.shownProofs[conjecture]
	proof = connectionIntroduction(conjecture, have)
	if(proof != None): return proof
	proof = lookForContradiction(have)
	if(proof != None): return Proof(conjecture, proof)
	return None

def setupProof(have,given = set()):
	have.proofByContradiction = False
	have.useProofByContradiction = False
	have.given = given
	have.assumed = set()
	have.assumptionNums = dict()
	have.numberAssumptions = 0
	have.shown = set()
	have.shownProofs = dict()
	have.states = set()

def constructiveProof(conjecture, given = set()):
	have = Struct() #will contain what we have assumed, shown, and been given
	setupProof(have,given)
	return prove(conjecture, have)

def classicalProof(conjecture, given = set()):
	have = Struct() #will contain what we have assumed, shown, and been given
	setupProof(have,given)
	have.proofByContradiction = True
	return prove(conjecture, have)

###############################################################################
####	DRAWING CODE
###############################################################################

def paranthesesFormat(s, previousConnective):
	OOO = {"~": 4, "&":1,"|":1,">":2, None:3} #order of operations
	breakDown = outerConnective(s)
	if(breakDown == None): return s
	connective = breakDown[0]
	prop1 = breakDown[1]
	prop2 = breakDown[2]
	if(connective == "~"):
		if(outerConnective(prop2) == None): return "~" + prop2
		else: return "~(" + paranthesesFormat(prop2, connective) + ")"
	if(OOO[connective] < OOO[previousConnective]): 
		return (paranthesesFormat(prop1, connective) + connective
				 + paranthesesFormat(prop2,connective))
	else: return "(" + (paranthesesFormat(prop1, connective) + connective
				 + paranthesesFormat(prop2,connective)) + ")"
	return s

def formatString(s):
	s = paranthesesFormat(s, None)
	
	s = s.replace("!", "\u22A5")
	s = s.replace(">", "\u2192")
	s = s.replace("&", "\u2227")
	s = s.replace("|", "\u2228")
	s = s.replace("~", "\u00AC")
	return s

def getProofWidth(data, proof):
	statementWidth = len(proof.statement)*data.pixelsPerLetter
	proofOfStatementWidth = 0
	branches = getBranches(proof)
	for branch in branches:
		proofOfStatementWidth += getProofWidth(data, branch)
	proofOfStatementWidth += data.ProofMargin*(len(branches)-1)
	return max(proofOfStatementWidth, statementWidth)

def getProofSteps(proof):
	steps = 1
	branches = getBranches(proof)
	for branch in branches:
		steps += getProofSteps(branch)
	return steps

def getProofDepth(proof):
	result = 1
	branches = getBranches(proof)
	for branch in branches:
		branchDepth = 1 + getProofDepth(branch)
		if(branchDepth > result): result = branchDepth
	return result

def getProofHeight(proof, data):
	return getProofDepth(proof)*data.ProofLineDifference

def getBranches(proof):
	branches = proof.reasons
	if(isinstance(branches,str)): return []
	return branches

def getBranchesDrawInfo(data, branches, center, y):
	branchesWidth = 0
	for branch in branches:
		branchesWidth += getProofWidth(data, branch)
	branchesWidth += data.ProofMargin*(len(branches) - 1)
	left = center - branchesWidth//2
	branchesDrawInfo = []
	for branch in branches:
		branchInfo = Struct()
		branchInfo.branch = branch
		branchWidth = getProofWidth(data,branch)
		branchInfo.x = left + branchWidth//2
		branchInfo.y = y - data.ProofLineDifference
		branchInfo.depth = getProofDepth(branch)
		branchesDrawInfo.append(branchInfo)
		left += branchWidth + data.ProofMargin
	return branchesDrawInfo

#returns which branch to draw first. Prioritizes depth
def getBranchToDraw(branchesDrawInfo):
	result = -1
	greatestDepth = -1
	for i in range(len(branchesDrawInfo)):
		if(branchesDrawInfo[i].depth > greatestDepth):
			greatestDepth = branchesDrawInfo[i].depth
			result = i
	return result

def drawDeductionLine(canvas,data,x,statementY,proof,branchesDrawInfo):
	y = statementY - data.ProofLineDifference//2
	widthOfStatement = len(formatString(proof.statement))*data.pixelsPerLetter
	statementLeft, statementRight = x-widthOfStatement//2, x+widthOfStatement//2

	if(len(branchesDrawInfo) == 0):
		if(proof.reasons.startswith("assumed")):
			assumptionNumber = int(proof.reasons.replace("assumed",""))
			otherAssumptionLines = data.assumptionLines.get(assumptionNumber, [])
			otherAssumptionLines.append([statementRight + data.ProofMargin//3, y])
			
			data.assumptionLines[assumptionNumber] = otherAssumptionLines
			canvas.create_line(statementLeft, y, statementRight, y)
	else: 
		leftBranchStatement = formatString(branchesDrawInfo[0].branch.statement)
		leftBranchStatementWidth = len(leftBranchStatement)*data.pixelsPerLetter
		branchLeft = branchesDrawInfo[0].x - leftBranchStatementWidth//2
		rightBranchStatement = formatString(branchesDrawInfo[-1].branch.statement)
		rightBranchStatementWidth=len(rightBranchStatement)*data.pixelsPerLetter
		branchRight = branchesDrawInfo[-1].x + rightBranchStatementWidth//2

		left = min(statementLeft, branchLeft)
		right = max(statementRight, branchRight)
		canvas.create_line(left, y, right, y)
		if(proof.assumptionCancellation != None):
			assumptionNumber = proof.assumptionCancellation
			canvas.create_text(right + data.ProofMargin//3, y, 
				text = str(assumptionNumber))
			assumptionLines = data.assumptionLines.get(assumptionNumber, [])
			for line in assumptionLines:
				x,y = line[0],line[1]
				canvas.create_text(x,y,text = str(assumptionNumber))

def drawSteps(canvas, data, proof, x, y, steps):
	branches = getBranches(proof)
	proofWidth = getProofWidth(data,proof)

	branchesDrawInfo = getBranchesDrawInfo(data, branches, x, y)
	auxBranchesDrawInfo = copy.deepcopy(branchesDrawInfo)
	while(len(branchesDrawInfo) > 0):
		i = getBranchToDraw(branchesDrawInfo)
		branchInfo = branchesDrawInfo[i]
		drawSteps(canvas,data,branchInfo.branch,branchInfo.x,branchInfo.y,steps)
		branchesDrawInfo.pop(i)

	if(data.stepsUsed > steps): return
	branchesDrawInfo = auxBranchesDrawInfo
	canvas.create_text(x,y,text=formatString(proof.statement),
														font = data.ProofFont)
	drawDeductionLine(canvas, data, x, y, proof, branchesDrawInfo)
	data.stepsUsed += 1

def drawProofStepsWrapper(canvas, data, proof, x = None, y = None):
	data.stepsUsed = 0
	data.assumptionLines = dict()
	proofHeight = getProofDepth(proof)*data.ProofLineDifference
	if(x == None): x = data.width//2
	if(y == None): y = data.height//2 + proofHeight//2
	drawSteps(canvas, data, proof, x, y, data.steps)

def drawProofWrapper(canvas, data, proof, x = None, y = None):
	data.assumptionLines = dict()
	proofHeight = getProofDepth(proof)*data.ProofLineDifference
	if(x == None): x = data.width//2
	if(y == None): y = data.height//2 + proofHeight//2
	drawProof(canvas, data, proof, x, y)


def drawProof(canvas, data, proof, x, y):
	branches = getBranches(proof)
	proofWidth = getProofWidth(data,proof)

	branchesDrawInfo = getBranchesDrawInfo(data, branches, x, y)
	auxBranchesDrawInfo = copy.deepcopy(branchesDrawInfo)
	while(len(branchesDrawInfo) > 0):
		i = getBranchToDraw(branchesDrawInfo)
		branchInfo = branchesDrawInfo[i]
		drawProof(canvas,data,branchInfo.branch,branchInfo.x,branchInfo.y)
		branchesDrawInfo.pop(i)

	branchesDrawInfo = auxBranchesDrawInfo
	canvas.create_text(x,y,text=formatString(proof.statement),
														font = data.ProofFont)
	drawDeductionLine(canvas,data,x,y,proof,branchesDrawInfo)

###############################################################################
####	TAUTOLOGY EVALUATION CODE
###############################################################################

def getProps(conjecture):
	nonProps = ['(', ')', '&', '|', '~', '>']
	props = [conjecture]
	for nonProp in nonProps:
		propsCopy = copy.copy(props)
		props = []
		for prop in propsCopy:
			props.extend(prop.split(nonProp))

	props = set(props)
	if('' in props): props.remove('')
	#sort from greatest to smallest length
	props = sorted(list(props), key = lambda x: -len(x))
	return props

def evalTruthAssignment(conjecture, props, assignments):
	truthConjecture = conjecture
	for i in range(len(props)):
		prop = props[i]
		assignment = assignments[i]
		truthConjecture = truthConjecture.replace(prop, str(assignment))

	return evalTruthAssignmentHelper(truthConjecture)

def evalTruthAssignmentHelper(truthConjecture):
	if(truthConjecture == ""): return None
	breakdown = outerConnective(truthConjecture)
	if(breakdown == None): return int(truthConjecture) #base case
	else:
		connective = breakdown[0]
		prop1 = breakdown[1]
		prop2 = breakdown[2]
		prop1Truth = evalTruthAssignmentHelper(prop1)
		prop2Truth = evalTruthAssignmentHelper(prop2)
		if(connective == "~"):
			return prop2Truth^1 #flip the bit
		if(connective == ">"):
			return 1 if (prop1Truth == 0 or prop2Truth == 1) else 0
		if(connective == "&"):
			return prop1Truth&prop2Truth #bitwise and
		if(connective == "|"):
			return prop1Truth|prop2Truth #bitwise or

def isTautology(conjecture):
	props = getProps(conjecture)
	assignments = [None]*len(props)
	falseAssignment = isTautologyHelper(conjecture, props, assignments)
	if(falseAssignment == None): return True
	falseDict = dict()
	for i in range(len(props)):
		falseDict[props[i]] = True if (falseAssignment[i]) else False
	return falseDict

def isTautologyHelper(conjecture, props, assignments, index = 0):
	if(index == len(props)): #base case
		truth = evalTruthAssignment(conjecture, props, assignments)
		if(truth): return None
		else: return assignments
	else:
		for i in [0,1]:
			assignments[index] = i
			solution = isTautologyHelper(conjecture, props, assignments,index+1)
			if(solution != None): return solution
			assignments[index] = None
	return None

###############################################################################
####	UI CODE
###############################################################################

###############################################################################
####	SHOW_FALSITY MODE
###############################################################################

def redrawAllSHOW_FALSITY(canvas, data):
	xc = data.width//2
	y0 = 100
	font = "Arial 14"
	message1 = "Your conjecture"
	canvas.create_text(xc, y0, text = message1, font = font)
	message2 = formatString(data.StatementEntry.get())
	canvas.create_text(xc, y0 + data.ProofLineDifference, text = message2, 
														font = font + " bold")
	message3 = "is false under the following truth assingment:"
	canvas.create_text(xc, y0 + 2*data.ProofLineDifference, text = message3, font = font)

	props = sorted(data.isTautology)
	for i in range(len(props)):
		line = props[i] + ": " + str(data.isTautology[props[i]])
		y = y0 + (i+4)*data.ProofLineDifference
		canvas.create_text(xc, y, text = line, font = font + " bold")

###############################################################################
####	PROVE MODE
###############################################################################

def enterProveMode(data):
	userStatement = replaceConnectives(data.StatementEntry.get())
	if(not validParentheses(userStatement)): 
		data.errorMessage = "ERROR: invalid paretheses formatting"
		return
	formattedStatement = formatProof(userStatement)
	if(formattedStatement.startswith("ERROR")):
		data.errorMessage = formattedStatement
		return
	try: 
		data.isTautology = isTautology(formattedStatement)
	except:
		data.errorMessage = "ERROR: invalid statement"
		return
	if(data.isTautology == True):
		data.MODE = "PROVE"
		data.proof = classicalProof(formattedStatement)
		data.proofSteps = getProofSteps(data.proof)
		data.steps = 0
	else: data.MODE = "SHOW_FALSITY"

def validParentheses(s):
	parenthesesDepth = 0
	for i in range(len(s)):
		char = s[i]
		if(char == "("): parenthesesDepth += 1
		elif(char == ")"): parenthesesDepth -= 1
		if(parenthesesDepth < 0): return False
	if(parenthesesDepth != 0): return False
	else: return True

def formatProof(s):
	s = s.replace(" ", "")
	if(s == ""): return "ERROR: no statement provided to prove"
	breakDown = outerConnective(s)
	if(breakDown == None):
		if(s[0] == "(" and s[-1] == ")"):
			return formatProof(s[1:-1])
		else: return s
	else:
		return s #recurse on the breakDown props later

def keyPressedPROVE(event, data):
	if(event.keysym == "Right"): data.steps = min(data.proofSteps - 1, data.steps + 1)
	if(event.keysym == "Left"): data.steps = max(0, data.steps - 1)
	if(event.keysym == "Escape"): data.MODE = "HOME"

def redrawAllPROVE(canvas, data):
	drawProofStepsWrapper(canvas, data, data.proof)

def initDrawProof(data):
	data.ProofFontSize = 10
	data.ProofFont = "Arial " + str(data.ProofFontSize) + " bold"
	data.ProofMargin = 40
	data.ProofLineDifference = 30
	data.pixelToFontRatio = 1
	data.pixelsPerLetter = data.pixelToFontRatio*data.ProofFontSize

###############################################################################
####	ABOUT PROPOSITIONAL LOGIC (ABL) MODE
###############################################################################

def changeMode(data, newMode):
	data.MODE = newMode

def enterABLMode(data):
	data.MODE = "ABL"
	#set the focus on the canvas so that an entry box from the previous page
	#is not still selected
	data.canvas.focus_set()

def keyPressedABL(event, data):
	if(event.keysym == "space"):
		data.MODE = "ABL"

def drawABLEscapeMessage(canvas, data):
	message = "Space: return to the About Propositional Logic page"
	canvas.create_text(10, 25, text = message, font = "Arial 8", anchor = "nw")

def redrawAllABL(canvas, data):
	if(data.MODE != "ABL"): drawABLEscapeMessage(canvas, data)
	if(data.MODE == "ABLCON"): redrawAllABLCON(canvas,data)
	elif(data.MODE == "ABLDIS"): redrawAllABLDIS(canvas, data)
	elif(data.MODE == "ABLIMP"): redrawAllABLIMP(canvas, data)
	elif(data.MODE == "ABLNEG"): redrawAllABLNEG(canvas, data)
	else:
		conjunctionButtonY = 150
		canvas.create_window(data.width//2, data.conjunctionButtonY,
				width = data.ABLButtonWidth, window = data.conjunctionButton)
		canvas.create_window(data.width//2, data.disjunctionButtonY, 
				width = data.ABLButtonWidth, window = data.disjunctionButton)
		canvas.create_window(data.width//2, data.implicationButtonY, 
				width = data.ABLButtonWidth, window = data.implicationButton)
		canvas.create_window(data.width//2, data.negationButtonY, 
				width = data.ABLButtonWidth, window = data.negationButton)

def redrawAllABLCON(canvas,data):
	message1 = '''\
Conjunction, which has the symbol \\and, is a logical connective that means "and".\n
A\\andB is true only when both A and B are true.\n\n
A proof of a conjunction follows from a proof of both propositions it connects.'''
	message1 = replaceTermsWithConnectives(message1)
	message1Y = 180
	canvas.create_text(data.width//2, message1Y, text = message1,
													font = data.ABLFont)
	proof1Statement = replaceTermsWithConnectives("A\\andB")
	proof1Reasons = [Proof("A","assumed1"), Proof("B","assumed1")]
	proof1 = Proof(proof1Statement, proof1Reasons)
	proof1Y = 350
	drawProofWrapper(canvas, data, proof1, data.width//2, proof1Y)
	message2 = '''A proof of a conjunction can be used to prove either \
proposition it connects.'''
	message2Y = 400
	canvas.create_text(data.width//2, message2Y, text = message2,
													font = data.ABLFont)
	proof2Statement = "A"
	proof2Reason = Proof(replaceTermsWithConnectives("A\\andB"), "assumed1")
	proof2 = Proof(proof2Statement, proof2Reason)
	proof2Y, proof2X = 500, data.width//3
	drawProofWrapper(canvas, data, proof2, proof2X, proof2Y)
	proof3Statement = "B"
	proof3Reason = Proof(replaceTermsWithConnectives("A\\andB"), "assumed1")
	proof3 = Proof(proof3Statement, proof2Reason)
	proof3Y, proof3X = proof2Y, 2*data.width//3
	drawProofWrapper(canvas, data, proof3, proof3X, proof3Y)

def redrawAllABLDIS(canvas, data):
	message = '''Disjunction, which has the symbol \or, is a logical \
connective that means "or". \nA\orB is true if either A is true, B is true, or \
both A and B are true.\n
A proof of a disjunction follows from a proof of either proposition it connects.
\n\n\n
Using a proof of disjunction can be a bit tricky. If you have a proof of a 
disjunction, and you can show that a new proposition follows from both sides 
of the disjunction, then you can use this to show that the new proposition 
follows from the disjunction.
In this example, we have a proof of C from a proof of A\\orB, a proof of C \
assuming A, 
and a proof of C assuming B. Notice that the assumptions of A and B are 
canceled in the final step of the proof.
'''
	message = replaceTermsWithConnectives(message)
	canvas.create_text(data.width//2, data.height//2, text = message, 
											font = data.ABLFont)

	proof1Statement = "A\orB"
	proof1Reason = Proof("A", "assumed1")
	proof1 = Proof(replaceTermsWithConnectives(proof1Statement), proof1Reason)
	proof1Y, proof1X = 290, data.width//3
	drawProofWrapper(canvas, data, proof1, proof1X, proof1Y)

	proof2Statement = "A\orB"
	proof2Reason = Proof("B", "assumed1")
	proof2 = Proof(replaceTermsWithConnectives(proof2Statement), proof2Reason)
	proof2Y, proof2X = proof1Y, 2*data.width//3
	drawProofWrapper(canvas, data, proof2, proof2X, proof2Y)

	proof3Statement = "C"
	ProofAtoC = Proof("C", Proof(":", Proof("A", "assumed1")))
	ProofBtoC = Proof("C", Proof(":", Proof("B", "assumed1")))
	proof3Reason = ([Proof(replaceTermsWithConnectives("A\orB"), "assumed2"),
		ProofAtoC, ProofBtoC])
	proof3 = Proof(proof3Statement, proof3Reason, assumptionCancellation = 1)
	proof3Y = 630
	drawProofWrapper(canvas, data, proof3, data.width//2, proof3Y)

def redrawAllABLIMP(canvas, data):
	message = '''Implication, which has the symbol \\to, is a logical \
connective that means "implies". \nFrom a semantics viewpoint, A\\toB is only \
false if A is true and B is false. If A is
false or B is true, then A\\toB is true. In this implication, A is known as the
antecedent and B is known as the consequent.\n
An implication can be proved by showing that the consequent follows from
assuming the antecedent. Note that the assumption of the antecedent is
canceled in the last step of the proof.\n\n\n\n\n
A proof of an implication and a proof of its antecedent can be used to 
prove the consequent.'''
	message = replaceTermsWithConnectives(message)
	canvas.create_text(data.width//2, data.height//2, text = message, 
											font = data.ABLFont)

	proof1Statement = replaceTermsWithConnectives("A\\toB")
	proof1Reason = Proof("B", Proof(":", Proof("A", "assumed1")))
	proof1 = Proof(proof1Statement, proof1Reason, assumptionCancellation = 1)
	proof1Y = 450
	drawProofWrapper(canvas, data, proof1, data.width//2, proof1Y)

	proof2Statement = "B"
	proof2Reasons = ([Proof(replaceTermsWithConnectives("A\\toB"), "assumed1"),
													Proof("A", "assumed1")])
	proof2 = Proof(proof2Statement, proof2Reasons)
	proof2Y = 600
	drawProofWrapper(canvas, data, proof2, data.width//2, proof2Y)

def redrawAllABLNEG(canvas, data):
	message = '''Negation, which has the symbol \\not, essentially means "not".
\\notA is true if A is false. A negation can be proved by assuming the
proposition it is attached to and showing that a contradiction follows. Note 
that the initial assumption is canceled at the last step of the proof\n\n\n\n\n
A proof of a negation, along with a proof of the proposition is negates, can be
used to prove a contradiction.'''
	message = replaceTermsWithConnectives(message)
	canvas.create_text(data.width//2, data.height//2, text = message,
												font = data.ABLFont)

	proof1Statement = replaceTermsWithConnectives("\\notA")
	proof1Reason = Proof(replaceTermsWithConnectives("\\false"),
											Proof(":", Proof("A", "assumed1")))
	proof1 = Proof(proof1Statement, proof1Reason, assumptionCancellation = 1)
	proof1Y = 400
	drawProofWrapper(canvas, data, proof1, data.width//2, proof1Y)

	proof2Statement = replaceTermsWithConnectives("\\false")
	proof2Reasons = ([Proof("A", "assumed1"), 
					Proof(replaceTermsWithConnectives("\\notA"), "assumed1")])
	proof2 = Proof(proof2Statement, proof2Reasons)
	proof2Y = 550
	drawProofWrapper(canvas, data, proof2, data.width//2, proof2Y)

def initABL(data):
	data.messageTop = 50
	data.ABLFont = "Arial 18"
	data.ABLButtonWidth = 220

	data.conjunctionButton = Button(data.root, text = "About Conjunction",
		relief = GROOVE, font = data.ABLFont, 
		command = lambda: changeMode(data, "ABLCON"))
	data.conjunctionButtonY = 200

	data.disjunctionButton = Button(data.root, text = "About Disjunction",
			relief = GROOVE, font = data.ABLFont, 
			command = lambda: changeMode(data, "ABLDIS"))
	data.disjunctionButtonY = 270

	data.implicationButton = Button(data.root, text = "About Implication",
			relief = GROOVE, font = data.ABLFont, 
			command = lambda: changeMode(data, "ABLIMP"))
	data.implicationButtonY = 340

	data.negationButton = Button(data.root, text = "About Negation",
			relief = GROOVE, font = data.ABLFont, 
			command = lambda: changeMode(data, "ABLNEG"))
	data.negationButtonY = 410

###############################################################################
####	BUILD MODE
###############################################################################

#taken from my 112 week 1 lab code
def rectanglesOverlap(x1, y1, w1, h1, x2, y2, w2, h2):
    return (((x1 <= x2 <= (x1 + w1) or x1 <= (x2 + w2) <= (x1 + w1)) 
    and (y1 <= y2 <= (y1 + h1) or y1 <= (y2 + h2) <= y1 + h1)) 
    or ((x2 <= x1 <= (x2 + w2) or x2 <=  (x1 + w1) <= (x2 + w2)) 
    and (y2 <= y1 <= (y2 + h2) or y2 <= (y1 + h1) <= y2 + h2)))

class ProofBlock(object):
	color = "light gray"
	focusBlock = None
	selectedBlocks = set()
	proofBlocks = []
	proofLineDifference = 30
	assumptionNumber = 1
	assumptionNums = dict()
	margin = 10
	proofMargin = 45
	EntryBoxHeight = 30

	def __init__(self, x, y, data):
		self.blockNumber = len(ProofBlock.proofBlocks)
		self.assumptions = set()
		self.proof = None
		self.xc = x
		self.yc = y
		self.width = 130
		self.height = ProofBlock.EntryBoxHeight
		self.left = self.xc - self.width//2
		self.right = self.left + self.width
		self.top = self.yc - self.height//2
		self.bot = self.top + self.height
		self.Entry = Entry(data.root)
		self.Entry.focus_set()
		self.errorMessage = None
		ProofBlock.proofBlocks.append(self)
		ProofBlock.focusBlock = self
		ProofBlock.selectedBlocks.add(self)

	def move(self, x, y):
		self.xc = x
		self.yc = y
		self.left = self.xc - self.width//2
		self.right = self.left + self.width
		self.top = self.yc - self.height//2
		self.bot = self.top + self.height

	def collides(self, other):
		return (rectanglesOverlap(self.left, self.top, self.width, self.height,
							other.left, other.top, other.width, other.height))

	def fixCollision(self, other):
		#def rectanglesOverlap(x1, y1, w1, h1, x2, y2, w2, h2):
		if(rectanglesOverlap(self.left, self.top, self.width, self.height, 
				other.left, other.top, other.width, other.height)):
			if(self.xc - other.xc > 0): #if self is to the right
				dx = self.left - other.right
			else: # if self is to the left
				dx = self.right - other.left

			if(self.yc - other.yc > 0): #if self is below
				dy = self.top - other.bot
			else:
				dy = self.bot - other.top
			#move the blocks as little as possible to fix the collision
			if(abs(dx) < abs(dy)): other.move(other.xc + dx, other.yc)
			else: other.move(other.xc, other.yc + dy)

	def isClicked(self, event):
		return (self.left <= event.x <= self.right and 
		   self.top <= event.y <= self.bot)

	def draw(self, canvas, data):
		selected = self in ProofBlock.selectedBlocks
		borderWidth = 4 if(selected) else 1
		outline = (data.selectedBlocksColor 
				if(selected and self != ProofBlock.focusBlock) else "Black")
		#print the background and border
		canvas.create_rectangle(self.left, self.top, self.right, self.bot,
				fill = ProofBlock.color, width = borderWidth, outline = outline)
		#print the proof
		if(self.proof != None):
			drawProofWrapper(canvas, data, self.proof, 
			self.xc, self.bot - self.EntryBoxHeight//2 - data.ProofLineDifference)
		#print the entry widget
		canvas.create_window(self.xc, self.bot - self.EntryBoxHeight//2,
															window = self.Entry)
		if(self.errorMessage != None):
			canvas.create_text(self.xc, self.bot + 10, text = self.errorMessage,
										fill = "red", font = "Arial 9 bold")

	def __eq__(self, other):
		if(not isinstance(other, ProofBlock)): return False
		return (self.proof == other.proof and self.xc == other.xc and 
				self.yc == other.yc)

	def resize(self, data):
		self.width = max(getProofWidth(data, 
							self.proof) + ProofBlock.proofMargin, self.width)
		self.height = (
			max(getProofHeight(self.proof, data) + self.EntryBoxHeight + 
											ProofBlock.margin,  self.height))
		self.left = self.xc - self.width//2
		self.right = self.left + self.width
		self.top = self.yc - self.height//2
		self.bot = self.top + self.height
		fixCollisions(data)

	def addToProof(self, data):
		statement = self.Entry.get()
		if(len(statement) == 0): return

		if(self.proof == None):
			self.assumptions.add(statement)
			self.proof = Proof(statement, 
								"assumed" + str(ProofBlock.assumptionNumber))
			if(statement not in ProofBlock.assumptionNums):
				ProofBlock.assumptionNums[replaceConnectives(statement)] = (
												ProofBlock.assumptionNumber)
				ProofBlock.assumptionNumber += 1
		else:
			newProof = validProof(statement)
			if(newProof != None): 
				self.proof = newProof
				self.errorMessage = None
			else: self.errorMessage = "invalid deduction"
		self.resize(data)

	def __hash__(self):
		return self.blockNumber

#checks for collisions on the board, and any collisions
def fixCollisions(data):
	if(ProofBlock.focusBlock == None): return
	for block in ProofBlock.proofBlocks:
		if(block == ProofBlock.focusBlock): continue
		else: ProofBlock.focusBlock.fixCollision(block)

#checks whether the deduction is a valid conjunction deduction
#returns true or false
def isValidConjunctionDeduction(statement, reason):
	reasonBreakDown = outerConnective(reason)
	if(reasonBreakDown == None or reasonBreakDown[0] != "&"): return False
	reasonProp1 = reasonBreakDown[1]
	reasonProp2 = reasonBreakDown[2]
	return (statement == reasonProp1 or statement == reasonProp2)

#checks whether the deduction is a conjunction introduction
#returns a proof object or None
def getConjunctionIntroductionProof(statement, reasons, proofs):
	statementBreakDown = outerConnective(statement)
	if(statementBreakDown == None or statementBreakDown[0] != "&"): return None
	statementProp1 = statementBreakDown[1]
	statementProp2 = statementBreakDown[2]
	if(statementProp1 in reasons and statementProp2 in reasons):
		return Proof(statement, proofs)
	else: return None	

#checks whether a statement is a valid disjunction introduction
#returns True or False
def isValidDisjunctionIntroduction(statement, reason):
	statementBreakDown = outerConnective(statement)
	if(statementBreakDown == None or statementBreakDown[0] != "|"): return False
	statementProp1 = statementBreakDown[1]
	statementProp2 = statementBreakDown[2]
	return (reason == statementProp1 or reason == statementProp2)

#checks whether a proof is a valid proof by contradiction
#returns a proof object or None
def getProofOfContradiction(statement, reasons, proofs):
	if(replaceConnectives(statement) != "!"): return None
	reason1, reason2 = reasons[0], reasons[1]
	(reasonBreakDown1, reasonBreakDown2) = (outerConnective(reason1), 
													outerConnective(reason2))
	if(reasonBreakDown1 != None and reasonBreakDown1[0] == "~"):
		if(reason2 == reasonBreakDown1[2]): return Proof(statement, proofs)
	elif(reasonBreakDown2 != None and reasonBreakDown2[0] == "~"):
		if(reason1 == reasonBreakDown2[2]): return Proof(statement, proofs)
	else: return None

#checks whether a statement is a valid implication elimination
#returns a proof object or None
def getImplicationEliminationProof(statement, reasons, proofs):
	reason1, reason2 = reasons[0], reasons[1]
	#if this is a proof by implication elimination, the implication is
	#necessarily longer than the antecedent, because it contains the antecedent
	implication = reason1 if(len(reason1) > len(reason2)) else reason2
	antecedent = reason1 if(implication != reason1) else reason2
	implicationBreakdown = outerConnective(implication)
	if(implicationBreakdown != None and implicationBreakdown[0] == ">"
									and implicationBreakdown[1] == antecedent):
		return Proof(statement, proofs)
	else: return None

#checks whether the proof is a valid implication deduction
#returns a proof object or None
def getImplicationDeductionProof(statement, reason, proof):
	statementBreakDown = outerConnective(statement)
	if(statementBreakDown == None or statementBreakDown[0] != ">"): return None
	statementProp1 = statementBreakDown[1]
	statementProp2 = statementBreakDown[2]
	if(reason == statementProp2):
		if(statementProp1 in getInitialAssumption(proof)):
			assumptionCancellation = ProofBlock.assumptionNums[statementProp1]
			return Proof(statement, proof, 
								assumptionCancellation = assumptionCancellation)
		else: return Proof(statement, proof)
	else: return None

#checks whether the proof is a proof or falsity/contradiction
#returns a proof object or None
def getFalsityProof(statement, reason, proof):
	reason = replaceConnectives(reason)
	if(reason != "!"): return None
	#check if the proof is a proof by contradiction
	statementBreakDown = outerConnective(statement)
	if(statementBreakDown != None and statementBreakDown[0] == "~"):
		negation = statementBreakDown[2]
		if(negation in getInitialAssumption(proof)):
			assumptionCancellation = ProofBlock.assumptionNums[negation]
			return Proof(statement, proof, 
							assumptionCancellation = assumptionCancellation)

	#check if the proof is a negation introduction proof
	if(statementBreakDown == None): negation = "~"+statement
	else: negation = "~(" + statement + ")"
	if(negation in getInitialAssumption(proof)):
		assumptionCancellation = ProofBlock.assumptionNums[negation]
		return Proof(statement, proof, 
						assumptionCancellation = assumptionCancellation)
	
	return Proof(statement, proof)

#checks whether the given statement follows from the selected proof blocks
def validProof(statement):
	if(len(statement) == 0): return None
	statement = replaceConnectives(statement)
	proofs = [block.proof for block in ProofBlock.selectedBlocks]
	reasons = [replaceConnectives(proof.statement) for proof in proofs]
	if(len(reasons) == 1):
		proof = proofs[0]
		reason = reasons[0]
		newProof = Proof(statement, proof)
		if(statement == reason): return newProof
		if(isValidConjunctionDeduction(statement, reason)): return newProof
		if(isValidDisjunctionIntroduction(statement, reason)): return newProof
		#check whether this proves an implication
		implicationDeductionProof = getImplicationDeductionProof(statement, 
																reason, proof)
		if(implicationDeductionProof != None): return implicationDeductionProof
		falsityProof = getFalsityProof(statement, reason, proof)
		if(falsityProof != None): return falsityProof

	if(len(reasons) == 2):
		conjunctionIntroductionProof = getConjunctionIntroductionProof(
													statement, reasons, proofs)
		if(conjunctionIntroductionProof != None): 
			return conjunctionIntroductionProof
		contradictionProof = getProofOfContradiction(statement, reasons, proofs)
		if(contradictionProof != None): return contradictionProof
		implicationEliminationProof = getImplicationEliminationProof(statement, 
																reasons, proofs)
		if(implicationEliminationProof != None): 
			return implicationEliminationProof

	if(len(reasons) == 3):
		pass

	return None

#returns a set of the initial assumptions made by the proof
def getInitialAssumption(proof):
	if(isinstance(proof.reasons, str)):
		return {replaceConnectives(proof.statement)}
	else:
		result = set()
		for reason in proof.reasons:
			result = result.union(getInitialAssumption(reason))
		return result

def enterBuildMode(data):
	data.canvas.focus_set()
	data.MODE = "BUILD"

def mousePressedBUILD(event, data):
	if("shift" in data.keysPressed and ProofBlock.focusBlock != None):
		for block in ProofBlock.proofBlocks:
			if(block.isClicked(event)): ProofBlock.selectedBlocks.add(block)
		return
	#give the focus to the canvas so that none of the entry boxes are
	#selected
	data.canvas.focus_set()
	ProofBlock.focusBlock = None
	ProofBlock.selectedBlocks = set()
	for block in ProofBlock.proofBlocks:
		if(block.isClicked(event)):
			ProofBlock.focusBlock = block
			ProofBlock.selectedBlocks.add(block)
			block.Entry.focus_set()
			#get the distance from the click to the center of the block
			data.dyc = event.y - block.yc
			data.dxc = event.x - block.xc

def mouseMotionBUILD(event, data):
	if(data.mouseClicked == False or ProofBlock.focusBlock == None): 
		return False
	else:
		ProofBlock.focusBlock.move(event.x - data.dxc, event.y - data.dyc)
		fixCollisions(data)
		return True


def keyPressedBUILD(event,data):
	if("control" in data.keysPressed and event.keysym == "q"):
		if(ProofBlock.focusBlock != None):
			ProofBlock.proofBlocks.remove(ProofBlock.focusBlock)
			ProofBlock.focusBlock = None

	if(event.keysym == "Return"):
		if(ProofBlock.focusBlock != None):
			ProofBlock.focusBlock.addToProof(data)
		else:
			newProofBlock = ProofBlock(event.x,event.y,data)
			ProofBlock.selected = newProofBlock

	elif(ProofBlock.focusBlock != None):
		Entry = ProofBlock.focusBlock.Entry
		statementText = Entry.get()
		originalStatementText = statementText
		statementText = replaceTermsWithConnectives(statementText)
		if(originalStatementText != statementText):
			cursorLocation = Entry.index(INSERT)
			Entry.delete(0,END)
			Entry.insert(INSERT, statementText)
			cursorLocation -= len(originalStatementText) - len(statementText)
			Entry.icursor(cursorLocation)

def redrawAllBUILD(canvas,data):
	canvas.create_window(data.buildHelpButtonX, data.buildHelpButtonY, 
												window = data.buildHelpButton)
	for block in ProofBlock.proofBlocks:
		if(block != ProofBlock.focusBlock): block.draw(canvas, data)
	if(ProofBlock.focusBlock != None): ProofBlock.focusBlock.draw(canvas, data)

def initBUILD(data):
	data.buildHelpButton = Button(data.root, text = "Help", relief = GROOVE,
								command = lambda: changeMode(data, "BUILDHELP"))
	data.buildHelpButtonX = 60
	data.buildHelpButtonY = 40
	data.selectedBlocksColor = "Yellow"

###############################################################################
####	BUILDHELP MODE
###############################################################################

def keyPressedBUILDHELP(event, data):
	if(event.keysym == "space"):
		data.MODE = "BUILD"

def drawBUILDEscapeMessage(canvas, data):
	message = "Space: return to the Build Proof page"
	canvas.create_text(10, 25, text = message, font = "Arial 8", anchor = "nw")

def redrawAllBUILDHELP(canvas, data):
	drawBUILDEscapeMessage(canvas, data)
	font = "Arial 18"
	message = '''To create a new proof block, make sure you have no blocks selected and press
Enter. You can then type your initial assumption into the text box and press Enter 
again begin writing your proof.\n
To select a proof block, simply click inside the proof block you want to select.
If you want to make a deduction that requires multiple proof blocks to prove,
you can select other proof blocks using Shift+Click.\n
To delete the selected proof block, press Ctrl+q'''
	canvas.create_text(data.width//2, data.height//2,font = font,text = message)

###############################################################################
####	SYNTAX MODE
###############################################################################

def redrawAllSYNTAX(canvas, data):
	font = "Arial 26"
	message0 = "To get the below symbols, enter the corresponding text"
	message0Y = 200
	canvas.create_text(data.width//2, message0Y, font = font, text = message0)
	symbolMessage1 = replaceTermsWithConnectives("\\and") + " : \\and"
	symbolMessage2 = replaceTermsWithConnectives("\or") + " : \\or"
	symbolMessage3 = replaceTermsWithConnectives("\\to") + " : \\to, \implies"
	symbolMessage4 = (replaceTermsWithConnectives("\\false") + 
												" : \\false, \contradiction")
	symbolMessage = (symbolMessage1 + "\n" + symbolMessage2 + "\n" + 
										symbolMessage3 + "\n" + symbolMessage4)
	symbolMessageY = 350
	canvas.create_text(data.width//2, symbolMessageY, font = font, 
														text = symbolMessage)

###############################################################################
####	HOME MODE
###############################################################################

def keyPressedHOME(event, data):
	statementText = data.StatementEntry.get()
	if(event.keysym == "Return"): 
			data.errorMessage = None
			enterProveMode(data)
	else:
		originalStatementText = statementText
		statementText = replaceTermsWithConnectives(statementText)
		if(originalStatementText != statementText):
			cursorLocation = data.StatementEntry.index(INSERT)
			data.StatementEntry.delete(0,END)
			data.StatementEntry.insert(INSERT, statementText)
			cursorLocation -= len(originalStatementText) - len(statementText)
			data.StatementEntry.icursor(cursorLocation)

def redrawAllHOME(canvas, data):
	canvas.create_window(data.width//2, data.titleY, window = data.title)
	canvas.create_window(data.ABLButtonX, data.ABLButtonY, 
											window = data.ABLButton)
	canvas.create_window(data.BuildButtonX, data.BuildButtonY,
											window = data.BuildButton)
	canvas.create_text(data.StatementEntryX, data.StatementEntryLabelY,
	text = "Enter a propositional statement to be proved",font=data.labelFont)
	canvas.create_window(data.StatementEntryX, data.StatementEntryY,
											window = data.StatementEntry)
	canvas.create_window(data.SyntaxButtonX, data.SyntaxButtonY,
											window = data.SyntaxButton)

	if(data.errorMessage != None):
		canvas.create_text(data.StatementEntryX, 
			data.StatementEntryY + 20, text = data.errorMessage, fill = "red")

def initHOME(data):
	data.title = Text(data.root, width = 14, height = 1, relief = FLAT, 
					font = "Arial 50 bold", background = data.backgroundColor)
	data.title.pack()
	data.title.insert(END, "Proper Proofer")
	data.title.tag_add("red1", 1.0, 1.4)
	data.title.tag_config("red1", foreground = "red", 
											background = data.backgroundColor)
	data.title.tag_add("red2", 1.7, 1.12)
	data.title.tag_config("red2", foreground = "red", 
											background = data.backgroundColor)
	data.title.configure(state = DISABLED)
	data.titleY = 125
	data.titleFont = "Arial 50 bold"
	data.ABLButton = Button(data.root, text = "About\nPropositional Logic",
		font = "Arial 14", command = lambda: enterABLMode(data),relief = GROOVE)
	data.ABLButtonX, data.ABLButtonY = data.width//2, 275

	data.BuildButton = Button(data.root, text = "Build A Proof",relief = GROOVE,
			height = 2, width = 15, font = "Arial 14", 
										command = lambda: enterBuildMode(data))
	data.BuildButtonX, data.BuildButtonY = data.width//2, 375
	data.StatementEntry = Entry(data.root, width = 50)
	data.StatementEntry.focus_set()
	data.StatementEntryX, data.StatementEntryY = data.width//2, 3*data.height//4
	data.StatementEntryLabelY = data.StatementEntryY - 20
	data.labelFont = "Arial 8 bold"
	data.SyntaxButton = Button(data.root, text = "Syntax Help", relief = GROOVE,
			font = "Arial 12", command = lambda: changeMode(data, "SYNTAX"))
	data.SyntaxButtonX, data.SyntaxButtonY = data.width//2, 550

###############################################################################
####	GENERAL UI CODE
###############################################################################

#barebones event animation code taken from 
#http://www.cs.cmu.edu/~112/notes/events-example0.py

def init(data):
	data.backgroundColor = rgbString(219, 190, 122)
	initHOME(data)
	initDrawProof(data)
	initBUILD(data)
	initABL(data)
	data.errorMessage = None
	data.mouseClicked = False
	data.MODE = "HOME"
	data.keysPressed = set()

def mousePressed(event, data):
	data.mouseClicked = True
	if(data.MODE == "BUILD"): mousePressedBUILD(event, data)

def mouseReleased(event, data):
	data.mouseClicked = False

def mouseMotion(event, data):
	if(data.MODE == "BUILD"):
		return mouseMotionBUILD(event, data)
	else: return False

def keyPressed(event, data):
	key = event.keysym.split("_")[0].lower()
	data.keysPressed.add(key)
	if(data.MODE != "HOME" and event.keysym == "Escape"): data.MODE = "HOME"
	if(data.MODE.startswith("ABL")): keyPressedABL(event, data)
	if(data.MODE == "HOME"): keyPressedHOME(event, data)
	if(data.MODE == "PROVE"): keyPressedPROVE(event, data)
	if(data.MODE == "BUILD"): keyPressedBUILD(event, data)
	if(data.MODE == "BUILDHELP"): keyPressedBUILDHELP(event, data)

def keyReleased(event, data):
	key = event.keysym.split("_")[0].lower()
	if(key in data.keysPressed):
		data.keysPressed.remove(key)

def timerFired(data):
	pass

def drawEscapeMessage(canvas, data):
	message = "ESC: return to Home"
	canvas.create_text(10, 10, text = message, font = "Arial 8", anchor = "nw")

def redrawAll(canvas, data):
	canvas.create_rectangle(-2,-2,data.width + 2, data.height + 2, 
													fill = data.backgroundColor)
	if(data.MODE != "HOME"): drawEscapeMessage(canvas, data)
	if(data.MODE.startswith("ABL")): redrawAllABL(canvas, data)
	if(data.MODE == "HOME"): redrawAllHOME(canvas, data)
	if(data.MODE == "PROVE"): redrawAllPROVE(canvas, data)
	if(data.MODE == "SHOW_FALSITY"): redrawAllSHOW_FALSITY(canvas, data)
	if(data.MODE == "BUILD"): redrawAllBUILD(canvas, data)
	if(data.MODE == "BUILDHELP"): redrawAllBUILDHELP(canvas, data)
	if(data.MODE == "SYNTAX"): redrawAllSYNTAX(canvas, data)

def run(width=300, height=300):
	def redrawAllWrapper(canvas, data):
		canvas.delete(ALL)
		canvas.create_rectangle(0, 0, data.width, data.height,
								fill='white', width=0)
		redrawAll(canvas, data)
		canvas.update()	

	def mousePressedWrapper(event, canvas, data):
		mousePressed(event, data)
		redrawAllWrapper(canvas, data)

	def mouseReleasedWrapper(event, canvas, data):
		mouseReleased(event, data)
		redrawAllWrapper(canvas, data)

	def mouseMotionWrapper(event, canvas, data):
	#it would be crazy to redraw everything every time there was a mouse motion
	#so instead, the mouseMotion function will return whether the screen needs
	#to be redrawn or not
		if(mouseMotion(event, data)):
			redrawAllWrapper(canvas, data)

	def keyPressedWrapper(event, canvas, data):
		keyPressed(event, data)
		redrawAllWrapper(canvas, data)

	def keyReleasedWrapper(event, canvas, data):
		keyReleased(event, data)
		redrawAllWrapper(canvas, data)

	def timerFiredWrapper(canvas, data):
		timerFired(data)
		redrawAllWrapper(canvas, data)
		# pause, then call timerFired again
		canvas.after(data.timerDelay, timerFiredWrapper, canvas, data)
	# Set up data
	data = Struct()
	data.width = width
	data.height = height
	data.timerDelay = 100 # milliseconds
	# create the root and the canvas
	root = Tk()
	#the root is added to the data struct so that we can create tkinter
	#widgets later on. root will be used as these widgets' parent widget.
	data.root = root
	root.wm_title("Proper Proofer")
	root.resizable(0,0) #prevent the window from being resized
	canvas = Canvas(root, width=data.width, height=data.height)
	#the canvas is added to the data struct so that we can hand the focus to
	#the canvas when editing the model. This is not used to violate MVC.
	data.canvas = canvas
	canvas.pack()

	init(data)
	# set up events
	root.bind("<ButtonPress-1>", lambda event:
                            mousePressedWrapper(event, canvas, data))
	root.bind("<ButtonRelease-1>", lambda event:
    						mouseReleasedWrapper(event, canvas, data))
	root.bind("<Motion>", lambda event:
							mouseMotionWrapper(event, canvas, data))
	root.bind("<KeyPress>", lambda event:
							keyPressedWrapper(event, canvas, data))
	root.bind("<KeyRelease>", lambda event:
							keyReleasedWrapper(event, canvas, data))
	timerFiredWrapper(canvas, data)
	root.mainloop()

run(1000, 650)