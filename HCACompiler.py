import re
import ast

#Input:
#name [States names], [ports names], [[data assignments]], [[relations]], [{Dynamical Systems}]
#Ex: states: [d0, d1], ports: [DA, DB], data assignments: [[1, 1, 1, 1, 0, 0], [1, 1, 1, 1, 0, 1]],
#relations (list of relations to match each state): [(transitions for first state)[(Ports involved)[DA], (Data constraint, ex: 1 in port DA)[DA, 1], (Finish state)d1], (transitions for second state)[...]]
#Dynamical Systems (one DS to match each state): [(DS for first state)[(initial value)5, (flow function)[(operation)['*','/','+','-'], (auxiliar value)1], (constraint value)0], [...]] 


def flowFunctionDefinition(stateName, DS):
    result = "Definition " + stateName + "FlowFunction (n: nat) : nat := \n  match n with \n"
    result += "  | 0 => " + str(DS[0]) + "\n"
    result += "  | n => n " + DS[1][0] + " " + str(DS[1][1])  + "\n"
    result += "end."

    return result

def portRecord(connectorName, portName):
    result = "Definition port" + portName + " := {| \n"
    result += "ConstraintAutomata.id := " + portName + ";\n"
    result += "ConstraintAutomata.dataAssignment := dataAssignment" + portName + ";\n"
    result += "ConstraintAutomata.timeStamp := timeStamp" + connectorName + portName + ";\n"
    result += "ConstraintAutomata.tdsCond := timeStamp" + connectorName + portName + "Holds;\n"
    result += "ConstraintAutomata.index := 0 |}."

    return result
    

def timeStampLemmaDefinition(connectorName, portName, DA):
    result = "Lemma timeStamp" + connectorName + portName + "Holds : forall n, Qlt (timeStamp" + connectorName + portName + " n) (timeStamp" + connectorName + portName + "(S n)).\n Proof."
    result += "\n intros. destruct n. unfold timeStamp" + connectorName + portName + ". reflexivity.\n"
    result += "unfold timeStamp" + connectorName + portName + ". case(n). reflexivity.\n"
    result += "intros n0. case (n0). reflexivity.\n"
    result += "intros n1. case (n1). reflexivity.\n"
    result += "intros n2. case (n2). reflexivity.\n"
    result += "intros n3. case (n3). reflexivity.\n"
    result += "intros n4. unfold Qlt. apply orderZofNat.  Defined."
    
    return result

def DADefinition(portName, DA):
    result = "Definition dataAssignment" + portName + " n :=\n  match n with \n"
    
    for i in range(len(DA)):
        if i == len(DA) - 1:
            auxString = "  | S n => " + str(DA[i])
        else:
            auxString = "  | " + str(i) + " => " + str(DA[i])

        auxString += "\n"
        result += auxString
    
    result += "  end."

    return result

#Standard timeStamp
def timeStampDefinition(connectorName, portName, DA):
    result = "Definition timeStamp" + connectorName + portName + " (n:nat) : QArith_base.Q :=\n  match n with \n"
    aux = 1
    for i in range(len(DA)):
        if i == len(DA) - 1:
            auxString = "  | S n => Z.of_N (N.of_nat(S n)) + 10#1"
        else:
            auxString = "  | " + str(i) + " => " + str(aux) + "#1"

        aux += 2
        auxString += "\n"
        result += auxString
    
    result += "  end."

    return result

def translate(connectorName, states, startState, ports, DA, relations, DS):
    result = ""

    #States definition
    statesString = "Inductive " + connectorName + "States : Type := "
    for i in range(len(states)):
        if i == len(states) - 1:
            statesString += states[i] + "."
        else:
            statesString += states[i] + " | "
    
    result += statesString + "\n\n"

    #Ports definition
    portsString = "Inductive " + connectorName + "Ports : Type := "
    for i in range(len(ports)):
        if i == len(ports) - 1:
            portsString += ports[i] + "."
        else:
            portsString += ports[i] + " | "
    
    result += portsString + "\n\n"

    #Data assignment definition
    DADefString = ""
    for i in range(len(ports)):
        auxString = DADefinition(ports[i], DA[i])
        auxString += "\n\n"
        DADefString += auxString
    
    result += DADefString + "\n\n"
    
    #Basic timeStamp
    timeStampDefString = ""
    for i in range(len(ports)):
        auxString = timeStampDefinition(connectorName, ports[i], DA[i])
        auxString += "\n\n"
        timeStampDefString += auxString
    
    result += timeStampDefString + "\n\n"
    
    #timeStamp lemma
    timeStampLemmaDefString = ""
    for i in range(len(ports)):
        auxString = timeStampLemmaDefinition(connectorName, ports[i], DA[i])
        auxString += "\n\n"
        timeStampLemmaDefString += auxString
    
    result += timeStampLemmaDefString + "\n\n"

    #portRecord
    portRecordString = ""
    for i in range(len(ports)):
        auxString = portRecord(connectorName, ports[i])
        auxString += "\n\n"
        portRecordString += auxString
    
    result += portRecordString + "\n\n"

    portsList = "Definition " + connectorName + "PortsList := ["
    for i in range(len(ports)):
        if i == len(ports) - 1:
            portsList += "port" + ports[i] + "]."
        else:
            portsList += "port" + ports[i] + ";"

    result += portsList + "\n\n"
    
    relationString = "Definition " + connectorName + "Rel (s: " + connectorName + "States) :\n"
    relationString += "set (set " + connectorName + "Ports " + "* ConstraintAutomata.DC " + connectorName + "Ports nat * " + connectorName + "States) := \n"
    relationString += "  match s with \n"

    for i in range(len(states)):
        stateRelationString = "  |  " + states[i] + " => ["

        for j in range(len(relations[i])):
            if j == len(relations[i]) - 1:
                currRelation = relations[i][j]
                currRelationString = "([" + currRelation[0] + "], (ConstraintAutomata.DC " + currRelation[1][0] + " " + str(currRelation[1][1]) + " ), " + currRelation[2] + ")"
                stateRelationString += currRelationString + "]"
            else:
                currRelation = relations[i][j]
                currRelationString = "([" + currRelation[0] + "], (ConstraintAutomata.DC " + currRelation[1][0] + " " + str(currRelation[1][1]) + " ), " + currRelation[2] + ")"
                stateRelationString += currRelationString + ", "
        
        relationString += stateRelationString + "\n"
    
    relationString += "end."

    result += relationString + "\n\n"

    #Constraint Automata
    CAString = "Definition " + connectorName + "CA := {|\n"
    CAString += "  ConstraintAutomata.Q := ["
    for i in range(len(ports)):
        if i == len(ports) - 1:
            CAString += ports[i] + "]"
        else:
            CAString += ports[i] + ";"
    
    CAString += ";\n"
    CAString += "  ConstraintAutomata.N := ["
    for i in range(len(states)):
        if i == len(states) - 1:
            CAString += states[i] + "]"
        else:
            CAString += states[i] + ";"
    CAString += ";\n"

    CAString += "  ConstraintAutomata.T := " + connectorName + "Rel;\n"
    CAString += "  ConstraintAutomata.Q0 := [" + startState + "]\n|}"

    result += CAString + "\n\n"

    #Dynamical Systems
    #StatesList

    statesListString = "Definition " + connectorName + "StatesList := ["
    for i in range(len(states)):
        if i == len(states) - 1:
            statesListString += states[i] + "]."
        else:
            statesListString += states[i] + ";"

    result += statesListString + "\n\n"

    flowFunctionDefinitionString = ""
    for i in range(len(states)):
        flowFunctionDefinitionString += flowFunctionDefinition(states[i], DS[i]) + "\n\n"
    

    result += flowFunctionDefinitionString + "\n\n"

    DSDefinitionString = ""
    for i in range(len(states)):
        DSDefinitionString += "Definition " + states[i] + "DS := (" + str(DS[i][0]) + ", " + states[i] + "FlowFunction, " + str(DS[i][0]) + ", " + str(DS[i][2]) + ").\n"

    result += DSDefinitionString + "\n\n"

    DSListString = "Definition " + connectorName + "DSList := ["
    for i in range(len(states)):
        if i == len(states) - 1:
            DSListString += states[i] + "DS" +"]."
        else:
            DSListString += states[i]+ "DS" + "; "
    
    result += DSListString + "\n\n"

    return result 

def translateString(input):
    #Input type {name} {[states]} {startState} {[ports]} {[[DA]]} {[[relations]]} {[[DS]]}
    pattern = r'{([^}]*)}'
    input = re.findall(pattern, input)

    connectorName = ast.literal_eval(input[0])
    states = ast.literal_eval(input[1])
    startState = ast.literal_eval(input[2])
    ports = ast.literal_eval(input[3])
    DA = ast.literal_eval(input[4])
    relations = ast.literal_eval(input[5])
    DS = ast.literal_eval(input[6])

    return connectorName, states, startState, ports, DA, relations, DS

#Example of use
relations = [[["DA", ["DA", 1], "d1"]], [["DA", ["DA", 1], "d0"]]]
dynamicalSystems = [[5, ["-", 1], 0], [0, ["+", 0], 0]]

#Input example:
inputEx = "{'delay'} {['do', 'd1']} {'d0'} {['DA', 'DB']} {[[1, 1, 1, 1, 0, 1], [0, 0, 0, 0, 1, 0]]} {[[['DA', ['DA', 1], 'd1']], [['DA', ['DA', 1], 'd0']]]} {[[5, ['-', 1], 0], [0, ['+', 0], 0]]}"
connectorName, states, startState, ports, DA, relations, DS = translateString(inputEx)

#translate(connectorName, states, startState, ports, DA, relations, DS)

#Output example:
# Inductive delayStates : Type := do | d1.

# Inductive delayPorts : Type := DA | DB.

# Definition dataAssignmentDA n :=
#   match n with
#   | 0 => 1
#   | 1 => 1
#   | 2 => 1
#   | 3 => 1
#   | 4 => 0
#   | S n => 1
#   end.

# Definition dataAssignmentDB n :=
#   match n with
#   | 0 => 0
#   | 1 => 0
#   | 2 => 0
#   | 3 => 0
#   | 4 => 1
#   | S n => 0
#   end.



# Definition timeStampdelayDA (n:nat) : QArith_base.Q :=
#   match n with
#   | 0 => 1#1
#   | 1 => 3#1
#   | 2 => 5#1
#   | 3 => 7#1
#   | 4 => 9#1
#   | S n => Z.of_N (N.of_nat(S n)) + 10#1
#   end.

# Definition timeStampdelayDB (n:nat) : QArith_base.Q :=
#   match n with
#   | 0 => 1#1
#   | 1 => 3#1
#   | 2 => 5#1
#   | 3 => 7#1
#   | 4 => 9#1
#   | S n => Z.of_N (N.of_nat(S n)) + 10#1
#   end.



# Lemma timeStampdelayDAHolds : forall n, Qlt (timeStampdelayDA n) (timeStampdelayDA(S n)).
#  Proof.
#  intros. destruct n. unfold timeStampdelayDA. reflexivity.
# unfold timeStampdelayDA. case(n). reflexivity.
# intros n0. case (n0). reflexivity.
# intros n1. case (n1). reflexivity.
# intros n2. case (n2). reflexivity.
# intros n3. case (n3). reflexivity.
# intros n4. unfold Qlt. apply orderZofNat.  Defined.

# Lemma timeStampdelayDBHolds : forall n, Qlt (timeStampdelayDB n) (timeStampdelayDB(S n)).
#  Proof.
#  intros. destruct n. unfold timeStampdelayDB. reflexivity.
# unfold timeStampdelayDB. case(n). reflexivity.
# intros n0. case (n0). reflexivity.
# intros n1. case (n1). reflexivity.
# intros n2. case (n2). reflexivity.
# intros n3. case (n3). reflexivity.
# intros n4. unfold Qlt. apply orderZofNat.  Defined.



# Definition portDA := {|
# ConstraintAutomata.id := DA;
# ConstraintAutomata.dataAssignment := dataAssignmentDA;
# ConstraintAutomata.timeStamp := timeStampdelayDA;
# ConstraintAutomata.tdsCond := timeStampdelayDAHolds;
# ConstraintAutomata.index := 0 |}.

# Definition portDB := {|
# ConstraintAutomata.id := DB;
# ConstraintAutomata.dataAssignment := dataAssignmentDB;
# ConstraintAutomata.timeStamp := timeStampdelayDB;
# ConstraintAutomata.tdsCond := timeStampdelayDBHolds;
# ConstraintAutomata.index := 0 |}.



# Definition delayPortsList := [portDA;portDB].

# Definition delayRel (s: delayStates) :
# set (set delayPorts * ConstraintAutomata.DC delayPorts nat * delayStates) :=
#   match s with
#   |  do => [([DA], (ConstraintAutomata.DC DA 1 ), d1)]
#   |  d1 => [([DA], (ConstraintAutomata.DC DA 1 ), d0)]
# end.

# Definition delayCA := {|
#   ConstraintAutomata.Q := [DA;DB];
#   ConstraintAutomata.N := [do;d1];
#   ConstraintAutomata.T := delayRel;
#   ConstraintAutomata.Q0 := [d0]
# |}

# Definition delayStatesList := [do;d1].

# Definition doFlowFunction (n: nat) : nat :=
#   match n with
#   | 0 => 5
#   | n => n - 1
# end.

# Definition d1FlowFunction (n: nat) : nat :=
#   match n with
#   | 0 => 0
#   | n => n + 0
# end.



# Definition doDS := (5, doFlowFunction, 5, 0).
# Definition d1DS := (0, d1FlowFunction, 0, 0).


# Definition delayDSList := [doDS; d1DS].