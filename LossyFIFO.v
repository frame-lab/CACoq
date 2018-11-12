Require Import CaMain.

(* LossySync Channel CA *)

  Inductive lossySyncStates := q0 | q0F | p0F | p1F.

  Inductive lossySyncPorts := A | B | AF | BF.

  Instance statesEq : EqDec lossySyncStates eq := 
	{equiv_dec x y := 
		match x, y with 
		| q0,q0 => in_left 
		| q0F,q0F => in_left 
		| p0F,p0F => in_left 
		| p1F,p1F => in_left 
		| q0,q0F => in_right 
		| q0,p0F => in_right 
		| q0,p1F => in_right 
		| q0F,q0 => in_right 
		| q0F,p0F => in_right 
		| q0F,p1F => in_right 
		| p0F,q0 => in_right 
		| p0F,q0F => in_right 
		| p0F,p1F => in_right 
		| p1F,q0 => in_right 
		| p1F,q0F => in_right 
		| p1F,p0F => in_right 
		end 
	}.
  Proof.
  all: congruence.
  Defined.

  Instance portsEq : EqDec lossySyncPorts eq := 
	{equiv_dec x y := 
		match x, y with 
		| A,A => in_left 
		| B,B => in_left 
		| AF,AF => in_left 
		| BF,BF => in_left 
		| A,B => in_right 
		| A,AF => in_right 
		| A,BF => in_right 
		| B,A => in_right 
		| B,AF => in_right 
		| B,BF => in_right 
		| AF,A => in_right 
		| AF,B => in_right 
		| AF,BF => in_right 
		| BF,A => in_right 
		| BF,B => in_right 
		| BF,AF => in_right 
		end 
	}.
  Proof.
  all: congruence.
  Defined.

   Definition dataAssignmentLossySyncBoth n := 
    match n with
    | 0 => Some 0
    | 1 => Some 1
    | S n => Some (1)
    end.

  Definition timeStampLossyA (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  0#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampLossyB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Lemma timeStampTestHoldsLossyA: forall n, 
    Qle (timeStampLossyA n) (timeStampLossyA (S n)). 
  Proof. Admitted.

  Lemma timeStampTestHoldsLossyB: forall n, 
    Qle (timeStampLossyB n) (timeStampLossyB (S n)).
  Proof. Admitted.

  Definition lossySyncCaBehavior (s: lossySyncStates) :=
    match s with
    | q0 => [([A;B] , ConstraintAutomata.eqDc nat A B, [q0]);
             ([A], (ConstraintAutomata.tDc lossySyncPorts nat), [q0])] 
    | _ => []
    end.

  (* The CA itself is formalized as *)
  Definition lossySyncCA := {|
    ConstraintAutomata.Q := [q0];
    ConstraintAutomata.N := [A;B];
    ConstraintAutomata.T := lossySyncCaBehavior;
    ConstraintAutomata.Q0 := [q0]
  |}.

  Definition portA := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentLossySyncBoth;
        ConstraintAutomata.timeStamp := timeStampLossyA;
        ConstraintAutomata.portCond := timeStampTestHoldsLossyA;
        ConstraintAutomata.index := 0 |}.

  Definition portB:= {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentLossySyncBoth;
        ConstraintAutomata.timeStamp := timeStampLossyB;
        ConstraintAutomata.portCond := timeStampTestHoldsLossyB;
        ConstraintAutomata.index := 0 |}.

  Eval compute in ConstraintAutomata.run lossySyncCA [portA;portB] 10. (*does not accept the TDS composed by portA and portB because
                                                                            B has data in theta.time, which is not comprised by the automaton's transitions *)
  
  (* FIFO CA *)

  (* Inductive FIFOStates : Type := q0F | p0F | p1F.
  Inductive FIFOports : Type := AF | BF.
  Instance portsEq : EqDec FIFOports eq :=
    {equiv_dec x y := 
      match x,y with
      | AF,AF | BF,BF => in_left
      | AF,BF | BF,AF => in_right
      end }.
   Proof.
   all: congruence.
   Defined. *)

  Definition dataAssignmentA n := 
    match n with
    | 0 => Some 0
    | 1 => Some 0
    | 2 => Some 1 
    | S n => Some (1)
    end.

  Definition dataAssignmentB n :=
    match n with
    | 0 => Some 0
    | 1 => Some (0)
    | 2 => Some 1
    (*| 3 | 4 | 5 => Some 1
    | 6 => None *)
    | S n => Some 1
    end.

  Definition timeStampFIFOA(n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | 1 =>  3#1
    | 2 =>  5#1
    | 3 =>  7#1
    | 4 =>  9#1
    | 5 =>  11#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1 
    end.

  Definition timeStampFIFOB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  2#1 (*1#1*)
    | 1 =>  4#1
    | 2 => 6#1
    | 3 => 8#1
    | 4 => 10#1
    | 5 => 12#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Lemma timeStampTestFIFOAHolds : forall n, Qle (timeStampFIFOA n) (timeStampFIFOA (S n)).
  Proof.
  induction n. 
  + unfold timeStampTest. cbv. intros. inversion H.
  + unfold timeStampTest. (*alguma tática de ring em cima de Q deve resolver aqui. procurar depois *)
  Admitted.

  Lemma timeStampTestFIFOBHolds : forall n, 
    Qle (timeStampFIFOB n) (timeStampFIFOB (S n)). 
  Proof.
  Admitted.

  Definition portAF := {|
        ConstraintAutomata.id := AF;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampFIFOA;
        ConstraintAutomata.portCond := timeStampTestFIFOAHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBF := {|
        ConstraintAutomata.id := BF;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampFIFOB;
        ConstraintAutomata.portCond := timeStampTestFIFOBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition realports := [portAF;portBF].

  (* A transition is defined as a subset of states x a set of record ports as defined by the           *)
  (* Record port in ConstraintAutomata, a data constraint which is represented by a bool (in           *)
  (* execution time it may always be satisfied, i.e., the data constraint needs to be true             *)
  (* in order to the transition to be triggered.                                                       *)
  (* Ideia: Montar a DC como um conjunto de transições associado à cada porta como um par (porta,dado).*)
  (* Assim, basta apenas pegar a porta e o dado correspondente em thetaDelta e comparar.               *)
  (* TODO *)
  (* Trnasições podem ser vistas como sendo um conjunto de transições a partir do estado ver NFA-e de RGCoq  *)
  (* Se optarmos por usar o tipo indutivo transition definido no modulo ConstraintAutomata, seria necessário *)
  (* pegar transições como parâmetros de entrada pra função abaixo (solução 1)                         *)

  (* ERICK: esse k abaixo é justamente o índice l_i tal que a(l_i) = teta.time(k), para algum l_i \in [0,1,...]*)
  (* NOTA: k abaixo náo é dado como parâmetro, é o índice da porta a ser avaliado. *)
  Definition oneBoundedFIFOrel (s:lossySyncStates) 
  (*set (set (ports) * ConstraintAutomata.DC ports (option nat) * set states)*) :=
    match s with
    | q0F => [([AF], (ConstraintAutomata.dc AF (Some 0)), [p0F]) ;
              ([AF], (ConstraintAutomata.dc AF (Some 1)), [p1F])]
    | p0F => [([BF], (ConstraintAutomata.dc BF (Some 0)), [q0F])]
    | p1F => [([BF], (ConstraintAutomata.dc BF (Some 1)), [q0F])] 
    | q0 => []
    end.

  (* falta definir transição para começar a brncar com a run.                                      *)
  Definition oneBoundedFIFOCA:= {|
    ConstraintAutomata.Q := [q0F;p0F;p1F];
    ConstraintAutomata.N := [AF;BF];
    ConstraintAutomata.T := oneBoundedFIFOrel;
    ConstraintAutomata.Q0 := [q0F]
  |}.

  Eval compute in ConstraintAutomata.run oneBoundedFIFOCA realports 8.


  (* The product construction of them can be acheived with *)

  Definition lossyFIFO := ProductAutomata.buildPA lossySyncCA oneBoundedFIFOCA.

  Definition timeStampLossyAF (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.


   Definition timeStampLossyBF (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  3#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

   Lemma timeStampTestHoldsLossyAF: forall n, 
     Qle (timeStampLossyAF n) (timeStampLossyAF (S n)). 
   Proof. Admitted.

  Definition portR1:= {|
      ConstraintAutomata.id := A;
      ConstraintAutomata.dataAssignment := dataAssignmentLossySyncBoth;
      ConstraintAutomata.timeStamp := timeStampLossyA;
      ConstraintAutomata.portCond := timeStampTestHoldsLossyA;
      ConstraintAutomata.index := 0 |}.

  Definition portR2:= {|
      ConstraintAutomata.id := B;
      ConstraintAutomata.dataAssignment := dataAssignmentLossySyncBoth;
      ConstraintAutomata.timeStamp := timeStampLossyB;
      ConstraintAutomata.portCond := timeStampTestHoldsLossyB;
      ConstraintAutomata.index := 0 |}.
  Definition portR3:= {|
      ConstraintAutomata.id := AF;
      ConstraintAutomata.dataAssignment := dataAssignmentLossySyncBoth;
      ConstraintAutomata.timeStamp := timeStampLossyB;
      ConstraintAutomata.portCond := timeStampTestHoldsLossyB;
      ConstraintAutomata.index := 0 |}.
  Definition portR4:= {|
      ConstraintAutomata.id := BF;
      ConstraintAutomata.dataAssignment := dataAssignmentLossySyncBoth;
      ConstraintAutomata.timeStamp := timeStampLossyB;
      ConstraintAutomata.portCond := timeStampTestHoldsLossyB;
      ConstraintAutomata.index := 0 |}.

   Eval compute in ConstraintAutomata.run lossyFIFO [portR1;portR2;portR3;portR4] 10.  
   Eval compute in ConstraintAutomata.T lossyFIFO (q0, q0F).