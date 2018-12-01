Require Import CaMain.

(* Alternating Bit Protocol *)

Inductive transformState := q0ls.
Instance transformStateEq : EqDec transformState eq := 
	{equiv_dec x y := 
		match x, y with 
		| q0ls,q0ls => in_left 
    end
	}.

   Proof.
   all: congruence.
   Defined.


Inductive abpStates := s0 | s1 | r0 | r1.
Inductive abpPorts := A | B | C.

Instance abpStatesEq : EqDec abpStates eq := 
	{equiv_dec x y := 
		match x, y with 
		| s0,s0 => in_left 
		| s1,s1 => in_left 
		| r0,r0 => in_left 
		| r1,r1 => in_left 
		| s0,s1 => in_right 
		| s0,r0 => in_right 
		| s0,r1 => in_right 
		| s1,s0 => in_right 
		| s1,r0 => in_right 
		| s1,r1 => in_right 
		| r0,s0 => in_right 
		| r0,s1 => in_right 
		| r0,r1 => in_right 
		| r1,s0 => in_right 
		| r1,s1 => in_right 
		| r1,r0 => in_right 
		end 
	}.
   Proof.
   all: congruence.
   Defined.

Instance abpPortsEq : EqDec abpPorts eq := 
	{equiv_dec x y := 
		match x, y with 
		| A,A => in_left 
		| B,B => in_left 
    | C,C => in_left
		| A,B => in_right 
		| B,A => in_right 
    | A,C | C, A | B , C | C, B => in_right
		end
	}.
  Proof.
  all:congruence.
  Defined.

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

  (* Definition timeStampABPA(n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | 1 =>  4#1
    | 2 =>  7#1
    | 3 =>  10#1
    | 4 =>  13#1
    | 5 =>  15#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1 
    end. *)

   Definition timeStampABPA(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1 
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampABPB (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Lemma timeStampTestABPAHolds : forall n, Qle (timeStampABPA n) (timeStampABPA (S n)).
  Proof.
  Admitted.

  Lemma timeStampTestABPBHolds : forall n, 
    Qle (timeStampABPB n) (timeStampABPB (S n)). 
  Proof.
  Admitted.

  Definition portAP := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampABPA;
        ConstraintAutomata.portCond := timeStampTestABPAHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBP := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampABPB;
        ConstraintAutomata.portCond := timeStampTestABPBHolds;
        ConstraintAutomata.index := 0 |}.

    Definition transformFunction (n:option nat) :=
    match n with
      | Some n => Some (n + 1)
      | None =>  None
    end.

    Definition transformCaBehavior (s: transformState) :=
    match s with
    | q1T => [([A;B] , ConstraintAutomata.trDc transformFunction A B, [q0ls])]
    end.

  (* A transform B *)
  Definition transformCA := {|
    ConstraintAutomata.Q := [q0ls];
    ConstraintAutomata.N := [A;B];
    ConstraintAutomata.T := transformCaBehavior;
    ConstraintAutomata.Q0 := [q0ls]
  |}.

  Eval compute in ConstraintAutomata.T transformCA.


  (*B lossySync C*)

  Inductive lossySyncStates := q0.

  Instance lossySyncStateEq: EqDec lossySyncStates eq :=
    {equiv_dec x y := 
      match x,y with
      | q0, q0 => in_left
      end }.
   Proof.
   reflexivity.
   Defined.

   Definition dataAssignmentLossySyncBoth n := 
    match n with
    | 0 => Some 0
    | 1 => Some 1
    | S n => Some (1)
    end.

  Definition timeStampLossyA (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampLossyB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  4#1
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
    | q0 => [([B;C] , ConstraintAutomata.eqDc nat B C, [q0]);
             ([B], (ConstraintAutomata.tDc abpPorts nat), [q0])] 
    end.

  Definition lossySyncCA := {|
    ConstraintAutomata.Q := [q0];
    ConstraintAutomata.N := [B;C];
    ConstraintAutomata.T := lossySyncCaBehavior;
    ConstraintAutomata.Q0 := [q0]
  |}.


  (* C lossySync A*)
  Inductive lossySyncStates2 := q02.

  Instance lossySyncState2Eq: EqDec lossySyncStates2 eq :=
    {equiv_dec x y := 
      match x,y with
      | q02, q02 => in_left
      end }.
   Proof.
   reflexivity.
   Defined.


  Definition lossySync2CaBehavior (s: lossySyncStates2) :=
    match s with
    | q02 => [([C;A] , ConstraintAutomata.eqDc nat C A, [q02]);
             ([C], (ConstraintAutomata.tDc abpPorts nat), [q02])] 
    end.

  Definition lossySync2CA := {|
    ConstraintAutomata.Q := [q02];
    ConstraintAutomata.N := [C;A];
    ConstraintAutomata.T := lossySync2CaBehavior;
    ConstraintAutomata.Q0 := [q02]
  |}.

  (*The product Automaton can be obtained by the product construction of the three automata above *)
  Definition transformLossySyncProduct := ProductAutomata.buildPA transformCA lossySyncCA.
  Definition resultingPaAbp := ProductAutomata.buildPA transformLossySyncProduct lossySync2CA.

  Eval compute in ConstraintAutomata.T transformLossySyncProduct (q0ls, q0).
  Eval compute in ConstraintAutomata.T resultingPaAbp (q0ls,q0,q02).
  