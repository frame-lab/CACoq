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
Inductive abpPorts := A | B | C | D | E | F.

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
    | D,D => in_left
    | E,E => in_left
    | F,F => in_left
		| A,B => in_right 
		| B,A => in_right 
    | F,A | F,B | B,F | A,F => in_right
    | D,C | C, D | D,E | E,D => in_right
    | A,C | C, A | B ,C | C, B => in_right
    | A,D | A, E | E,A | D,A  => in_right
    | B,D | B, E | E,B | D,B  => in_right
    | D,F | F,D | F, E | E,F | C,F | F,C | C, E | E,C => in_right
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
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

  Definition dataAssignmentC n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

  Definition dataAssignmentD n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

  Definition dataAssignmentE n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

  Definition dataAssignmentF n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

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


  Definition timeStampABPC (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampABPD (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampABPE (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampABPF (n:nat) : QArith_base.Q :=
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

  Lemma timeStampABPCHolds : forall n, 
    Qle (timeStampABPC n) (timeStampABPC (S n)). 
  Proof.
  Admitted.

  Lemma timeStampABPDHolds : forall n, 
    Qle (timeStampABPD n) (timeStampABPD (S n)). 
  Proof.
  Admitted.

  Lemma timeStampABPEHolds : forall n, 
    Qle (timeStampABPE n) (timeStampABPB (S n)). 
  Proof.
  Admitted.

  Lemma timeStampABPFHolds : forall n, 
    Qle (timeStampABPF n) (timeStampABPF (S n)). 
  Proof.
  Admitted.

  Definition portA := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampABPA;
        ConstraintAutomata.portCond := timeStampTestABPAHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portB := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampABPB;
        ConstraintAutomata.portCond := timeStampTestABPBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portC := {|
        ConstraintAutomata.id := C;
        ConstraintAutomata.dataAssignment := dataAssignmentC;
        ConstraintAutomata.timeStamp := timeStampABPC;
        ConstraintAutomata.portCond := timeStampABPCHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portD := {|
        ConstraintAutomata.id := D;
        ConstraintAutomata.dataAssignment := dataAssignmentD;
        ConstraintAutomata.timeStamp := timeStampABPD;
        ConstraintAutomata.portCond := timeStampABPDHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portE := {|
        ConstraintAutomata.id := E;
        ConstraintAutomata.dataAssignment := dataAssignmentE;
        ConstraintAutomata.timeStamp := timeStampABPE;
        ConstraintAutomata.portCond := timeStampABPEHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portF := {|
        ConstraintAutomata.id := F;
        ConstraintAutomata.dataAssignment := dataAssignmentF;
        ConstraintAutomata.timeStamp := timeStampABPF;
        ConstraintAutomata.portCond := timeStampABPFHolds;
        ConstraintAutomata.index := 0 |}.

    Definition transformFunction (n:option nat) :=
    match n with
      | Some n => Some (n + 1)
      | None =>  None
    end.

  Definition transformCaBehavior (s: transformState) :=
    match s with
    | q0ls => [([A;B] , ConstraintAutomata.trDc transformFunction A B, [q0ls])]
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


  (* D lossySync E*)
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
    | q02 => [([D;E] , ConstraintAutomata.eqDc nat D E, [q02]);
             ([D], (ConstraintAutomata.tDc abpPorts nat), [q02])] 
    end.

  Definition lossySync2CA := {|
    ConstraintAutomata.Q := [q02];
    ConstraintAutomata.N := [D;E];
    ConstraintAutomata.T := lossySync2CaBehavior;
    ConstraintAutomata.Q0 := [q02]
  |}.


  (* E filter F *)

  Inductive filterStates3 := q03.

  Instance filterState3Eq: EqDec filterStates3 eq :=
    {equiv_dec x y := 
      match x,y with
      | q03, q03 => in_left
      end }.
   Proof.
   reflexivity.
   Defined.


  Definition filterCaBehavior (s: filterStates3) :=
    match s with
    | q03 => [([E;F] , ConstraintAutomata.andDc (ConstraintAutomata.eqDc nat E B) 
                                                 (ConstraintAutomata.eqDc nat E F), [q03]);
              ([E] , ConstraintAutomata.negDc (ConstraintAutomata.eqDc nat E B), [q03])]
    end.

  Definition filterCA := {|
    ConstraintAutomata.Q := [q03];
    ConstraintAutomata.N := [E;F];
    ConstraintAutomata.T := filterCaBehavior;
    ConstraintAutomata.Q0 := [q03]
  |}.


  (*The product Automaton can be obtained by the product construction of the three automata above *)
  Definition filterLossySyncProduct := ProductAutomata.buildPA transformCA lossySyncCA.
  Definition filterLossySyncProduct2 := ProductAutomata.buildPA lossySync2CA filterCA.
  Definition resultingPaAbp := ProductAutomata.buildPA filterLossySyncProduct filterLossySyncProduct2.

  Eval compute in ConstraintAutomata.T filterLossySyncProduct (q0ls, q0).
  Eval compute in ConstraintAutomata.T filterLossySyncProduct2 (q02, q03).
  Eval compute in ConstraintAutomata.Q resultingPaAbp.
  Eval compute in ConstraintAutomata.T resultingPaAbp (q0ls, q0, (q02, q03)).

  (* Ex 1*)
  Definition tdsRun1 := [portA;portB;portC;portD;portE;portF].
  Definition steamAcce := Eval compute in ConstraintAutomata.run resultingPaAbp tdsRun1 3.
  Lemma streamAccept8 : ~ In ([]) (steamAcce).
  Proof. unfold not. unfold steamAcce. simpl. intros. repeat (destruct H ; inversion H). Defined.


  Definition dataAssignmentA2 n := 
    match n with
    | 0 => Some 0
    | 1 => Some 0
    | 2 => Some 1
    | S n => Some (1)
    end.

  Definition dataAssignmentB2 n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

  Definition dataAssignmentC2 n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

  Definition dataAssignmentD2 n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

  Definition dataAssignmentE2 n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

  Definition dataAssignmentF2 n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

   Definition timeStampABPA2(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1 
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampABPB2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.


  Definition timeStampABPC2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampABPD2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#10
    | 1 => 5#10
    | 2 => 8#10
    | 3 => 11#10
    | 4 => 14#10
    | 5 => 17#10
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampABPE2(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampABPF2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.


  Lemma timeStampTestABPAHolds2 : forall n, Qle (timeStampABPA2 n) (timeStampABPA2 (S n)).
  Proof.
  Admitted.

  Lemma timeStampTestABPBHolds2 : forall n, 
    Qle (timeStampABPB2 n) (timeStampABPB2 (S n)). 
  Proof.
  Admitted.

  Lemma timeStampABPCHolds2 : forall n, 
    Qle (timeStampABPC2 n) (timeStampABPC2 (S n)). 
  Proof.
  Admitted.

  Lemma timeStampABPDHolds2 : forall n, 
    Qle (timeStampABPD2 n) (timeStampABPD2 (S n)). 
  Proof.
  Admitted.

  Lemma timeStampABPEHolds2 : forall n, 
    Qle (timeStampABPE2 n) (timeStampABPB2 (S n)). 
  Proof.
  Admitted.

  Lemma timeStampABPFHolds2 : forall n, 
    Qle (timeStampABPF2 n) (timeStampABPF2 (S n)). 
  Proof.
  Admitted.

  Definition portA2 := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA2;
        ConstraintAutomata.timeStamp := timeStampABPA2;
        ConstraintAutomata.portCond := timeStampTestABPAHolds2;
        ConstraintAutomata.index := 0 |}.

  Definition portB2 := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB2;
        ConstraintAutomata.timeStamp := timeStampABPB2;
        ConstraintAutomata.portCond := timeStampTestABPBHolds2;
        ConstraintAutomata.index := 0 |}.

  Definition portC2 := {|
        ConstraintAutomata.id := C;
        ConstraintAutomata.dataAssignment := dataAssignmentC2;
        ConstraintAutomata.timeStamp := timeStampABPC2;
        ConstraintAutomata.portCond := timeStampABPCHolds2;
        ConstraintAutomata.index := 0 |}.

  Definition portD2 := {|
        ConstraintAutomata.id := D;
        ConstraintAutomata.dataAssignment := dataAssignmentD2;
        ConstraintAutomata.timeStamp := timeStampABPD2;
        ConstraintAutomata.portCond := timeStampABPDHolds2;
        ConstraintAutomata.index := 0 |}.

  Definition portE2 := {|
        ConstraintAutomata.id := E;
        ConstraintAutomata.dataAssignment := dataAssignmentE2;
        ConstraintAutomata.timeStamp := timeStampABPE2;
        ConstraintAutomata.portCond := timeStampABPEHolds2;
        ConstraintAutomata.index := 0 |}.

  Definition portF2 := {|
        ConstraintAutomata.id := F;
        ConstraintAutomata.dataAssignment := dataAssignmentF2;
        ConstraintAutomata.timeStamp := timeStampABPF2;
        ConstraintAutomata.portCond := timeStampABPFHolds2;
        ConstraintAutomata.index := 0 |}.

  (* Ex 2 *)
  Definition input2 := [portA2;portB2;portC2;portD2;portE2;portF2].
  Definition onlyDHasData := Eval compute in ConstraintAutomata.run resultingPaAbp input2 5.
  Definition onlyDwithData : ~ In [] onlyDHasData.
  Proof. unfold not. unfold steamAcce. simpl. intros. repeat (destruct H ; inversion H). Defined.


  Definition dataAssignmentA3 n := 
    match n with
    | 0 => Some 0
    | 1 => Some 0
    | 2 => Some 1
    | S n => Some (1)
    end.

  Definition dataAssignmentB3 n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

  Definition dataAssignmentC3 n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

  Definition dataAssignmentD3 n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

  Definition dataAssignmentE3 n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

  Definition dataAssignmentF3 n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

   Definition timeStampABPA3(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1 
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampABPB3 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.


  Definition timeStampABPC3 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampABPD3 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampABPE3(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 5#1
    | 2 => 8#10
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampABPF3 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.


  Lemma timeStampTestABPAHolds3 : forall n, Qle (timeStampABPA2 n) (timeStampABPA2 (S n)).
  Proof.
  Admitted.

  Lemma timeStampTestABPBHolds3 : forall n, 
    Qle (timeStampABPB3 n) (timeStampABPB3 (S n)). 
  Proof.
  Admitted.

  Lemma timeStampABPCHolds3 : forall n, 
    Qle (timeStampABPC3 n) (timeStampABPC3 (S n)). 
  Proof.
  Admitted.

  Lemma timeStampABPDHolds3: forall n, 
    Qle (timeStampABPD3 n) (timeStampABPD3 (S n)). 
  Proof.
  Admitted.

  Lemma timeStampABPEHolds3 : forall n, 
    Qle (timeStampABPE3 n) (timeStampABPE3 (S n)). 
  Proof.
  Admitted.

  Lemma timeStampABPFHolds3 : forall n, 
    Qle (timeStampABPF3 n) (timeStampABPF3 (S n)). 
  Proof.
  Admitted.

  Definition portA3 := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA3;
        ConstraintAutomata.timeStamp := timeStampABPA3;
        ConstraintAutomata.portCond := timeStampTestABPAHolds3;
        ConstraintAutomata.index := 0 |}.

  Definition portB3 := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB3;
        ConstraintAutomata.timeStamp := timeStampABPB3;
        ConstraintAutomata.portCond := timeStampTestABPBHolds3;
        ConstraintAutomata.index := 0 |}.

  Definition portC3 := {|
        ConstraintAutomata.id := C;
        ConstraintAutomata.dataAssignment := dataAssignmentC3;
        ConstraintAutomata.timeStamp := timeStampABPC3;
        ConstraintAutomata.portCond := timeStampABPCHolds3;
        ConstraintAutomata.index := 0 |}.

  Definition portD3 := {|
        ConstraintAutomata.id := D;
        ConstraintAutomata.dataAssignment := dataAssignmentD3;
        ConstraintAutomata.timeStamp := timeStampABPD3;
        ConstraintAutomata.portCond := timeStampABPDHolds3;
        ConstraintAutomata.index := 0 |}.

  Definition portE3 := {|
        ConstraintAutomata.id := E;
        ConstraintAutomata.dataAssignment := dataAssignmentE3;
        ConstraintAutomata.timeStamp := timeStampABPE3;
        ConstraintAutomata.portCond := timeStampABPEHolds3;
        ConstraintAutomata.index := 0 |}.

  Definition portF3 := {|
        ConstraintAutomata.id := F;
        ConstraintAutomata.dataAssignment := dataAssignmentF3;
        ConstraintAutomata.timeStamp := timeStampABPF3;
        ConstraintAutomata.portCond := timeStampABPFHolds3;
        ConstraintAutomata.index := 0 |}.
  
  (* Ex 3 *)
  Definition input3 := [portA3;portB3;portC3;portD3;portE3;portF3].
  Definition runAbpCAnotAccept := Eval compute in ConstraintAutomata.run resultingPaAbp input3 6.
  Lemma runAbpCAnotAc : In [] runAbpCAnotAccept.
  Proof. simpl;auto. Defined.