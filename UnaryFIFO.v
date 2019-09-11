Require Import CaMain.
Require Import ReoCA.

(* An unary FIFO as a simple example *)
Inductive automatonStates := q0 | q1.
Inductive automatonPorts := A | B.

Instance automatonStatesEq : EqDec automatonStates eq := 
	{equiv_dec x y := 
		match x, y with 
		| q0,q0 => in_left 
		| q1, q1 => in_left
    | q0,q1 | q1,q0 => in_right
		end 
	}.
   Proof.
   all: congruence.
   Defined.

Instance automatonPortsEq : EqDec automatonPorts eq := 
	{equiv_dec x y := 
		match x, y with 
		| A,A => in_left 
		| B,B => in_left 
		| A,B => in_right 
		| B,A => in_right 
		end 
	}.
  Proof.
  all:congruence.
  Defined.

  Definition dataAssignmentA n := 
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S n =>  0
    end.

  Definition dataAssignmentB n :=
    match n with
    | 0 =>  1
    | 1 =>  (1)
    | 2 =>  0
    | S n =>  0
    end.

   Definition timeStampAutomatonA(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1 
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat (S n) + 16#1 
    end.

  Definition timeStampAutomatonB (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 9#1
    | 3 => 12#1
    | 4 => 15#1
    | 5 => 18#1
    | S n =>  Z.of_nat(S n) + 170#1
    end.


  Lemma timeStampAutomatonAHolds : forall n, 
    Qlt (timeStampAutomatonA n) (timeStampAutomatonA (S n)).
  Proof.
  intros. destruct n. unfold timeStampAutomatonA. reflexivity.
  unfold timeStampAutomatonA. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.
  
  Lemma timeStampAutomatonBHolds : forall n, 
    Qlt (timeStampAutomatonB n) (timeStampAutomatonB (S n)). 
  Proof.
  intros. destruct n. unfold timeStampAutomatonB. reflexivity.
  unfold timeStampAutomatonB. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. apply orderZofNat. Defined.


  Definition portA := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampAutomatonA;
        ConstraintAutomata.portCond := timeStampAutomatonAHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portB := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampAutomatonB;
        ConstraintAutomata.portCond := timeStampAutomatonBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition automatonTransition (s:automatonStates):=
    match s with
    | q0 => [([A], (ConstraintAutomata.tDc automatonPorts nat), q1)]
    | q1 => [([B], (ConstraintAutomata.tDc automatonPorts nat), q0)]
   
    end.

  Definition unaryFIFO := ReoCa.ReoCABinaryChannel A B [q0;q1] [q0] automatonTransition.

  (* Structural Properties *) 

  (* For any transtition from a starting state, it must have data only in A and accept any data *)
  (* (its guard condition equals true) *)
  Lemma initialStateData : forall st, In st (ConstraintAutomata.Q0(unaryFIFO))  -> forall t,
    In t ((ConstraintAutomata.T unaryFIFO) st) -> fst(fst(t)) = [A] /\ snd(fst(t)) = ConstraintAutomata.tDc _ _.
  Proof.
  intros.
  destruct st.
  - simpl in H0. destruct H0. rewrite <- H0. simpl. split; reflexivity. inversion H0.
  - simpl in H. destruct H. inversion H. inversion H.
  Qed.

  (* The automaton will empty its data item only when data flows through port B, returning *)
  (* to its initial state                                                                  *)

  Lemma emptyTheAutomaton: forall st, forall t, st = q1 /\ In t (ConstraintAutomata.T unaryFIFO st) -> 
                           fst(fst(t)) = [B] /\  
                           snd(fst(t)) = ConstraintAutomata.tDc _ _ /\
                           In (snd(t)) (ConstraintAutomata.Q0 unaryFIFO).
  Proof.
  intros. destruct H. rewrite H in H0. simpl in H0. destruct H0.
  - rewrite <- H0. split. reflexivity. split. reflexivity. simpl. left. reflexivity.
  - inversion H0.
  Qed.


  Eval compute in ConstraintAutomata.run unaryFIFO [portA;portB] 11.
