Require Import CaMain.
Open Scope Q_scope.
Axiom orderZofNat : forall n, forall a, Z.of_nat (S n) + a # 1 <= Z.of_nat (S (S n)) + a # 1.
Close Scope Q_scope.

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

Inductive alternatorStates := s0 | q0a | p0a| p1a.
Inductive alternatorPorts := A | B | C | D | E | F | G | H | I | J | K.

Instance alternatorStatesEq : EqDec alternatorStates eq := 
	{equiv_dec x y := 
		match x, y with 
		| s0,s0 => in_left 
		| q0a,q0a => in_left 
		| p0a,p0a => in_left 
		| p1a,p1a => in_left 
		| s0,q0a => in_right 
		| s0,p0a => in_right 
		| s0,p1a => in_right 
		| q0a,s0 => in_right 
		| q0a,p0a => in_right 
		| q0a,p1a => in_right 
		| p0a,s0 => in_right 
		| p0a,q0a => in_right 
		| p0a,p1a => in_right 
		| p1a,s0 => in_right 
		| p1a,q0a => in_right 
		| p1a,p0a => in_right 
		end 
	}.
   Proof.
   all: congruence.
   Defined.

Instance alternatorPortsEq : EqDec alternatorPorts eq := 
	{equiv_dec x y := 
		match x, y with 
		| A,A => in_left 
		| B,B => in_left 
		| C,C => in_left 
		| D,D => in_left 
		| E,E => in_left 
		| F,F => in_left 
		| G,G => in_left 
		| H,H => in_left 
		| I,I => in_left 
		| J,J => in_left 
		| K,K => in_left 
		| A,B => in_right 
		| A,C => in_right 
		| A,D => in_right 
		| A,E => in_right 
		| A,F => in_right 
		| A,G => in_right 
		| A,H => in_right 
		| A,I => in_right 
		| A,J => in_right 
		| A,K => in_right 
		| B,A => in_right 
		| B,C => in_right 
		| B,D => in_right 
		| B,E => in_right 
		| B,F => in_right 
		| B,G => in_right 
		| B,H => in_right 
		| B,I => in_right 
		| B,J => in_right 
		| B,K => in_right 
		| C,A => in_right 
		| C,B => in_right 
		| C,D => in_right 
		| C,E => in_right 
		| C,F => in_right 
		| C,G => in_right 
		| C,H => in_right 
		| C,I => in_right 
		| C,J => in_right 
		| C,K => in_right 
		| D,A => in_right 
		| D,B => in_right 
		| D,C => in_right 
		| D,E => in_right 
		| D,F => in_right 
		| D,G => in_right 
		| D,H => in_right 
		| D,I => in_right 
		| D,J => in_right 
		| D,K => in_right 
		| E,A => in_right 
		| E,B => in_right 
		| E,C => in_right 
		| E,D => in_right 
		| E,F => in_right 
		| E,G => in_right 
		| E,H => in_right 
		| E,I => in_right 
		| E,J => in_right 
		| E,K => in_right 
		| F,A => in_right 
		| F,B => in_right 
		| F,C => in_right 
		| F,D => in_right 
		| F,E => in_right 
		| F,G => in_right 
		| F,H => in_right 
		| F,I => in_right 
		| F,J => in_right 
		| F,K => in_right 
		| G,A => in_right 
		| G,B => in_right 
		| G,C => in_right 
		| G,D => in_right 
		| G,E => in_right 
		| G,F => in_right 
		| G,H => in_right 
		| G,I => in_right 
		| G,J => in_right 
		| G,K => in_right 
		| H,A => in_right 
		| H,B => in_right 
		| H,C => in_right 
		| H,D => in_right 
		| H,E => in_right 
		| H,F => in_right 
		| H,G => in_right 
		| H,I => in_right 
		| H,J => in_right 
		| H,K => in_right 
		| I,A => in_right 
		| I,B => in_right 
		| I,C => in_right 
		| I,D => in_right 
		| I,E => in_right 
		| I,F => in_right 
		| I,G => in_right 
		| I,H => in_right 
		| I,J => in_right 
		| I,K => in_right 
		| J,A => in_right 
		| J,B => in_right 
		| J,C => in_right 
		| J,D => in_right 
		| J,E => in_right 
		| J,F => in_right 
		| J,G => in_right 
		| J,H => in_right 
		| J,I => in_right 
		| J,K => in_right 
		| K,A => in_right 
		| K,B => in_right 
		| K,C => in_right 
		| K,D => in_right 
		| K,E => in_right 
		| K,F => in_right 
		| K,G => in_right 
		| K,H => in_right 
		| K,I => in_right 
		| K,J => in_right 
		end 
	}.
  Proof.
  all:congruence.
  Defined.

  Definition dataAssignmentA n := 
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 0
    | S n => Some 0
    end.

  Definition dataAssignmentB n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 0
    | S n => Some 0
    end.

  Definition dataAssignmentC n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 0
    | S n => Some 0
    end.

  Definition dataAssignmentD n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 0
    | S n => Some 0
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

  Definition dataAssignmentG n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 0
    | S n => Some 0
    end.

  Definition dataAssignmentH n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 2
    | S n => Some 2
    end.

  Definition dataAssignmentI n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 0
    | S n => Some 0
    end.

  Definition dataAssignmentJ n :=
    match n with
    | 0 => Some 1
    | 1 => Some (1)
    | 2 => Some 0
    | S n => Some 0
    end.

   Definition timeStampSequencerA(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1 
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat (S n) + 16#1 
    end.

  Definition timeStampSequencerB (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat(S n) + 17#1
    end.


  Definition timeStampSequencerC (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 3#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat(S n) + 18#1
    end.

  Definition timeStampSequencerD (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 4#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat(S n) + 19#1
    end.

  Definition timeStampSequencerE (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat(S n) + 17#1
    end.

  Definition timeStampSequencerG (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 3#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat(S n) + 18#1
    end.

  Definition timeStampSequencerH (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 4#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat(S n) + 19#1
    end.


  Lemma timeStampSequencerAHolds : forall n, Qle (timeStampSequencerA n) (timeStampSequencerA (S n)).
  Proof.
  intros. destruct n. unfold timeStampSequencerA. discriminate.
  unfold timeStampSequencerA. case (n). discriminate.
  intros n0. case (n0). discriminate.
  intros n1. case (n1). discriminate.
  intros n2. case (n2). discriminate.
  intros n3. case (n3). discriminate.
  intros n4. apply orderZofNat. Defined.
  
  Lemma timeStampSequencerBHolds : forall n, 
    Qle (timeStampSequencerB n) (timeStampSequencerB (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerB. discriminate.
  unfold timeStampSequencerB. case (n). discriminate.
  intros n0. case (n0). discriminate.
  intros n1. case (n1). discriminate.
  intros n2. case (n2). discriminate.
  intros n3. case (n3). discriminate.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerCHolds : forall n, 
    Qle (timeStampSequencerC n) (timeStampSequencerC (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerC. discriminate.
  unfold timeStampSequencerC. case (n). discriminate.
  intros n0. case (n0). discriminate.
  intros n1. case (n1). discriminate.
  intros n2. case (n2). discriminate.
  intros n3. case (n3). discriminate.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerDHolds : forall n, 
    Qle (timeStampSequencerD n) (timeStampSequencerD (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerD. discriminate.
  unfold timeStampSequencerD. case (n). discriminate.
  intros n0. case (n0). discriminate.
  intros n1. case (n1). discriminate.
  intros n2. case (n2). discriminate.
  intros n3. case (n3). discriminate.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerEHolds : forall n, 
    Qle (timeStampSequencerE n) (timeStampSequencerE (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerE. discriminate.
  unfold timeStampSequencerE. case (n). discriminate.
  intros n0. case (n0). discriminate.
  intros n1. case (n1). discriminate.
  intros n2. case (n2). discriminate.
  intros n3. case (n3). discriminate.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerGHolds : forall n, 
    Qle (timeStampSequencerG n) (timeStampSequencerG (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerG. discriminate.
  unfold timeStampSequencerG. case (n). discriminate.
  intros n0. case (n0). discriminate.
  intros n1. case (n1). discriminate.
  intros n2. case (n2). discriminate.
  intros n3. case (n3). discriminate.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerHHolds : forall n, 
    Qle (timeStampSequencerH n) (timeStampSequencerH (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerH. discriminate.
  unfold timeStampSequencerH. case (n). discriminate.
  intros n0. case (n0). discriminate.
  intros n1. case (n1). discriminate.
  intros n2. case (n2). discriminate.
  intros n3. case (n3). discriminate.
  intros n4. apply orderZofNat. Defined.

  Definition portA := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampSequencerA;
        ConstraintAutomata.portCond := timeStampSequencerAHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portB := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampSequencerB;
        ConstraintAutomata.portCond := timeStampSequencerBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portC := {|
        ConstraintAutomata.id := C;
        ConstraintAutomata.dataAssignment := dataAssignmentC;
        ConstraintAutomata.timeStamp := timeStampSequencerC;
        ConstraintAutomata.portCond := timeStampSequencerCHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portD := {|
        ConstraintAutomata.id := D;
        ConstraintAutomata.dataAssignment := dataAssignmentD;
        ConstraintAutomata.timeStamp := timeStampSequencerD;
        ConstraintAutomata.portCond := timeStampSequencerDHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portE := {|
        ConstraintAutomata.id := E;
        ConstraintAutomata.dataAssignment := dataAssignmentE;
        ConstraintAutomata.timeStamp := timeStampSequencerE;
        ConstraintAutomata.portCond := timeStampSequencerEHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portG := {|
        ConstraintAutomata.id := G;
        ConstraintAutomata.dataAssignment := dataAssignmentG;
        ConstraintAutomata.timeStamp := timeStampSequencerG;
        ConstraintAutomata.portCond := timeStampSequencerGHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portH := {|
        ConstraintAutomata.id := H;
        ConstraintAutomata.dataAssignment := dataAssignmentH;
        ConstraintAutomata.timeStamp := timeStampSequencerH;
        ConstraintAutomata.portCond := timeStampSequencerHHolds;
        ConstraintAutomata.index := 0 |}.

  (*A FIFO E *)
  Definition aToEFIFOrel (s:alternatorStates) :=
    match s with
    | q0a => [([A], (ConstraintAutomata.dc A (Some 0)), [p0a]) ;
              ([A], (ConstraintAutomata.dc A (Some 1)), [p1a])]
    | p0a => [([E], (ConstraintAutomata.dc E (Some 0)), [q0a])]
    | p1a => [([E], (ConstraintAutomata.dc E (Some 1)), [q0a])] 
    | s0 => []
    end.

  Definition aToEFIFOCA:= {|
    ConstraintAutomata.Q := [q0a;p0a;p1a];
    ConstraintAutomata.N := [A;E];
    ConstraintAutomata.T := aToEFIFOrel;
    ConstraintAutomata.Q0 := [q0a]
  |}.

  (*E FIFO G *)
  Definition eToGFIFOrel (s:alternatorStates) :=
    match s with
    | q0a => [([E], (ConstraintAutomata.dc E (Some 0)), [p0a]) ;
              ([E], (ConstraintAutomata.dc E (Some 1)), [p1a])]
    | p0a => [([G], (ConstraintAutomata.dc G (Some 0)), [q0a])]
    | p1a => [([G], (ConstraintAutomata.dc G (Some 1)), [q0a])] 
    | s0 => []
    end.

  Definition eToGFIFOCA:= {|
    ConstraintAutomata.Q := [q0a;p0a;p1a];
    ConstraintAutomata.N := [E;G];
    ConstraintAutomata.T := eToGFIFOrel;
    ConstraintAutomata.Q0 := [q0a]
  |}.

  (*G FIFO H*)
  Definition gToHFIFOrel (s:alternatorStates):=
    match s with
    | q0a => [([G], (ConstraintAutomata.dc G (Some 0)), [p0a]) ;
              ([G], (ConstraintAutomata.dc G (Some 1)), [p1a])]
    | p0a => [([H], (ConstraintAutomata.dc H (Some 0)), [q0a])]
    | p1a => [([H], (ConstraintAutomata.dc H (Some 1)), [q0a])] 
    | s0 => []
    end.

  Definition gToHFIFOCA:= {|
    ConstraintAutomata.Q := [q0a;p0a;p1a];
    ConstraintAutomata.N := [G;H];
    ConstraintAutomata.T := gToHFIFOrel;
    ConstraintAutomata.Q0 := [q0a]
  |}.

(* E Sync B *)
  Definition syncEBCaBehavior (s: alternatorStates) :=
    match s with
    | s0 => [([E;B] , ConstraintAutomata.eqDc nat E B, [s0])] 
    | _ => []
    end.

  Definition EBsyncCA := {|
    ConstraintAutomata.Q := [s0];
    ConstraintAutomata.N := [E;B];
    ConstraintAutomata.T := syncEBCaBehavior;
    ConstraintAutomata.Q0 := [s0]
  |}.


(* G Sync C *)
  Definition syncGCCaBehavior (s: alternatorStates) :=
    match s with
    | s0 => [([G;C] , ConstraintAutomata.eqDc nat G C, [s0])] 
    | _ => []
    end.

  Definition GCsyncCA := {|
    ConstraintAutomata.Q := [s0];
    ConstraintAutomata.N := [G;C];
    ConstraintAutomata.T := syncGCCaBehavior;
    ConstraintAutomata.Q0 := [s0]
  |}.


(* H Sync D *)
  Definition syncHDCaBehavior (s: alternatorStates) :=
    match s with
    | s0 => [([H;D] , ConstraintAutomata.eqDc nat H D, [s0])] 
    | _ => []
    end.

  Definition HDsyncCA := {|
    ConstraintAutomata.Q := [s0];
    ConstraintAutomata.N := [H;D];
    ConstraintAutomata.T := syncHDCaBehavior;
    ConstraintAutomata.Q0 := [s0]
  |}.

  Definition fifo1Product := ProductAutomata.buildPA aToEFIFOCA EBsyncCA.
  Definition fifo2Product := ProductAutomata.buildPA fifo1Product eToGFIFOCA.
  Definition fifo3Product := ProductAutomata.buildPA fifo2Product GCsyncCA.
  Definition fifo4Product := ProductAutomata.buildPA fifo3Product gToHFIFOCA.
  Definition resultingSequencerProduct := ProductAutomata.buildPA fifo4Product HDsyncCA.

  Definition singleExecInput := [portA;portB;portC;portD;portE;portG;portH].

  Eval compute in ConstraintAutomata.Q resultingSequencerProduct.

  Definition run1 := Eval vm_compute in ConstraintAutomata.run resultingSequencerProduct singleExecInput 4.
  Print run1.

  Lemma acceptingRunAllPortsWData :  ~ In [] (run1) /\
                                       In [(p1a, s0, q0a, s0, q0a, s0)] (run1) /\
                                       In [(q0a, s0, p1a, s0, q0a, s0)] (run1) /\
                                       In [(q0a, s0, q0a, s0, p1a, s0)] (run1).
  Proof.
  unfold run1. split.
  unfold not. intros. simpl in H0. repeat (destruct H0; inversion H0).
  repeat (split; simpl;auto).
  Defined.

(* Ex 2 *)
Definition timeStampSequencerA2(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1 
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat (S n) + 16#1
    end.

  Definition timeStampSequencerB2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat (S n) + 16#1
    end.


  Definition timeStampSequencerC2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 3#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat (S n) + 16#1
    end.

  Definition timeStampSequencerD2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 4#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_nat (S n) + 16#1
    end.

  Definition timeStampSequencerE2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>   Z.of_nat (S n) + 16#1
    end.

  Definition timeStampSequencerG2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 3#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>   Z.of_nat (S n) + 16#1
    end.

  Definition timeStampSequencerH2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 4#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>   Z.of_nat (S n) + 16#1
    end.


  Definition timeStampSequencerI2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 4#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>   Z.of_nat (S n) + 16#1
    end.

  Definition timeStampSequencerJ2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 4#1
    | 1 => 6#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>   Z.of_nat (S n) + 16#1
    end.

  Lemma timeStampSequencerA2Holds : forall n, 
    Qle (timeStampSequencerA2 n) (timeStampSequencerA2 (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerA2. discriminate.
  unfold timeStampSequencerA2. case (n). discriminate.
  intros n0. case (n0). discriminate.
  intros n1. case (n1). discriminate.
  intros n2. case (n2). discriminate.
  intros n3. case (n3). discriminate.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerB2Holds : forall n, 
    Qle (timeStampSequencerB2 n) (timeStampSequencerB2 (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSequencerB2. discriminate.
  unfold timeStampSequencerB2. case (n). discriminate.
  intros n0. case (n0). discriminate.
  intros n1. case (n1). discriminate.
  intros n2. case (n2). discriminate.
  intros n3. case (n3). discriminate.
  intros n4. apply orderZofNat. Defined.
  Lemma timeStampSequencerC2Holds : forall n, 
    Qle (timeStampSequencerC2 n) (timeStampSequencerC2 (S n)). 
  Proof.
  Proof.
  intros. destruct n. unfold timeStampSequencerC2. discriminate.
  unfold timeStampSequencerC2. case (n). discriminate.
  intros n0. case (n0). discriminate.
  intros n1. case (n1). discriminate.
  intros n2. case (n2). discriminate.
  intros n3. case (n3). discriminate.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerD2Holds : forall n, 
    Qle (timeStampSequencerD2 n) (timeStampSequencerD2 (S n)). 
  Proof.
  Proof.
  intros. destruct n. unfold timeStampSequencerD2. discriminate.
  unfold timeStampSequencerD2. case (n). discriminate.
  intros n0. case (n0). discriminate.
  intros n1. case (n1). discriminate.
  intros n2. case (n2). discriminate.
  intros n3. case (n3). discriminate.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerE2Holds : forall n, 
    Qle (timeStampSequencerE2 n) (timeStampSequencerB2 (S n)). 
  Proof.
  Proof.
  intros. destruct n. unfold timeStampSequencerE2. discriminate.
  unfold timeStampSequencerE2. case (n). discriminate.
  intros n0. case (n0). discriminate.
  intros n1. case (n1). discriminate.
  intros n2. case (n2). discriminate.
  intros n3. case (n3). discriminate.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerG2Holds : forall n, 
    Qle (timeStampSequencerG2 n) (timeStampSequencerG2 (S n)). 
  Proof.
  Proof.
  intros. destruct n. unfold timeStampSequencerG2. discriminate.
  unfold timeStampSequencerG2. case (n). discriminate.
  intros n0. case (n0). discriminate.
  intros n1. case (n1). discriminate.
  intros n2. case (n2). discriminate.
  intros n3. case (n3). discriminate.
  intros n4. apply orderZofNat. Defined.

  Lemma timeStampSequencerH2Holds : forall n, 
    Qle (timeStampSequencerH2 n) (timeStampSequencerH2 (S n)). 
  Proof.
  Proof.
  intros. destruct n. unfold timeStampSequencerH2. discriminate.
  unfold timeStampSequencerH2. case (n). discriminate.
  intros n0. case (n0). discriminate.
  intros n1. case (n1). discriminate.
  intros n2. case (n2). discriminate.
  intros n3. case (n3). discriminate.
  intros n4. apply orderZofNat. Defined.

  Definition portA2 := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampSequencerA2;
        ConstraintAutomata.portCond := timeStampSequencerA2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portB2 := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampSequencerB2;
        ConstraintAutomata.portCond := timeStampSequencerB2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portC2 := {|
        ConstraintAutomata.id := C;
        ConstraintAutomata.dataAssignment := dataAssignmentC;
        ConstraintAutomata.timeStamp := timeStampSequencerC2;
        ConstraintAutomata.portCond := timeStampSequencerC2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portD2 := {|
        ConstraintAutomata.id := D;
        ConstraintAutomata.dataAssignment := dataAssignmentD;
        ConstraintAutomata.timeStamp := timeStampSequencerD2;
        ConstraintAutomata.portCond := timeStampSequencerD2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portE2 := {|
        ConstraintAutomata.id := E;
        ConstraintAutomata.dataAssignment := dataAssignmentE;
        ConstraintAutomata.timeStamp := timeStampSequencerE2;
        ConstraintAutomata.portCond := timeStampSequencerE2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portG2 := {|
        ConstraintAutomata.id := G;
        ConstraintAutomata.dataAssignment := dataAssignmentG;
        ConstraintAutomata.timeStamp := timeStampSequencerG2;
        ConstraintAutomata.portCond := timeStampSequencerG2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portH2 := {|
        ConstraintAutomata.id := H;
        ConstraintAutomata.dataAssignment := dataAssignmentH;
        ConstraintAutomata.timeStamp := timeStampSequencerH2;
        ConstraintAutomata.portCond := timeStampSequencerH2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition secondExInput := [portA2;portB2;portC2;portD2;portE2;portG2;portH2].

  Definition run2 := Eval vm_compute in ConstraintAutomata.run resultingSequencerProduct secondExInput 7.
  Print run2.

  Lemma nonAcceptingRun : In [] (run2).
  Proof.
  simpl. auto. Defined.

  Require Extraction.
  Extraction Language Haskell.
  Extraction "SequencerCertified" resultingSequencerProduct.
