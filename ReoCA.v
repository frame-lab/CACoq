Require Import CaMain.

Open Scope Q_scope.
Axiom orderZofNat : forall n, forall a, Z.of_nat (S n) + a # 1 < Z.of_nat (S (S n)) + a # 1.
Close Scope Q_scope.

(* Implementation Examples of canonical Constraint Automata as presented by Baier et al.'s paper *)

(* Sync channel CA *)
  Inductive syncState := X.
  Inductive syncPorts := E | F.

  Instance syncStateEq: EqDec syncState eq :=
    {equiv_dec x y := 
      match x,y with
      | X,X => in_left
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentBoth n := 
    match n with
    | 0 => Some 0
    | 1 => Some 455
    | S n => Some (1)
    end.

 Definition timeStampTestSync (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 2#1 (* an example of a time stamp function, by injecting N to Z *)
    end.

  Lemma timeStampTestHoldsSync : forall n, 
    Qlt (timeStampTestSync n) (timeStampTestSync (S n)). 
  Proof.
  intros. destruct n. unfold timeStampTestSync. simpl. Search (Qlt). reflexivity. 
  unfold timeStampTestSync.
  apply orderZofNat. Defined.

  Instance syncPortsEq: EqDec syncPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | E,E | F,F => in_left
      | E,F | F,E => in_right
      end }.
   Proof.
   all: congruence.
   Defined.


  Definition portE := {|
        ConstraintAutomata.id := E;
        ConstraintAutomata.dataAssignment := dataAssignmentBoth;
        ConstraintAutomata.timeStamp := timeStampTestSync;
        ConstraintAutomata.portCond := timeStampTestHoldsSync;
        ConstraintAutomata.index := 0 |}.

  Definition portF:= {|
        ConstraintAutomata.id := F;
        ConstraintAutomata.dataAssignment := dataAssignmentBoth;
        ConstraintAutomata.timeStamp := timeStampTestSync;
        ConstraintAutomata.portCond := timeStampTestHoldsSync;
        ConstraintAutomata.index := 0 |}.

  Check ConstraintAutomata.tDc.

  Definition syncCaBehavior (s: syncState) :=
    match s with
    | X => [([E;F] , ConstraintAutomata.eqDc nat E F, [X])] 
    end.

  Definition syncCA := {|
    ConstraintAutomata.Q := [X];
    ConstraintAutomata.N := [E;F];
    ConstraintAutomata.T := syncCaBehavior;
    ConstraintAutomata.Q0 := [X]
  |}.

  Eval compute in ConstraintAutomata.run syncCA [portE;portF] 20.


  (* LossySync CA *)
  Inductive lossySyncStates := q0.

  Inductive lossySyncPorts := A | B.

  Instance lossySyncStateEq: EqDec lossySyncStates eq :=
    {equiv_dec x y := 
      match x,y with
      | q0, q0 => in_left
      end }.
   Proof.
   reflexivity.
   Defined.

   Instance LossySyncPortsEq: EqDec lossySyncPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | A,A | B,B => in_left
      | A,B | B,A => in_right
      end }.
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
    | 0 =>  1#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 69#1
    end.

  Definition timeStampLossyB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 3#1
    end.

  Lemma timeStampTestHoldsLossyA: forall n, 
    Qlt (timeStampLossyA n) (timeStampLossyA (S n)). 
  Proof.
  intros. destruct n. unfold timeStampLossyA. reflexivity. 
  unfold timeStampLossyA.
  apply orderZofNat. Defined.

  Lemma timeStampTestHoldsLossyB: forall n, 
    Qlt (timeStampLossyB n) (timeStampLossyB (S n)).
  Proof.
  intros. destruct n. unfold timeStampLossyB. reflexivity. 
  unfold timeStampLossyB.
  apply orderZofNat. Defined.

  Definition lossySyncCaBehavior (s: lossySyncStates) :=
    match s with
    | q0 => [([A;B] , ConstraintAutomata.eqDc nat A B, [q0]);
             ([A], (ConstraintAutomata.tDc lossySyncPorts nat), [q0])] 
    end.

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
                                                                         only B has data in theta.time(2), which is not comprised by the automaton's transitions *)
  
  (* FIFO CA *)

  Inductive FIFOStates : Type := q0F | p0F | p1F.
  Inductive FIFOports : Type := AF | BF.
  Instance portsEq : EqDec FIFOports eq :=
    {equiv_dec x y := 
      match x,y with
      | AF,AF | BF,BF => in_left
      | AF,BF | BF,AF => in_right
      end }.
   Proof.
   all: congruence.
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
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1 
    end.

  Definition timeStampFIFOB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  2#1 
    | 1 =>  4#1
    | 2 => 6#1
    | 3 => 8#1
    | 4 => 10#1
    | 5 => 12#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 10#1
    end.

  Lemma timeStampTestFIFOAHolds : forall n, Qlt (timeStampFIFOA n) (timeStampFIFOA (S n)).
  Proof.
  intros. destruct n. unfold timeStampFIFOA. reflexivity.
  unfold timeStampFIFOA. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.

  Lemma timeStampTestFIFOBHolds : forall n, 
    Qlt (timeStampFIFOB n) (timeStampFIFOB (S n)). 
  Proof.
  intros. destruct n. unfold timeStampFIFOB. reflexivity.
  unfold timeStampFIFOB. case (n). reflexivity.
  intros n0. case (n0). reflexivity.
  intros n1. case (n1). reflexivity.
  intros n2. case (n2). reflexivity.
  intros n3. case (n3). reflexivity.
  intros n4. unfold Qlt. apply orderZofNat.  Defined.

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

  Definition oneBoundedFIFOrel (s:FIFOStates) :=
    match s with
    | q0F => [([AF], (ConstraintAutomata.dc AF (Some 0)), [p0F]) ;
              ([AF], (ConstraintAutomata.dc AF (Some 1)), [p1F])]
    | p0F => [([BF], (ConstraintAutomata.dc BF (Some 0)), [q0F])]
    | p1F => [([BF], (ConstraintAutomata.dc BF (Some 1)), [q0F])] 
    end.

  Definition oneBoundedFIFOCA:= {|
    ConstraintAutomata.Q := [q0F;p0F;p1F];
    ConstraintAutomata.N := [AF;BF];
    ConstraintAutomata.T := oneBoundedFIFOrel;
    ConstraintAutomata.Q0 := [q0F]
  |}.

  Lemma dataInAF: forall s, In AF (ConstraintAutomata.retrievePortsFromRespTransitions (ConstraintAutomata.T oneBoundedFIFOCA s)) <->
    s = q0F.
  Proof.
  split. 
  - intros. destruct s. 
    + reflexivity.
    + simpl in H. inversion H. discriminate. inversion H0.
    + simpl in H. inversion H. discriminate. inversion H0.
  - intros. rewrite H. simpl. left. reflexivity.
  Defined.

  Eval compute in ConstraintAutomata.run oneBoundedFIFOCA realports 8.

  (* SyncDrain CA *)

  Inductive syncDrainState := q1D.
  Inductive syncDrainPorts :=  AD | BD.

  Instance syncDrainStateEq: EqDec syncDrainState eq :=
    {equiv_dec x y := 
      match x,y with
      | q1D, q1D => in_left
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentSyncDrainBoth n := 
    match n with
    | 0 => Some 0
    | 1 => Some 69
    | S n => Some (1)
    end.

 Definition timeStampSyncDrain (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Lemma timeStampSyncDrainHolds : forall n, 
    Qlt (timeStampSyncDrain n) (timeStampSyncDrain (S n)). 
  Proof.
  intros. destruct n. unfold timeStampSyncDrain. reflexivity.
  unfold timeStampSyncDrain. case (n). reflexivity.
  intros n0. unfold timeStampSyncDrain. apply orderZofNat.  Defined.

  Instance syncDrainPortsEq: EqDec syncDrainPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | AD,AD | BD,BD => in_left
      | AD,BD | BD,AD => in_right
      end }.
   Proof.
   all: congruence.
   Defined.


  Definition portAD := {|
        ConstraintAutomata.id := AD;
        ConstraintAutomata.dataAssignment := dataAssignmentSyncDrainBoth;
        ConstraintAutomata.timeStamp := timeStampSyncDrain;
        ConstraintAutomata.portCond := timeStampSyncDrainHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBD:= {|
        ConstraintAutomata.id := BD;
        ConstraintAutomata.dataAssignment := dataAssignmentSyncDrainBoth;
        ConstraintAutomata.timeStamp := timeStampSyncDrain;
        ConstraintAutomata.portCond := timeStampSyncDrainHolds;
        ConstraintAutomata.index := 0 |}.

  Definition syncDrainCaBehavior (s: syncDrainState) :=
    match s with
    | q1D => [([AD;BD] , ConstraintAutomata.tDc syncDrainPorts nat, [q1D])] 
    end.

  Definition SyncDrainCA := {|
    ConstraintAutomata.Q := [q1D];
    ConstraintAutomata.N := [AD;BD];
    ConstraintAutomata.T := syncDrainCaBehavior;
    ConstraintAutomata.Q0 := [q1D]
  |}.

  Eval compute in ConstraintAutomata.run SyncDrainCA [portAD;portBD] 15.

  (* AsyncDrain *)
  Inductive aSyncDrainState := q1A.
  Inductive aSyncDrainPorts :=  AA | BA.

  Instance aSyncDrainStateEq: EqDec aSyncDrainState eq :=
    {equiv_dec x y := 
      match x,y with
      | q1A, q1A => in_left
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentASyncDrainBoth n := 
    match n with
    | 0 => Some 0
    | 1 => Some 0
    | S n => Some (1)
    end.

 Definition timeStampASyncDrainA (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  0#1
    | 1 =>  3#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 7#1
    end.

   Definition timeStampASyncDrainB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

  Lemma timeStampASyncDrainHolds : forall n, 
    Qlt (timeStampASyncDrainA n) (timeStampASyncDrainA (S n)). 
  Proof.
  intros. destruct n. unfold timeStampASyncDrainA. reflexivity.
  unfold timeStampASyncDrainA. case (n). reflexivity.
  intros n0. unfold timeStampASyncDrainA. apply orderZofNat.  Defined.


  Lemma timeStampASyncDrainBHolds : forall n, 
    Qlt (timeStampASyncDrainB n) (timeStampASyncDrainB (S n)). 
  Proof.
  intros. destruct n. unfold timeStampASyncDrainB. reflexivity.
  unfold timeStampASyncDrainB. case (n). reflexivity.
  intros n0. unfold timeStampASyncDrainB. apply orderZofNat. Defined.

  Instance aSyncDrainPortsEq: EqDec aSyncDrainPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | AA,AA | BA,BA => in_left
      | AA,BA | BA,AA => in_right
      end }.
   Proof.
   all: congruence.
   Defined.


  Definition portAA := {|
        ConstraintAutomata.id := AA;
        ConstraintAutomata.dataAssignment := dataAssignmentASyncDrainBoth;
        ConstraintAutomata.timeStamp := timeStampASyncDrainA;
        ConstraintAutomata.portCond := timeStampASyncDrainHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBA:= {|
        ConstraintAutomata.id := BA;
        ConstraintAutomata.dataAssignment := dataAssignmentASyncDrainBoth;
        ConstraintAutomata.timeStamp := timeStampASyncDrainB;
        ConstraintAutomata.portCond := timeStampASyncDrainBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition aSyncDrainCaBehavior (s: aSyncDrainState) :=
    match s with
    | q1A => [([AA] , ConstraintAutomata.tDc aSyncDrainPorts nat, [q1A]);
              ([BA] , ConstraintAutomata.tDc aSyncDrainPorts nat, [q1A])] 
    end.

  Definition aSyncDrainCA := {|
    ConstraintAutomata.Q := [q1A];
    ConstraintAutomata.N := [AA;BA];
    ConstraintAutomata.T := aSyncDrainCaBehavior;
    ConstraintAutomata.Q0 := [q1A]
  |}.

  Eval compute in ConstraintAutomata.run aSyncDrainCA  [portAA;portBA] 10.

  (* Filter CA *)
  Inductive filterState := q1F.
  Inductive filterPorts :=  C | D.

  Instance filterStateEq: EqDec filterState eq :=
    {equiv_dec x y := 
      match x,y with
      | q1F, q1F => in_left
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentfilterBoth n := 
    match n with
    | 0 => Some 0
    | 1 => Some 0
    | S n => Some (1)
    end.

 Definition timeStampfilterA (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  0#1
    | 1 =>  3#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 7#1
    end.

   Definition timeStampfilterB (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 4#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 20#1
    end.

  Lemma timeStampfilterHolds : forall n, 
    Qlt (timeStampfilterA n) (timeStampfilterA (S n)).   
  Proof.
  intros. destruct n. unfold timeStampfilterA. reflexivity.
  unfold timeStampfilterA. case (n). reflexivity.
  intros n0. unfold timeStampfilterA. apply orderZofNat. Defined.

  Lemma timeStampfilterBHolds : forall n, 
    Qlt (timeStampfilterB n) (timeStampfilterB (S n)). 
  Proof.   
  intros. destruct n. unfold timeStampfilterB. reflexivity.
  unfold timeStampfilterB. apply orderZofNat. Defined.

  Instance filterPortsEq: EqDec filterPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | C,C | D,D => in_left
      | C,D | D,C => in_right
      end }.
   Proof.
   all: congruence.
   Defined.


  Definition portC := {|
        ConstraintAutomata.id := C;
        ConstraintAutomata.dataAssignment := dataAssignmentfilterBoth;
        ConstraintAutomata.timeStamp := timeStampfilterA;
        ConstraintAutomata.portCond := timeStampfilterHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portD:= {|
        ConstraintAutomata.id := D;
        ConstraintAutomata.dataAssignment := dataAssignmentfilterBoth;
        ConstraintAutomata.timeStamp := timeStampfilterB;
        ConstraintAutomata.portCond := timeStampfilterBHolds;
        ConstraintAutomata.index := 0 |}.

  (*As an example, the filter condition over the data item in port A is the data should be  Some 3 *)
  Definition filterCaBehavior (s: filterState) :=
    match s with
    | q1F => [([C;D] , ConstraintAutomata.andDc (ConstraintAutomata.dc C (Some 3)) 
                                                 (ConstraintAutomata.eqDc nat C D), [q1F]);
              ([C] , ConstraintAutomata.negDc (ConstraintAutomata.dc C (Some 3)), [q1F]) ]
    end.

  (* The CA itself is formalized as *)
  Definition filterCA := {|
    ConstraintAutomata.Q := [q1F];
    ConstraintAutomata.N := [C;D];
    ConstraintAutomata.T := filterCaBehavior;
    ConstraintAutomata.Q0 := [q1F]
  |}.

  Eval compute in ConstraintAutomata.run filterCA [portC;portD] 3.


  (* Transform CA *)

  Definition trasformFunction (n: option nat) :=
    match n with
    | Some x => Some (x + 3)
    | None   => None
    end.

  Inductive transformState := q1T.
  Inductive transformPorts :=  AT | BT.

  Instance transformStateEq: EqDec transformState eq :=
    {equiv_dec x y := 
      match x,y with
      | q1T, q1T => in_left
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmenttransformAF n := 
    match n with
    | 0 => Some 0
    | 1 => Some 0
    | 2 => Some 0
    | 3 => Some 0
    | S n => Some (1)
    end.

  Definition dataAssignmenttransformBF n := 
    match n with
    | 0 => Some 3
    | 1 => Some 3
    | 2 => Some 3
    | 3 => Some 3
    | S n => Some (4)
    end.

 Definition timeStamptransformA (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  0#1
    | 1 =>  2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

   Definition timeStamptransformB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  0#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

  Lemma timeStamptransformHolds : forall n, 
    Qlt (timeStamptransformA n) (timeStamptransformA (S n)). 
  Proof.   
  intros. destruct n. unfold timeStamptransformA. reflexivity.
  unfold timeStamptransformA. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Lemma timeStamptransformBHolds : forall n, 
    Qlt (timeStamptransformB n) (timeStamptransformB (S n)). 
  Proof.   
  intros. destruct n. unfold timeStamptransformB. reflexivity.
  unfold timeStamptransformB. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Instance transformPortsEq: EqDec transformPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | AT,AT | BT,BT => in_left
      | AT,BT | BT,AT => in_right
      end }.
   Proof.
   all: congruence.
   Defined.


  Definition portAT := {|
        ConstraintAutomata.id := AT;
        ConstraintAutomata.dataAssignment := dataAssignmenttransformAF;
        ConstraintAutomata.timeStamp := timeStamptransformA;
        ConstraintAutomata.portCond := timeStamptransformHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBT:= {|
        ConstraintAutomata.id := BT;
        ConstraintAutomata.dataAssignment := dataAssignmenttransformBF;
        ConstraintAutomata.timeStamp := timeStamptransformB;
        ConstraintAutomata.portCond := timeStamptransformBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition transformCaBehavior (s: transformState) :=
    match s with
    | q1T => [([AT;BT] , ConstraintAutomata.trDc trasformFunction AT BT, [q1T])]
    end.

  Definition transformCA := {|
    ConstraintAutomata.Q := [q1T];
    ConstraintAutomata.N := [AT;BT];
    ConstraintAutomata.T := transformCaBehavior;
    ConstraintAutomata.Q0 := [q1T]
  |}.

  Eval compute in ConstraintAutomata.run transformCA [portAT;portBT] 10.

  (* Merger CA*)
  Inductive mergerState := q1M.
  Inductive mergerPorts :=  AM | BM | CM.

  Instance mergerStateEq: EqDec mergerState eq :=
    {equiv_dec x y := 
      match x,y with
      | q1M, q1M => in_left
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentmergerBoth n := 
    match n with
    | 0 => Some 0
    | 1 => Some 555
    | 3 => Some 69
    | S n => Some (1)
    end.

 Definition timeStampmergerA (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

   Definition timeStampmergerB (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

  Definition timeStampmergerC (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

  Lemma timeStampmergerHolds : forall n, 
    Qlt (timeStampmergerA n) (timeStampmergerA (S n)). 
  Proof.   
  intros. destruct n. unfold timeStampmergerA. reflexivity.
  unfold timeStampmergerA. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Lemma timeStampmergerBHolds : forall n, 
    Qlt (timeStampmergerB n) (timeStampmergerB (S n)). 
  Proof.   
  intros. destruct n. unfold timeStampmergerB. reflexivity.
  unfold timeStampmergerB. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Lemma timeStampmergerCHolds : forall n, 
    Qlt (timeStampmergerC n) (timeStampmergerC (S n)). 
  Proof.   
  intros. destruct n. unfold timeStampmergerC. reflexivity.
  unfold timeStampmergerC. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Instance mergerPortsEq: EqDec mergerPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | AM,AM | BM,BM  | CM, CM => in_left
      | AM,BM | AM,CM | BM,AM | BM,CM | CM, AM | CM, BM => in_right
      end }.
   Proof.
   all: congruence.
   Defined.


  Definition portAM := {|
        ConstraintAutomata.id := AM;
        ConstraintAutomata.dataAssignment := dataAssignmentmergerBoth;
        ConstraintAutomata.timeStamp := timeStampmergerA;
        ConstraintAutomata.portCond := timeStampmergerHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBM:= {|
        ConstraintAutomata.id := BM;
        ConstraintAutomata.dataAssignment := dataAssignmentmergerBoth;
        ConstraintAutomata.timeStamp := timeStampmergerB;
        ConstraintAutomata.portCond := timeStampmergerBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portCM:= {|
        ConstraintAutomata.id := CM;
        ConstraintAutomata.dataAssignment := dataAssignmentmergerBoth;
        ConstraintAutomata.timeStamp := timeStampmergerC;
        ConstraintAutomata.portCond := timeStampmergerCHolds;
        ConstraintAutomata.index := 0 |}.

  Definition mergerCaBehavior (s: mergerState) :
    set (set mergerPorts * ConstraintAutomata.DC mergerPorts nat * set mergerState) :=
    match s with
    | q1M => [([AM;CM] , ConstraintAutomata.eqDc nat AM CM, [q1M]);
              ([BM;CM] , ConstraintAutomata.eqDc nat BM CM, [q1M])] 
    end. 

  Definition mergerCA := {|
    ConstraintAutomata.Q := [q1M];
    ConstraintAutomata.N := [AM;BM;CM];
    ConstraintAutomata.T := mergerCaBehavior;
    ConstraintAutomata.Q0 := [q1M]
  |}.

  Eval compute in ConstraintAutomata.run mergerCA [portAM;portBM;portCM] 10.

  (* Replicator CA *)
  Inductive replicatorState := q1R.
  Inductive replicatorPorts :=  AR | BR | CR.

  Instance replicatorStateEq: EqDec replicatorState eq :=
    {equiv_dec x y := 
      match x,y with
      | q1R, q1R => in_left
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentreplicatorBoth n := 
    match n with
    | 0 => Some 0
    | 1 => Some 1
    | 3 => Some 2
    | S n => Some (1 + S n)
    end.

 Definition timeStampreplicatorA (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

   Definition timeStampreplicatorB (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

  Definition timeStampreplicatorC (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

  Lemma timeStampreplicatorHolds : forall n, 
    Qlt (timeStampreplicatorA n) (timeStampreplicatorA (S n)). 
  Proof.   
  intros. destruct n. unfold timeStampreplicatorA. reflexivity.
  unfold timeStampreplicatorA. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Lemma timeStampreplicatorBHolds : forall n, 
    Qlt (timeStampreplicatorB n) (timeStampreplicatorB (S n)). 
  Proof.   
  intros. destruct n. unfold timeStampreplicatorB. reflexivity.
  unfold timeStampreplicatorB. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Lemma timeStampreplicatorCHolds : forall n, 
    Qlt (timeStampreplicatorC n) (timeStampreplicatorC (S n)). 
  Proof.   
  intros. destruct n. unfold timeStampreplicatorC. reflexivity.
  unfold timeStampreplicatorC. case n. reflexivity.
  intros n0. apply orderZofNat. Defined.

  Instance replicatorPortsEq: EqDec replicatorPorts eq :=
    {equiv_dec x y := 
      match x,y with
      | AR,AR | BR,BR  | CR, CR => in_left
      | AR,BR | AR,CR | BR,AR | BR,CR | CR, AR | CR, BR => in_right
      end }.
   Proof.
   all: congruence.
   Defined.


  Definition portAR := {|
        ConstraintAutomata.id := AR;
        ConstraintAutomata.dataAssignment := dataAssignmentreplicatorBoth;
        ConstraintAutomata.timeStamp := timeStampreplicatorA;
        ConstraintAutomata.portCond := timeStampreplicatorHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBR:= {|
        ConstraintAutomata.id := BR;
        ConstraintAutomata.dataAssignment := dataAssignmentreplicatorBoth;
        ConstraintAutomata.timeStamp := timeStampreplicatorB;
        ConstraintAutomata.portCond := timeStampreplicatorBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portCR:= {|
        ConstraintAutomata.id := CR;
        ConstraintAutomata.dataAssignment := dataAssignmentreplicatorBoth;
        ConstraintAutomata.timeStamp := timeStampreplicatorC;
        ConstraintAutomata.portCond := timeStampreplicatorCHolds;
        ConstraintAutomata.index := 0 |}.

  Definition replicatorCaBehavior (s: replicatorState) :
    set (set replicatorPorts * ConstraintAutomata.DC replicatorPorts nat * set replicatorState) :=
    match s with
    | q1R => [([AR;BR;CR] , ConstraintAutomata.andDc (ConstraintAutomata.eqDc nat AR BR) 
                                                     (ConstraintAutomata.eqDc nat AR CR), [q1R])] 
    end.

  Definition replicatorCA := {|
    ConstraintAutomata.Q := [q1R];
    ConstraintAutomata.N := [AR;BR;CR];
    ConstraintAutomata.T := replicatorCaBehavior;
    ConstraintAutomata.Q0 := [q1R]
  |}.

  Eval compute in ConstraintAutomata.run replicatorCA [portAR;portBR;portCR] 11.




