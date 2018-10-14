Require Import CaMain.

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
    | 1 => Some 1
    | S n => Some (1)
    end.

 Definition timeStampTestSync (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1 (* injecting N to Z *)
    end.

  Lemma timeStampTestHoldsSync : forall n, 
    Qle (timeStampTestSync n) (timeStampTestSync (S n)). 
  Proof. Admitted.

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

  Definition syncCaBehavior (s: syncState) :=
    match s with
    | X => [([E;F] , (ConstraintAutomata.orDc (ConstraintAutomata.andDc (ConstraintAutomata.dc (E) (Some 0)) 
                                                ((ConstraintAutomata.dc (F) (Some 0))))

                          (ConstraintAutomata.andDc (ConstraintAutomata.dc (E) (Some 1)) 
                                                ((ConstraintAutomata.dc (F) (Some 1)))
                            )
                        ), [X])] 
    end.

  (* The CA itself is formalized as *)
  Definition syncCA := {|
    ConstraintAutomata.Q := [X];
    ConstraintAutomata.N := [E;F];
    ConstraintAutomata.T := syncCaBehavior;
    ConstraintAutomata.Q0 := [X]
  |}.

Eval compute in ConstraintAutomata.run syncCA [portE;portF] 20 20.


(* LossySync Channel CA *)

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
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampLossyB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  0#1
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
    | q0 => [([A;B] , (ConstraintAutomata.orDc (ConstraintAutomata.andDc (ConstraintAutomata.dc (A) (Some 0)) 
                                                ((ConstraintAutomata.dc (B) (Some 0))))

                          (ConstraintAutomata.andDc (ConstraintAutomata.dc (A) (Some 1)) 
                                                ((ConstraintAutomata.dc (B) (Some 1)))
                            )
                        ), [q0]);([A], (ConstraintAutomata.tDc lossySyncPorts nat), [q0])] 
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

  Eval compute in ConstraintAutomata.run lossySyncCA [portA;portB] 10 20. (*does not accept the TDS composed by portA and portB because
                                                                            B has data in theta.time, which is not comprised by the automaton's transitions *)
  
  (* FIFO CA *)

  Inductive FIFOStates : Type := q0F | p0F | p1F.
  Inductive FIFOports : Type := AF | BF. (*usar um tipo já definido se quiser *)
 (*Program não resolve aqui... eu tinha esquecido que estou usando a tática incorreta*)
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
  Definition oneBoundedFIFOrel (s:FIFOStates) 
  (*set (set (ports) * ConstraintAutomata.DC ports (option nat) * set states)*) :=
    match s with
    | q0F => [([AF], (ConstraintAutomata.dc AF (Some 0)), [p0F]) ;
              ([AF], (ConstraintAutomata.dc AF (Some 1)), [p1F])]
    | p0F => [([BF], (ConstraintAutomata.dc BF (Some 0)), [q0F])]
    | p1F => [([BF], (ConstraintAutomata.dc BF (Some 1)), [q0F])] 
    end.

  (* falta definir transição para começar a brncar com a run.                                      *)
  Definition oneBoundedFIFOCA:= {|
    ConstraintAutomata.Q := [q0F;p0F;p1F];
    ConstraintAutomata.N := [AF;BF];
    ConstraintAutomata.T := oneBoundedFIFOrel;
    ConstraintAutomata.Q0 := [q0F]
  |}.

  Eval compute in ConstraintAutomata.run oneBoundedFIFOCA realports 10 69.

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
    Qle (timeStampSyncDrain n) (timeStampSyncDrain (S n)). 
  Proof. Admitted.

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

  (* The CA itself is formalized as *)
  Definition SyncDrainCA := {|
    ConstraintAutomata.Q := [q1D];
    ConstraintAutomata.N := [AD;BD];
    ConstraintAutomata.T := syncDrainCaBehavior;
    ConstraintAutomata.Q0 := [q1D]
  |}.

  Eval compute in ConstraintAutomata.run SyncDrainCA [portAD;portBD] 10 10.

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
    Qle (timeStampASyncDrainA n) (timeStampASyncDrainA (S n)). 
  Proof. Admitted.

  Lemma timeStampASyncDrainBHolds : forall n, 
    Qle (timeStampASyncDrainB n) (timeStampASyncDrainB (S n)). 
  Proof. Admitted.

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

  (* The CA itself is formalized as *)
  Definition aSyncDrainCA := {|
    ConstraintAutomata.Q := [q1A];
    ConstraintAutomata.N := [AA;BA];
    ConstraintAutomata.T := aSyncDrainCaBehavior;
    ConstraintAutomata.Q0 := [q1A]
  |}.

  Eval compute in ConstraintAutomata.run aSyncDrainCA  [portAA;portBA] 10 12.

  (* Filter CA *)

  (* Transform CA *)

  Definition trasformFunction := fun x => x + 1.
  Eval compute in trasformFunction 3.

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

  Definition dataAssignmenttransformBoth n := 
    match n with
    | 0 => Some 0
    | 1 => Some 0
    | S n => Some (1)
    end.

 Definition timeStamptransformA (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  0#1
    | 1 =>  3#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 7#1
    end.

   Definition timeStamptransformB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | 1 => 2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 11#1
    end.

  Lemma timeStamptransformHolds : forall n, 
    Qle (timeStamptransformA n) (timeStamptransformA (S n)). 
  Proof. Admitted.

  Lemma timeStamptransformBHolds : forall n, 
    Qle (timeStamptransformB n) (timeStamptransformB (S n)). 
  Proof. Admitted.

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
        ConstraintAutomata.dataAssignment := dataAssignmenttransformBoth;
        ConstraintAutomata.timeStamp := timeStamptransformA;
        ConstraintAutomata.portCond := timeStamptransformHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBT:= {|
        ConstraintAutomata.id := BT;
        ConstraintAutomata.dataAssignment := dataAssignmenttransformBoth;
        ConstraintAutomata.timeStamp := timeStamptransformB;
        ConstraintAutomata.portCond := timeStamptransformBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition transformCaBehavior (s: transformState) :=
    match s with
    | q1T => [([AT;BT] , ConstraintAutomata.dc BT (Some 0), [q1T])] 
    end. (* --> tá errado. preciso de uma forma de permitir meter um dado diretão da porta AT, algo mais genérico. *)
         (* Talvez uma definição a mais de CA que permita pegar o dado direto da porta no thetaTime *)

  (* The CA itself is formalized as *)
  Definition transformCA := {|
    ConstraintAutomata.Q := [q1T];
    ConstraintAutomata.N := [AT;BT];
    ConstraintAutomata.T := transformCaBehavior;
    ConstraintAutomata.Q0 := [q1T]
  |}.


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
    (*match n with
    | 0 =>  0#1
    | 1 =>  3#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 7#1
    end. *)
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
    Qle (timeStampmergerA n) (timeStampmergerA (S n)). 
  Proof. Admitted.

  Lemma timeStampmergerBHolds : forall n, 
    Qle (timeStampmergerB n) (timeStampmergerB (S n)). 
  Proof. Admitted.

  Lemma timeStampmergerCHolds : forall n, 
    Qle (timeStampmergerC n) (timeStampmergerC (S n)). 
  Proof. Admitted.

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
        ConstraintAutomata.timeStamp := timeStampmergerB;
        ConstraintAutomata.portCond := timeStampmergerBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition mergerCaBehavior (s: mergerState) :
    set (set mergerPorts * ConstraintAutomata.DC mergerPorts nat * set mergerState) :=
    match s with
    | q1M => [([AM;CM] , ConstraintAutomata.eqDc nat AM CM, [q1M]);
              ([BM;CM] , ConstraintAutomata.eqDc nat BM CM, [q1M])] 
    end. (* --> tá errado. preciso de uma forma de permitir meter um dado diretão da porta AT, algo mais genérico. *)
         (* Talvez uma definição a mais de CA que permita pegar o dado direto da porta no thetaTime *)

    Check mergerCaBehavior.

  (* The CA itself is formalized as *)
  Definition mergerCA := {|
    ConstraintAutomata.Q := [q1M];
    ConstraintAutomata.N := [AM;BM;CM];
    ConstraintAutomata.T := mergerCaBehavior;
    ConstraintAutomata.Q0 := [q1M]
  |}.

  Eval compute in ConstraintAutomata.xamboca2 mergerCA [portAM;portBM;portCM] 10 10.
  Eval compute in ConstraintAutomata.run mergerCA [portAM;portBM;portCM] 10 10. (*all of them are in theta-time *)

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
    Qle (timeStampreplicatorA n) (timeStampreplicatorA (S n)). 
  Proof. Admitted.

  Lemma timeStampreplicatorBHolds : forall n, 
    Qle (timeStampreplicatorB n) (timeStampreplicatorB (S n)). 
  Proof. Admitted.

  Lemma timeStampreplicatorCHolds : forall n, 
    Qle (timeStampreplicatorC n) (timeStampreplicatorC (S n)). 
  Proof. Admitted.

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
        ConstraintAutomata.timeStamp := timeStampreplicatorB;
        ConstraintAutomata.portCond := timeStampreplicatorBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition replicatorCaBehavior (s: replicatorState) :
    set (set replicatorPorts * ConstraintAutomata.DC replicatorPorts nat * set replicatorState) :=
    match s with
    | q1R => [([AR;BR;CR] , ConstraintAutomata.andDc (ConstraintAutomata.eqDc nat AR BR) 
                                                     (ConstraintAutomata.eqDc nat AR CR), [q1R])] 
    end.

    Check replicatorCaBehavior.

  (* The CA itself is formalized as *)
  Definition replicatorCA := {|
    ConstraintAutomata.Q := [q1R];
    ConstraintAutomata.N := [AR;BR;CR];
    ConstraintAutomata.T := replicatorCaBehavior;
    ConstraintAutomata.Q0 := [q1R]
  |}.

  Eval compute in ConstraintAutomata.run replicatorCA [portAR;portBR;portCR] 10 10.




