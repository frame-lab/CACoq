Require Import CaMain.

(* FIFO CA *)

Inductive fifoStates := q0a | p0a | p1a | q0b | p0b | p1b.
Inductive fifoPorts := A | B | C | D.

Instance fifoStatesEq : EqDec fifoStates eq := 
	{equiv_dec x y := 
		match x, y with 
		| q0a,q0a => in_left 
		| p0a,p0a => in_left 
		| p1a,p1a => in_left 
		| q0b,q0b => in_left 
		| p0b,p0b => in_left 
		| p1b,p1b => in_left 
		| q0a,p0a => in_right 
		| q0a,p1a => in_right 
		| q0a,q0b => in_right 
		| q0a,p0b => in_right 
		| q0a,p1b => in_right 
		| p0a,q0a => in_right 
		| p0a,p1a => in_right 
		| p0a,q0b => in_right 
		| p0a,p0b => in_right 
		| p0a,p1b => in_right 
		| p1a,q0a => in_right 
		| p1a,p0a => in_right 
		| p1a,q0b => in_right 
		| p1a,p0b => in_right 
		| p1a,p1b => in_right 
		| q0b,q0a => in_right 
		| q0b,p0a => in_right 
		| q0b,p1a => in_right 
		| q0b,p0b => in_right 
		| q0b,p1b => in_right 
		| p0b,q0a => in_right 
		| p0b,p0a => in_right 
		| p0b,p1a => in_right 
		| p0b,q0b => in_right 
		| p0b,p1b => in_right 
		| p1b,q0a => in_right 
		| p1b,p0a => in_right 
		| p1b,p1a => in_right 
		| p1b,q0b => in_right 
		| p1b,p0b => in_right 
		end 
	}.
   Proof.
   all: congruence.
   Defined.

Instance fifoPortsEq : EqDec fifoPorts eq := 
	{equiv_dec x y := 
		match x, y with 
		| A,A => in_left 
		| B,B => in_left 
		| C,C => in_left 
		| D,D => in_left 
		| A,B => in_right 
		| A,C => in_right 
		| A,D => in_right 
		| B,A => in_right 
		| B,C => in_right 
		| B,D => in_right 
		| C,A => in_right 
		| C,B => in_right 
		| C,D => in_right 
		| D,A => in_right 
		| D,B => in_right 
		| D,C => in_right 
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
    | S n => Some (0)
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
    | 1 =>  4#1
    | 2 =>  7#1
    | 3 =>  10#1
    | 4 =>  13#1
    | 5 =>  15#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1 
    end.

  Definition timeStampFIFOB (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  2#1 (*1#1*)
    | 1 =>  5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition dataAssignmentC n :=
    match n with
    | 0 => Some 0
    | 1 => Some (0)
    | 2 => Some 1
    (*| 3 | 4 | 5 => Some 1
    | 6 => None *)
    | S n => Some 0
    end.

  Definition timeStampFIFOC(n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  3#1
    | 1 =>  6#1
    | 2 =>  9#1
    | 3 =>  12#1
    | 4 =>  15#1
    | 5 =>  18#1
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

  Lemma timeStampTestFIFOCHolds : forall n, 
    Qle (timeStampFIFOC n) (timeStampFIFOC (S n)). 
  Proof.
  Admitted.

  Definition portAF := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampFIFOA;
        ConstraintAutomata.portCond := timeStampTestFIFOAHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBF := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampFIFOB;
        ConstraintAutomata.portCond := timeStampTestFIFOBHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portCF := {|
        ConstraintAutomata.id := C;
        ConstraintAutomata.dataAssignment := dataAssignmentC;
        ConstraintAutomata.timeStamp := timeStampFIFOC;
        ConstraintAutomata.portCond := timeStampTestFIFOCHolds;
        ConstraintAutomata.index := 0 |}.

  Definition realports := [portAF;portBF;portCF].

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
  Definition oneBoundedFIFOrel (s:fifoStates) 
  (*set (set (ports) * ConstraintAutomata.DC ports (option nat) * set states)*) :=
    match s with
    | q0a => [([A], (ConstraintAutomata.dc A (Some 0)), [p0a]) ;
              ([A], (ConstraintAutomata.dc A (Some 1)), [p1a])]
    | p0a => [([B], (ConstraintAutomata.dc B (Some 0)), [q0a])]
    | p1a => [([B], (ConstraintAutomata.dc B (Some 1)), [q0a])] 
    | q0b | p0b | p1b => []
    end.

  Definition oneBoundedFIFOCA:= {|
    ConstraintAutomata.Q := [q0a;p0a;p1a];
    ConstraintAutomata.N := [A;B];
    ConstraintAutomata.T := oneBoundedFIFOrel;
    ConstraintAutomata.Q0 := [q0a]
  |}.

  Eval compute in ConstraintAutomata.run oneBoundedFIFOCA realports 10.

(*Second FIFO CA *)

  Definition oneBoundedFIFOrel2 (s:fifoStates) 
  (*set (set (ports) * ConstraintAutomata.DC ports (option nat) * set states)*) :=
    match s with
    | q0b => [([B], (ConstraintAutomata.dc B (Some 0)), [p0b]) ;
              ([B], (ConstraintAutomata.dc B (Some 1)), [p1b])]
    | p0b => [([C], (ConstraintAutomata.dc C (Some 0)), [q0b])]
    | p1b => [([C], (ConstraintAutomata.dc C (Some 1)), [q0b])] 
    | q0a | p0a | p1a => []
    end.

  Definition oneBoundedFIFOCA2 := {|
    ConstraintAutomata.Q := [q0b;p0b;p1b];
    ConstraintAutomata.N := [B;C];
    ConstraintAutomata.T := oneBoundedFIFOrel2;
    ConstraintAutomata.Q0 := [q0b]
  |}.

  Definition twoBoundedFifo := ProductAutomata.buildPA oneBoundedFIFOCA oneBoundedFIFOCA2.

  (* Eval compute in ConstraintAutomata.T twoBoundedFifo (p0a, q0b).
  Eval compute in ConstraintAutomata.Q twoBoundedFifo.
  Eval compute in ConstraintAutomata.xamboca2 twoBoundedFifo realports 5.
  Eval compute in ConstraintAutomata.run twoBoundedFifo realports 6. *)

  (* Lemma productTransition : forall s, ConstraintAutomata.T twoBoundedFifo s = [([B], ConstraintAutomata.andDc (ConstraintAutomata.dc B (Some 0)) (ConstraintAutomata.dc B (Some 0)),
        [(q0a, p0b)]);
       ([B], ConstraintAutomata.andDc (ConstraintAutomata.dc B (Some 0)) (ConstraintAutomata.dc B (Some 1)),
       [(q0a, p1b)])]
        <-> s = (p0a, q0b).
  Proof.
  split.
  - intros. induction s. simpl in H. simpl in H. unfold ProductAutomata.transitionPA in H. 
    unfold oneBoundedFIFOCA in H. unfold oneBoundedFIFOCA2 in H. case_eq ((a, b) == (p0a, q0b)).
    intros. inversion e. reflexivity.  simpl in H. *)

  Definition ru6 := Eval compute in ConstraintAutomata.run twoBoundedFifo realports 6.

  Lemma ru6Accept : ~ (In ([]) (ru6)).
  Proof.
  intros. unfold not. unfold ru6. simpl. intros. repeat (destruct H ; inversion H). Defined.

  (* Second data flow *)

    Definition dataAssignmentA2 n := 
    match n with
    | 0 => Some 0
    | 1 => Some 0
    | 2 => Some 1
    | S n => Some (0)
    end.

  Definition dataAssignmentB2 n :=
    match n with
    | 0 => Some 0
    | 1 => Some (0)
    | 2 => Some 1
    (*| 3 | 4 | 5 => Some 1
    | 6 => None *)
    | S n => Some 1
    end.

  Definition timeStampFIFOA2(n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | 1 =>  3#1
    | 2 =>  7#1
    | 3 =>  10#1
    | 4 =>  13#1
    | 5 =>  15#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1 
    end.

  Definition timeStampFIFOB2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  2#1 (*1#1*)
    | 1 =>  5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition dataAssignmentC2 n :=
    match n with
    | 0 => Some 0
    | 1 => Some (0)
    | 2 => Some 1
    (*| 3 | 4 | 5 => Some 1
    | 6 => None *)
    | S n => Some 0
    end.

  Definition timeStampFIFOC2(n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  4#1
    | 1 =>  6#1
    | 2 =>  9#1
    | 3 =>  12#1
    | 4 =>  15#1
    | 5 =>  18#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1 
    end.

  Lemma timeStampTestFIFOA2Holds : forall n, Qle (timeStampFIFOA2 n) (timeStampFIFOA2 (S n)).
  Proof.
  induction n. 
  + unfold timeStampTest. cbv. intros. inversion H.
  + unfold timeStampTest.
  Admitted.

  Lemma timeStampTestFIFOB2Holds : forall n, 
    Qle (timeStampFIFOB2 n) (timeStampFIFOB2 (S n)). 
  Proof.
  Admitted.

  Lemma timeStampTestFIFOC2Holds : forall n, 
    Qle (timeStampFIFOC2 n) (timeStampFIFOC2 (S n)). 
  Proof.
  Admitted.

  Definition portA2 := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA2;
        ConstraintAutomata.timeStamp := timeStampFIFOA2;
        ConstraintAutomata.portCond := timeStampTestFIFOA2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portB2 := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB2;
        ConstraintAutomata.timeStamp := timeStampFIFOB2;
        ConstraintAutomata.portCond := timeStampTestFIFOB2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition portC2 := {|
        ConstraintAutomata.id := C;
        ConstraintAutomata.dataAssignment := dataAssignmentC2;
        ConstraintAutomata.timeStamp := timeStampFIFOC2;
        ConstraintAutomata.portCond := timeStampTestFIFOC2Holds;
        ConstraintAutomata.index := 0 |}.

  Definition ru62 := Eval compute in ConstraintAutomata.run twoBoundedFifo [portA2;portB2;portC2] 8.

  Lemma ru62Accept : ~ (In ([]) (ru62)).
  Proof.
  intros. unfold not. unfold ru62. simpl. intros. repeat (destruct H ; inversion H). Defined.

  Lemma fullFifoWith0 : In [(p0a,p0b)] ru62.
  Proof. simpl; auto. Defined.

  
