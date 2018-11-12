Require Import CaMain.

(* Alternating Bit Protocol *)

Inductive abpStates := s0 | s1 | r0 | r1.
Inductive abpPorts := A | B.

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
		| A,B => in_right 
		| B,A => in_right 
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


  Definition apbRel (s:abpStates) 
  (*set (set (ports) * ConstraintAutomata.DC ports (option nat) * set states)*) :=
    match s with
    | s0 => [([A;B], ConstraintAutomata.andDc (ConstraintAutomata.dc A (Some 0))
                                             (ConstraintAutomata.dc B (Some 0)), [r0]);
             ([A],  ConstraintAutomata.dc A (Some 0), [s0])]
    | r0 => [([A;B], ConstraintAutomata.andDc (ConstraintAutomata.dc A (Some 0))
                                             (ConstraintAutomata.dc B (Some 0)), [s1]);
             ([B],  ConstraintAutomata.dc B (Some 0), [r0]);
             ([A],  ConstraintAutomata.dc A (Some 0), [s0])] (* ou r0? (a pode enviar mesmo depois de b ter recebido mas não respondeu *)
    | s1 => [([A;B], ConstraintAutomata.andDc (ConstraintAutomata.dc A (Some 1))
                                             (ConstraintAutomata.dc B (Some 1)), [r1]);
             ([A],  ConstraintAutomata.dc A (Some 1), [s1])]
    | r1 => [([A;B], ConstraintAutomata.andDc (ConstraintAutomata.dc A (Some 1))
                                             (ConstraintAutomata.dc B (Some 1)), [s0]);
             ([B],  ConstraintAutomata.dc B (Some 1), [r1]); (*ver o correspondente pra r0 *)
             ([A],  ConstraintAutomata.dc A (Some 1), [s1])]
    (* | s0 => [([A], (ConstraintAutomata.dc A (Some 0)), [r1])]
    | r1 => [([A], (ConstraintAutomata.dc A (Some 0)), [r1]);
               [A], (ConstraintAutomata.dc A (Some 0)), [r1]]
    | r0 => [([B], (ConstraintAutomata.dc B (Some 1)), [s0])] 
    | s1 | p0b| p1b => [] *)
    end.

  Definition abpCA:= {|
    ConstraintAutomata.Q := [s0;s1;r0;r1];
    ConstraintAutomata.N := [A;B];
    ConstraintAutomata.T := apbRel;
    ConstraintAutomata.Q0 := [s0]
  |}.

  (* Non accepting data flow *)

  Definition runAbpCAnotAccept :=  Eval compute in ConstraintAutomata.run abpCA [portAP; portBP] 4.

  Lemma runAbpCAnotAc : In [] runAbpCAnotAccept.
  Proof. simpl. repeat (right;auto). Defined.

  Eval compute in runAbpCAnotAccept.

  (* Accepting Data flow *)


   Definition dataAssignmentAS n := 
    match n with
    | 0 => Some 0
    | 1 => Some 0
    | 2 => Some 1
    | 3 => Some 1
    | 4 => Some 0
    | 5 => Some 0
    | 6 => Some 1
    | S n => Some 1
    end.

  Definition dataAssignmentBS n :=
    match n with
    | 0 => Some 0
    | 1 => Some (0)
    | 2 => Some 1
    (*| 3 | 4 | 5 => Some 1
    | 6 => None *)
    | 3 => Some 1
    | 4 => Some 0
    | 5 => Some 0
    | 6 => Some 1
    | S n => Some 1
    end.

   Definition timeStampABPAS(n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1 
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampABPBS (n:nat) : QArith_base.Q :=
    match n with
    | 0 => 2#1
    | 1 => 5#1
    | 2 => 8#1
    | 3 => 11#1
    | 4 => 14#1
    | 5 => 17#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Lemma timeStampTestABPASHolds : forall n, Qle (timeStampABPA n) (timeStampABPA (S n)).
  Proof.
  Admitted.

  Lemma timeStampTestABPBSHolds : forall n, 
    Qle (timeStampABPB n) (timeStampABPB (S n)). 
  Proof.
  Admitted.

  Definition portAPS := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentAS;
        ConstraintAutomata.timeStamp := timeStampABPAS;
        ConstraintAutomata.portCond := timeStampTestABPASHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portBPS := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentBS;
        ConstraintAutomata.timeStamp := timeStampABPBS;
        ConstraintAutomata.portCond := timeStampTestABPBSHolds;
        ConstraintAutomata.index := 0 |}.

  Definition steamAcce := Eval compute in ConstraintAutomata.run abpCA [portAPS;portBPS] 7.
  Lemma streamAccept8 : ~ In ([]) (steamAcce).
  Proof. simpl. unfold not. intros. repeat (destruct H; inversion H). Defined.
