Require Import ListSet.
Require Import List.
Require Import Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import QArith.
Require Import Coq.Numbers.BinNums.
Require Import Coq.micromega.Lia.

Open Scope Q_scope.

(* The following lemma was formalized thanks to anonymous reviewers' contribution *)
Lemma orderZofNat : forall n, forall a, (Z.of_nat (S n) + a) # 1 < Z.of_nat (S (S n)) + a # 1.
Proof.
intros.
assert (forall z, z # 1 < (z + 1) # 1).
+ intros. assert (inject_Z z < inject_Z (z + 1)). rewrite <- Zlt_Qlt. 
  omega. unfold inject_Z in H. exact H.
+ assert (forall b, forall a, (b + a) # 1 < ((b + 1) + a) # 1).
  intros. rewrite <- Z.add_assoc. rewrite (Z.add_comm 1).
  rewrite Z.add_assoc. apply H.
  assert (forall n, Z.of_nat (S n) = ((Z.of_nat n) + 1)%Z).
  intro. simpl. lia. rewrite (H1 ((S n))). apply H0. Defined.

Close Scope Q_scope.

Obligation Tactic := unfold complement, equiv ; program_simpl.


Set Implicit Arguments.
Set Maximal Implicit Insertion.


Import ListNotations.
(* ---------------------------------------- Utils ---------------------------------------------------------------- *)

Instance option_eqdec A `(EqDec A eq) : EqDec (option A) eq :=
{
  equiv_dec x y :=
    match x, y with
      | Some a, Some b => if a == b then in_left else in_right
      | None, None => in_left
      | Some _, None | None, Some _ => in_right
    end
 }.
Proof.
all:congruence.
Defined.

Instance pair_eqdec A B `(EqDec A eq) `(EqDec B eq) : EqDec (A * B) eq :=
{
  equiv_dec x y:=
    match x, y with
      | (a, b), (c,d) => if a == c then
                            if b == d then in_left else in_right
                         else in_right
    end
}.
Proof.
all: congruence.
Defined.

Program Fixpoint s1_in_s2 {A} `{EqDec A eq} (s1 s2 : set A) :=
  match s1 with
    | [] => true
    | a::t => set_mem equiv_dec a s2 && s1_in_s2 t s2
  end.

Fixpoint set_eq {A} `{EqDec A eq} (s1 s2 : set A) :=
  if (length s1 == length s2) then
      if (s1_in_s2 s1 s2) then
          if (s1_in_s2 s2 s1) then true else false
      else false
  else false.

Lemma set_eq_sound {A} `{EqDec A eq} : forall s1 : set A, forall s2 : set A,
   set_eq s1 s2 = true <-> ((length s1 = length s2))
   /\ s1_in_s2 s1 s2 = true /\ s1_in_s2 s2 s1 = true.
  Proof.
  split.
  - intros. destruct s1. destruct s2.
  + split. reflexivity. split. assumption. assumption.
  + inversion H0.
  + unfold set_eq in H0. destruct equiv_dec in H0.
    case_eq (s1_in_s2 (a :: s1) s2). case_eq (s1_in_s2 s2 (a :: s1)). intros. rewrite H1 in H0. rewrite H2 in H0. inversion e.
    split. reflexivity. auto. intros. rewrite H2 in H0. rewrite H1 in H0. inversion H0. intros. 
    rewrite H1 in H0. inversion H0. congruence. 
  - intros. destruct s1. destruct s2.
  + reflexivity.
  + destruct H0. inversion H0.
  + simpl. destruct H0. destruct H1. simpl in H0. rewrite H0.
    simpl s1_in_s2 in H1. rewrite H1. rewrite H2. repeat simpl. destruct equiv_dec. reflexivity. congruence.
  Defined.


(* --------------------------------------------------------------------------------------------------------------- *)

Module ConstraintAutomata.
  Section ConstraintAutomata.

    Variable state name data: Set. 

    Context `{EqDec name eq} `{EqDec state eq} `{EqDec (data) eq}.

    Notation " a <? b " := (negb (Qle_bool b a)).
    Notation "a =? b" := (Qeq_bool a b).

    Record port := mkport {
      id : name;
      dataAssignment : nat -> data; 
      timeStamp : nat -> QArith_base.Q;
      portCond : forall n:nat, Qlt (timeStamp n) (timeStamp (S n));
      index : nat

    }.

    Inductive DC name data:= 
    | tDc : DC name data
    | dc : name -> data -> DC name data
    | eqDc : name -> name -> DC name data
    | andDc : DC name data -> DC name data -> DC name data
    | orDc  : DC name data -> DC name data -> DC name data
    | trDc  : (data -> data) -> name -> name -> DC name data
    | negDc : DC name data -> DC name data.

    Notation "a @ b" := (andDc a b)(no associativity, at level 69).
    Notation "a $ b" := (orDc a b) (no associativity, at level 69).

    Definition evalDC (po: option port) (d : data) : bool :=
       match po with
       | Some p => if (dataAssignment p(index p) == d) then true else false
       | None => false
       end.

    Lemma evalDCSound : forall po, forall d, evalDC po d = true <-> exists x, po = Some x /\ 
      dataAssignment x(index x) = d.
    Proof.
    split.
    - intros. destruct po. simpl in H2. destruct equiv_dec in H2.
    + exists p. inversion e. auto.
    + inversion H2.
    + inversion H2.
    - intros. destruct H2. destruct H2. rewrite H2. unfold evalDC. rewrite H3. destruct equiv_dec.
      reflexivity. congruence.
    Defined.


    (* The following definition searches for a port in a set of tds, returning it if it exists and None otherwise *)
    Fixpoint retrievePortFromInput (s:set port) (n: name) :=
      match s with
      | [] => None
      | a::t => if (n == id a) then Some a else retrievePortFromInput t n
      end.
    Lemma retrievePortFromInputSound : forall s:set port, forall n: name,forall a, retrievePortFromInput s n = Some a
    -> In a s /\ n = id a.
    Proof.
    - intros. 
    + induction s. inversion H2.
    simpl in H2. destruct equiv_dec in H2. inversion e. split. inversion H2. simpl. auto. inversion H2. reflexivity.
    apply IHs in H2. split. simpl. destruct H2. right. exact H2. destruct H2. exact H3. Defined.

    Definition eqDataPorts (n1: name) (n2: name) (s: set port) :=
      match (retrievePortFromInput s n1) with
      | Some a => match (retrievePortFromInput s n2) with
                  | Some b => if (dataAssignment a(index a)) == (dataAssignment b(index b)) then true else false
                  | None => false
                  end
      | None => false
      end.

    Lemma eqDataPortsSound : forall n1, forall n2, forall s , eqDataPorts n1 n2 s = true <-> 
      exists a, retrievePortFromInput s n1 = Some a /\ exists b, retrievePortFromInput s n2 = Some b 
      /\ (dataAssignment a(index a)) = (dataAssignment b(index b)).
    Proof.
    split.
    - intros. unfold eqDataPorts in H2. case_eq (retrievePortFromInput s n1). 
      case_eq (retrievePortFromInput s n2).
    + intros. rewrite H3 in H2.  rewrite H4 in H2. destruct equiv_dec in H2. inversion e.
      exists p0. split. reflexivity. exists p. split. reflexivity. assumption.
      inversion H2.
    + intros. rewrite H4 in H2. rewrite H3 in H2. inversion H2.
    + intros. rewrite H3 in H2. inversion H2.
    - intros. destruct H2. destruct H2. destruct H3. destruct H3. 
      unfold eqDataPorts. rewrite H2. rewrite H3. rewrite H4. destruct equiv_dec. reflexivity. congruence.
  Defined.

    Definition transformDC (transform: data -> data) (n1: name) (n2: name) (s:set port) :=
      match (retrievePortFromInput s n1) with
      | Some a => match (retrievePortFromInput s n2) with
                  | Some b => if transform((dataAssignment a(index a))) == (dataAssignment b(index b)) then true else false
                  | None => false
                  end
      | None => false
      end.

    Lemma transformDCsound : forall transform, forall n1, forall n2, forall s, transformDC transform n1 n2 s = true <->
      exists a, retrievePortFromInput s n1 = Some a /\ exists b, retrievePortFromInput s n2 = Some b 
      /\ transform((dataAssignment a(index a))) = (dataAssignment b(index b)).
    Proof.
    split.
    - intros. unfold transformDC in H2. case_eq (retrievePortFromInput s n1). 
      case_eq (retrievePortFromInput s n2).
    + intros. rewrite H3 in H2.  rewrite H4 in H2. destruct equiv_dec in H2. inversion e.
      exists p0. split. reflexivity. exists p. split. reflexivity. assumption.
      inversion H2.
    + intros. rewrite H4 in H2. rewrite H3 in H2. inversion H2.
    + intros. rewrite H3 in H2. inversion H2.
    - intros. destruct H2. destruct H2. destruct H3. destruct H3. 
      unfold transformDC. rewrite H2. rewrite H3. rewrite H4. destruct equiv_dec. reflexivity. congruence.
    Defined.

    Fixpoint evalCompositeDc (s:set port) (dc: DC name data) : bool :=
      match dc with
      | tDc _ _ => true
      | dc a b => evalDC (retrievePortFromInput s a) (b)
      | eqDc _ a b => eqDataPorts a b s
      | andDc a b => evalCompositeDc s a && evalCompositeDc s b
      | orDc a b => evalCompositeDc s a || evalCompositeDc s b
      | trDc transform a b  => transformDC transform a b s
      | negDc a => negb (evalCompositeDc s a)
      end.  

      Lemma evalCompositeDcSound : forall s, forall dca: DC name data, evalCompositeDc s dca = true <-> 
      dca = tDc _ _ \/ 
      (exists a, exists b, dca = dc a b /\ (evalDC (retrievePortFromInput s a) b) = true ) \/
      (exists a, exists b, dca = eqDc _ a b /\ eqDataPorts a b s = true) \/
      (exists a, exists b, dca = andDc a b /\ evalCompositeDc s a && evalCompositeDc s b = true) \/
      (exists a,exists b, dca = orDc a b /\ evalCompositeDc s a || evalCompositeDc s b = true) \/
      (exists a, exists b, exists tr, dca = trDc tr a b /\ transformDC tr a b s = true) \/
      (exists a, dca = negDc a /\ negb (evalCompositeDc s a) = true).
      Proof.  
      split.
      - intros. destruct dca.
      + left. reflexivity.
      + simpl in H2. right. left. exists n. exists d. auto.
      + simpl in H2. right. right. left. exists n. exists n0. auto.
      + simpl in H2. right. right. right. left.  exists dca1. exists dca2. auto.
      + simpl in H2. right. right. right. right. left. exists dca1. exists dca2. auto.
      + simpl in H2. right. right. right. right. right. left. exists n. exists n0. exists d. auto.
      + simpl in H2. repeat right. exists dca.  auto.
      - intros. destruct H2.
      + rewrite H2. reflexivity.
      + destruct H2. destruct H2. destruct H2. destruct H2. rewrite H2. simpl. exact H3.
        destruct H2. destruct H2. destruct H2. destruct H2. rewrite H2. simpl. exact H3.
        destruct H2. destruct H2. destruct H2. destruct H2. rewrite H2. simpl. exact H3.
        destruct H2. destruct H2. destruct H2. destruct H2. rewrite H2. simpl. exact H3.
        destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. rewrite H2. simpl. exact H3.
        destruct H2. destruct H2. rewrite H2. simpl. exact H3.
      Defined. 

    Record constraintAutomata : Type := CA {
      Q : set state;
      N : set name;
      T : state -> set (set (name) * DC name data * state);
      Q0 : set state;
    }.

    Fixpoint returnSmallerNumber (m:QArith_base.Q) (l:set QArith_base.Q) :=
      match l with
      | [] => m
      | a::t => if ((a <? m)) then 
                   returnSmallerNumber a t else returnSmallerNumber m t
      end.
    Open Scope Q_scope.

    Theorem returnSmallerNumber_sound : forall m, forall l, returnSmallerNumber m l <> m 
    -> l <> [] /\ exists a, In a l /\ a <? m = true.
    Proof.
    - intros.
    induction l.
    unfold returnSmallerNumber in H2. congruence.
    simpl in H2. split.
    discriminate.
    case_eq (a <? m). intros. rewrite H3 in H2. exists a. simpl. auto.
    intros. rewrite H3 in H2. apply IHl in H2. destruct H2. repeat (destruct H4).
    exists x. split. simpl. right. exact H4. exact H5.
    Defined.

    Notation "x |> f" := (f x) (at level 69, only parsing).

    Close Scope Q_scope.

    Definition getThetaTimeCandidate (p:port) :=
      [timeStamp p(index(p))].

    Fixpoint getAllThetaTimes (s: set port) :=
      match s with
      | [] => []
      | a::t => getThetaTimeCandidate a++getAllThetaTimes t
      end.
    Lemma getAllThetaTimesSound : forall s: set port, getAllThetaTimes s <> [] <-> exists a, In a s.
    Proof.
    split.
    - intros. destruct s. simpl in H2. congruence. exists p. simpl. auto.
    - intros. destruct s. inversion H2. inversion H3. simpl. discriminate.
    Defined.

    Definition minimum (l: set QArith_base.Q) :=
       returnSmallerNumber (hd (Qmake 0 1) l) (tl l).

    Definition thetaTime (s:set port) :=
      minimum(getAllThetaTimes s).

    Definition timeStampEqThetaTime (s:set port) (a:port) :=
      (timeStamp a(index a) =? thetaTime (s)).

    Lemma timeStampEqThetaTimeSound : forall s, forall a, timeStampEqThetaTime s a = true <-> 
      ((timeStamp a(index a) =? thetaTime (s)) = true).
    Proof.
    split.
    - intros. unfold timeStampEqThetaTime in H2. exact H2.
    - intros. unfold timeStampEqThetaTime. rewrite H2. reflexivity.
    Defined.

    Fixpoint thetaN (tds: set port) (tds2:set port) : set name := 
      match tds2 with
      | a::t => if (timeStampEqThetaTime tds a ) then
                    id a :: thetaN tds t
                else thetaN tds t
      | []   => []
      end.

    Lemma thetaNSound : forall tds, forall tds2, thetaN tds tds2 <> [] <-> 
    (exists a, In a tds2 /\ timeStampEqThetaTime tds a = true).
    Proof.
    split.
    - intros. induction tds2.
    + simpl in H2. congruence.
    + simpl in H2. case_eq (timeStampEqThetaTime tds a).
    { intros. exists a. split. simpl;auto. exact H3. }
    { intros. rewrite H3 in H2. apply IHtds2 in H2. destruct H2. destruct H2.
      exists x. split. simpl;auto. exact H4. }
    -  intros. induction tds2. 
    + destruct H2.  destruct H2. inversion H2.
    + simpl. case_eq (timeStampEqThetaTime tds a). intros. discriminate.
      intros. apply IHtds2. destruct H2. destruct H2. simpl in H2. destruct H2.  rewrite <- H2 in H4. 
      congruence. exists x. split. exact H2. exact H4.
    Defined. 

    Fixpoint thetaDelta (tds: set port) (tds2:set port) : set((name * data)) := 
      match tds2 with
      | a::t => if (timeStampEqThetaTime tds a) then
                   ((id a) , (dataAssignment a(index(a)))) :: thetaDelta tds t
                else thetaDelta tds t
      | []   => []
      end.

    Lemma thetaDeltaSound : forall tds, forall tds2, thetaDelta tds tds2 <> [] <-> 
    (exists a, In a tds2 /\ timeStampEqThetaTime tds a = true).
    Proof.
    split.
    - intros. induction tds2.
    + simpl in H2. congruence.
    + simpl in H2. case_eq (timeStampEqThetaTime tds a).
    { intros. exists a. split. simpl;auto. exact H3. }
    { intros. rewrite H3 in H2. apply IHtds2 in H2. destruct H2. destruct H2.
      exists x. split. simpl;auto. exact H4. }
    -  intros. induction tds2. 
    + destruct H2.  destruct H2. inversion H2.
    + simpl. case_eq (timeStampEqThetaTime tds a). intros. discriminate.
      intros. apply IHtds2. destruct H2. destruct H2. simpl in H2. destruct H2.  rewrite <- H2 in H4. 
      congruence. exists x. split. exact H2. exact H4.
    Defined. 

    Close Scope Q_scope.

    Definition derivative (p: port) := mkport (id p) (dataAssignment p) (timeStamp p)
        (portCond p) (S (index p)).

    Lemma derivative_sound : forall p, derivative p = mkport (id p) (dataAssignment p) (timeStamp p)
        (portCond p) ( S(index p)).
    Proof.
    reflexivity.
    Defined.

    Fixpoint derivativePortInvolved (s:set name) (a: port)  :=
      match s with
      | [] => [a] 
      | x::t => if x == id a then [derivative(a)]
                else derivativePortInvolved t a
      end.

    Definition allDerivativesFromPortsInvolved (names: set name) (tds:set port) : set port :=
      flat_map (derivativePortInvolved names) tds.

    Definition portsDerivative (names: set name) (tds: set port) := 
      allDerivativesFromPortsInvolved names tds. 

    Fixpoint portsOutsideTransition (p: port) (portNames : set name) :=
      match portNames with
       | [] => true
       | a::t => if (id p <> a) then portsOutsideTransition p t else false
      end.

    Lemma portsOutsideTransitionSound : forall p, forall portNames, portsOutsideTransition p portNames = false <->
      (exists b, In b portNames /\ (id p = b)).
    Proof.
    split.
    - intros. induction portNames.
    + simpl in H2. inversion H2.
    + simpl in H2. destruct nequiv_dec in H2. apply IHportNames in H2.
      repeat destruct H2. exists x. split.
      simpl;auto.
      exact H3.
      inversion e. exists a.
      split. simpl;auto.
      exact H3.
    - intros. induction portNames.
    + repeat destruct H2.
    + simpl. destruct nequiv_dec. apply IHportNames. repeat destruct H2. congruence. exists x. split; assumption.
      reflexivity. 
    Defined.
    
    Definition retrievePortsFromThetaN (tds: set port) :=
      thetaN (tds) (tds).

    Fixpoint step' (tds : set port) (portNames: set name)
     (transitions: set(set name * DC name data * state)) :=
     match transitions with
     | [] => []
     | a::t => if (set_eq (portNames)((fst(fst(a))))) 
                   && (evalCompositeDc (tds) (snd(fst(a)))) then snd(a)::step' tds portNames t
                   else step' tds portNames t
     end.

    Lemma step'_sound : forall tds, forall portNames, forall transitions, step' tds portNames transitions <> [] -> exists a,
    In a transitions /\ (set_eq (portNames)((fst(fst(a)))))
                   && (evalCompositeDc (tds) (snd(fst(a)))) = true.
    Proof. 
    - intros. induction transitions. simpl in H2. congruence. simpl in H2. 
    case_eq (set_eq (portNames)((fst(fst(a))))). 
    case_eq (evalCompositeDc tds (snd (fst a))). intros.
    + exists a. split. simpl;auto. rewrite H3. rewrite H4. reflexivity.
    + intros. rewrite H3 in H2. rewrite H4 in H2. apply IHtransitions in H2.
      destruct H2. destruct H2. exists x. split. simpl;auto. exact H5.
    + intros. rewrite H3 in H2. apply IHtransitions in H2.
      destruct H2. destruct H2. exists x. split. simpl;auto. exact H4.
    Defined.

    Definition stepAux (ca:constraintAutomata) (tds:set port) (portNames:set name) (s: state) :=
      step' tds portNames (T ca s).

    (* We apply the step to every state in the given configuration:                     *)
    Definition stepa (ca:constraintAutomata) (s: set state) (tds:set port) (portNames: set name):=
     (portNames, flat_map (stepAux ca tds portNames) s).

    Definition step (ca:constraintAutomata) (s: set state) (tds:set port) :=
      stepa ca s tds (retrievePortsFromThetaN tds).

    Definition run' (ca:constraintAutomata)  : 
      set port -> nat -> set state -> set (set state) -> set (set state) :=
      fix rec tds k initialStates trace := 
        match k with 
          | 0 => trace
          | S m => trace ++ [snd (step ca initialStates tds)]
                    |> rec
                      (flat_map(derivativePortInvolved(fst((step ca initialStates tds)))) tds) m (snd (step ca initialStates tds))
        end.

    Definition run (ca:constraintAutomata) (tds: set port) (k : nat) :=
      run' ca tds k (Q0 ca) [Q0 ca].

  (* We define some functions to retrieve data from transitions, in order to prove *)
  (* properties about behavior of automata                                         *)

  Fixpoint retrievePortsFromRespTransitions (s : set (set (name) * DC name data * state)) :=
    match s with
    | [] => []
    | a::t => set_union equiv_dec (fst (fst a) ) (retrievePortsFromRespTransitions t)
    end.

  Definition portsOfTransition (ca: constraintAutomata) (s : state) :=
    retrievePortsFromRespTransitions (ConstraintAutomata.T ca s).

  (* Bisimulation as boolean verification *)

  (* We filter the transition to be compared with a transition that contains the same name set *)
  Fixpoint getTransition (portNames: set name) (t2 : set (set(name) * DC name data * state)) :=
    match t2 with
    | [] => [] 
    | a::t => if (set_eq portNames (fst(fst(a)))) then a::getTransition portNames t else getTransition portNames t
    end. 

  (* We need to evalate whether the next reached states are also equivalent. Then, we need to store *)
  (* pairs of states to be evaluated *)
  Fixpoint getReachedStatesFromPair (t1 : (set(name) * DC name data * state)) (setT2 : set (set(name) * DC name data * state)) :=
    match setT2 with
    | [] => []
    | a::nextT2 =>  set_add equiv_dec (snd(t1),snd(a)) (getReachedStatesFromPair t1 nextT2)
    end.

  (* Check whether exists a transition with port names equal to the port name of a single transition of A1 *)
  Fixpoint iterateTransitionsQ1A1 (ca1: constraintAutomata) (ca2: constraintAutomata) (q1: state) (q2: state) 
    (setT1 : set (set(name) * DC name data * state)) (setT2: set (set(name) * DC name data * state)) 
    (acc: set (state * state)) :=
    match setT1 with
    | [] => (q1,q2)::acc 
    | a::t => if set_eq ((getReachedStatesFromPair (a) (getTransition (fst(fst(a))) (setT2)))) ([]) then [] else 
              ((getReachedStatesFromPair (a) (getTransition (fst(fst(a))) (setT2))))++ iterateTransitionsQ1A1 ca1 ca2 q1 q2 t setT2 acc
    end.
 
  (* Expanding the reached states *)
  Definition iterateOverNextStates (ca1: constraintAutomata) (ca2: constraintAutomata) (acc : set (state * state))
  (states : set (state * state)) :=
    match states with
    | [] => []
    | a::t => iterateTransitionsQ1A1 ca1 ca2 (fst(a)) (snd(a)) (ConstraintAutomata.T ca1 (fst(a))) 
              (ConstraintAutomata.T ca2 (snd(a))) acc 
    end.

  Fixpoint bisimilarStates (ca1: constraintAutomata) (ca2: constraintAutomata) (q1: state) (q2: state) 
    (setT1 : set (set(name) * DC name data * state)) (setT2: set (set(name) * DC name data * state)) 
    (acc: set (state * state)) :=
    match setT1 with
    | [] => (q1,q2)::acc
    | a::t => if set_eq ((getReachedStatesFromPair (a) (getTransition (fst(fst(a))) (setT2)))) ([]) then [] else
              bisimilarStates ca1 ca2 q1 q2 t setT2 acc
    end.

  (* Retrieving only the bisimilar states after each round. *)
  Fixpoint retrieveCleanStates (ca1: constraintAutomata) (ca2: constraintAutomata)
  (acc: set (state * state)) (states: set (state * state)) :=
    match states with
    | [] => []
    | a::t => set_union equiv_dec (bisimilarStates ca1 ca2 (fst(a)) (snd(a)) (ConstraintAutomata.T ca1 (fst(a))) (ConstraintAutomata.T ca2 (snd(a))) acc)
              (retrieveCleanStates ca1 ca2 acc t)
    end. 
  
  (* Auxiliary definition that iterates over the set of (possible) bisimilar states, recursively verifying whether they indeed are bisimilar *)
  Definition evaluateObtainedStates (ca1: constraintAutomata) (ca2: constraintAutomata) : nat -> set (state * state) -> 
  set (state * state) -> set (state * state) :=
    fix rec steps acc nextPairStates :=
    match steps with
    | 0 =>  acc
    | S n =>
            set_union equiv_dec (rec n acc (iterateOverNextStates ca1 ca2 acc nextPairStates)) 
            (retrieveCleanStates ca1 ca2 acc ((iterateOverNextStates ca1 ca2 acc nextPairStates)))
    end.

  Fixpoint iterateOverA2States (ca1: constraintAutomata) (ca2: constraintAutomata) (q1: state) (q2: set (state)) 
    (acc: set (state * state)) :=
    match q2 with
    | [] => acc
    | a::t => evaluateObtainedStates ca1 ca2 (length(ConstraintAutomata.Q(ca1))) acc [(q1,a)]  
              ++ iterateOverA2States ca1 ca2 q1 t acc
    end.  

  Fixpoint iterateOverA1States (ca1: constraintAutomata) (ca2: constraintAutomata) (q1: set (state)) (q2: set (state)) 
  (acc: set (state * state)) : set (state * state) :=
    match q1 with
    | [] => acc
    | a::t => iterateOverA2States ca1 ca2 a q2 acc ++ iterateOverA1States ca1 ca2 t q2 acc
    end.

  Fixpoint containsSymmetric (setPairs : set (state * state)) (setPairsFull: set (state * state)):=
    match setPairs with
    | [] => []
    | a::t => match a with
              | (q1,q2) => if existsb (fun x : (state * state) => match x with
                                       |(a,b) => (equiv_decb a q2) && (equiv_decb b q1)  end) (setPairsFull) then (q1,q2)::containsSymmetric t setPairsFull
                           else containsSymmetric t setPairsFull
              end
    end.

  Fixpoint isSymmetricAux (setPairs : set (state * state)) (setPairsFull: set (state * state)) :=
    set_eq (setPairs) (containsSymmetric (setPairs) setPairsFull).

  Definition bisimulationAux (ca1: constraintAutomata) (ca2: constraintAutomata) :=
    (iterateOverA1States ca1 ca2 (ConstraintAutomata.Q0 ca1) (ConstraintAutomata.Q0 ca2) []) ++ 
    (iterateOverA1States ca2 ca1 (ConstraintAutomata.Q0 ca2) (ConstraintAutomata.Q0 ca1) []).

  (* bisimulation is commutative *)
  Lemma bisimulationAuxCommutative : forall ca1, forall ca2, forall a, 
   (In a (bisimulationAux ca1 ca2)) <-> (In a (bisimulationAux ca2 ca1)).
  Proof.
  intros.
  split.
  - intros. unfold bisimulationAux. unfold bisimulationAux in H2. apply in_or_app.
    apply in_app_or in H2. destruct H2. right. exact H2. left. exact H2.
  - intros. unfold bisimulationAux. unfold bisimulationAux in H2. apply in_or_app.
    apply in_app_or in H2. destruct H2. right. exact H2. left. exact H2.
  Defined.

  Definition isEquivalent (setPairs : set (state * state)) :=
    if isSymmetricAux (setPairs) (setPairs) then setPairs else [].

  Definition bisimulation (ca1: constraintAutomata) (ca2: constraintAutomata) :=
    isEquivalent (bisimulationAux ca1 ca2).


  (* We calculate the partition Q / R *)
  Fixpoint mountSubsetFromPairs (pairStates : state) (setPairs : set (state * state)) :=
    match setPairs with
    | [] => [pairStates]
    | a::t => if (fst(a) == pairStates) then set_add equiv_dec (snd(a)) (mountSubsetFromPairs pairStates t)
              else mountSubsetFromPairs pairStates t
    end.

  Fixpoint getQrelR (setRel : set (state * state)) :=
    match setRel with
    | [] => []
    | a::t =>  set_add equiv_dec (mountSubsetFromPairs (fst(a)) (setRel)) (getQrelR t)
    end.


  (* We define the Notation 3.8, DC_A(q,N,P) as Baier et al. define for bisimulation as dcBisim *)

  Fixpoint getReachedDcs (t: set (set name * DC name data * state)) (setStates: set state) :=
    match t with
    | [] => []
    | a::t => if set_mem equiv_dec (snd(a)) (setStates)
              then (snd(fst(a)))::(getReachedDcs t setStates)
              else (getReachedDcs t setStates)
    end.

  Fixpoint orDcs (dc : DC name data) :=
    match dc with
    | andDc a b => ConstraintAutomata.orDc (ConstraintAutomata.negDc (orDcs a)) (ConstraintAutomata.negDc(orDcs b))
    | _ => dc
    end.

  (* Then we build the conjunctions of all dcs of a single transition that reaches a state in P *)
  Fixpoint conjunctionOfDcs (setDcs : set(DC name data))  :=
    match setDcs with
    | [] => ConstraintAutomata.negDc(ConstraintAutomata.tDc name data)
    | a::t => match a with
              | andDc x y => (ConstraintAutomata.orDc (orDcs a) (conjunctionOfDcs t)) 
              | _ => (ConstraintAutomata.orDc (a) (conjunctionOfDcs t))
              end
    end.

   Definition dcBisim (ca: constraintAutomata) (q: state) (portNames : set name) (P: set state) :=
    conjunctionOfDcs((getReachedDcs (getTransition (portNames) (ConstraintAutomata.T ca q))) (P)).

  (* Equivalence for DCs. Requires that an equality relation to be defined for functions data -> data *)
  Context `{EqDec (data -> data) eq}.
  
  Instance dc_eqDec `(EqDec name eq) `(EqDec data eq)  : EqDec (DC name data) eq :=
    { equiv_dec := fix rec dc1 dc2 :=
      match dc1,dc2 with
       | tDc _ _, tDc _ _ => in_left
       | dc a b, dc c d => if a == c then if b == d then in_left else in_right else in_right
       | eqDc _ a b, eqDc _ c d => if a == c then if b == d then in_left else in_right else in_right
       | andDc a b, andDc c d => if rec a c then if rec b d then in_left else in_right else in_right
       | orDc a b, orDc c d => if rec a c then if rec b d then in_left else in_right else in_right
       | negDc a, negDc b => if rec a b then in_left else in_right
       | trDc f a b, trDc g c d => if f == g then if a == c then if b == d then in_left else in_right else in_right else in_right
       | _, _ => in_right
      end
    }.
    Proof. 
    all : congruence.
    Defined.

  (* After reconstructing a DC as Notation 3.8 from a set of possible data constraints of transitions q -> P *)
  (* We need to evaluate whether they are equivalent or not                                                  *)
  Fixpoint dismantleDc (dc: DC name data) :=
    match dc with
    | tDc _ _ => [tDc _ _]
    | eqDc _ a b => [eqDc _ a b]
    | dc a b => [dc]
    | negDc a => [negDc a]
    | trDc f a b => [trDc f a b]
    | orDc a b | andDc a b => set_union equiv_dec (dismantleDc a) (dismantleDc b)
    end.

  (* We search for conditions !A \/ A in a single DC, which makes it always true *)

  Fixpoint existsComplementOrTrue (setDc : set (DC name data)) :=
    match setDc with
    | [] => false
    | a::t => match a with
              | tDc _ _ => true
              | _ => if (set_mem equiv_dec (negDc(a)) (setDc)) then true else (existsComplementOrTrue t)
              end
    end.

  Lemma existsComplementOrTrueSound  : forall setDc,
    existsComplementOrTrue setDc = true -> In (tDc _ _) setDc \/ (exists a, In (a) (setDc) /\ In (negDc(a)) (setDc)).
  Proof.
  - intros. induction setDc. inversion H3. simpl in H3. destruct a. left. simpl;auto.
  + destruct equiv_dec in H3. inversion e. destruct set_mem eqn:ha in H3. apply set_mem_correct1 in ha. unfold set_In in ha. 
    right. exists (dc n d). split. simpl;auto. simpl. right. exact ha. apply IHsetDc in H3.
    destruct H3. left. simpl;auto. destruct H3. destruct H3. right. exists x. split.
    simpl. right. assumption. simpl. right. assumption. 
  + destruct equiv_dec in H3. inversion e. destruct set_mem eqn:ha in H3. apply set_mem_correct1 in ha. unfold set_In in ha. 
    right. exists (eqDc data n n0). split. simpl;auto. simpl. right. exact ha. apply IHsetDc in H3.
    destruct H3. left. simpl;auto. destruct H3. destruct H3. right. exists x. split.
    simpl. right. assumption. simpl. right. assumption. 
  + destruct equiv_dec in H3. inversion e. destruct set_mem eqn:ha in H3. apply set_mem_correct1 in ha. unfold set_In in ha. 
    right. exists (a1 @ a2). split. simpl;auto. simpl. right. exact ha. apply IHsetDc in H3.
    destruct H3. left. simpl;auto. destruct H3. destruct H3. right. exists x. split.
    simpl. right. assumption. simpl. right. assumption. 
  + destruct equiv_dec in H3. inversion e. destruct set_mem eqn:ha in H3. apply set_mem_correct1 in ha. unfold set_In in ha. 
    right. exists (a1 $ a2) . split. simpl;auto. simpl. right. exact ha. apply IHsetDc in H3.
    destruct H3. left. simpl;auto. destruct H3. destruct H3. right. exists x. split.
    simpl. right. assumption. simpl. right. assumption. 
  + destruct equiv_dec in H3. inversion e. destruct set_mem eqn:ha in H3. apply set_mem_correct1 in ha. unfold set_In in ha. 
    right. exists (trDc d n n0). split. simpl;auto. simpl. right. exact ha. apply IHsetDc in H3.
    destruct H3. left. simpl;auto. destruct H3. destruct H3. right. exists x. split.
    simpl. right. assumption. simpl. right. assumption. 
  + destruct equiv_dec in H3. inversion e.
    right. exists (negDc a). split. simpl;auto. simpl. left. reflexivity. destruct set_mem eqn:ha in H3. apply set_mem_correct1 in ha. unfold set_In in ha. 
    right. exists (negDc a). split. simpl;auto. simpl. right. exact ha. apply IHsetDc in H3.
    destruct H3. left. simpl;auto. destruct H3. destruct H3. right. exists x. split.
    simpl. right. assumption. simpl. right. assumption. 
    Qed.
    

  Definition areEquivalentAux (dc1 : set (DC name data)) (dc2: set (DC name data)) :=
    set_eq ((dc1)) ((dc2)) || 
      ((existsComplementOrTrue dc1) && (existsComplementOrTrue dc2)).

  (* We define equivalence of DCs as defined by Notation 3.8 (aforementioned) *)
  Fixpoint areEquivalent (dc1 : DC name data) (dc2: DC name data) :=
    areEquivalentAux (dismantleDc dc1) (dismantleDc dc2).

  (*We define the powerset's construction, in order to verify all possible port names' labels for transitions *)
  Fixpoint powerset (s: set name) :=
    match s with 
    | [] => []
    | a::t => concat (map (fun f => [a::f;f]) (powerset t))
    end.

  (* The comparison of dcBisim for all port names of both automata *)
  Fixpoint compareDcBisimPortName (ca1: constraintAutomata) (ca2: constraintAutomata) (q1: state)
  (q2: state) (P: set state) (setNames: set (set name)) :=
    match setNames with
    | [] => true
    | a::t => areEquivalent((dcBisim (ca1) (q1) a P)) ((dcBisim (ca2) (q2) a P)) && 
              (compareDcBisimPortName ca1 ca2 q1 q2 P t)
    end.

  (* Now we want to know if compareDcBisimPortName holds for every P \in Q / R as elements of the bisimulation relation *)
  Fixpoint compareDcBisimPartition (ca1: constraintAutomata) (ca2: constraintAutomata) (q1: state)
  (q2: state) (setNames: set (set name)) (qMinusR : set (set state)):=
    match qMinusR with
    | [] => true
    | a::t => (compareDcBisimPortName ca1 ca2 q1 q2 a setNames) && (compareDcBisimPartition ca1 ca2 q1 q2 setNames t)
    end.

  (* We need to check if the above condition holds for every pair of states (q1,q2) \in R as the bisim. relation *)
  Fixpoint compareDcBisimStates (ca1: constraintAutomata) (ca2: constraintAutomata) 
  (setNames: set (set name)) (qMinusR : set (set state)) (pairStates : set (state * state)) :=
    match pairStates with
    | [] => true
    | a::t =>  (compareDcBisimPartition ca1 ca2 (fst(a)) (snd(a)) setNames qMinusR) &&
               (compareDcBisimStates ca1 ca2 setNames qMinusR t)
    end.

  (* We have to ensure that all states of both CA have been comprehended by the obtained bisimulation relation *)

  Fixpoint statesA1InSetPairStates (setPairStates: set (state * state)) : set state:=
    match setPairStates with
    | [] => []
    | a::t => set_add equiv_dec (fst(a)) (statesA1InSetPairStates t)
    end.

  Fixpoint statesA2InSetPairStates (setPairStates: set (state * state)) : set state:=
    match setPairStates with
    | [] => []
    | a::t => set_add equiv_dec (snd(a)) (statesA2InSetPairStates t)
    end.

  Definition containsAllStatesOfBothCa (setQ1 : set state) (setQ2 : set state) (setBisim : set (state * state)) :=
    (s1_in_s2 (setQ1) (statesA1InSetPairStates setBisim)) && (s1_in_s2 (setQ2) (statesA2InSetPairStates setBisim)).
  
  Definition areBisimilar (ca1: constraintAutomata) (ca2: constraintAutomata) (bisimRelation : set (state * state)) :=
    if (set_eq (ConstraintAutomata.N ca1) (ConstraintAutomata.N ca2)) then  
    compareDcBisimStates ca1 ca2 (powerset (ConstraintAutomata.N ca1)) (getQrelR (bisimRelation)) (bisimRelation)  &&
    containsAllStatesOfBothCa (ConstraintAutomata.Q ca1) (ConstraintAutomata.Q ca2) (containsSymmetric (bisimRelation) (bisimRelation))
    else false.
    
  Definition languageEquivalent (ca1: constraintAutomata) (ca2: constraintAutomata) :=
    areBisimilar ca1 ca2 (bisimulation ca1 ca2).

  End ConstraintAutomata.
End ConstraintAutomata.

Module ProductAutomata.
  Section ProductAutomata.
    Variable state name data state2: Set.
    Context `{EqDec name eq} `{EqDec state eq} `{EqDec state2 eq} `{EqDec (data) eq}.

    Definition constraintAutomata  := ConstraintAutomata.constraintAutomata state name data.
    Definition constraintAutomata2 := ConstraintAutomata.constraintAutomata state2 name data.
    Definition DC := ConstraintAutomata.DC name data.

    Definition statesSet (a1:ConstraintAutomata.constraintAutomata state name data) (a2:ConstraintAutomata.constraintAutomata state2 name data) :=
      list_prod (ConstraintAutomata.Q a1) (ConstraintAutomata.Q a2).

    Lemma statesSetSound :forall a1,forall a2, forall a, forall b,
      In (a,b) (statesSet a1 a2) <-> In a (ConstraintAutomata.Q a1) /\ In b (ConstraintAutomata.Q a2).
    Proof.
    intros. apply in_prod_iff. 
    Defined.

    Definition nameSet (a1:ConstraintAutomata.constraintAutomata state name data) (a2:ConstraintAutomata.constraintAutomata state2 name data) :=
      set_union equiv_dec (ConstraintAutomata.N a1) (ConstraintAutomata.N a2).
    
    Lemma nameSetSound : forall a1, forall a2, forall a,
      In a (nameSet a1 a2) <-> In a (ConstraintAutomata.N a1) \/ In a (ConstraintAutomata.N a2).
    Proof.
    intros. apply set_union_iff.
    Defined.

    Definition initialStates (a1: constraintAutomata) (a2: constraintAutomata2) :=
      list_prod (ConstraintAutomata.Q0 a1) (ConstraintAutomata.Q0 a2).

    Lemma initialStatesSound : forall a1, forall a2, forall a, forall b,
      In (a,b) (initialStates a1 a2) <-> In a (ConstraintAutomata.Q0 a1) /\ In b (ConstraintAutomata.Q0 a2).
    Proof.
    intros. apply in_prod_iff. 
    Defined.

  
    Definition condR1 (t1 : ( set(name) * DC * state)) (t2 : (set(name) * DC * state2))
      (names1 : set name) (names2: set name) :=
      set_eq (set_inter equiv_dec (names2) (fst(fst(t1)))) (set_inter equiv_dec (names1) (fst(fst(t2)))).

    Lemma condR1Sound : forall t1, forall t2, forall names1, forall names2,
    condR1 t1 t2 names1 names2 = true <-> 
    set_eq (set_inter equiv_dec (names2) (fst(fst(t1)))) (set_inter equiv_dec (names1) (fst(fst(t2)))) = true.
    Proof. 
    split. 
    - intros. unfold condR1 in H2. case_eq (set_eq (set_inter equiv_dec names2 (fst (fst t1)))
         (set_inter equiv_dec names1 (fst (fst t2)))).
    + intros. reflexivity.
    + intros. unfold condR1 in H3. rewrite H4 in H3. discriminate.
    - intros. unfold condR1. rewrite H3. reflexivity.
    Defined.

    Definition singleTransitionR1 (Q1: state) (Q2: state2)
      (transition1: (set (name) * DC * (state))) 
      (transition2: (set (name) * DC * (state2))) 
      (names1 : set name) (names2: set name) :  (set (state * state2 * ((set name * DC) * (state * state2)))) :=
        if (condR1 (transition1) (transition2) (names1) (names2)) then
                  [((Q1,Q2),(((set_union equiv_dec (fst(fst(transition1))) (fst(fst(transition2)))),ConstraintAutomata.andDc (snd(fst(transition1))) 
                            (snd(fst(transition2)))),(snd(transition1) , (snd(transition2)))))]
        else [].

    Lemma singleTransitionR1Sound : forall Q1, forall Q2, forall transition1, 
    forall transition2, forall names1, forall names2, singleTransitionR1 Q1 Q2 transition1 transition2
    names1 names2 <> [] <-> (condR1 (transition1) (transition2) (names1) (names2)) = true.
    Proof.
    split.
    - intros. unfold singleTransitionR1 in H3. 
      case_eq (condR1 (transition1) (transition2) (names1) (names2)). reflexivity. 
      intros. rewrite H4 in H3. congruence.
    - intros. unfold singleTransitionR1. rewrite H3. discriminate.
    Defined.

    Fixpoint moreTransitionsR1 (Q1: state) (Q2: state2)
      (transition1: (set (name) * DC * (state))) 
      (transition2: set (set (name) * DC * (state2))) 
      (names1 : set name) (names2: set name) :=
      match transition2 with
      | [] => []
      | a::t => (singleTransitionR1 Q1 Q2 transition1 a names1 names2)++
                (moreTransitionsR1 Q1 Q2 transition1 t names1 names2)
      end.

    Fixpoint transitionsForOneStateR1 (Q1: state) (Q2: state2)
      (transition1: set (set (name) * DC * (state))) 
      (transition2: set (set (name) * DC * (state2))) 
      (names1 : set name) (names2: set name) :=
      match transition1 with
      | [] => []
      | a::t => (moreTransitionsR1 Q1 Q2 a transition2 names1 names2)++
                (transitionsForOneStateR1 Q1 Q2 t transition2 names1 names2)
      end.

    Fixpoint iterateOverA2R1 (Q1: state) (Q2: set state2)
      (transition1: state -> set (set (name) * DC * (state))) 
      (transition2: state2 -> set (set (name) * DC * (state2))) 
      (names1 : set name) (names2: set name) :=
      match Q2 with
      | [] => []
      | a::t => (transitionsForOneStateR1 Q1 a (transition1 Q1) (transition2 a) names1 names2)++
                (iterateOverA2R1 Q1 t transition1 transition2 names1 names2)
      end.

    Fixpoint allTransitionsR1 (Q1: set state) (Q2: set state2)
      (transition1: state -> set (set (name) * DC * (state))) 
      (transition2: state2 -> set (set (name) * DC * (state2))) 
      (names1 : set name) (names2: set name) :=
      match Q1 with
      | [] => []
      | a::t => (iterateOverA2R1 a Q2 transition1 transition2 names1 names2)++
                (allTransitionsR1 t Q2 transition1 transition2 names1 names2)
    end. 


    Definition transitionsRule1 (a1: constraintAutomata) (a2: constraintAutomata2) := 
      allTransitionsR1 (ConstraintAutomata.Q a1) (ConstraintAutomata.Q a2) 
                       (ConstraintAutomata.T a1) (ConstraintAutomata.T a2) 
                       (ConstraintAutomata.N a1) (ConstraintAutomata.N a2).

    Definition condR2 (tr: set (name) * DC * state) (names2: set name) :=
      if (set_inter equiv_dec (fst(fst(tr))) names2) == nil then true else false.

    Lemma condR2Sound : forall tr, forall names2, condR2 tr names2 = true <->
      set_inter equiv_dec (fst(fst(tr))) names2 = nil.
    Proof.
    split.
    - intros. unfold condR2 in H3. destruct equiv_dec in H3. inversion e. reflexivity.
      inversion H3.
    - intros. unfold condR2. rewrite H3. reflexivity.
    Defined.

    Fixpoint singleTransitionR2 (q1:state) (transition : (set (name) * DC * (state))) (a2States : set state2) (a2Names: set name)   
    : set (state * state2 * ((set name * DC) * (state * state2))) :=
    match a2States with
    | [] => []
    | q2::t => if (condR2 (transition) (a2Names)) then 
                 ((q1,q2),((fst(transition)), ((snd(transition)), (q2))))::singleTransitionR2 q1 transition t a2Names
                else singleTransitionR2 q1 transition t a2Names
    end.

    Lemma singleTransitionR2Sound : forall q1, forall transition, forall a2States, forall a2Names, 
      singleTransitionR2 q1 transition a2States a2Names <> [] <-> condR2 (transition) (a2Names) = true /\ a2States <> [].
    Proof.
    split.
    - intros. induction a2States. unfold singleTransitionR2 in H3. congruence.
      simpl in H3. case_eq (condR2 transition a2Names). intros. split. reflexivity. congruence.
      intros. rewrite H4 in H3. simpl in H3. apply IHa2States in H3. destruct H3. congruence.
    - intros. induction a2States. unfold singleTransitionR2. destruct H3. congruence.
      simpl. case_eq (condR2 transition a2Names). discriminate. intros. destruct H3. congruence.
    Defined.
     
    Definition transitionR2 (q1:state) : set (set (name) * DC * (state)) -> 
      set state2 -> set name 
      -> set (state * state2 * ((set name * DC) * (state * state2))) :=
      fix rec transitions q2 names2 :=
        match transitions with
        | [] => [] 
        | a::t =>  (singleTransitionR2 q1 a q2 names2)++(rec t q2 names2)
        end.

    Fixpoint allTransitionsR2 (Q1: set state) (transitions: state -> set (set (name) * DC * (state))) 
      (names2: set name) (a2States : set state2) := 
      match Q1 with
      | [] => []
      | a::t => (transitionR2 a (transitions(a)) a2States names2)++(allTransitionsR2 t transitions names2 a2States)
      end.

    Definition transitionsRule2 (a1: constraintAutomata) (a2 : constraintAutomata2)  :=
      (allTransitionsR2 (ConstraintAutomata.Q a1) (ConstraintAutomata.T a1) 
                                      (ConstraintAutomata.N a2) (ConstraintAutomata.Q a2)).

    Definition condR3 (tr: set (name) * DC * state2) (names1: set name) :=
      if (set_inter equiv_dec (fst(fst(tr))) names1) == nil then true else false.

    Lemma condR3Sound : forall tr, forall names1, condR3 tr names1 = true <->
      set_inter equiv_dec (fst(fst(tr))) names1 = nil.
    Proof.
    split.
    - intros. unfold condR3 in H3. destruct equiv_dec in H3. inversion e. reflexivity.
      inversion H3.
    - intros. unfold condR3. rewrite H3. reflexivity.
    Defined.

    Fixpoint singleTransitionR3 (q2:state2) (transition : (set (name) * DC * (state2))) (a2States : set state) (a1Names: set name)   
    : set (state * state2 * ((set name * DC) * (state * state2))) :=
    match a2States with
    | [] => []
    | q1::t => if (condR3 (transition) (a1Names)) then 
                 ((q1,q2),((fst(transition)), ((q1) , (snd(transition)))))::singleTransitionR3 q2 transition t a1Names
                else singleTransitionR3 q2 transition t a1Names
    end.

    Lemma singleTransitionR3Sound : forall q2, forall transition, forall a1States, forall a1Names,
    singleTransitionR3 q2 transition a1States a1Names <> [] <-> 
    condR3 (transition) (a1Names) = true /\ a1States <> [].
    Proof.
    split. 
    - intros. induction a1States. simpl in H3. congruence.
    simpl in H3. case_eq (condR3 (transition) (a1Names)). split. reflexivity. discriminate.
    intros. rewrite H4 in H3. apply IHa1States in H3. destruct H3. congruence.
    - intros. induction a1States. destruct H3. congruence.
    simpl. case_eq (condR3 (transition) (a1Names)). discriminate.
    destruct H3. congruence.
    Defined.
  
    Definition transitionR3 (q2:state2) : set (set (name) * DC * (state2)) -> 
      set state -> set name  
      -> set (state * state2 * ((set name * DC) * (state * state2))) :=
      fix rec transitions q1 names1 :=
        match transitions with
        | [] => [] 
        | a::t =>  (singleTransitionR3 q2 a q1 names1)++(rec t q1 names1)
        end.

    Fixpoint allTransitionsR3 (Q2: set state2) (transitions: state2 -> set (set (name) * DC * (state2))) 
      (names1: set name) (a1States : set state) := 
      match Q2 with
      | [] => []
      | a::t => (transitionR3 a (transitions(a)) a1States names1)++(allTransitionsR3 t transitions names1 a1States)
      end.

    Definition transitionsRule3 (a1: constraintAutomata) (a2 : constraintAutomata2)  :=
      (allTransitionsR3 (ConstraintAutomata.Q a2) (ConstraintAutomata.T a2) 
                       (ConstraintAutomata.N a1) (ConstraintAutomata.Q a1)).

    Definition buildTransitionRuleProductAutomaton (a1: constraintAutomata) (a2: constraintAutomata2) :=
      (transitionsRule1 a1 a2)++(transitionsRule2 a1 a2)++(transitionsRule3 a1 a2).

    Fixpoint recoverResultingStatesPA (st: (state * state2)) 
      (t:set (state * state2 * ((set name * DC) * (state * state2)))) :=
      match t with
      | [] => []
      | a::tx => if st == fst((a)) then (snd((a))::recoverResultingStatesPA st tx)
                 else recoverResultingStatesPA st tx
      end.

    Lemma recoverResultingStatesPASound : forall st, forall t, recoverResultingStatesPA st t <> [] <->
      exists a, In a t /\ st = fst(a).
    Proof.
    split.
    - intros. induction t. simpl in H3. congruence.
      simpl in H3. destruct equiv_dec in H3. inversion e. exists a. split. simpl; auto. reflexivity.
      apply IHt in H3. destruct H3. exists x. destruct H3. split. simpl. auto. exact H4. 
    - intros. induction t. destruct H3. destruct H3. inversion H3. 
      simpl. destruct equiv_dec.  discriminate. apply IHt. destruct H3. destruct H3. simpl in H3. destruct H3. 
      rewrite <- H3 in H4. congruence. exists x. split. exact H3. exact H4.
    Defined.

    Definition transitionPA (a1: constraintAutomata) (a2: constraintAutomata2) (s: (state * state2)) :=
      Eval compute in recoverResultingStatesPA s (buildTransitionRuleProductAutomaton a1 a2). 

    Definition buildPA (a1: constraintAutomata) (a2:constraintAutomata2) := 
      ConstraintAutomata.CA (statesSet a1 a2) (nameSet a1 a2) (transitionPA a1 a2) (initialStates a1 a2).

  End ProductAutomata.
End ProductAutomata.


Require Export ListSet.
Require Export List.
Require Export Classes.EquivDec.
Require Export Coq.Program.Program.
Require Export QArith.
Require Export Coq.Numbers.BinNums.