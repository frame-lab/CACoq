Require Import ListSet.
Require Import List.
Require Import Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import QArith.
Require Import Coq.Numbers.BinNums.


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

Program Fixpoint s1_in_s2 {A} `{EqDec A eq} (s1 s2 : set A) :=
  match s1 with
    | [] => true
    | a::t => set_mem equiv_dec a s2 && s1_in_s2 t s2
  end.

Fixpoint set_eq {A} `{EqDec A eq} (s1 s2 : set A) :=
  if (length s1 == length s2) then
      if (s1_in_s2 s1 s2 == true) then
          if (s1_in_s2 s2 s1 == true) then true else false
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
  + unfold set_eq in H0. destruct equiv_dec in H0. destruct equiv_dec in H0. destruct equiv_dec in H0.
    auto. inversion H0. inversion H0. inversion H0.
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

    Context `{EqDec name eq} `{EqDec state eq} `{EqDec (option data) eq}.

    Notation " a <? b " := (Qle_bool a b).
    Notation "a =? b" := (Qeq_bool a b).

    Record port := mkport{
      id : name;
      dataAssignment : nat -> option data; 
      timeStamp : nat -> QArith_base.Q;
      portCond : forall n:nat, Qlt (timeStamp n) (timeStamp (S n));
      index : nat

    }.

    Inductive DC := 
    | tDc : DC
    | dc : name -> option data -> DC
    | eqDc : name -> name -> DC
    | andDc : DC -> DC -> DC
    | orDc  : DC -> DC -> DC
    | trDc  : (option data -> option data) -> name -> name -> DC
    | negDc : DC -> DC.

    Notation "a @ b" := (andDc a b)(no associativity, at level 69).
    Notation "a $ b" := (orDc a b) (no associativity, at level 69).

    Definition evalDC (po: option port) (d : option data) : bool :=
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

    (* The following definition searches for a port in a set of ports, returning it if it exists and None otherwise *)
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

    Definition transformDC (transform: option data -> option data) (n1: name) (n2: name) (s:set port) :=
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

    Fixpoint evalCompositeDc (s:set port) (dc: DC) : bool :=
      match dc with
      | tDc => true
      | dc a b => evalDC (retrievePortFromInput s a) (b)
      | eqDc a b => eqDataPorts a b s
      | andDc a b => evalCompositeDc s a && evalCompositeDc s b
      | orDc a b => evalCompositeDc s a || evalCompositeDc s b
      | trDc transform a b  => transformDC transform a b s
      | negDc a => negb (evalCompositeDc s a)
      end.  

      Lemma evalCompositeDcSound : forall s, forall dca: DC, evalCompositeDc s dca = true <-> 
      dca = tDc \/ 
      (exists a, exists b, dca = dc a b /\ (evalDC (retrievePortFromInput s a) b) = true ) \/
      (exists a, exists b, dca = eqDc a b /\ eqDataPorts a b s = true) \/
      (exists a, exists b, dca = andDc a b /\ evalCompositeDc s a && evalCompositeDc s b = true) \/
      (exists a,exists b, dca = orDc a b /\ evalCompositeDc s a || evalCompositeDc s b = true) \/
      (exists a, exists b, exists tr, dca = trDc tr a b /\ transformDC tr a b s = true) \/
      (exists a, dca = negDc a /\ negb (evalCompositeDc s a) = true).
      Proof.  
      split.
      - intros. destruct dca.
      + left. reflexivity.
      + simpl in H2. right. left. exists n. exists o. auto.
      + simpl in H2. right. right. left. exists n. exists n0. auto.
      + simpl in H2. right. right. right. left.  exists dca1. exists dca2. auto.
      + simpl in H2. right. right. right. right. left. exists dca1. exists dca2. auto.
      + simpl in H2. right. right. right. right. right. left. exists n. exists n0. exists o. auto.
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
      T : state -> set (set (name) * DC * set(state));
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

    Definition hasData (p:port) :=
      match (dataAssignment p(index p)) with
      | Some a => true
      | None => false
      end.

    Lemma hasDataSound : forall p, hasData p = true <-> exists data, dataAssignment p((index p)) = Some data.
    Proof.
    intros. split.
    - intros Ha. unfold hasData in Ha. destruct dataAssignment. exists d. reflexivity.
      inversion Ha.
    - intros Ha. unfold hasData. inversion Ha. rewrite H2. reflexivity.
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
       returnSmallerNumber (1000000#1) (l).

    Program Fixpoint count_into_list (n:nat) :=
      match n with
      | 0 => 0::nil
      | S n => count_into_list n ++ [S n]
      end.

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
      | a::t => if (hasData a && timeStampEqThetaTime tds a ) then
                    id a :: thetaN tds t
                else thetaN tds t
      | []   => []
      end.

    Lemma thetaNSound : forall tds, forall tds2, thetaN tds tds2 <> [] <-> 
    (exists a, In a tds2 /\ (hasData a) = true /\ timeStampEqThetaTime tds a = true).
    Proof.
    split.
    - intros. induction tds2.
    + simpl in H2. congruence.
    + simpl in H2. case_eq (hasData a). case_eq (timeStampEqThetaTime tds a).
    { intros. exists a. split. simpl;auto. split. exact H4. exact H3. }
    { intros. rewrite H4 in H2. rewrite H3 in H2. apply IHtds2 in H2. destruct H2. destruct H2.
      destruct H5. exists x. split. simpl;auto. split. exact H5. exact H6. }
    { intros. rewrite H3 in H2. apply IHtds2 in H2. destruct H2. destruct H2. destruct H4.
      exists x. split. simpl;auto. split. exact H4. exact H5. }
    -  intros. induction tds2. 
    + destruct H2.  destruct H2. inversion H2.
    + simpl. case_eq (hasData a). case_eq (timeStampEqThetaTime tds a). intros. discriminate.
      intros. apply IHtds2. destruct H2. destruct H2. simpl in H2. destruct H2. destruct H5. rewrite <- H2 in H5. 
      congruence. exists x. split. exact H2. exact H5.
      intros. apply IHtds2. destruct H2. destruct H2. simpl in H2. destruct H2. rewrite <- H2 in H4. destruct H4. 
      congruence. exists x. split. exact H2. exact H4. Defined. 

    Fixpoint portsWithData (tds: set port) (tds2:set port) : set((name * option data)) := 
      match tds2 with
      | a::t => if (hasData a && timeStampEqThetaTime tds a) then
                   ((id a) , (dataAssignment a(index(a)))) :: portsWithData tds t
                else portsWithData tds t
      | []   => []
      end.

    Lemma portsWithDataSound : forall tds, forall tds2, portsWithData tds tds2 <> [] <-> 
    (exists a, In a tds2 /\ (hasData a) = true /\ timeStampEqThetaTime tds a = true).
    Proof.
    split.
    - intros. induction tds2.
    + simpl in H2. congruence.
    + simpl in H2. case_eq (hasData a). case_eq (timeStampEqThetaTime tds a).
    { intros. exists a. split. simpl;auto. split. exact H4. exact H3. }
    { intros. rewrite H4 in H2. rewrite H3 in H2. apply IHtds2 in H2. destruct H2. destruct H2.
      destruct H5. exists x. split. simpl;auto. split. exact H5. exact H6. }
    { intros. rewrite H3 in H2. apply IHtds2 in H2. destruct H2. destruct H2. destruct H4.
      exists x. split. simpl;auto. split. exact H4. exact H5. }
    -  intros. induction tds2. 
    + destruct H2.  destruct H2. inversion H2.
    + simpl. case_eq (hasData a). case_eq (timeStampEqThetaTime tds a). intros. discriminate.
      intros. apply IHtds2. destruct H2. destruct H2. simpl in H2. destruct H2. destruct H5. rewrite <- H2 in H5. 
      congruence. exists x. split. exact H2. exact H5.
      intros. apply IHtds2. destruct H2. destruct H2. simpl in H2. destruct H2. rewrite <- H2 in H4. destruct H4. 
      congruence. exists x. split. exact H2. exact H4. Defined. 

    Definition thetaDelta (tds: set port) := 
      portsWithData tds tds.

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


    Fixpoint retrievePortsOutsideTransition (tds: set port) (portNames : set name) :=
      match tds with
      | [] => []
      | a::x => if (portsOutsideTransition a portNames) then a::retrievePortsOutsideTransition x portNames
                else retrievePortsOutsideTransition x portNames
      end.

    Lemma retrievePortsOutsideTransitionSound : forall tds, forall portNames,
    retrievePortsOutsideTransition tds portNames <> [] <-> exists a, portsOutsideTransition a portNames = true /\
    In a tds.
    Proof.
    split.
    - intros. induction tds.
    + simpl in H2. congruence.
    + simpl in H2. case_eq (portsOutsideTransition a portNames).
      intros. exists a. split. exact H3. simpl;auto.
      intros. rewrite H3 in H2. apply IHtds in H2. destruct H2. exists x. destruct H2.
      split. assumption. simpl;auto.
    - intros. induction tds. destruct H2. destruct H2. 
    + inversion H3. 
    + simpl. case_eq (portsOutsideTransition a portNames). discriminate.
      intros.
      apply IHtds. destruct H2.
      destruct H2. simpl in H4.
      destruct H4. rewrite <- H4 in H2. congruence.
      exists x. split. exact H2. exact H4. Defined. 

    Fixpoint hasDataInThetaDelta (p: port) (thetadelta: set (name * option data)) :=
      match thetadelta with
      | [] => false
      | a::t => if ((id p ==(fst(a)))) then
                    if snd(a) <> None then true 
                    else hasDataInThetaDelta (p) (t)
                else hasDataInThetaDelta p t
      end.

    Lemma hasDataInThetaDeltaSound : forall p, forall thetadelta, hasDataInThetaDelta p thetadelta = true <-> 
      exists a, In a thetadelta /\ (id p = (fst(a))) /\ (snd(a)<> None).
    Proof.
    split.
    - intros. induction thetadelta.
    + inversion H2.
    + simpl in H2. destruct equiv_dec in H2. destruct nequiv_dec in H2. inversion e.
      exists a. split.
      simpl;auto.
      split. exact H4.
      congruence.
      apply IHthetadelta in H2. destruct H2. destruct H2. exists x. split.
      simpl;auto. exact H3.
      apply IHthetadelta in H2. destruct H2. destruct H2. exists x. split.
      simpl;auto. exact H3.
    - intros. induction thetadelta.
    + repeat destruct H2. 
    +  destruct H2. destruct H2. destruct H3. simpl in H2. 
       simpl. destruct equiv_dec. destruct nequiv_dec. reflexivity. inversion e0. 
       destruct H2. rewrite H2 in H6. congruence.
       apply IHthetadelta. exists x. inversion e.
       repeat split; assumption. apply IHthetadelta.
       destruct H2. rewrite <- H2 in H3. congruence.
       exists x. repeat split;assumption.
    Defined.

    Fixpoint checkPorts (tds:set port) (thetadelta: set (name * option data)) :=
      match tds with
      | [] => true
      | a::x => if (negb (hasDataInThetaDelta a thetadelta)) then checkPorts x thetadelta
                else false
      end.

    Lemma checkPortsSound : forall tds, forall thetadelta, checkPorts tds thetadelta = false <->
      exists a, In a tds /\ negb (hasDataInThetaDelta a thetadelta) = false.
    Proof.
    split.
    - intros. induction tds.
    + inversion H2.
    + simpl in H2. case_eq (negb (hasDataInThetaDelta a thetadelta)). 
      intros. rewrite H3 in H2. apply IHtds in H2. repeat destruct H2.
      exists x. split. simpl;auto. exact H4.
      exists a. destruct hasDataInThetaDelta. split. simpl;auto. reflexivity.  simpl in H3. congruence.
    - intros. induction tds.
    + repeat destruct H2.
    + simpl. case_eq (negb (hasDataInThetaDelta a thetadelta)). intros. apply IHtds. destruct H2. destruct H2. simpl in H2. destruct H2.
      rewrite H2 in H3. congruence.
      exists x. split. exact H2. exact H4. reflexivity.
      Defined.

    Definition onlyPortsInvolvedContainsData (portNames : set name) (tds : set port) :=
      checkPorts (retrievePortsOutsideTransition (tds) portNames) (thetaDelta (tds)).

    Definition retrievePortsFromThetaN (tds: set port) :=
      thetaN (tds) (tds).

    Fixpoint step' (tds : set port) (portNames: set name)
     (transitions: set(set name * DC * set(state))) :=
     match transitions with
     | [] => []
     | a::t => if (set_eq (portNames)((fst(fst(a))))) && 
                  (onlyPortsInvolvedContainsData (fst(fst(a))) tds)
                   && (evalCompositeDc (tds) (snd(fst(a)))) then snd(a)++step' tds portNames t
                   else step' tds portNames t
     end.

    Lemma step'_sound : forall tds, forall portNames, forall transitions, step' tds portNames transitions <> [] -> exists a,
    In a transitions /\ (set_eq (portNames)((fst(fst(a))))) && (onlyPortsInvolvedContainsData (fst(fst(a))) tds)
                   && (evalCompositeDc (tds) (snd(fst(a)))) = true.
    Proof. 
    - intros. induction transitions. simpl in H2. congruence. simpl in H2. 
    case_eq (set_eq (portNames)((fst(fst(a))))).  
    case_eq (onlyPortsInvolvedContainsData (fst(fst(a))) tds).
    case_eq (evalCompositeDc tds (snd (fst a))). intros.
    + exists a. split. simpl;auto. rewrite H3. rewrite H4. rewrite H5. reflexivity.
    + intros. rewrite H3 in H2. rewrite H4 in H2. rewrite H5 in H2. apply IHtransitions in H2.
      destruct H2. destruct H2. exists x. split. simpl;auto. exact H6.
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
      set port -> list nat -> set state -> set (set state) -> set (set state) :=
      fix rec tds k acc resp :=
        match k with 
          | [] => resp
          | a::t => resp ++ [snd (step ca acc tds)]
                    |> rec
                      (flat_map(derivativePortInvolved(fst((step ca acc tds)))) tds) t (snd (step ca acc tds))
        end.

    Definition run (ca:constraintAutomata) (tds: set port) (k : nat) :=
      run' ca tds (count_into_list k) (Q0 ca) [Q0 ca].

  (* We define some functions to retrieve data from transitions, in order to prove *)
  (* properties about instantiated automata's behavior                             *)

  Fixpoint retrievePortsFromRespTransitions (s : set (set (name) * DC * set(state))) :=
    match s with
    | [] => []
    | a::t => set_union equiv_dec (fst (fst a) ) (retrievePortsFromRespTransitions t)
    end.

  Definition retrivePortsFromSingleTransition (ca: constraintAutomata) (s : state) :=
    retrievePortsFromRespTransitions (ConstraintAutomata.T ca s).

  End ConstraintAutomata.
End ConstraintAutomata.

Module ProductAutomata.
  Section ProductAutomata.
    Variable state name data state2: Set.
    Context `{EqDec name eq} `{EqDec state eq} `{EqDec state2 eq} `{EqDec (option data) eq}.

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

  
    Definition condR1 (t1 : ( set(name) * DC * set(state))) (t2 : (set(name) * DC * set(state2)))
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

    Fixpoint unfoldStatesR1 (p1: state) (p2: set state2) :=
      match p2 with
      | [] => []
      | a::t => (p1,a)::unfoldStatesR1 p1 t
      end.

    Lemma unfoldStatesR1Sound : forall p1, forall p2, 
      unfoldStatesR1 p1 p2 <> [] <-> p2 <> [].
    Proof.
    split.
    - intros. destruct p2.
    + simpl in H3. congruence.
    + discriminate.
    - intros. destruct p2.
    + congruence.
    + discriminate.
    Defined.

    Fixpoint resultingStatesTransition (p1: set state) (p2: set state2) :=
      match p1 with
      | [] => []
      | a::t => unfoldStatesR1 a p2++
                resultingStatesTransition t p2
      end.

    Definition singleTransitionR1 (Q1: state) (Q2: state2)
      (transition1: (set (name) * DC * (set(state)))) 
      (transition2: (set (name) * DC * (set(state2)))) 
      (names1 : set name) (names2: set name) :  (set (state * state2 * ((set name * DC) * set (state * state2)))) :=
      if (condR1 (transition1) (transition2) (names1) (names2)) then
                  [((Q1,Q2),(((set_union equiv_dec (fst(fst(transition1))) (fst(fst(transition2)))),ConstraintAutomata.andDc (snd(fst(transition1))) 
                            (snd(fst(transition2)))),(resultingStatesTransition(snd(transition1)) (snd(transition2)))))]
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
      (transition1: (set (name) * DC * (set(state)))) 
      (transition2: set (set (name) * DC * (set(state2)))) 
      (names1 : set name) (names2: set name) :=
      match transition2 with
      | [] => []
      | a::t => (singleTransitionR1 Q1 Q2 transition1 a names1 names2)++
                (moreTransitionsR1 Q1 Q2 transition1 t names1 names2)
      end.

    Fixpoint transitionsForOneStateR1 (Q1: state) (Q2: state2)
      (transition1: set (set (name) * DC * (set(state)))) 
      (transition2: set (set (name) * DC * (set(state2)))) 
      (names1 : set name) (names2: set name) :=
      match transition1 with
      | [] => []
      | a::t => (moreTransitionsR1 Q1 Q2 a transition2 names1 names2)++
                (transitionsForOneStateR1 Q1 Q2 t transition2 names1 names2)
      end.

    Fixpoint iterateOverA2R1 (Q1: state) (Q2: set state2)
      (transition1: state -> set (set (name) * DC * (set(state)))) 
      (transition2: state2 -> set (set (name) * DC * (set(state2)))) 
      (names1 : set name) (names2: set name) :=
      match Q2 with
      | [] => []
      | a::t => (transitionsForOneStateR1 Q1 a (transition1 Q1) (transition2 a) names1 names2)++
                (iterateOverA2R1 Q1 t transition1 transition2 names1 names2)
      end.

    Fixpoint allTransitionsR1 (Q1: set state) (Q2: set state2)
      (transition1: state -> set (set (name) * DC * (set(state)))) 
      (transition2: state2 -> set (set (name) * DC * (set(state2)))) 
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

    Definition condR2 (tr: set (name) * DC * set(state)) (names2: set name) :=
      if (set_inter equiv_dec (fst(fst(tr))) names2) == nil then true else false.

    Lemma condR2Sound : forall tr, forall names2, condR2 tr names2 = true <->
      set_inter equiv_dec (fst(fst(tr))) names2 = nil.
    Proof.
    split.
    - intros. unfold condR2 in H3. destruct equiv_dec in H3. inversion e. reflexivity.
      inversion H3.
    - intros. unfold condR2. rewrite H3. reflexivity.
    Defined.

    Fixpoint outboundStatesR2  (p1: set state) (q2: state2) :=
      match p1 with
      | [] => []
      | a::t => set_add equiv_dec ((a,q2))(outboundStatesR2 t q2)
      end.

    Fixpoint outboundStatesR3 (q1: state) (p2: set state2) :=
      match p2 with
      | [] => []
      | a::t => set_add equiv_dec ((q1,a))(outboundStatesR3 q1 t)
      end.

    Fixpoint singleTransitionR2 (q1:state) (transition : (set (name) * DC * (set(state)))) (a2States : set state2) (a2Names: set name)   
    : set (state * state2 * ((set name * DC) * set (state * state2))) :=
    match a2States with
    | [] => []
    | q2::t => if (condR2 (transition) (a2Names)) then 
                 ((q1,q2),((fst(transition)), (outboundStatesR2 (snd(transition)) (q2))))::singleTransitionR2 q1 transition t a2Names
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
     
    Definition transitionR2 (q1:state) : set (set (name) * DC * (set(state))) -> 
      set state2 -> set name 
      -> set (state * state2 * ((set name * DC) * set (state * state2))) :=
      fix rec transitions q2 names2 :=
        match transitions with
        | [] => [] 
        | a::t =>  (singleTransitionR2 q1 a q2 names2)++(rec t q2 names2)
        end.

    Fixpoint allTransitionsR2 (Q1: set state) (transitions: state -> set (set (name) * DC * (set(state)))) 
      (names2: set name) (a2States : set state2) := 
      match Q1 with
      | [] => []
      | a::t => (transitionR2 a (transitions(a)) a2States names2)++(allTransitionsR2 t transitions names2 a2States)
      end.

    Definition transitionsRule2 (a1: constraintAutomata) (a2 : constraintAutomata2)  :=
      (allTransitionsR2 (ConstraintAutomata.Q a1) (ConstraintAutomata.T a1) 
                                      (ConstraintAutomata.N a2) (ConstraintAutomata.Q a2)).

    Definition condR3 (tr: set (name) * DC * set(state2)) (names1: set name) :=
      if (set_inter equiv_dec (fst(fst(tr))) names1) == nil then true else false.

    Lemma condR3Sound : forall tr, forall names1, condR3 tr names1 = true <->
      set_inter equiv_dec (fst(fst(tr))) names1 = nil.
    Proof.
    split.
    - intros. unfold condR3 in H3. destruct equiv_dec in H3. inversion e. reflexivity.
      inversion H3.
    - intros. unfold condR3. rewrite H3. reflexivity.
    Defined.

    Fixpoint singleTransitionR3 (q2:state2) (transition : (set (name) * DC * (set(state2)))) (a2States : set state) (a1Names: set name)   
    : set (state * state2 * ((set name * DC) * set (state * state2))) :=
    match a2States with
    | [] => []
    | q1::t => if (condR3 (transition) (a1Names)) then 
                 ((q1,q2),((fst(transition)), (outboundStatesR3 (q1) (snd(transition)))))::singleTransitionR3 q2 transition t a1Names
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
  
    Definition transitionR3 (q2:state2) : set (set (name) * DC * (set(state2))) -> 
      set state -> set name  
      -> set (state * state2 * ((set name * DC) * set (state * state2))) :=
      fix rec transitions q1 names1 :=
        match transitions with
        | [] => [] 
        | a::t =>  (singleTransitionR3 q2 a q1 names1)++(rec t q1 names1)
        end.

    Fixpoint allTransitionsR3 (Q2: set state2) (transitions: state2 -> set (set (name) * DC * (set(state2)))) 
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

  
    Variable a1 : (constraintAutomata).
    Variable a2 : (constraintAutomata2).

    Fixpoint recoverResultingStatesPA (st: (state * state2)) 
      (t:set (state * state2 * ((set name * DC) * set (state * state2)))) :=
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

    Definition transitionPA (s: (state * state2)) :=
      Eval compute in recoverResultingStatesPA s (buildTransitionRuleProductAutomaton a1 a2). 

    Definition buildPA := ConstraintAutomata.CA 
      (statesSet a1 a2) (nameSet a1 a2) (transitionPA) (initialStates a1 a2). 

  End ProductAutomata.
End ProductAutomata.


Require Export ListSet.
Require Export List.
Require Export Classes.EquivDec.
Require Export Coq.Program.Program.
Require Export QArith.
Require Export Coq.Numbers.BinNums.