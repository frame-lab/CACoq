Require Import ListSet.
Require Import List.
Require Import Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import QArith.
Require Import Coq.Numbers.BinNums.

(* Keywords: ERICK, TODO *)

Close Scope Q_scope.

Obligation Tactic := unfold complement, equiv ; program_simpl.


Set Implicit Arguments.
Set Maximal Implicit Insertion.


Import ListNotations.
(* ---------------------------------------- Utils ---------------------------------------------------------------- *)
(* We define a function that computes the powerset of a set *)
Fixpoint powerset {A} (l:set A) : set (set A) :=
match l with
  | [] => [[]]
  | a::t => concat (map (fun f => [a::f;f]) (powerset t))
end.

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

(* Returns true if all elements of s1 is in s2 *)
Fixpoint s1_in_s2 {A} `{EqDec A eq} (s1 s2 : set A) :=
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

(* --------------------------------------------------------------------------------------------------------------- *)

Module ConstraintAutomata.
  Section ConstraintAutomata.

    Variable state name data: Type. 

    Context `{EqDec name eq} `{EqDec state eq} `{EqDec (option data) eq}.
    (*`{EqDec data eq} será necessária p/ satisfazer a DC.*)

    Notation " a <? b " := (Qle_bool a b).
    Notation "a =? b" := (Qeq_bool a b).
    (* We define a port as a record containing its identifier and the data it contains *)
    Record port := mkport{
      id : name;
      dataAssignment : nat -> option data; 
      timeStamp : nat -> QArith_base.Q (* nat -> real *);
      (* We need to assure that timeStamp is always crescent:                                        *)
      portCond : forall n:nat, Qle (timeStamp n) (timeStamp (S n));
      index : nat (* the actual index of the port; aka a way to calculate the derivative.            *)

      (* The portCond field is useful to ensure the correctness of the modelled worlds (in terms of the *)
      (* time in which a data item is observed in a given port). If the user does not want to prove     *)
      (* that, it is only needed to supply an axiom of the same type as the proof as the argument.      *)
      (* This obliges the user to supply a proof of the same type as portCond, but if they rather not   *)
      (* prove it, they can axiomixe it                                                                 *)

      (* A idéia de limitar a "profundidade" das funções nat -> Q e nat -> Data  vai ser aplicada na run. *)
    }.
    Check dataAssignment.

    (* TDS^names can be seen as a set of ports as defined above.. *)
    (* In order to totalize the functions, we opted to use option type for both data and the time when  *)
    (* the data happens in a port. This lets the user to define a instant that there will be no data in *)
    (* a given port A_i                                                                                 *)

    Record constraintAutomata : Type := CA {
      Q : set state;
      N : set name; (* ou set port?*) 
      T : state -> nat -> set (set (name) * bool * set(state)); (* ERICK -> set(state) por causa do comportamento não determinístico do CA. *)
                                                                       (* Also, set (set name)) * ... p/ permitir a verificação correta da porta na*)
                                                                       (* na transição em questão.                                                 *)
      Q0 : set state;
    }.

    Fixpoint returnSmallerNumber (m:QArith_base.Q) (l:set QArith_base.Q) :=
      match l with
      | [] => m
      | a::t => if ((a <? m) == true) then 
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
     (* exists a. split. simpl;auto.*)
    (* case_eq ( a <? m); intros hyp_ab. *)
    destruct equiv_dec in H2. inversion e. exists a. simpl; auto. 
    apply IHl in H2. destruct H2. destruct H3. destruct H3. exists x. split. simpl. right. exact H3.
    exact H4.
    Defined.

    (* Lemma returnSmallerNumber_sound2 : forall m, forall l, l <> [] /\ (exists a, In a l /\ a <? m = true)
    -> returnSmallerNumber m l <> m.
    Proof.
    intros. induction l.
    + destruct H2. congruence.
    + simpl. destruct H2. destruct equiv_dec. apply returnSmallerNumber_sound in IHl.
      destruct equiv_dec with (x:= (a <? m)) . *)
    

    Eval compute in returnSmallerNumber (999999#1) [222#1;31#2;4#5;5#100;69#69;8#8].

    (* The following function returns true if at some point k the port has data in it :             *)
    (* isso vai ser útil na hora de definir a run para ver quais portas possuem dados no tempo a(k) *)
    Definition hasData (p:port) (k:nat) :=
      match (dataAssignment p(k)) with
      | Some a => true
      | None => false
      end.

    Lemma hasDataSound : forall p, forall k, hasData p k = true <-> exists data, dataAssignment p(k) = Some data.
    Proof.
    intros. split.
    - intros Ha. unfold hasData in Ha. destruct dataAssignment. exists d. reflexivity.
      inversion Ha.
    - intros Ha. unfold hasData. inversion Ha. rewrite H2. reflexivity.
    Defined.

    (* mapAp is a function that given a natural number and a set of functions, returns the result *)
    (* of all functions within the set with the given natural number:                             *)
    Fixpoint mapAp (n:nat) (l:set (nat -> QArith_base.Q)) : set QArith_base.Q:=
      match l with
      | [] =>  []
      | f::t => f n :: mapAp n t
      end.

    Lemma mapAppSound : forall n, forall l, mapAp n l <> [] <-> l <> [].
    Proof.
    split.
    - intros. destruct l.
    + simpl in H2. congruence.
    + discriminate.
    - intros. destruct l.
    + simpl. auto.
    + simpl. discriminate.
    Defined.

   Fixpoint getTimeStampFromPorts (l : set port) : set (nat -> QArith_base.Q) :=
     match l with
     | [] => []
     | a::t => (timeStamp a)::getTimeStampFromPorts t
     end.

    Lemma getTimeStampFromPortsSound : forall l, getTimeStampFromPorts l <> [] <-> l <>[].
    Proof.
    split.
    - intros. destruct l.
    + auto.
    + congruence.
    - intros. destruct l.
    + auto.
    + simpl. discriminate.
    Defined.
    

    Notation "x |> f" := (f x) (at level 69, only parsing).


    (* In order to calculate the definition of theta.time correctly, we first bind it to its zero. *)
    Definition thetaTimeInZero (s:set port)  := 
      returnSmallerNumber (100000#1) (mapAp 0 ((s) |> getTimeStampFromPorts)).


    (* Fixpoint getNextThetaTime (p: port) (k : nat) (s: set port) :=
      match k with
      | 0 => if (timeStream p(0) > thetaTimeInZero s) then (timeStream p(0)) else (thetaTimeInZero s)
      | *)
 
    (* We can define thetaTime as a function that a given natural k, returns the smaller number from a set of *)
    (* rational numbers obtained by applying f to k.                                                          *)
    (* ERICK: theta.time(k) é calculado na entrada, e não no conjunto de portas do autômato...                *)
    (* s: TDS         de entrada do autômato                                                                  *)
    Definition thetaTime (s:set port) (k:nat)  := 
      returnSmallerNumber (100000#1) (mapAp k ((s) |> getTimeStampFromPorts)).
      (* match k with
      | 0 => returnSmallerNumber (100000#1) (mapAp 0 ((s) |> getTimeStampFromPorts)).
      | S n => *)

    Close Scope Q_scope.

    (* By algorithmic aspects, we define the following function as a function that implements the *)
    (* idea behind the calculus of theta.N(k) by imposing a upper bound to find the li value where*)
    (* ai(li) = theta.time(k)                                                                     *)
    Fixpoint timeStampEqThetaTime (ca:set port) (k: nat) (l: nat) (a:port) :=
      match l with
      | 0 => if (timeStamp a(0) =? thetaTime (ca) (k) == true) then true else false
      | S n => if (timeStamp a(S n) =? thetaTime (ca)(k) == true) then true else timeStampEqThetaTime (ca) (k) (n) (a)
      end.

    Lemma timeStampEqThetaTimeSound : forall ca, forall k, forall l, forall a, 
    timeStampEqThetaTime ca k l a = true ->  timeStamp a(l) =? thetaTime (ca) (k) = true \/ 
    (exists x, x < l /\ timeStamp a(x) =? thetaTime (ca) (k) = true).
    Proof.
    (* split. *)
    - intros. induction l.
    + simpl in H2. destruct equiv_dec in H2. auto. discriminate.
    + simpl in H2. destruct equiv_dec in H2. inversion e. left. reflexivity.
      right. apply IHl in H2. destruct H2.
      exists l. split. auto.
      assumption. destruct H2. destruct H2. exists x.
      split. auto. assumption. Defined.

    (*Lemma timeStampEqThetaTimeSound2 : forall ca, forall k, forall l, forall a, 
    timeStamp a(l) =? thetaTime (ca) (k) = true \/ 
    (exists x, x < l /\ timeStamp a(x) =? thetaTime (ca) (k) = true) ->  timeStampEqThetaTime ca k l a = true.
    Proof.
    - intros. induction l. 
    + destruct H2. simpl. rewrite H2. auto. destruct H2. destruct H2. inversion H2.
    + simpl. destruct equiv_dec. reflexivity. 
      destruct H2. congruence.
      destruct H2. destruct H2.
      unfold timeStampEqThetaTime.
    Admitted. *)

    (*ERICK : timeStampEqThetaTime serve para encontrar se em algum l_i da timestamp bate com o theta(k) *)
    (* atual, vide a teoria em Arbab (2004)                                                              *) 


    (*The following definition returns the i-th natural number where timeStamp a(S n) = thetaTime(k).     *)
    (* For it to work properly, one must supply a default return number greater than the specified        *)
    (* l number. Therefore, it returns 0<=i<=l if if timeStamp a(i) =? thetaTime(k) and default           *)
    (* otherwise                                                                                          *)
    (* TODO: definir se o default será fixo ou deixa para o usuário especificar o número que ele desejar? *)
    (* Decidido que o default é 0. Isso tem que ser explicitado na documentação. *)
    Fixpoint timeStampIndex (ca: set port)(*constraintAutomata)*) (k:nat) (l:nat) (a:port) :=
      match l with
      | 0 => if (timeStamp a(0) =? thetaTime (ca) (k) == true) then 0 else 0
      | S n => if (timeStamp a(S n) =? thetaTime (ca) (k) == true) then S n else timeStampIndex (ca) (k) (n) (a) 
      end.

    Definition timeStampIndexSound : forall ca, forall k, forall l, forall a, 
    timeStampIndex ca k l a <> 0 -> (exists n, timeStamp a(n) =? thetaTime (ca) (k) = true /\ n <> 0).
    Proof.
    (*split. *)
    - intros. induction l. 
    + simpl in H2. destruct equiv_dec in H2. congruence. congruence.
    + simpl in H2. destruct equiv_dec in H2. exists (S l).
      { split. inversion e. reflexivity. exact H2. }
      { apply IHl. exact H2. }
    Defined.

    Check timeStampIndex.
    (* Therefore it is possible to define tetaN: l has the same meaning as in timeStampEqThetaTime       *)
    (* ERICK: é necessário passar duas instâncias da TDS de entrada, uma é usada para calcular thetaTime *)
    (* e a outra para montar o thetaN                                                                    *)
    Fixpoint thetaN (ca: set port) (k:nat) (l:nat) (s:set port) : set name := 
      match s with
      | a::t => match hasData a(k) with
                | true => if (timeStampEqThetaTime ca k l a == true) then
                             id a :: thetaN ca k l t
                          else thetaN ca k l t
                | false => thetaN ca k l t
                end
      | []   => []
      end.

    Lemma thetaNSound : forall ca, forall k, forall l, forall s, thetaN ca k l s <> [] <-> 
    (exists a, In a s /\ hasData a(k) = true /\ timeStampEqThetaTime ca k l a = true).
    Proof.
    split.
    - intros. induction s.
    + simpl in H2. congruence.
    + simpl in H2. 
      unfold hasData in H2. Admitted.
      


    (* Returns tuples of ports, data and the time where a given data item is "seen" in a given port *)
    (* in the instant denoted by timeStamp k                                                        *)

    (* The following function retrieves all ports as tuples (name, data(k), timeStamp(k)) iff the port*)
    (* contains data at time teta.time(k), where teta.time(k) is the smallest time stamp obtained     *)
    (* by merging all time stamps with a given natural number "k"                                     *)
    (* the two following function implements thetaDelta.                                               *)
    (* TODO definir uma função igual a timeStampEqThetaTime que retorna o indice li tal que           *)
    (* timeStamp a(S n) =? thetaTime(k)  FEITO: timeStampIndex                                        *)
   

    Fixpoint portsWithData (ca:set port) (k:nat) (l:nat) (s:set port) : set((name * option data) ) :=
      match s with
      | [] => []
      | a::t => match hasData(a) (k) with
                | true => if (timeStampEqThetaTime ca k l a) then
                           ((id a) , (dataAssignment a(timeStampIndex ca (k) (l) (a) ))) 
                           :: portsWithData ca k l t
                         else portsWithData ca k l t 
                | false => portsWithData ca k l t
                end
      end.

    (* Idéia: salvar o índice de thetaDelta pra cada função. Porém falha ao lembrar que ele pode ser diferente pra *)
    (* cada dataStream em cada porta. Porém parece ser possível usar a ideia da função acima pra pegar o índice   *)
    (* exato para avaliar a porta na transição:                                                                   *)
    (* Fixpoint indexportsWithData (ca:set port) (k:nat) (l:nat) (s:set port) : set((name * nat) ) :=
      match s with ERICK: a ideia aqui implementada está implementada na função acima.
      | [] => []
      | a::t => match hasData(a) (k) with
                | true => if (timeStampEqThetaTime ca k l a) then
                           ((id a) , (timeStampIndex ca (k) (l) (a))) 
                           :: indexportsWithData ca k l t 
                         else indexportsWithData ca k l t
                | false => indexportsWithData ca k l t 
                end
      end. *)
    (* Enquanto eu escrevia isso eu tive uma ideia melhor até: "existsb" nat tal que a definição da dc na transição *)
    (* avaliada em k bata com o mesmo valor da porta em thetaDelta(k)                                                *)

    Definition thetaDelta (ca:constraintAutomata) (k : nat) (l:nat) (po: set port) := 
      portsWithData po k l po.
    Check thetaDelta.

    Close Scope Q_scope.


    (* We model a function to update the record of a given port that is used in a transition; a way to  *)
    (* model the derivative of a atream:                                                                *)
    Definition derivative (p: port) := mkport (id p) (dataAssignment p) (timeStamp p)
        (portCond p) (S (index p)).

    Lemma derivative_sound : forall p, derivative p = mkport (id p) (dataAssignment p) (timeStamp p)
        (portCond p) ( S(index p)).
    Proof.
    reflexivity.
    Defined.

    Check derivative.

    
    Definition DC (p:port) (k:nat) (d : option data) : bool :=
       if (dataAssignment p(k) == d) then true else false.

    Lemma DCSound : forall p, forall k, forall d, DC p k d = true <-> dataAssignment p(k) = d.
    Proof.
    split.
    - intros. unfold DC in H2. destruct equiv_dec.
    + exact e.
    + discriminate.
    - intros. destruct H2. unfold DC. destruct equiv_dec.
    + reflexivity.
    + congruence.
    Defined.


    Fixpoint derivativePortInvolved (s:set name) (a: port) :=
      match s with
      | [] => [] (*ERICK wtf esse derivative aqui embaixo?*)
      | x::t => if x == id a then derivative(a)::derivativePortInvolved t a
                else a::derivativePortInvolved t a
      end.

    Lemma derivativePortsInvolvedSound : forall s, forall a, 
      derivativePortInvolved s a <> [] <-> s <> [].
    Proof.
    split.
    - intros. induction s.
    + simpl in H2. congruence.
    + simpl in H2. discriminate.
    - intros. induction s.
    + simpl. congruence.
    + simpl. destruct equiv_dec. discriminate. discriminate.
    Defined.
  

    (* NEW then we have a way to calculate the derivatives from all ports in the input involved with the actual step *)
    Fixpoint allDerivativesFromPortsInvolved (names: set name) (ports:set port) : set port :=
      match ports with
      | [] => []
      | a::t => derivativePortInvolved names a ++ allDerivativesFromPortsInvolved names t
      end.
    Check allDerivativesFromPortsInvolved.

    Lemma allDerivativesFromPortsInvolvedSound : forall names, forall ports, 
      allDerivativesFromPortsInvolved names ports <> [] <-> names <> [] /\ ports <> [].
    Proof.
    split.
    - intros. induction ports.
    +  simpl in H2. congruence.
    +  destruct names.  simpl in H2. apply IHports in H2. destruct H2. congruence.
       split. congruence. congruence.
    - intros. induction ports. destruct H2.
    + simpl. exact H3.
    + destruct names. simpl. apply IHports. destruct H2. split. exact H2. congruence.
      simpl. destruct equiv_dec. simpl. congruence. simpl. congruence.
    Defined.

   (* The following function may calculate the derivative of ports involved in a given transition *)
    Definition portsDerivative (names: set name) (input: set port) := 
      allDerivativesFromPortsInvolved names input. (* NOTICE: no longer used *)


    (* We also need to check if the ports involved in a transition are the only ones with data so it can fire *)

    Fixpoint portsOutsideTransition (input: port) (ports : set name) :=
      match ports with
       | [] => true
       | a::t => if (id input <> a) then portsOutsideTransition input t else false
      end.

    Lemma portsOutsideTransitionSound : forall input, forall ports, portsOutsideTransition input ports = false <->
      (* ports <> [] /\ (exists b, In b ports /\ (id input = b)). *)
      (*     split.
    - intros. induction ports.
    + split. inversion H2. inversion H2.
    + simpl in H2. destruct nequiv_dec in H2. apply IHports in H2.
      destruct H2. destruct H3. destruct H3.
      split. discriminate. exists x. split. simpl;auto.
      exact H4. split. discriminate. exists a. split. simpl;auto. inversion e. reflexivity.
    - intros. induction ports. 
    + destruct H2. congruence.
    + simpl. destruct nequiv_dec. apply IHports. destruct H2. destruct H3. destruct H3. simpl in H3.
      destruct H3. congruence. split. apply in_split in H3. destruct H3. destruct H3. rewrite H3. Admitted.*)
    (* - intros. induction ports.
      destruct H2. destruct H2. inversion H2.
      simpl. destruct nequiv_dec. apply IHports.
      destruct H2. *)
      (exists b, In b ports /\ (id input = b)).
    Proof.
    split.
    - intros. induction ports.
    + simpl in H2. inversion H2.
    + simpl in H2. destruct nequiv_dec in H2. apply IHports in H2.
      repeat destruct H2. exists x. split.
      simpl;auto.
      exact H3.
      inversion e. exists a.
      split. simpl;auto.
      exact H3.
    - intros. induction ports.
    + repeat destruct H2.
    + simpl. destruct nequiv_dec. apply IHports. repeat destruct H2. congruence. exists x. split; assumption.
      reflexivity. 
    Defined.


    Fixpoint retrievePortsOutsideTransition (input: set port) (ports : set name) :=
      match input with
      | [] => []
      | a::x => if (portsOutsideTransition a ports) == true then a::retrievePortsOutsideTransition x ports
                else retrievePortsOutsideTransition x ports
      end.

    Lemma retrievePortsOutsideTransitionSound : forall input, forall ports,
    retrievePortsOutsideTransition input ports <> [] <-> exists a, portsOutsideTransition a ports = true /\
    In a input.
    Proof.
    split.
    - intros. induction input.
    + simpl in H2. congruence.
    + simpl in H2. destruct equiv_dec in H2. inversion e.
      exists a. split. reflexivity.  simpl;auto.
      apply IHinput in H2. destruct H2. exists x. destruct H2.
      split. assumption.
      simpl;auto.
    - intros. induction input. destruct H2. destruct H2. 
    + inversion H3. 
    + simpl. destruct equiv_dec.
      discriminate. 
      apply IHinput. destruct H2.
      destruct H2. simpl in H3.
      destruct H3. rewrite <- H3 in H2. congruence.
      exists x. split. exact H2. exact H3. Defined.
    
    

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
    Proof. (*descartar o In a thetadelta *)
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
       (*destruct H2. simpl. rewrite H2. destruct equiv_dec. destruct nequiv_dec. reflexivity.
       inversion e0. congruence. congruence. *)
       simpl. destruct equiv_dec. destruct nequiv_dec. reflexivity. inversion e0. 
       apply IHthetadelta. exists a. Admitted.

      

    Fixpoint checkPorts (t:set port) (thetadelta: set (name * option data)) :=
      match t with
      | [] => true
      | a::x => if negb (hasDataInThetaDelta a thetadelta) then checkPorts x thetadelta
                else false
      end.

    Definition onlyPortsInvolvedContainsData (ca:constraintAutomata) (ports : set name) 
      (k l : nat) (input : set port) :=
      checkPorts (retrievePortsOutsideTransition (input) ports) (thetaDelta (ca) (k) (l) (input)).


    (* Before taking a step, we want to retrieve ports in theta.N                                               *)
    Definition retrievePortsFromThetaN (k l : nat) (input: set port) :=
      thetaN (input) (k) (l) (input).

   Check retrievePortsFromThetaN.


    (* A single step can be defined in terms of the following definitions:                                    *)
    (* ERICK: falta um intermediário que pegue a step de acordo com cada índice de cada porta. *)
    Fixpoint step' (ca:constraintAutomata) (k l : nat) (input : set port) (ports: set name)
     (s: set(set name * bool * set(state))) :=
     match s with
     | [] => []
     | a::t => if (set_eq (ports)(*thetaN (input) (k) (l) (input)*) ((fst(fst(a))))) && 
                  (onlyPortsInvolvedContainsData ca (fst(fst(a))) k l input)
                   && (snd(fst(a))) then snd(a)++step' ca k l  input ports t
                   else step' ca k l input ports t
     end.
    Check step'.

    Definition istep' (ca:constraintAutomata) (k l : nat) (input : set port) 
    (s: set(set name * bool * set(state))) (ports:set name)  :=
      (step' ca k l input ports s).
    Check istep'.

    Definition stepAux (ca:constraintAutomata) (k l : nat) (input:set port) (ports:set name) (s: state) :=
      istep' ca k l input (T ca s k) ports. (* O correto nessa chamada é k, e não l *)
    Check stepAux.

    (* We apply the step to every state in the given configuration:                     *)
    Definition stepa (ca:constraintAutomata) (s: set state) (k l : nat) (input:set port) (ports: set name):=
     (ports, flat_map (stepAux ca k l input ports) s).

    Check stepa.

    Definition step (ca:constraintAutomata) (s: set state) (k l : nat) (input:set port) :=
      stepa ca s k l input (retrievePortsFromThetaN k l input).

   (* We define run' as a function that iterates over a list of naturals. v0                                *)
   (* ERICK: note que a noção de runa' é diferente do trace de execução do autômato (dada por run').        *)
   (* Isso aparenta ser inútil pois constraint automata não possui noção de estados finais, embora possamos dizer 
     que uma run é aceita se sempre é possível disparar uma transição em algum estado ao longo da run. *)
    Definition runa' (ca:constraintAutomata) (*s:state*)  : 
      set port -> list nat -> nat -> (set state) -> set state :=
      (* k : índice de execução               *)
      (* l : profundidade da busca            *)
      fix rec input k l acc :=
        match k with 
          | [] => acc
          | a::t => snd (step ca acc a l input)
                    |> rec (portsDerivative(fst((step ca acc a l input))) input) t  l 
        end. 


    Definition run' (ca:constraintAutomata)  : 
      set port -> list nat -> nat -> set state -> set (set state) -> set (set state) :=
      (* k : índice de execução               *)
      (* l : profundidade da busca            *)
      fix rec input k l acc resp :=
        match k with 
          | [] => resp
          | a::t => resp ++ [snd (step ca acc a l input)]
                    |> rec input (*portsDerivative(fst((step ca acc a l input))) input*) t  l (snd (step ca acc a l input))
        end.
    (* In order to use run' as defined above, we define a function that given a natural number n, it creates an ordered *)
    (* list containing naturals that ranges from 0 to n                                                 *)
    Program Fixpoint count_into_list (n:nat) :=
      match n with
      | 0 => 0::nil
      | S n => count_into_list n ++ [S n]
      end.

    (* We define a run on a constraint automaton. *)
    Definition run (ca:constraintAutomata) (input: set port) (k l : nat) :=
      run' ca input (count_into_list k) l (Q0 ca) [Q0 ca].


    (* Beginning of Product Automata *)

    (* Variable state1 state2 : Type. <- não necessário visto que o primeiro produto é o produto de dois autômatos *)
    (* "normais" *)

    (* Vale notar que o tipo de estados de ambos os autômatos devem ser o mesmo.*)
    (* Existe um problema na run para esse caso : ela não espera como argumento um par de estados como um estado inicial.
       Uma possível solução consiste em criar uma "run" que chama a run atual adaptada pra cada elemento de cada par
       (q_i,q_j) \in Q0,1 X Q0,2 (Ou não, dependendo de como os estados no autômato resultante vão ficar.*)
    (* We produce the reusulting set of states *)
    Definition resultingStatesSet (a1: constraintAutomata) (a2: constraintAutomata) :=
      list_prod (Q a1) (Q a2). (*list_prod: cartesian product of lists *)

    Lemma resultingStatesSetSound : forall a1, forall a2, forall a, forall b,
      In (a,b) (resultingStatesSet a1 a2) <-> In a (Q a1) /\ In b (Q a2).
    Proof.
    intros. apply in_prod_iff. 
    Defined.

    (* We produce the resulting set name *)
    Definition resultingNameSet (a1:constraintAutomata) (a2: constraintAutomata) :=
      set_union equiv_dec (N a1) (N a2).
    
    Lemma resultingNameSetSound : forall a1, forall a2, forall a,
      In a (resultingNameSet a1 a2) <-> In a (N a1) \/ In a (N a2).
    Proof.
    intros. apply set_union_iff.
    Defined.

    (* We produce the resulting set of initial states *)

    Definition resultingInitialStatesSet (a1: constraintAutomata) (a2: constraintAutomata) :=
      list_prod (Q0 a1) (Q0 a2).

    Lemma resultingInitialStatesSetSound : forall a1, forall a2, forall a, forall b,
      In (a,b) (resultingInitialStatesSet a1 a2) <-> In a (Q0 a1) /\ In b (Q0 a2).
    Proof.
    intros. apply in_prod_iff. 
    Defined.

    (* We define an inductive type in order to denote a transition in the resulting automaton. *)

(*    Inductive productTransition q1 q2 state := 
    (* let us label state as the resulting state of this composite transition, which may contain 1 or more target
       states *)
    | resTrans : (q1 * q2) -> (* nat ->*) set (set (name) * bool * set(state)) -> productTransition q1 q2 state.
    (*ERICK: isso aqui tá trash *)

    (* The following definitions stand for the definition of the resulting transition set. *)

    (* The first definition 
    Fixpoint retrieveNotAffectedTransitions (s : set (state * state))
*)
    (* Second transition generation rule *)
    (*ERICK: essa função recebe uma relação de transição de um autômato e um conjunto de portas que vai ser o
     do outro autômato. Logo, posso parametrizá-la com A1 e A2, onde me interessa a relação de transição de A1 
     O conjunto final de transições será montado tal como o resultante do nfa sem transição epsilon a partir de um
     nfa epsilon tal como feito no RGCoq (um conjunto que possui todas as transições geradas conforme as regras espe
     cificadas em Arbab (2006)   *)
    (* The following definition is bound to recover a transition only present in one of the automatons which is not *)
    (* influencend by the other, as specified by the transition derivation in Arbab (2006)                          *)

      Definition getTransitionsFromSingleCA (a1: constraintAutomata) (q1 : state) :=
      if (fst(q1 |> (T(a1))) == true) then 3 else 4.

    *)

  End ConstraintAutomata.
End ConstraintAutomata.

(* Module ProductAutomata.
  Section ProductAutomata.

  Variables states names : Type.

  Variables a1 a2 : ConstraintAutomata.constraintAutomata states names.

    (* Beginning of Product Automata *)
    (* Vale notar que o tipo de estados de ambos os autômatos devem ser o mesmo.*)
    (* Existe um problema na run para esse caso : ela não espera como argumento um par de estados como um estado inicial.
       Uma possível solução consiste em criar uma "run" que chama a run atual adaptada pra cada elemento de cada par
       (q_i,q_j) \in Q0,1 X Q0,2 (Ou não, dependendo de como os estados no autômato resultante vão ficar.*)
    (* We produce the reusulting set of states *)
    Definition resultingStatesSet :=
      list_prod (ConstraintAutomata.Q a1) (ConstraintAutomata.Q a2). (*list_prod: cartesian product of lists *)

    Lemma resultingStatesSetSound : forall a1 : ConstraintAutomata.constraintAutomata states names, forall a2, forall a, forall b,
      In (a,b) (resultingStatesSet a1 a2) <-> In a (ConstraintAutomata.Q a1) /\ In b (ConstraintAutomata.Q a2).
    Proof.
    intros. apply in_prod_iff. 
    Defined.

    (* We produce the resulting set name *)
    Definition resultingNameSet (a1:constraintAutomata) (a2: constraintAutomata) :=
      set_union equiv_dec (N a1) (N a2).
    
    Lemma resultingNameSetSound : forall a1, forall a2, forall a,
      In a (resultingNameSet a1 a2) <-> In a (N a1) \/ In a (N a2).
    Proof.
    intros. apply set_union_iff.
    Defined.

    (* We produce the resulting set of initial states *)

    Definition resultingInitialStatesSet (a1: constraintAutomata) (a2: constraintAutomata) :=
      list_prod (Q0 a1) (Q0 a2).

    Lemma resultingInitialStatesSetSound : forall a1, forall a2, forall a, forall b,
      In (a,b) (resultingInitialStatesSet a1 a2) <-> In a (Q0 a1) /\ In b (Q0 a2).
    Proof.
    intros. apply in_prod_iff. 
    Defined.

    (* The following definitions stand for the definition of the resulting transition set. *)/

    (* The first definition 
    Fixpoint retrieveNotAffectedTransitions (s : set (state * state))
*)
    (* Second transition generation rule *)
    (*ERICK: essa função recebe uma relação de transição de um autômato e um conjunto de portas que vai ser o
     do outro autômato. Logo, posso parametrizá-la com A1 e A2, onde me interessa a relação de transição de A1 
     e o conjunto de estados de A2. *)

  End ProductAutomata.
End ProductAutomata. *)


  Definition foo (n:nat) : nat :=
    match n with
    | 0 => 1
    | 1 => 2
    | S n => S (S n)
    end.


  (* Example  *) 

  Definition timeStampTest (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1 (* injecting N to Z *)
    end.

  Definition timeStampTest2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  5#1 (*1#1*)
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Inductive states : Type := q0 | p0 | p1.
  Inductive ports : Type := A | B.
 (*Program não resolve aqui... eu tinha esquecido que estou usando a tática incorreta*)
  Instance portsEq : EqDec ports eq :=
    {equiv_dec x y := 
      match x,y with
      | A,A | B,B => in_left
      | A,B | B,A => in_right
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentA n := 
    match n with
    | 0 => Some 0
    | 1 => None
    | 2 => Some 1 
    | 3 => None
    | 4 => Some 1
    | S n => Some (1)
    end.

  Definition dataAssignmentB n :=
    match n with
    | 0 => None
    | 1 => Some (0)
    | 2 => None
    | 3 => Some 1
    | 4 => None
    | S n => Some 1
    end.

  Lemma timeStampTestHolds : forall n, Qle (timeStampTest n) (timeStampTest (S n)).
  Proof.
  induction n. 
  + unfold timeStampTest. cbv. intros. inversion H.
  + unfold timeStampTest. (*alguma tática de ring em cima de Q deve resolver aqui. procurar depois *)
  Admitted.

  Lemma timeStampTestHolds2 : forall n, 
    Qle (timeStampTest2 n) (timeStampTest2 (S n)). 
  Proof.
  Admitted.

  Definition portA := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampTest;
        ConstraintAutomata.portCond := timeStampTestHolds;
        ConstraintAutomata.index := 0 |}.

  Definition portB := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampTest2;
        ConstraintAutomata.portCond := timeStampTestHolds2;
        ConstraintAutomata.index := 0 |}.


  Check ConstraintAutomata.DC.
  Definition realports := [portA;portB].

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
  Definition oneBoundedFIFOrel (s:states) (l:nat) : 
  set (set (ports) * bool * set states) :=
    match s with
    | q0 => [([A], (ConstraintAutomata.DC(portA) l (Some 0)), [p0]) ;
             ([A], (ConstraintAutomata.DC(portA) l (Some 1)), [p1])]
    | p0 => [([B], (ConstraintAutomata.DC(portB) l (Some 0)), [q0])]
    | p1 => [([B], (ConstraintAutomata.DC(portB) l (Some 1)), [q0])]
    end.


  (* falta definir transição para começar a brncar com a run.                                      *)
  Definition oneBoundedFIFOCA:= {|
    ConstraintAutomata.Q := [q0;p0;p1];
    ConstraintAutomata.N := [A;B]; (*TODO : ports -> Names  *)
    ConstraintAutomata.T := oneBoundedFIFOrel;
    ConstraintAutomata.Q0 := [q0]
  |}.

  Eval compute in ConstraintAutomata.thetaDelta oneBoundedFIFOCA 0 0 [portA;portB].

  Eval compute in ConstraintAutomata.retrievePortsFromThetaN 0 20 [portA;portB].

  (*Eval compute in ConstraintAutomata.thetaDelta oneBoundedFIFOCA 2 20 [portA;portB].*)
  (*onlyPortsInvolvedContainsData (ca:constraintAutomata) (ports : set name) 
      (k l default : nat) (input : set port)
    Definition thetaDelta (ca:constraintAutomata) (k : nat) (l:nat) (po: set port) (default:nat) := 
      portsWithData po k l po default.*)
  Eval compute in ConstraintAutomata.onlyPortsInvolvedContainsData (oneBoundedFIFOCA) [A] 
      0 20 [portA;portB]. 

  Eval compute in ConstraintAutomata.step oneBoundedFIFOCA [p0] 1 10 [portA;portB].

  Definition x := Eval compute in ConstraintAutomata.portsDerivative ([A]) ([portA;portB]).
  Definition videos := Eval compute in ConstraintAutomata.portsDerivative ([A]) (x).


  (* TODO: thetaDelta aparenta estar ok. A porta de entrada é parametrizada. O problema parece ser na definição de DC
   estar fixa em uma porta (a inicial, sem atualização de index (cálculo de derivada)                                 *)
  Eval compute in ConstraintAutomata.thetaDelta oneBoundedFIFOCA 2 20 videos.
  Print videos.

  Eval compute in ConstraintAutomata.thetaDelta oneBoundedFIFOCA 5 20 [portA;portB].

  (* Debugging - 22072018 *)

  Eval compute in ConstraintAutomata.step oneBoundedFIFOCA (ConstraintAutomata.Q0 oneBoundedFIFOCA) 0 20  (* --> PEGUEI O FDP *)
  [portA;portB].

  Eval compute in ConstraintAutomata.step' oneBoundedFIFOCA  0 20 [portA;portB].

  Eval compute in ConstraintAutomata.run oneBoundedFIFOCA [portA;portB] 4 20.
  Eval compute in oneBoundedFIFOrel (q0) .


  (* Sync channel CA *)
  Inductive syncState := X.
  Inductive syncPorts := E | F.

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

  (*Erick : questiono se as portas tiverem uma stream de tempo diferente, 
    onde uma sempre está atrasada em comparação à outra. Essa porta jamais verá dados? (não aparece em theta.time *)
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

  Definition syncCaBehavior (s: syncState) (l:nat) : 
  set (set (syncPorts) * bool * set syncState) :=
    match s with
    | X => [([E;F] , (ConstraintAutomata.DC(portE) l (ConstraintAutomata.dataAssignment(portF)(l))), [X])] 
    end.

  Definition syncCA := {|
    ConstraintAutomata.Q := [X];
    ConstraintAutomata.N := [E;F];
    ConstraintAutomata.T := syncCaBehavior;
    ConstraintAutomata.Q0 := [X]
  |}.

 (* Alguma coisa na run está bichada. o cálculo da derivada tá quebrado. *)
 Eval compute in syncCaBehavior X 2.
 Eval compute in ConstraintAutomata.retrievePortsFromThetaN 1 10 [portE;portF].
 Eval compute in ConstraintAutomata.stepa syncCA [X] 1 10 [portE;portF] [E;F].

 Eval compute in ConstraintAutomata.run syncCA [portE;portF] 20 20.

(* We model another example seen in Airbab(2004)  *)

  Inductive states2 : Type := qa | qb.
  Inductive ports2 : Type := A0 | B0.
  Instance portsEq2 : EqDec ports2 eq :=
    {equiv_dec x y := 
      match x,y with
      | A0,A0 | B0,B0 => in_left
      | A0,B0 | B0,A0 => in_right
      end }.
   Proof.
   all: congruence.
   Defined.

  Definition dataAssignmentA0 n := 
    match n with
    | 0 => Some 0
    | 1 => Some 1

    | S n => Some (1)
    end.

  Definition dataAssignmentB0 n :=
    match n with
    | 0 => Some 0
    | 1 => Some 1

    | S n => Some (1)
    end.

  Definition timeStampTestA0 (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1 (* injecting N to Z *)
    end.


  Lemma timeStampTestHoldsA0 : forall n, 
    Qle (timeStampTestA0 n) (timeStampTestA0 (S n)). 
  Proof. Admitted.

  (*Erick : questiono se as portas tiverem uma stream de tempo diferente, 
    onde uma sempre está atrasada em comparação à outra. Essa porta jamais verá dados? (não aparece em theta.time *)

  Definition portA0 := {|
        ConstraintAutomata.id := A0;
        ConstraintAutomata.dataAssignment := dataAssignmentA0;
        ConstraintAutomata.timeStamp := timeStampTestA0;
        ConstraintAutomata.portCond := timeStampTestHoldsA0;
        ConstraintAutomata.index := 0 |}.

   Definition timeStampTestB0 (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  2#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1 (* injecting N to Z *)
    end.

  Lemma timeStampTestHoldsB0 : forall n, 
    Qle (timeStampTestB0 n) (timeStampTestB0 (S n)). 
  Proof. Admitted.

  Definition portB0 := {|
        ConstraintAutomata.id := B0;
        ConstraintAutomata.dataAssignment := dataAssignmentA0;
        ConstraintAutomata.timeStamp := timeStampTestB0;
        ConstraintAutomata.portCond := timeStampTestHoldsB0;
        ConstraintAutomata.index := 0 |}.

  Definition anotherCABehaves (s:states2) (l:nat) : 
  set (set (ports2) * bool * set states2) :=
    match s with
    | qa => [([A0], (true), [qa]) ;
             ([A0], (true), [qb])]
    | qb => [([A0;B0] , (ConstraintAutomata.DC(portA0) l (ConstraintAutomata.dataAssignment(portB0)(l))), [qb])] 
    end.


  Definition anotherCA := {|
    ConstraintAutomata.Q := [qa;qb];
    ConstraintAutomata.N := [A0;B0];
    ConstraintAutomata.T := anotherCABehaves;
    ConstraintAutomata.Q0 := [qa]
  |}.

  Eval compute in ConstraintAutomata.onlyPortsInvolvedContainsData (anotherCA) [A0;B0] 
      2 20 [portA0;portB0].

  Eval compute in ConstraintAutomata.thetaDelta anotherCA 2 20 [portA0;portB0].

  Eval compute in anotherCABehaves qb 2.

  Eval compute in ConstraintAutomata.step' anotherCA 3 20 [portA0;portB0] [A0;B0] (ConstraintAutomata.T anotherCA qb 2).

  (* step' (ca:constraintAutomata) (k l : nat) (input : set port) (ports: set name)
     (s: set(set name * bool * set(state))) *)
  Eval compute in ConstraintAutomata.stepa anotherCA [qa;qb] 1 10 [portA0;portB0] [A0;B0].

  Eval compute in ConstraintAutomata.step anotherCA ([qb]) 2 20 [portA0;portB0].

  (* Sem o cálculo de derivada não trava, mas ainda assim o resultado está incorreto. *)
  (* Erick : acho que não entendi como passar a entrada corretamente pro autômato, não pode ser *)
  (* ou a implementação de theta.time pode não estar correta. *)
  Eval compute in ConstraintAutomata.run anotherCA [portA0;portB0] 4 20.







