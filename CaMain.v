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
(*
Lemma s1_in_s2_sound {A} `{EqDec A eq} : forall s1, forall s2, s1_in_s2 s1 s2 = true <-> s1 = [] \/
                                         (forall a, In a s1 -> set_mem equiv_dec a s2 && s1_in_s2 t s2 == true).
*)
Fixpoint set_eq {A} `{EqDec A eq} (s1 s2 : set A) :=
  if (length s1 == length s2) then
      if (s1_in_s2 s1 s2) then
          if (s1_in_s2 s2 s1) then true else false
      else false
  else false.

(*
Lemma set_eq_sound {A} `{EqDec A eq} : forall s1 : set A, forall s2 : set A, set_eq s1 s2 = true <-> ((length s1 = length s2))
                                                              /\ s1_in_s2 s1 s2 = true /\ s1_in_s2 s2 s1 = true.
  Proof.
  split.
  - intros. destruct s1. destruct s2.
  + split. reflexivity. split. repeat assumption.
*)
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
      timeStamp : nat -> QArith_base.Q (* models nat -> real *);
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
    Check port.


    (* TDS^names can be seen as a set of ports as defined above.. *)
    (* In order to totalize the functions, we opted to use option type for both data and the time when  *)
    (* the data happens in a port. This lets the user to define a instant that there will be no data in *)
    (* a given port A_i                                                                                 *)

    (* Begin da nova DC *)
    Inductive DC := (*TODO parametrizar a dc? *)
    | tDc : DC (* permite a formalização de DCs como tendo um booleano direto (leia-se true) *)
    | dc : name -> option data -> DC (*esse option data fica a critério do usuário usar ou já forço aqui? *)
                                     (*isso não afeta o funcionamento do autõmato                         *)
    | andDc : DC -> DC -> DC
    | orDc  : DC -> DC -> DC
    | negDc : DC -> DC.
    (*alguma coisa que separe cada data constraint em uma construção como essa
      se nesse contexto o primeiro data seja o dado da porta e o segundo um item
      de dado (que também pode ser um conteúdo de uma porta, um evalDC da vida
      vai pegar a porta em questão e ver na entrada se o dado naquele momento atende
      a dc. Por essa perspectiva, um data só ja serve. *)

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

    (* The following definition dismembers composite DCs into "canonical" ones in order to check whether they are
      satisfied *)
    (*s : set port (que será chamado na run com as portas atualizadas *)
    Fixpoint evalCompositeDc (s:set port) (dc: DC) : bool :=
      match dc with
      | tDc => true
      | dc a b => evalDC (retrievePortFromInput s a) (b)
      | andDc a b => evalCompositeDc s a && evalCompositeDc s b
      | orDc a b => evalCompositeDc s a || evalCompositeDc s b
      | negDc a => negb (evalCompositeDc s a)
      end.  

    (* End da nova DC *)

    Record constraintAutomata : Type := CA {
      Q : set state;
      N : set name;
      T : state -> set (set (name) * DC * set(state));
      Q0 : set state;
    }.
    Check CA.

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
    destruct equiv_dec in H2. inversion e. exists a. simpl; auto. 
    apply IHl in H2. destruct H2. destruct H3. destruct H3. exists x. split. simpl. right. exact H3.
    exact H4.
    Defined.

    Lemma returnSmallerNumber_sound2 : forall m, forall l, l <> [] /\ (exists a, In a l /\ a <? m = true)
    -> returnSmallerNumber m l <> m.
    Proof.
    intros. induction l.
    + destruct H2. congruence.
    + simpl. destruct equiv_dec. Admitted.
    

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
    (*Definition thetaTime (s:set port) (k:nat)  := 
      returnSmallerNumber (100000#1) (mapAp k ((s) |> getTimeStampFromPorts)).*)

    Close Scope Q_scope.

    (* gets candidates from a port's time stream *)
    Fixpoint getThetaTimeCandidate (p:port) (k:set nat) :=
      match k with
      | [] => []
      | a::t => timeStamp p(a)::getThetaTimeCandidate p t (*ERICK: isso aqui tá errado. 
                            o tempo tem que ser calculado em cima do index*)
      end.

    Check getThetaTimeCandidate.

    Fixpoint getAllThetaTimes (s: set port) (k : set nat) :=
      match s with
      | [] => []
      | a::t => getThetaTimeCandidate a k++getAllThetaTimes t k
      end.

  Check getAllThetaTimes.

    Definition getNextThetaTime (l: set QArith_base.Q) :=
       returnSmallerNumber (1000000#1) (l).

    Program Fixpoint count_into_list (n:nat) :=
      match n with
      | 0 => 0::nil
      | S n => count_into_list n ++ [S n]
      end.

    Definition thetaTime (s:set port) (k:nat) :=
      match k with
      | 0 => thetaTimeInZero s
      | S n => getNextThetaTime (getAllThetaTimes s (count_into_list(S n)))
      end.

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

    Lemma timeStampEqThetaTimeSound2 : forall ca, forall k, forall l, forall a, 
    timeStamp a(l) =? thetaTime (ca) (k) = true \/ 
    (exists x, x < l /\ timeStamp a(x) =? thetaTime (ca) (k) = true) ->  timeStampEqThetaTime ca k l a = true.
    Proof.
    - intros. induction l. 
    + destruct H2. simpl. rewrite H2. auto. destruct H2. destruct H2. inversion H2.
    + simpl. destruct equiv_dec. reflexivity. 
      destruct H2. congruence.
      destruct H2. destruct H2.
      unfold timeStampEqThetaTime.
    Admitted.

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
    Definition derivative (p: port) := Eval compute in mkport (id p) (dataAssignment p) (timeStamp p)
        (portCond p) (S (index p)).

    Lemma derivative_sound : forall p, derivative p = mkport (id p) (dataAssignment p) (timeStamp p)
        (portCond p) ( S(index p)).
    Proof.
    reflexivity.
    Defined.


    (* BEGIN calculating a port's derivative *)
    (* First we need to define an equality relation for ports *)
    (* Context `{EqDec port eq}. *)
    Fixpoint derivativePortInvolved (s:set name) (a: port) :=
      match s with
      | [] => [] 
      | x::t => if x == id a then derivative(a)::derivativePortInvolved t a(*set_add equiv_dec (derivative(a))(derivativePortInvolved t a)*)
                else (*set_add equiv_dec (a)(derivativePortInvolved t a)*)(derivativePortInvolved t a)
      end.

    Lemma derivativePortsInvolvedSound : forall s, forall a, 
      derivativePortInvolved s a <> [] <-> s <> [] /\ exists x, In x s /\ x = id a.
    Proof.
    split.
    - intros. induction s.
    + simpl in H2. congruence.
    + simpl in H2. (*discriminate.
    - intros. induction s.
    + simpl. congruence.
    + simpl. destruct equiv_dec. *) Admitted. (*simpl. discriminate. discriminate.
    Defined.*)
  

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
      simpl. destruct equiv_dec. Admitted. (*simpl. congruence. simpl. congruence.
    Defined *)
   (* The following function may calculate the derivative of ports involved in a given transition *)
    Definition portsDerivative (names: set name) (input: set port) := 
      allDerivativesFromPortsInvolved names input.

    (* END calculate derivative *)

    (* We also need to check if the ports involved in a transition are the only ones with data so it can fire *)

    Fixpoint portsOutsideTransition (input: port) (ports : set name) :=
      match ports with
       | [] => true
       | a::t => if (id input <> a) then portsOutsideTransition input t else false
      end.

    Lemma portsOutsideTransitionSound : forall input, forall ports, portsOutsideTransition input ports = false <->
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
    Check retrievePortsOutsideTransition.

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

    Fixpoint checkPorts (t:set port) (thetadelta: set (name * option data)) :=
      match t with
      | [] => true
      | a::x => if negb (hasDataInThetaDelta a thetadelta) then checkPorts x thetadelta
                else false
      end.

    Lemma checkPortsSound : forall t, forall thetadelta, checkPorts t thetadelta = false <->
      exists a, In a t /\ hasDataInThetaDelta a thetadelta = true.
    Proof.
    split.
    - intros. induction t.
    + inversion H2.
    + simpl in H2. destruct negb in H2. apply IHt in H2. repeat destruct H2.
      exists x. split. simpl;auto. exact H3.
      exists a. simpl.  Admitted.

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
     (s: set(set name * DC * set(state))) :=
     match s with
     | [] => []
     | a::t => if (set_eq (ports)((fst(fst(a))))) && 
                  (onlyPortsInvolvedContainsData ca (fst(fst(a))) k l input)
                   && (evalCompositeDc (input) (snd(fst(a)))) then snd(a)++step' ca k l  input ports t
                   else step' ca k l input ports t
     end.
    Check step'.

    Definition istep' (ca:constraintAutomata) (k l : nat) (input : set port) 
    (s: set(set name * DC * set(state))) (ports:set name)  :=
      (step' ca k l input ports s).
    Check istep'.

    Definition stepAux (ca:constraintAutomata) (k l : nat) (input:set port) (ports:set name) (s: state) :=
      istep' ca k l input (T ca s) ports. (* O correto nessa chamada é k, e não l *)
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
                    |> rec
                      (flat_map(derivativePortInvolved(fst((step ca acc a l input)))) input) t  l (snd (step ca acc a l input))
        end.

    (* We define a run on a constraint automaton. *)
    Definition run (ca:constraintAutomata) (input: set port) (k l : nat) :=
      run' ca input (count_into_list k) l (Q0 ca) [Q0 ca].

  End ConstraintAutomata.
End ConstraintAutomata.

Module ProductAutomata.
(*DESATIVAR Module ProductAutomata.*)
  Section ProductAutomata.
      Variable state name data : Type.
      Context `{EqDec name eq} `{EqDec state eq} `{EqDec (option data) eq}.
      (*Variables a1 a2 : ConstraintAutomata.constraintAutomata state name data.*)
      (* Beginning of Product Automata  ---------------------------------------------------- *)

    Definition constraintAutomata := ConstraintAutomata.constraintAutomata state name data.
    Definition DC := ConstraintAutomata.DC name data.
    (*ERICK: as definições acima é apenas pra não ficar (exaustivamente) escrevendo todos os parâmetros *)

    (* Vale notar que o tipo de estados de ambos os autômatos devem ser o mesmo.*)
    (* Existe um problema na run para esse caso : ela não espera como argumento um par de estados como um estado inicial.
       Uma possível solução consiste em criar uma "run" que chama a run atual adaptada pra cada elemento de cada par
       (q_i,q_j) \in Q0,1 X Q0,2 (Ou não, dependendo de como os estados no autômato resultante vão ficar.*)
    (* We produce the reusulting set of states *)
    (*Definition paState : Type  := (state * state).
    Check paState.
    Check (state , state).*)

    Definition resultingStatesSet (a1:ConstraintAutomata.constraintAutomata state name data) (a2:ConstraintAutomata.constraintAutomata state name data) :=
      list_prod (ConstraintAutomata.Q a1) (ConstraintAutomata.Q a2).
    Check resultingStatesSet.

    Lemma resultingStatesSetSound :forall a1,forall a2, forall a, forall b,
      In (a,b) (resultingStatesSet a1 a2) <-> In a (ConstraintAutomata.Q a1) /\ In b (ConstraintAutomata.Q a2).
    Proof.
    intros. apply in_prod_iff. 
    Defined.

    (* We produce the resulting set name *)
    Definition resultingNameSet (a1:ConstraintAutomata.constraintAutomata state name data) (a2:ConstraintAutomata.constraintAutomata state name data) :=
      set_union equiv_dec (ConstraintAutomata.N a1) (ConstraintAutomata.N a2).
    
    Lemma resultingNameSetSound : forall a1, forall a2, forall a,
      In a (resultingNameSet a1 a2) <-> In a (ConstraintAutomata.N a1) \/ In a (ConstraintAutomata.N a2).
    Proof.
    intros. apply set_union_iff.
    Defined.

    (* We produce the resulting set of initial states *)

    Definition resultingInitialStatesSet (a1: constraintAutomata) (a2: constraintAutomata) :=
      list_prod (ConstraintAutomata.Q0 a1) (ConstraintAutomata.Q0 a2).

    Lemma resultingInitialStatesSetSound : forall a1, forall a2, forall a, forall b,
      In (a,b) (resultingInitialStatesSet a1 a2) <-> In a (ConstraintAutomata.Q0 a1) /\ In b (ConstraintAutomata.Q0 a2).
    Proof.
    intros. apply in_prod_iff. 
    Defined.

    (* Definition of transitions in the product automaton *)
    (* The following definiton may evaluate the necessary conditions to create a transition as specified by the first rule *)
    Definition evaluateConditionsFirstRule (t1 : ( set(name) * DC * set(state))) (t2 : (set(name) * DC * set(state)))
      (names1 : set name) (names2: set name) :=
      if set_eq (set_inter equiv_dec (names2) (fst(fst(t1)))) (set_inter equiv_dec (names1) (fst(fst(t2)))) then true else false.

    (* Retrieve the outgoing resulting state of the resulting transition in the product automaton as depicted by Arbab(2006). *)
    (*ERICK: acho que está inutilizada. A não ser que eu tenha que extrair isso do conjunto de estados do autômato. *)
    Fixpoint recoverOutboundStateRule1 (q1 : state) (q2 : state) (states : set (state * state)) :=
      match states with
      | [] => None
      | a::t => (*if (((q1 == fst(a)) = true) && ((q2 == snd(a))= true))*)
                if (q1 == fst(a)) then 
                    if (q2 == snd(a)) then Some a else recoverOutboundStateRule1 q1 q2 t
                else recoverOutboundStateRule1 q1 q2 t
      end.  

    (*Definition buildResultingTransitionRule1 (q1: state) (q2 : state) (n1: set (name)) (n2 : set (name))
      (g1 : DC) (g2: DC) (p1: state) (p2: state) :=
      ((q1,q2),(((set_union equiv_dec (n1) (n2)),ConstraintAutomata.andDc (g1) (g2)),(p1,p2))).
    Check buildResultingTransitionRule1.*)

    Fixpoint buildResultingTransitionFromStatesRule1 (p1: state) (p2: set state) :=
      match p2 with
      | [] => []
      | a::t => (p1,a)::
                buildResultingTransitionFromStatesRule1 p1 t
      end.
    Check buildResultingTransitionFromStatesRule1.

    Fixpoint buildResultingTransitionFromStatesBothTransitionsRule1 (p1: set state) (p2: set state) :=
      match p1 with
      | [] => []
      | a::t => buildResultingTransitionFromStatesRule1 a p2++
                buildResultingTransitionFromStatesBothTransitionsRule1 t p2
      end.
    Check buildResultingTransitionFromStatesBothTransitionsRule1.

    (*Given two single transitions as hereby formalized, this definition builds all resulting states according to *)
    (* the first rule that defines the transition relation of the product automata *)
    (* Essa definição tá errada (daonde saiu esse q2: set state? q2 é um state, não um set state *)
    (* TODO a definição abaixo 
      Define a regra1 de forma canônica (agora falta chamar para todas as combinações de transições de a1 e a2) *)
    Definition buildResultingTransitionFromSingleStateRule1 (Q1: state) (Q2: state)
      (transition1: (set (name) * DC * (set(state)))) 
      (transition2: (set (name) * DC * (set(state)))) 
      (names1 : set name) (names2: set name) : (*set*) (set (state * state * ((set name * DC) * set (state * state)))) :=
      if (evaluateConditionsFirstRule (transition1) (transition2) (names1) (names2)) == true then
                  [((Q1,Q2),(((set_union equiv_dec (fst(fst(transition1))) (fst(fst(transition1)))),ConstraintAutomata.andDc (snd(fst(transition1))) 
                            (snd(fst(transition2)))),(buildResultingTransitionFromStatesBothTransitionsRule1(snd(transition1)) (snd(transition2)))))]
                  (*buildResultingTransitionFromStatesBothTransitionsRule1 Q1 Q2 (fst(fst(transition1))) 
                  (fst(fst(transition2))) (snd(fst(transition1))) (snd(fst(transition2))) (snd(transition1)) 
                  (snd(transition2))*)
                else [].
    Check buildResultingTransitionFromSingleStateRule1.

    Fixpoint buildTransitionFromMoreTransitionsRule1 (Q1: state) (Q2: state)
      (transition1: (set (name) * DC * (set(state)))) 
      (transition2: set (set (name) * DC * (set(state)))) 
      (names1 : set name) (names2: set name) :=
      match transition2 with
      | [] => []
      | a::t => (buildResultingTransitionFromSingleStateRule1 Q1 Q2 transition1 a names1 names2)++
                (buildTransitionFromMoreTransitionsRule1 Q1 Q2 transition1 t names1 names2)
      end.
    Check buildTransitionFromMoreTransitionsRule1.

    Fixpoint buildTransitionFromMoreAllTransitionsSingleState (Q1: state) (Q2: state)
      (transition1: set (set (name) * DC * (set(state)))) 
      (transition2: set (set (name) * DC * (set(state)))) 
      (names1 : set name) (names2: set name) :=
      match transition1 with
      | [] => []
      | a::t => (buildTransitionFromMoreTransitionsRule1 Q1 Q2 a transition2 names1 names2)++
                (buildTransitionFromMoreAllTransitionsSingleState Q1 Q2 t transition2 names1 names2)
      end.

    (*iterates over a set of states of the second automaton in order to apply the transition generation rule to *)
    (* every state: we fix one state while  *)
    Fixpoint iterateOverStatesBuildingTransitionsOne (Q1: state) (Q2: set state)
      (transition1: state -> set (set (name) * DC * (set(state)))) 
      (transition2: state -> set (set (name) * DC * (set(state)))) 
      (names1 : set name) (names2: set name) :=
      match Q2 with
      | [] => []
      | a::t => (buildTransitionFromMoreAllTransitionsSingleState Q1 a (transition1 Q1) (transition2 a) names1 names2)++
                (iterateOverStatesBuildingTransitionsOne Q1 t transition1 transition2 names1 names2)
      end.

    Fixpoint buildAllTransitionsRule1 (Q1: set state) (Q2: set state)
      (transition1: state -> set (set (name) * DC * (set(state)))) 
      (transition2: state -> set (set (name) * DC * (set(state)))) 
      (names1 : set name) (names2: set name) :=
      match Q1 with
      | [] => []
      | a::t => (iterateOverStatesBuildingTransitionsOne a Q2 transition1 transition2 names1 names2)++
                (buildAllTransitionsRule1 t Q2 transition1 transition2 names1 names2)
    end. (* ERICK: a princípio, esse buildAllTransitionsRule1 tem o comportamento necessário *)

    Definition transitionRule1 (a1: constraintAutomata) (a2: constraintAutomata) := 
      buildAllTransitionsRule1 (ConstraintAutomata.Q a1) (ConstraintAutomata.Q a2) 
                               (ConstraintAutomata.T a1) (ConstraintAutomata.T a2) 
                               (ConstraintAutomata.N a1) (ConstraintAutomata.N a2).
    Check transitionRule1.

    (* Second transition generation rule *)
    (*ERICK: essa função recebe uma relação de transição de um autômato e um conjunto de portas que vai ser o
     do outro autômato. Logo, posso parametrizá-la com A1 e A2, onde me interessa a relação de transição de A1 
     O conjunto final de transições será montado tal como o resultante do nfa sem transição epsilon a partir de um
     nfa epsilon tal como feito no RGCoq (um conjunto que possui todas as transições geradas conforme as regras espe
     cificadas em Arbab (2006)   *)


    (*The following definitions aims to recover the necessary data in order to build transitions as specified by the *)
    (* second rule *)
    (* Option type is needed to check whether the transition holds or not. Further processing can get rid of these Nones.*)
    Definition intersectionNAndNames (tr: set (name) * DC * set(state)) (names2: set name) :=
      if (set_inter equiv_dec (fst(fst(tr))) names2) == nil then true else false.
    (* ERICK : separar em duas funções a fim de facilitar o cálculo dos estados resultantes/destinos de uma determinada
      transição.
    Fixpoint recoverStateProductAutomatonRule2 (s1 : state) (s2: state) (states: set (state * state)) :=
      match states with
      | [] => []
      | a::t => if  (fst(a) == s1) then (*then Some a else recoverStateProductAutomata s t*)
                    (set_add equiv_dec a (recoverStateProductAutomatonRule2 s1 s2 t))
                else if (fst(a) == s2) 
                      then (set_add equiv_dec a (recoverStateProductAutomatonRule2 s1 s2 t))
                else recoverStateProductAutomatonRule2 s1 s2 t
      end.*) 
    (* Recovers all pairs of states where the first state is the departing state of a transition *)
    Fixpoint recoverOriginStateProductAutomatonRule2 (s1 : state) (states: set (state * state)) :=
      match states with
      | [] => []
      | a::t => if  (fst(a) == s1) then
                    (set_add equiv_dec a (recoverOriginStateProductAutomatonRule2 s1 t))
                else  recoverOriginStateProductAutomatonRule2 s1 t
      end.
    (* Recoverrs all pairs of state where the first state is the "arriving" state of a tranisition *)
    Fixpoint recoverDestinationStateProductAutomatonRule2 (s2 : state) (states: set (state * state)) :=
      match states with
      | [] => []
      | a::t => if  (fst(a) == s2) then
                    (set_add equiv_dec a (recoverDestinationStateProductAutomatonRule2 s2 t))
                else  recoverDestinationStateProductAutomatonRule2 s2 t
      end.
    Check recoverDestinationStateProductAutomatonRule2.

    (*A function that iterates over pairs of states in order to create the transitions *)
    (*Definition createTransition (q1: (state * state)) (p1: (state * state))  (transition : (set (name) * DC (* set(state*))) :=
      ((q1,transition),p1).*)

    (* The following definition recovers all states from the set of states that are affected by nondeterministic transitions *)
    Definition recoverDetinationStatesFromAllStates (pastates: set (state * state)) : set state -> set (state * state):=
      fix rec states := (*states com tipo set states vai ser o resultado de uma transição no formato state -> (set (name) * DC  set(state)))*)
        match states with
        | [] => []
        | a::t => set_union equiv_dec (recoverDestinationStateProductAutomatonRule2 a pastates) (rec t)
        end.

    Definition createTransition (q1:(state * state)) (transition : (set (name) * DC * (set(state)))) 
        (p1: (state * state)) := ((q1,((fst(transition)), p1))).
    Check createTransition.

    Fixpoint iterateOverOutboundStatesRule2  (p1: set state) (q2: state) :=
      match p1 with
      | [] => []
      | a::t => (*set_add equiv_dec (createTransition q1 transition a) (iterateOverIncomingStates q1 transition t)*)
                set_add equiv_dec ((a,q2))(iterateOverOutboundStatesRule2 t q2)
      end.
    (*Chamar iterateOverIncomingStates 2x : para gerar o estado inbound da transição e de outbound (ou não)*)
    Check iterateOverOutboundStatesRule2.

    Fixpoint iterateOverOutboundStatesRule3 (q1: state) (p1: set state) :=
      match p1 with
      | [] => []
      | a::t => (*set_add equiv_dec (createTransition q1 transition a) (iterateOverIncomingStates q1 transition t)*)
                set_add equiv_dec ((q1,a))(iterateOverOutboundStatesRule3 q1 t)
      end.
    (*Chamar iterateOverIncomingStates 2x : para gerar o estado inbound da transição e de outbound *)
    Check iterateOverOutboundStatesRule3.


    (* Builds an single resulting transition as specified by rule 2 *)
    Fixpoint createSingleTransition (q1:state) (transition : (set (name) * DC * (set(state)))) (a2States : set state) (a2Names: set name)   
    : set (state * state * ((set name * DC) * set (state * state))) :=
    match a2States with
    | [] => []
    | q2::t => if (intersectionNAndNames (transition) (a2Names) == true) then 
                 ((q1,q2),((fst(transition)), (iterateOverOutboundStatesRule2 (snd(transition)) (q2))))::createSingleTransition q1 transition t a2Names
                else createSingleTransition q1 transition t a2Names
    end.
    Check createSingleTransition.
    (* Builds all resulting transitions as specified by rule2 *)
    (* q1: origin state *)
    Definition createTransitionRule2 (*(q1:state) (transitions : set (set (name) * DC * (set(state))))) (names2: set name) 
      (pastates : set (state * state))*) (q1:state) : set (set (name) * DC * (set(state))) -> 
      set state -> set name   (*a2States : estados do autômato a2. Em um primeiro momento, para um único q2 *)
      -> set (state * state * ((set name * DC) * set (state * state))) :=
      fix rec transitions q2 names2 (*sem necessidade do fix *):=
        match transitions with
        | [] => [] 
        | a::t =>  (createSingleTransition q1 a q2 names2)++(rec t q2 names2)
        end.
    Check createTransitionRule2.

    (* Iterates over a set of states of the first automaton in order to apply the second derivation rule to all of its states *)
    Fixpoint createTransitionRule2AllStates (Q1: set state) (transitions: state -> set (set (name) * DC * (set(state)))) 
      (names2: set name) (a2States : set state) := 
      match Q1 with
      | [] => []
      | a::t => (createTransitionRule2 a (transitions(a)) a2States names2)++(createTransitionRule2AllStates t transitions names2 a2States)
      end.
    Check createTransitionRule2.

    (* Given two automatons, builds the resulting set of transitions for their product automaton *)
    Definition transitionsRule2 (a1: constraintAutomata) (a2 : constraintAutomata)  :=
      (createTransitionRule2AllStates (ConstraintAutomata.Q a1) (ConstraintAutomata.T a1) 
                                      (ConstraintAutomata.N a2) (ConstraintAutomata.Q a2)).
    Check transitionsRule2.

    (*Following the idea presented above, we formalize this rule's symetric as *)
    Definition transitionsRule3 (a1: constraintAutomata) (a2 : constraintAutomata)  :=
      (createTransitionRule2AllStates (ConstraintAutomata.Q a2) (ConstraintAutomata.T a2) 
                                      (ConstraintAutomata.N a1) (ConstraintAutomata.Q a1)).
    Check transitionsRule3. (*TODO: ERICK rever se necessário uma nova definição para a simétrica da rule 2*)

    (* The following definition builds the set of states as depicted by the rules presented in Arbab(2006) *)
    Definition buildTransitionRuleProductAutomaton (a1: constraintAutomata) (a2: constraintAutomata) :=
      (transitionRule1 a1 a2)++(transitionsRule2 a1 a2)++(transitionsRule3 a1 a2).
    Check buildTransitionRuleProductAutomaton.

    (*ERICK: provavelmente isso deve ser jogado em outra seção pra fazer state * state ser aceito como um estado *)
    Variable a1 a2 : (constraintAutomata).

    (*The following definition iterates over the set of transiitons of the PA in order to retrieve the 
      inbound states *)
    Fixpoint recoverResultingStatesPA (st: (state * state)) 
      (t:set (state * state * ((set name * DC) * set (state * state))))(*: set ((state * state)) *):=
      match t with
      | [] => []
      | a::tx => if st == fst((a)) then (snd((a))::recoverResultingStatesPA st tx)
                 else recoverResultingStatesPA st tx
      end.
    Check recoverResultingStatesPA.

    Definition buildTransitionsSetProductAutomaton (a1: constraintAutomata) (a2: constraintAutomata) :=
      buildTransitionRuleProductAutomaton a1 a2.
    Check buildTransitionsSetProductAutomaton.

    (*We may define a transition relation with the same type as required by the constraint automaton's definition *)
    Definition transitionPA (s: (state * state)) :=
      recoverResultingStatesPA s (buildTransitionsSetProductAutomaton a1 a2).

    Definition buildPA := ConstraintAutomata.CA 
      (resultingStatesSet a1 a2) (resultingNameSet a1 a2) (transitionPA) (resultingInitialStatesSet a1 a2). 
      (*{|
      ConstraintAutomata.Q := (resultingStatesSet a1 a2);
      ConstraintAutomata.N :=  (resultingNameSet a1 a2);
      ConstraintAutomata.T :=  transitionPA; (* o tipo esperado da transição de um CA é um set resultante 
                                                ou seja, será necessário recuperar um conjunto de estados ao invés de um single
                                                state na função resultante (ou melhor, na forma de armazenar as transições. Talvez usar
                                                a abordagem de considerar um estado como sendo o próprio set state resolva.)*)
      ConstraintAutomata.Q0 := (resultingInitialStatesSet a1 a2)
    |}.
    ERICK: necessário testes. TODO bolar um exemplo maneiro para testar isso aqui (ou um bem basiquinho) *)

  End ProductAutomata.
End ProductAutomata.

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
    | 1 =>  3#1
    | 2 =>  5#1
    | 3 =>  7#1
    | 4 =>  9#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1 
    end.

  Definition timeStampTest2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  2#1 (*1#1*)
    | 1 =>  4#1
    | 2 => 6#1
    | 3 => 8#1
    | 4 => 10#1
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
  Definition oneBoundedFIFOrel (s:states) 
  (*set (set (ports) * ConstraintAutomata.DC ports (option nat) * set states)*) :=
    match s with
    | q0 => [([A], (ConstraintAutomata.dc A (Some 0)), [p0]) ;
             ([A], (ConstraintAutomata.dc A (Some 1)), [p1])]
    | p0 => [([B], (ConstraintAutomata.dc B (Some 0)), [q0])]
    | p1 => [([B], (ConstraintAutomata.dc B (Some 1)), [q0])] 
    end.

    Check oneBoundedFIFOrel.

  (* falta definir transição para começar a brncar com a run.                                      *)
  Definition oneBoundedFIFOCA:= {|
    ConstraintAutomata.Q := [q0;p0;p1];
    ConstraintAutomata.N := [A;B];
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

  Eval compute in ConstraintAutomata.step oneBoundedFIFOCA [p0] 0 10 [portA;portB].

  Definition x := Eval compute in ConstraintAutomata.portsDerivative ([A]) ([portA;portB]).
  Definition videos := Eval compute in ConstraintAutomata.portsDerivative ([A]) (x).


  (* TODO: thetaDelta aparenta estar ok. A porta de entrada é parametrizada. O problema parece ser na definição de DC
   estar fixa em uma porta (a inicial, sem atualização de index (cálculo de derivada)                                 *)
  Eval compute in ConstraintAutomata.thetaDelta oneBoundedFIFOCA 2 20 videos.
  Print videos.

  Eval compute in ConstraintAutomata.thetaDelta oneBoundedFIFOCA 0 20 [portA;portB].

  Eval compute in ConstraintAutomata.step oneBoundedFIFOCA (ConstraintAutomata.Q0 oneBoundedFIFOCA) 0 20  (* --> PEGUEI O FDP *)
  [portA;portB].

  Eval compute in ConstraintAutomata.run oneBoundedFIFOCA [portA;portB] 5 20.
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

  Definition syncCaBehavior (s: syncState) 
  (*set (set (syncPorts) * bool * set syncState)*) :=
    match s with
    | X => [([E;F] , (ConstraintAutomata.orDc (ConstraintAutomata.andDc (ConstraintAutomata.dc (E) (Some 0)) 
                                                ((ConstraintAutomata.dc (F) (Some 0))))

                          (ConstraintAutomata.andDc (ConstraintAutomata.dc (E) (Some 1)) 
                                                ((ConstraintAutomata.dc (F) (Some 1)))
                            )
                        ), [X])] 
    end.

  Definition syncCA := {|
    ConstraintAutomata.Q := [X];
    ConstraintAutomata.N := [E;F];
    ConstraintAutomata.T := syncCaBehavior;
    ConstraintAutomata.Q0 := [X]
  |}.

 (* Eval compute in syncCaBehavior X.
 Eval compute in ConstraintAutomata.retrievePortsFromThetaN 3 10 [portE;portF].
 Eval compute in ConstraintAutomata.stepa syncCA [X] 4 10 [portE;portF] [E;F]. *)

 Definition teste0 := Eval compute in ConstraintAutomata.step syncCA (ConstraintAutomata.Q0 syncCA) 0 20 [portE;portF].
  (*Eval compute in ConstraintAutomata.step syncCA 
    (ConstraintAutomata.Q0 syncCA) 1 20 (ConstraintAutomata.portsDerivative 
    (fst(ConstraintAutomata.step syncCA (ConstraintAutomata.Q0 syncCA) 0 20 [portE;portF])) ([portE;portF])).
    (* peguei o erro: porta pra caralho bugando aqui. Usar set_add. 
       --> usar set_add é suicídio.*) *)
  Eval compute in (fst(ConstraintAutomata.step syncCA (ConstraintAutomata.Q0 syncCA) 0 20 [portE;portF])).

  (*flat_map(derivativePortInvolved(fst((step ca acc a l input)))) input*)

  Eval compute in flat_map (ConstraintAutomata.derivativePortInvolved
    (fst(ConstraintAutomata.step syncCA (ConstraintAutomata.Q0 syncCA) 0 20 [portE;portF]))) ([portE;portF]).

    Eval compute in ConstraintAutomata.step syncCA 
    (ConstraintAutomata.Q0 syncCA) 1 20 (flat_map (ConstraintAutomata.derivativePortInvolved
    (fst(ConstraintAutomata.step syncCA (ConstraintAutomata.Q0 syncCA) 0 20 [portE;portF]))) ([portE;portF])).

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

  Definition anotherCABehaves (s:states2) :
    set (set (ports2) * ConstraintAutomata.DC ports2 nat  * set states2)  :=
    match s with
    | qa => [([A0], (ConstraintAutomata.tDc ports2 nat), [qa]) ;
             ([A0], (ConstraintAutomata.tDc ports2 nat), [qb])]
    | qb => [([A0;B0] , (ConstraintAutomata.orDc (ConstraintAutomata.andDc (ConstraintAutomata.dc (A0) (Some 0)) 
                                                ((ConstraintAutomata.dc (B0) (Some 0))))

                          (ConstraintAutomata.andDc (ConstraintAutomata.dc (A0) (Some 1)) 
                                                ((ConstraintAutomata.dc (B0) (Some 1)))
                            )
                        ), [qb])] 
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

  Eval compute in anotherCABehaves qb.

  Eval compute in ConstraintAutomata.step' anotherCA 3 20 [portA0;portB0] [A0;B0] (ConstraintAutomata.T anotherCA qb).

  (* step' (ca:constraintAutomata) (k l : nat) (input : set port) (ports: set name)
     (s: set(set name * bool * set(state))) *)
  Eval compute in ConstraintAutomata.stepa anotherCA [qa;qb] 1 10 [portA0;portB0] [A0;B0].

  Eval compute in ConstraintAutomata.step anotherCA ([qb]) 0 20 [portA0;portB0].

  (* Sem o cálculo de derivada não trava, mas ainda assim o resultado está incorreto. *)
  (* Erick : acho que não entendi como passar a entrada corretamente pro autômato, não pode ser *)
  (* ou a implementação de theta.time pode não estar correta. *)
  Eval compute in ConstraintAutomata.run anotherCA [portA0;portB0] 21 20.


