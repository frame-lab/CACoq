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

    (* the inductive type that follows defines all possible data constraints for a given Constraint *)
    (* automaton. It uses a Boolean as parameter instead of Prop                                    *)
    (* porta: tipo indutivo que carrega um id (que seria um outro tipo indutivo dado por name) e uma função
    ( de tipo nat -> data *)
    (* TODO rever a modelagem de uma Data Constraint *)
    (* não faz muito sentido usar a formalização abaixo. é melhor usar um boolean diretamente... *)
    (*Inductive DC :=
    | g  : bool -> DC. *)

    Record constraintAutomata : Type := CA {
      Q : set state;
      N : set port; 
      T : state -> nat -> nat -> set (set (name) * bool * set(state)); (* ERICK -> set(state) por causa do comportamento não determinístico do CA. *)
                                                                       (* Also, set (set name)) * ... p/ permitir a verificação correta da porta na*)
                                                                       (* na transição em questão.                                                 *)
      Q0 : set state;
    }.

    Fixpoint returnSmallerNumber (m:QArith_base.Q) (l:set QArith_base.Q) :=
      match l with
      | [] => m
      | a::t => if ((a <? m)) then 
                   returnSmallerNumber a t else returnSmallerNumber m t
      end.
    Open Scope Q_scope.
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

   Fixpoint getTimestampFromPorts (l : set port) : set (nat -> QArith_base.Q) :=
     match l with
     | [] => []
     | a::t => (timeStamp a)::getTimestampFromPorts t
     end.

    Notation "x |> f" := (f x) (at level 69, only parsing).

    (* We can define thetaTime as a function that a given natural k, returns the smaller number from a set of *)
    (* rational numbers obtained by applying f to k.                                                          *)
    (* ERICK: theta.time(k) é calculado na entrada, e não no conjunto de portas do autômato...                *)
    (* s: TDS         de entrada do autômato                                                                  *)
    Definition thetaTime (s:set port) (k:nat)  := 
       Eval vm_compute in returnSmallerNumber (99999#1) (mapAp k ((s) |> getTimestampFromPorts)).


    (*Aqui vai entrar uma função que faz timeStamp a(l) =? thetaTime(k) para algum dado l \in 1..m*)

    Close Scope Q_scope.

    (* By algorithmic aspects, we define the following function as a function that implements the *)
    (* idea behind the calculus of theta.N(k) by imposing a upper bound to find the li value where*)
    (* ai(li) = theta.time(k)                                                                     *)
    Fixpoint timeStampEqThetaTime (ca:set port) (k: nat) (l: nat) (a:port) :=
      (*if timeStamp a(l) =? thetaTime (ca) (k) then true else false.
      ERICK: isso aqui está incorreto. Eu interpretei errado a definição no artigo. (ou seria o de cima errado?) *)
      match l with
      | 0 => if timeStamp a(0) =? thetaTime (ca) (k) then true else false
      | S n => if timeStamp a(S n) =? thetaTime (ca)(k) then true else timeStampEqThetaTime (ca) (k) (n) (a)
      end.

     (*Lemma timeStampEqThetaTimeSound : forall ca, forall k l, forall a,
       timeStampEqThetaTime ca k l a = true <-> timeStamp a(l) =? thetaTime (ca) (k) = true.
     Proof.
     intros.
     split.
     - destruct l.
     + simpl; intros. unfold timeStampEqThetaTime in H2. inversion H2. destruct Qeq_bool.
     reflexivity. inversion H2.
     + intros. unfold timeStampEqThetaTime in H2. inversion H2. destruct Qeq_bool. reflexivity. inversion H2.
     - intros. unfold timeStampEqThetaTime. destruct Qeq_bool. reflexivity. inversion H2.
     Qed. *)
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
      | 0 => if timeStamp a(0) =? thetaTime (ca) (k) then 0 else 0
      | S n => if timeStamp a(S n) =? thetaTime (ca) (k) then S n else timeStampIndex (ca) (k) (n) (a) 
      end.
    (* Definition timeStampIndex (ca:set port) (k:nat) (l:nat) (a:port) :=
      if timeStamp a(l) =? thetaTime ca k then l else 0. *)


    Check timeStampIndex.
    (* Therefore it is possible to define tetaN: l has the same meaning as in timeStampEqThetaTime       *)
    (* ERICK: é necessário passar duas instâncias da TDS de entrada, uma é usada para calcular thetaTime *)
    (* e a outra para montar o thetaN                                                                    *)
    Fixpoint thetaN (ca: set port) (k:nat) (l:nat) (s:set port) : set name := 
      match s with
      | a::t => match hasData a(k) with
                | true => if (timeStampEqThetaTime ca k l a) then
                             id a :: thetaN ca k l t
                          else thetaN ca k l t
                | false => thetaN ca k l t
                end
      | []   => []
      end.

    (* Returns tuples of ports, data and the time where a given data item is "seen" in a given port *)
    (* in the instant denoted by timeStamp k                                                        *)

    (* The following function retrieves all ports as tuples (name, data(k), timeStamp(k)) iff the port*)
    (* contains data at time teta.time(k), where teta.time(k) is the smallest time stamp obtained     *)
    (* by merging all time stamps with a given natural number "k"                                     *)
    (* the two following function implements tetaDelta.                                               *)
    (* TODO definir uma função igual a timeStampEqThetaTime que retorna o indice li tal que           *)
    (* timeStamp a(S n) =? thetaTime(k)  FEITO: timeStampIndex                                        *)
   

    Fixpoint portsWithData (ca:set port) (k:nat) (l:nat) (s:set port) : set((name * option data) ) :=
      match s with
      | [] => []
      | a::t => match hasData(a) (k) with
                | true => if (timeStampEqThetaTime ca k l a) then
                            (*(dataAssignment a(timeStampIndex ca (k) (l) (a) (default)) corresponde à alpha_i(l_i))*)
                           ((id a) , (dataAssignment a(timeStampIndex ca (k) (l) (a) ))) 
                           :: portsWithData ca k l t
                         else portsWithData ca k l t 
                | false => portsWithData ca k l t
                end
      end.

    (* Above definition for a specific automaton                                                     *)
    Definition CAportsWithData (ca: constraintAutomata) (k l : nat) :=
      portsWithData (N ca) k l (ConstraintAutomata.N ca). 

    (* Idéia: salvar o índice de tetaDelta pra cada função. Porém falha ao lembrar que ele pode ser diferente pra *)
    (* cada dataStream em cada porta. Porém parece ser possível usar a ideia da função acima pra pegar o índice   *)
    (* exato para avaliar a porta na transição:                                                                   *)
    Fixpoint indexportsWithData (ca:set port) (k:nat) (l:nat) (s:set port) : set((name * nat) ) :=
      match s with
      | [] => []
      | a::t => match hasData(a) (k) with
                | true => if (timeStampEqThetaTime ca k l a) then
                           ((id a) , (timeStampIndex ca (k) (l) (a))) 
                           :: indexportsWithData ca k l t 
                         else indexportsWithData ca k l t
                | false => indexportsWithData ca k l t 
                end
      end.
    (* Enquanto eu escrevia isso eu tive uma ideia melhor até: "existsb" nat tal que a definição da dc na transição *)
    (* avaliada em k bata com o mesmo valor da porta em tetaDelta(k)                                                *)

    Definition tetaDelta (ca:constraintAutomata) (k : nat) (l:nat) (po: set port) := 
      portsWithData po k l po.
    Check tetaDelta.

    Close Scope Q_scope.
    (* ao importar QArith o escopo tá em números racionais. Acho que haverá um overhead          *)
    (* de ter que ficar abrindo o escopo para type e Q_scope alternativamente (espero que apenas *)
    (* em tempo de implementação                                                                 *)

    (* Isso pode ser útil no futuro                                                              *)
    (* Given a port name and a set of ports retrieves a port with the same port name given.      *)
    Fixpoint retrieveport (na:name) (s: set port) : option port :=
      match s with
      | [] => None
      | a::t => if (na == (id a)) then (Some a) else retrieveport na t
      end.


    (* Before starting a run in a CA, it is interesting to verify whether the given set of TDS given as *)
    (* input contains a TDS for each port defined in the CA:                                            *)
    (* We will define TDS slightly different as defined by the authors; instead of pairs of (alpha, a)  *)
    (* for each port in the automaton, we define as pairs (id,alpha,a) where id refers to the port this *)
    (* pair is meant to carry data for.                                                                 *)
    (* Therefore, the following function checks whether for a given port and a given set of ports, there*)
    (* is a TDS definition for the given port in the set:                                               *)
    Fixpoint portInSet (a:port) (c: set port) : bool :=
      match c with
      | [] => false
      | y::t => if (id a == id y) then true else portInSet a t
      end.

    (* Now it is possible to define a function that will check if for a given CA and a given TDS there  *)
    (* is a port record for all ports defined in the Constraint Automaton:                               *)
    (* TODO como a entrada é uma tds \in tds^names, a entrada é um conjunto de portas da mesma forma que*)
    (* são formalizadas portas do autômato.                                                             *)
    Fixpoint TDSForAllports (s: set port) (ca: constraintAutomata) : bool :=
      match s with 
      | [] => true
      | a::t => if (portInSet (a) (ConstraintAutomata.N ca)) then TDSForAllports t ca else false
      end.

    (* One can define a guard condition as either a value that port "A" should contain in theta.time(k) *)
    (* Obviamente essa modelagem abaixo pode sofrer alterações:                                         *)

    Fixpoint dataMatchesData (p:name) (d: option data) (s: set((name * option data))) :=
      match s with
      | [] => false
      | a::t => match fst(a) with
                | p => if d == snd(a) then true else dataMatchesData p d t
                end
      end.

    (* Now the above function may be called with its "nice" values: *)
    (* NOTA: em termos de desempenho não fora testada ainda! Testarei para o v0                         *)
     Definition isDCmatchedByThetaDelta (ca:constraintAutomata) (p:port) (d: option data) (s: set((name * option data))) 
     (k:nat) (l:nat) (s:set port) := 
       dataMatchesData (id p) d (portsWithData (s) (k) (l) (s)).

     Check isDCmatchedByThetaDelta.

    (* We model a function to update the record of a given port that is used in a transition; a way to  *)
    (* model the derivative of a atream:                                                                *)
    Definition derivative (p: port) := mkport (id p) (dataAssignment p) (timeStamp p)
        (portCond p) (S (index p)).

    Check derivative.

    (* ERICK : o comportamento de DC deve ser modificado para receber um name e um set port (a tds de entrada)
    a fim de comparar se no index da porta na input referente ao name dado como parâmetro, a data constraint vale *)
    Definition DC (p:port) (k:nat) (d : option data) : bool :=
       if (dataAssignment p(k) == d) then true else false.
    (* DC apenas define que pra um determinado índice k, o valor na porta será igual ao dado ou não     *) 

    (* We can start thinking about formalizing a run in such formalism:                                 *)
    (* The run can start in any q0 \in Q0. Hence, we must define a function that first runs starting    *)
    (* a state so it is possible to define a procedure that starts the run in all states recursively    *)

    (* The following two definitions extracts the index where the port contains data in theta.time(k) *)
    Fixpoint dataFromPortInThetaTime (na:name) (se: set(name * nat)) (k l : nat) :=
      match se with
      | [] => 0
      | a::t => if na == fst(a) then snd(a) else dataFromPortInThetaTime na t k l 
      end.
    (* returns the l_i index where the port given by na contains data, with a(l_i) = theta.time(k) *)
    Definition dataFromThetaDelta (na: name) (s:set port) (k l : nat) :=
      dataFromPortInThetaTime na (indexportsWithData (s) (k) (l) (s) ) k l.

    (* Checks for a set of port if the data in it in index l_i such that a(l_i) = theta.time(k) is *)
    (* different from None, meaning that there is data in the port in such instant                 *)
    Fixpoint allPortsHaveData (st: set port) (k l :nat) (s:set port) :=
      match st with
      | [] => true
      | a::t => if (dataAssignment(a)(dataFromThetaDelta (id a) s  k l)) <> None then 
                allPortsHaveData t k l s else false
      end.

    (* Now we can define a single step: *)
    (*Definition step' (*st:state*) (k l default: nat) 
     (* ERICK: uma única transição como parâmetro (aqui é definido uma single step), representada por s *)
     (* Retorna os estados acessíveis por essa transição caso os critérios de disparo sejam atingidos.  *)
     (s: (set(ConstraintAutomata.port) * bool * set(state))) := 
        if (allPortsHaveData (fst(fst(s))) k l default (fst(fst(s)))) && (snd(fst(s))) then snd(s) else [].*)
     (* ERICK: vale notar que aqui, todas as portas usadas nesta "step" devem ser atualizadas na TDS de   *) 
     (* entrada. Ou seja, uma nova TDS tem que ser criada com a derivada das streams aqui usadas.         *)
    (* We define a step based on if a given transition can be triggered, i.e., its guard is satisfied and *)
    (* its ports contains data in theta.time(k)                                                           *)

    Fixpoint derivativePortInvolved (s:set name) (a: port) :=
      match s with
      | [] => []
      | x::t => if x == id a then derivative(a)::derivativePortInvolved t a
                else derivativePortInvolved t a
      end.

    (* NEW then we have a way to calculate the derivatives from all ports in the input involved with the actual step *)
    Fixpoint allDerivativesFromPortsInvolved(names: set name) (ports:set port) : set port :=
      match ports with
      | [] => []
      | a::t => derivativePortInvolved names a ++ allDerivativesFromPortsInvolved names t
      end.
    Check allDerivativesFromPortsInvolved.

   (* The following function may calculate the derivative of ports involved in a given transition *)
    Definition portsDerivative (names: set name) (input: set port) := 
      allDerivativesFromPortsInvolved names input.

    (* We also need to check if the ports involved in a transition are the only ones with data so it can fire *)

    Fixpoint portsOutsideTransition (input: port) (transition : set name) :=
      match transition with
       | [] => true
       | a::t => if (id input <> a) then portsOutsideTransition input t else false
      end.

    Fixpoint retrievePortsOutsideTransition (input: set port) (transition : set name) :=
      match input with
      | [] => []
      | a::x => if portsOutsideTransition a transition then a::retrievePortsOutsideTransition x transition
                else retrievePortsOutsideTransition x transition
      end.

    Fixpoint hasDataInThetaDelta (p: port) (thetadelta: set (name * option data)) :=
      match thetadelta with
      | [] => false
      | a::t => if ((id p ==(fst(a)))) then
                    if snd(a) <> None then true 
                    else hasDataInThetaDelta (p) (t)
                else hasDataInThetaDelta p t
      end.

    Fixpoint checkPorts (t:set port) (thetadelta: set (name * option data)) :=
      match t with
      | [] => true
      | a::x => if negb (hasDataInThetaDelta a thetadelta) then checkPorts x thetadelta
                else false
      end.

    Definition onlyPortsInvolvedContainsData (ca:constraintAutomata) (ports : set name) 
      (k l : nat) (input : set port) :=
      checkPorts (retrievePortsOutsideTransition (input) ports) (tetaDelta (ca) (k) (l) (input)).


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
     | a::t => if (set_eq (ports) ((fst(fst(a))))) && 
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
      istep' ca k l input (T ca s k l) ports.
    Check stepAux.

    (* We apply the step to every state in the given configuration:                     *)
    Definition stepa (ca:constraintAutomata) (s: set state) (k l : nat) (input:set port) (ports: set name):=
     (ports, flat_map (stepAux ca k l input ports) s).

    Check stepa.

    Definition step (ca:constraintAutomata) (s: set state) (k l : nat) (input:set port) :=
      stepa ca s k l input (retrievePortsFromThetaN k l input).

   (* We define run' as a function that iterates over a list of naturals. v0                                *)
   (* ERICK: note que a noção de run' é diferente do trace de execução do autômato *)
    Definition runa' (ca:constraintAutomata) (*s:state*)  : 
      set port -> list nat -> nat -> set state -> set state :=
      (* k : índice de execução               *)
      (* l : profundidade da busca            *)
      fix rec input k l acc :=
        match k with 
          | [] => acc
          | a::t => snd (step ca acc a l input)
                 (*++*)|> rec (portsDerivative(fst((step ca acc a l input))) input) t  l (*(snd (step ca acc a l input))*)
        end. 

    Definition run' (ca:constraintAutomata) (*s:state*)  : 
      set port -> list nat -> nat -> set state -> set (set state) -> set (set state) :=
      (* k : índice de execução               *)
      (* l : profundidade da busca            *)
      fix rec input k l acc resp :=
        match k with 
          | [] => resp
          | a::t => resp ++ [snd (step ca acc a l input)]
                 (*++*)|> rec (portsDerivative(fst((step ca acc a l input))) input) t  l (snd (step ca acc a l input))
        end.
    (* In order to use run' as defined above, we define a function that given a natural number n, it creates an ordered *)
    (* list containing naturals that ranges from 0 to n                                                 *)
    Program Fixpoint count_into_list (n:nat) :=
      match n with
      | 0 => 0::nil
      | S n => count_into_list n ++ [S n]
      end.

    (* A run está bugada. Eu devo rever isto aqui. *)
    Definition run (ca:constraintAutomata) (input: set port) (k l : nat) :=
      run' ca input (count_into_list k) l (Q0 ca) [].

   (* Um passo de um estado para outro *)
   (* Definition step (ca:constraintAutomata) (s:state) (k l default : nat) (input:set port) :=
      applyEligibleStep (step'' ca k l default input (T ca s k l)).
    (* No momento de uma "single step", a TDS de entrada (obviamente) também deve ser levada *)
    (* em conta, além das transições acessíveis a partir de um estado. *)
    (* Definition step (ca: constraintAutomata) (s:state)(input: set port) (k l default: nat)  :=
      (step' ca k l default) input (T ca s k l). Check step. *) 

    (* We define a function that updates the ports used in a transition in the input: *)
    Fixpoint calculateADerivative (po: name) (input: set port) :=
      match input with
      | [] => []
      | a::t => if (po == id a) then derivative a::calculateADerivative po t else calculateADerivative po t
      end.

    Fixpoint calculateDerivative (ports:set name) (input: set port) :=
      match ports with
      | [] => []
      | a::t => calculateADerivative a input::calculateDerivative t input
      end.

    (* Me parece possível definir uma run que faça em momentos diferentes a run e o applyEligibleStep *)
    (* A ideia aqui é a cada iteração é rodar step'', pegar as portas pra calcular a derivada 
      na input e aplicar o eligibleStep e fazer isso recursivamente até que k atinja l *)
    (* l: nº de iterações *)
    (* run' será chamada com os parâmetros do autômato. *)
    Fixpoint run' (k l default: nat) (input: set port) (s: set(set name * bool * set(state))):=
    (* ERICK: aparentemente k é o nosso iterador, sendo que ele mesmo pode ser o número de iterações        *)
    (* A princípio o 0 ainda é usado. Porém a partir do momento que ele passar a ser o "default", isso terá *)
    (* que ser modificado                                                                                   *)
      match k with
      | 0 => step'' 0 l input
      
     (* ERICK: aqui vai ser necessário atualizar a entrada que se dá para run' (a TDS) tal como é feito*)
     (* na parse' da gramática *)
     (*ERICK: TODO 
    Fixpoint run' (step: state -> (set(ConstraintAutomata.port) * bool * set(state))) 
    (input: set port)  (k l default:nat) :=
      match k with
      | 0 => 
      *)
    (* k : índice da busca *)
    (* l : limite da busca *)
    (* default (sumirá em breve) : valor de retorno padrão p funções theta.time e etc. *)
   (* ERICK: note que definimos tanto a entrada quanto as portas do CA do tipo Port: Nesse caso, para *)
   (* a TDS de entrada do autômato deverá ser definida uma porta para cada porta definida no autômato.*)
   (* Seguindo a definição de transição como pautada na última reunião, o default deve ser também     *)
   (* junto da definição.    *)                                                         *)
  End ConstraintAutomata.
End ConstraintAutomata.

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
    (* | 1 => None *)
    | S n => Some (1)
    end.

  Definition dataAssignmentB n :=
    match n with
    | 0 => Some 0
    | S n => Some (1)
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

  Check ConstraintAutomata.isDCmatchedByThetaDelta.

  Check option_eqdec.
  (* ERICK: esse k abaixo é justamente o índice l_i tal que a(l_i) = teta.time(k), para algum l_i \in [0,1,...]*)
  (* NOTA: k abaixo náo é dado como parâmetro, é o índice da porta a ser avaliado. *)
  Definition oneBoundedFIFOrel (s:states) (k:nat) (l:nat) : 
  set (set (ports) * bool * set states) :=
    match s with
    | q0 => [([A], (ConstraintAutomata.DC(portA) (k) (Some 0)), [p0]) ;
             ([A], (ConstraintAutomata.DC(portA) (k) (Some 1)), [p1])]
    | p0 => [([B], (ConstraintAutomata.DC(portB) (k) (Some 0)), [q0])]
    | p1 => [([B], (ConstraintAutomata.DC(portB) (k) (Some 1)), [q0])]
    end.


  (* falta definir transição para começar a brncar com a run.                                      *)
  Definition oneBoundedFIFOCA:= {|
    ConstraintAutomata.Q := [q0;p0;p1];
    ConstraintAutomata.N := realports; (*TODO : ports -> Names  *)
    ConstraintAutomata.T := oneBoundedFIFOrel;
    ConstraintAutomata.Q0 := [q0]
  |}.

  Eval compute in ConstraintAutomata.tetaDelta oneBoundedFIFOCA 0 0 [portA;portB].

  Eval compute in ConstraintAutomata.retrievePortsFromThetaN  0 0 [portA;portB].
  (*onlyPortsInvolvedContainsData (ca:constraintAutomata) (ports : set name) 
      (k l default : nat) (input : set port)
    Definition tetaDelta (ca:constraintAutomata) (k : nat) (l:nat) (po: set port) (default:nat) := 
      portsWithData po k l po default.*)
  Eval compute in ConstraintAutomata.onlyPortsInvolvedContainsData (oneBoundedFIFOCA) [A] 
      0 20 [portA;portB]. 

  Eval compute in ConstraintAutomata.step oneBoundedFIFOCA [q0] 0 0 [portA;portB].
  (* (ca:constraintAutomata) (s: state) (k l default: nat) (input:set port) *)

  Eval compute in ConstraintAutomata.run oneBoundedFIFOCA [portA;portB] 10 20.
  (* Eval compute in ConstraintAutomata.run' oneBoundedFIFOCA [portA;portB] [0;1;2;3;4;5;6;7;8;9;10] 
  20 (ConstraintAutomata.Q oneBoundedFIFOCA). *)

Fixpoint count_into_list (n:nat) :=
  match n with
  | 0 => 0::nil
  | S n => count_into_list n ++ [S n]
  end.
Fixpoint rev_fat (n:nat) :=
  match n with
  | 0 => 1
  | S n => rev_fat n * S n
  end.
Theorem rev_fat_5 : rev_fat 5 = 120.
Proof. auto. Qed.
Eval compute in count_into_list 5. (* Já temos algo parecido com o iterator tabajara *)

