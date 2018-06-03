Require Import ListSet.
Require Import List.
Require Import Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import QArith.
Require Import Coq.Numbers.BinNums.

(* Keywords: ERICK, TODO *)

Close Scope Q_scope.

Obligation Tactic := unfold complement, equiv ; program_simpl.

(*Q_scope is the scope of Rational Numbers as in https://coq.inria.fr/stdlib/Coq.ZArith.Znat.html *)

Set Implicit Arguments.
Set Maximal Implicit Insertion.


Import ListNotations.
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

      (* The above field is useful to ensure the correctness of the modelled worlds (in terms of the *)
      (* time in which a data item is observed in a given port. If the user does not want to prove   *)
      (* that, it is only needed to supply an axiom of the same type as the proof as the argument.   *)
      (* This obliges the user to supply a proof of the same type as portCond, but if they rather not*)
      (* prove it, they can axiomixe it                                                              *)

      (* A idéia de limitar a "profundidade" das funções nat -> Q e nat -> Data  vai ser aplicada na run. *)
    }.
    Check dataAssignment.
(*   End ConstraintAutomata.
End ConstraintAutomata.
   Check ConstraintAutomata.dataAssignment *)
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
      T : state -> nat -> nat -> set (set (port) * bool * set(state)); (* ERICK -> set(state) por causa do comportamento não determinístico do CA. *)
      Q0 : set state;
    }.
    (* Worth notice that T represents the type of the functions that contains transitions. *)
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

    Fixpoint mapApp (n:nat) (l:set (port)) : set QArith_base.Q:=
      match l with
      | [] =>  []
      | f::t => (timeStamp f n) :: mapApp n t
      end. 
   (*TODO AQUI!!!!*)
   (*Added 18/05/2018 - setTimeStream bug *)
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
    (* timeStamp: function within ports which type is nat -> Q                                   *)
    (* the definition below is no longer needed.                                               *)
    (* Definition timeIsTeta (l:nat) (k:nat) (a:port) : bool := timeStamp a(l) =? thetaTime(k). *)
    Close Scope Q_scope.

    (* By algorithmic aspects, we define the following function as a function that implements the *)
    (* idea behind the calculus of theta.N(k) by imposing a upper bound to find the li value where*)
    (* ai(li) = theta.time(k)                                                                     *)
    (* TODO usando record variável, muitas das funções aqui devem ser revisitadas.                *)
     Fixpoint timeStampEqThetaTime (ca:set port) (k: nat) (l: nat) (a:port) :=
      match l with
      | 0 => if timeStamp a(0) =? thetaTime (ca) (k) then true else false
      | S n => if timeStamp a(S n) =? thetaTime (ca)(k) then true else timeStampEqThetaTime (ca) (k) (n) (a)
      end. 
    (*ERICK : timeStampEqThetaTime serve para encontrar se em algum l_i da timestamp bate com o theta(k) *)
    (* atual, vide a teoria em Arbab (2004)                                                              *) 


    (*The following definition returns the i-th natural number where timeStamp a(S n) = thetaTime(k).*)
    (* For it to work properly, one must supply a default return number greater than the specified  *)
    (* l number. Therefore, it returns 0<=i<=l if if timeStamp a(i) =? thetaTime(k) and default      *)
    (* otherwise                                                                                    *)
    (* TODO: definir se o default será fixo ou deixa para o usuário especificar o número que ele desejar? *)
     Fixpoint timeStampIndex (ca: set port)(*constraintAutomata)*) (k:nat) (l:nat) (a:port) (default: nat) :=
      match l with
      | 0 => if timeStamp a(0) =? thetaTime (ca) (k) then 0 else default
      | S n => if timeStamp a(S n) =? thetaTime (ca) (k) then S n else timeStampIndex (ca) (k) (n) (a) (default)
      end.
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
   

    (* TODO: talvez seja interessante nesse ponto extrair a porta ao invés do nome dela...            *)
    Fixpoint portsWithData (ca:set port) (k:nat) (l:nat) (s:set port) (default:nat) : set((name * option data) ) :=
      match s with
      | [] => []
      | a::t => match hasData(a) (k) with
                | true => if (timeStampEqThetaTime ca k l a) then
                            (*(dataAssignment a(timeStampIndex ca (k) (l) (a) (default)) corresponde à alpha_i(l_i))*)
                           ((id a) , (dataAssignment a(timeStampIndex ca (k) (l) (a) (default)))) 
                           :: portsWithData ca k l t default
                         else portsWithData ca k l t default
                | false => portsWithData ca k l t default
                end
      end.

    (* Above definition for a specific automaton                                                     *)
    Definition CAportsWithData (ca: constraintAutomata) (k l default: nat) :=
      portsWithData (N ca) k l (ConstraintAutomata.N ca) default. 

    (* Idéia: salvar o índice de tetaDelta pra cada função. Porém falha ao lembrar que ele pode ser diferente pra *)
    (* cada dataStream em cada porta. Porém parece ser possível usar a ideia da função acima pra pegar o índice   *)
    (* exato para avaliar a porta na transição:                                                                   *)
    Fixpoint indexportsWithData (ca:set port) (k:nat) (l:nat) (s:set port) (default:nat) : set((name * nat) ) :=
      match s with
      | [] => []
      | a::t => match hasData(a) (k) with
                | true => if (timeStampEqThetaTime ca k l a) then
                           ((id a) , (timeStampIndex ca (k) (l) (a) (default))) 
                           :: indexportsWithData ca k l t default
                         else indexportsWithData ca k l t default
                | false => indexportsWithData ca k l t default
                end
      end.
    (* Enquanto eu escrevia isso eu tive uma ideia melhor até: "existsb" nat tal que a definição da dc na transição *)
    (* avaliada em k bata com o mesmo valor da porta em tetaDelta(k)                                                *)

    (* Definition forceIndex (ca:constraintAutomata) (k:nat) (l:nat) (default:nat) (ca: constraintAutomata) := 
      Eval vm_compute in indexportsWithData ca k l (ConstraintAutomata.N (ca)) default. *)

    Definition tetaDelta (ca:constraintAutomata) (k : nat) (l:nat) (po: set port) (default:nat) := 
      portsWithData po k l po default.
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


    (* A procedure to inject N to Z is defined as  Z.to_N in the standard library: It takes as argument *)
    (* natural numbers defined in a binary way as seen in N that can be obtained from nat numbers by    *)
    (*  Z.to_N                                                                                          *)


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
     (k:nat) (l:nat) (s:set port) (default:nat) := 
       dataMatchesData (id p) d (portsWithData (s) (k) (l) (s) (default)).

     Check isDCmatchedByThetaDelta.

    (* We model a function to update the record of a given port that is used in a transition; a way to  *)
    (* model the derivative of a atream:                                                                *)
    Definition derivative (p: port) := mkport (id p) (dataAssignment p) (timeStamp p)
        (portCond p) (S (index p)).

    Check derivative.

    (* 19/05/2018: TODO alterações na definição de uma DC na transição: do jeito que estava, tinhamos um *)
    (* problema que na verdade era em tempo de definição já ver se a DC é satisfeita pela disposição de *)
    (* theta.delta. Procuro corrigir isso fazendo a função a seguir:                                    *)

    Definition DC (p:port) (k:nat) (d : option data) : bool :=
       if (dataAssignment p(k) == d) then true else false.
    (* DC apenas define que pra um determinado índice k, o valor na porta será igual ao dado ou não     *) 

    (* We can also define for when a value that port "A" must have the same value as port "B":          *)
    (* TODO Na verdade, acho que isso é capturado pela função acima.                                    *)


    (* We can start thinking about formalizing a run in such formalism:                                 *)
    (* The run can start in any q0 \in Q0. Hence, we must define a function that first runs starting    *)
    (* a state so it is possible to define a procedure that starts the run in all states recursively    *)

    (* A princípio, a ideia de uma entrada é um conjunto de tds e um número natural k que limitará a TDS*)
    (* em "profundidade".                                                                               *)
    (* primeiro uma run baseada em fixpoint: roda o caso base, caso seja "true", passa p k + 1. senão   *)
    (* retorna 0 ali mesmo.                                                                             *)

    (* We make use of Module iteration to build up the "run" function on a CA as seen in                *)
    (*  http://compcert.inria.fr/doc/html/Iteration.html                                                *)

    (* We have to consider that when a step is taken (a port is used in a transition, it have to be upda*)
    (* ted with a new index. Here we evaluate a single transition.                                      *)
    (* ERICK: ideia: verifica se uma transição (conjunto de portas e DC) são satisfeitas pelo theta.    *)
    (* delta. Caso sejam, atualizar a porta na stream de entrada (é isso?)  *)
    (* Definition step (s: state) (k:nat) (dc: (set (ConstraintAutomata.port) * bool * state)) :=
      match fst(dc) with
      | [] => []
      | a::t =>  *)

    (* The following definition returns true iff the set of names corresponds to the ports given :      *)
    (*Fixpoint nameInPorts (ports: set port) (na: name) :=
      match ports with
      | [] => false
      | a::t => if (id a) == na then true else nameInPorts t na
      end.
    (* Then we can check that given a set of names and a set of ports, the names corresponds to the ports.*)
    (* This will be useful to check which ports that contains data in thetaN so the transition can fire   *)
    Fixpoint namesEqualsPorts (ports: set port) (setNames: set name) :=
      match setNames with
      | [] => true
      | a::t => if negb (nameInPorts ports a) then false else namesEqualsPorts ports t
      end.  ERICK: não acho que seja mais necessário isso (27/05/2018) *)

    (* The following two definitions extracts the index where the port contains data in theta.time(k) *)
    Fixpoint dataFromPortInThetaTime (na:name) (se: set(name * nat)) (k l default: nat) :=
      match se with
      | [] => default
      | a::t => if na == fst(a) then snd(a) else dataFromPortInThetaTime na t k l default
      end.
    (* returns the l_i index where the port given by na contains data, with a(l_i) = theta.time(k) *)
    Definition dataFromThetaDelta (na: name) (s:set port) (k l default: nat) :=
      dataFromPortInThetaTime na (indexportsWithData (s) (k) (l) (s) (default)) k l default.

    (* Checks for a set of port if the data in it in index l_i such that a(l_i) = theta.time(k) is *)
    (* different from None, meaning that there is data in the port in such instant                 *)
    Fixpoint allPortsHaveData (st: set port) (k l default:nat) (s:set port) :=
      match st with
      | [] => true
      | a::t => if (dataAssignment(a)(dataFromThetaDelta (id a) s  k l default)) <> None then 
                allPortsHaveData t k l default s else false
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
    (*ERICK: Rever esse carinha aqui. Aqui tem que entrar também a tds teta de entrada (que é um set de
     ports). Creio que as portas nas transições são em cima das portas de entrada (duh), porém -> nesse
     caso não é tão simples quanto uma aplicação de delta em FA. ou é na verdade. *)
    Fixpoint step' (*st:state*) (k l default: nat) (input : set port)
     (s: set(set(ConstraintAutomata.port) * bool * set(state))) := 
      match s with
      | [] => []
      | a::t => if (allPortsHaveData (fst(fst(a))) k l default (input)) 
                && (snd(fst(a))) then snd(a)::(step' k l default input t) else (step' k l default input t)
      end.

    Check step'.
    Check T.
    (*ERICK: Aqui tá errado, eu defino uma step baseada nas transições do autômato *)
    (* No momento de uma "single step", a TDS de entrada (obviamente) também deve ser levada *)
    (* em conta, além das transições acessíveis a partir de um estado. *)
    Definition step (ca: constraintAutomata) (s:state)(input: set port) (k l default: nat)  :=
      (step' k l default) input (T ca s k l). Check step. 
     (* ERICK: aqui vai ser necessário atualizar a entrada que se dá para run' (a TDS) tal como é feito*)
     (* na parse' da gramática *)
     (*ERICK: TODO 
    Fixpoint run' (step: state -> (set(ConstraintAutomata.port) * bool * set(state))) 
    (input: set port)  (k l default:nat) :=
      match k with
      | 0 => 
      (* ideia: flat_map no conjunto de estados iniciais. *)*)


   (* ERICK: note que definimos tanto a entrada quanto as portas do CA do tipo Port: Nesse caso, para *)
   (* a TDS de entrada do autômato deverá ser definida uma porta para cada porta definida no autômato.*)
   (* Seguindo a definição de transição como pautada na última reunião, o default deve ser também     *)
   (* junto da definição.                                                                             *)
  End ConstraintAutomata.
End ConstraintAutomata.

Check ConstraintAutomata.timeStampEqThetaTime.
Check ConstraintAutomata.thetaTime.
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
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Definition timeStampTest2 (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  5#1
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
    | S n => Some (S n)
    end.

  Definition dataAssignmentB n :=
    match n with
    | 0 => None
    | S n => Some (S n)
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
  (* k é necessário aqui para a satisfabilidade das data constraints em teta.time(k), que é o que nos interesa. *)
  (* EDIT: mesmo após parametrizar as funções com um CA, continua dando o mesmo problema: 18/05/2018            *)
  (* O problema pode estar nessa definição de transição...                                                      *)
  (* Definition oneBoundedFIFOrel (s:states) (k:nat) (l:nat)
    : set (set (ConstraintAutomata.port ports nat) * bool * states) :=
    match s with
    (* TODO refatorar o uso dessa função pra que use diretamente o Automato sem ter que explicitar (ou não) *)
    | q0 => [([portA] , (ConstraintAutomata.isDCmatchedByThetaDelta (portA) (Some 0)),
             (ConstraintAutomata.portsWithData (k) (l) ([portA]) (69)) , p0) ; 
             ([portA] , (ConstraintAutomata.isDCmatchedByThetaDelta (portA) (Some 1)),
             (ConstraintAutomata.portsWithData (k) (l) ([portA]) (69)),  p1)] 
    | p1 => [([portB] , (ConstraintAutomata.isDCmatchedByThetaDelta ((portB)) (Some 1)),
             (ConstraintAutomata.portsWithData (k) (l) ([portB]) (69)) , q0)]
    | p0 => [([portB] , (ConstraintAutomata.isDCmatchedByThetaDelta states ports (option nat) portB (Some 0)),
             (ConstraintAutomata.portsWithData (k) (l) ([portB]) (69)) , q0)]
    | _ => []
    end.  *)

  Check ConstraintAutomata.DC.
  Check option_eqdec.
  (* ERICK: esse k abaixo é justamente o índice l_i tal que a(l_i) = teta.time(k), para algum l_i... *)
  Definition oneBoundedFIFOrel (s:states) (k:nat) (l:nat) : 
  set (set (ConstraintAutomata.port ports nat) * bool * set states) :=
    (* ERICK: ideia; definir o retorno da transição como set(states), uma vez que o comportamento *)
    (* da definição de constraint automata é não determinístico.                                  *)
    match s with
    | q0 => [([portA], (ConstraintAutomata.DC(portA) (k) (Some 0)), [q0]) ;
             ([portA], (ConstraintAutomata.DC(portA) (k) (Some 1)), [p1])]
    | p0 => [([portB], (ConstraintAutomata.DC(portB) (k) (Some 0)), [q0])]
    | p1 => [([portB], (ConstraintAutomata.DC(portB) (k) (Some 1)), [q0])]
    end.

  (* Definition isDCmatchedByThetaDelta (p:name) (d: option data) (s: set((name * option data))) 
     (k:nat) (l:nat) (s:set port) (default:nat) := 
       dataMatchesData p d (portsWithData(k) (l) (s) (default)).*)

  (* falta definir transição para começar a brncar com a run.                                      *)
  Definition oneBoundedFIFOCA:= {|
    ConstraintAutomata.Q := [q0;p0;p1];
    ConstraintAutomata.N := realports;
    ConstraintAutomata.T := oneBoundedFIFOrel;
    ConstraintAutomata.Q0 := [q0]
  |}.

  (* Assustadoramente, funciona *)
  Eval compute in ConstraintAutomata.thetaTime (ConstraintAutomata.N oneBoundedFIFOCA) 1.
  Eval compute in ConstraintAutomata.timeStamp portA 1.
  (* Nesta implementação a porta só é incluída em thetaN se conter algum dado em theta.time(k) *)
  Eval compute in ConstraintAutomata.thetaN (ConstraintAutomata.N oneBoundedFIFOCA) (2) (20) (ConstraintAutomata.N oneBoundedFIFOCA).
  Eval compute in ConstraintAutomata.portsWithData (ConstraintAutomata.N oneBoundedFIFOCA) (0) (20) (ConstraintAutomata.N oneBoundedFIFOCA) (200).
  (* Estrutura do CA *)
  (* Eval vm_compute in ConstraintAutomata.T (oneBoundedFIFOCA) p1 1 20. *)
  Eval compute in ConstraintAutomata.dataFromThetaDelta
      (A) [portA;portB] 0 0 200.
  (*  Definition dataFromThetaDelta (na: name) (s:set port) (k l default: nat) :=
      dataFromPortInThetaTime na (indexportsWithData (s) (k) (l) (s) (default)) k l default. *)
  (*ERICK : Step está bugada. *)
  Eval compute in ConstraintAutomata.step (oneBoundedFIFOCA) (q0) [portA;portB] 0 20 200.

