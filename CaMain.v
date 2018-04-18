Require Import ListSet.
Require Import List.
Require Import Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import QArith.
Require Import Coq.Numbers.BinNums.


Close Scope Q_scope.

Obligation Tactic := unfold complement, equiv ; program_simpl.

(*olhar QArith, biblioteca Coq com números racionais. https://coq.inria.fr/stdlib/Coq.ZArith.Znat.html#*)
(* a time stamp agora é definida como uma função do tipo nat -> Q, Q o conjunto dos números racionais.*)
Set implicit arguments.
Set Maximal Implicit Insertion.


Import ListNotations.
(* We define a function that computes the powerset of a set *)
Fixpoint powerset {A} (l:set A) : set (set A) :=
match l with
  | [] => [[]]
  | a::t => concat (map (fun f => [a::f;f]) (powerset t))
end.

Program Instance option_eqdec A `(EqDec A eq) : EqDec (option A) eq :=
{
  equiv_dec x y :=
    match x, y with
      | Some a, Some b => if a == b then in_left else in_right
      | None, None => in_left
      | Some _, None | None, Some _ => in_right
    end
 }.
 Eval compute in Z.of_N (3).
Module ConstraintAutomata.
  Section ConstraintAutomata.

    Variables state name data: Type.
    Variable dataset : set data.
    (*Open Scope Q_scope.*)
    (* Record timeStream := {
       timeStamp : nat -> QArith_base.Q;
       timeStampSound : forall k, timeStamp(k) < timeStamp(k+1)
    }. *)


    Variable setTimeStream : set (nat -> QArith_base.Q).
    Context `{EqDec name eq} `{EqDec state eq} (*`{EqDec data eq} será necessária p/ satisfazer a DC.*).

    Notation " a <? b " := (Qle_bool a b).
    Notation "a =? b" := (Qeq_bool a b).
    (* We define a port as a record containing its identifier and the data it contains *)
    (* ver o que mk<nome_do_record> efetivamente faz*)
    Record port: Type := mkport{
      id : name;
      (* nat -> data will fit better, being usable in checking whether at some time n the port *)
      (* can have a data item x                                                                      *)
      (* maybe option data to totalize:None, if there is no data defined for a given k               *)
      (* Some x, for x in data                                                                       *)
      dataAssignment : nat -> option data; 
      timeStamp : nat -> QArith_base.Q (* nat -> real *);
      (* We need to assure that timeStamp is always crescent:                                        *)
      portCond : forall n:nat, Qle (timeStamp n) (timeStamp (S n)) 
      (* True não pode ser fornecido assim (nem se colocar um \/ True no fim). A solução pode ser pa-*)
      (* ssar o tipo de portCond para Prop. Porém o usuário vai poder provar qualquer coisa se isso  *)
      (* for feito.                                                                                  *)


      (* The above field is useful to ensure the correctness of the modelled worlds (in terms of the *)
      (* time in which a data item is observed in a given port. If the user does not want to prove   *)
      (* that, it is only needed to supply "True" as the argument.                                   *)
    }.

    (* TDS^names can be seen as a set of ports as defined above.. *)
    (* In order to totalize the functions, we opted to use option type for both data and the time when  *)
    (* the data happens in a port. This lets the user to define a instant that there will be no data in *)
    (* a given port A_i                                                                                 *)

    (* the inductive type that follows defines all possible data constraints for a given Constraint *)
    (* automaton. It uses a Boolean as parameter instead of Prop                                    *)
    (* porta: tipo indutivo que carrega um id (que seria um outro tipo indutivo dado por name) e uma função
    ( de tipo nat -> data *)
    (* TODO rever a modelagem de uma Data Constraint *)
    Inductive DC :=
    | g  : bool -> DC.

    Record constraintAutomata := CA {
      Q : set state;
      N : set port; (* ou set name?*)
      T : state -> set port -> DC -> state;
      (* A definição atual de T não vai dar certo se para um mesmo estado tivermos 2 definições diferentes
      (i.e., transições com diferentes conjuntos de portas ou uma diferente DC válidas simultaneamente.
      Uma solução é talvez modelá-la como modelado as transições de um NFA-epsilon no RGCoq.                *)
      (* Na verdade vai, agora que eu entendi que o teta.time(k) é quem regula. se tiver dois conjuntos     *)
      (* de portas em 2 transições diferentes mas ambas com dados em teta.time(k) então ambas as transições *)
      (* serão disparadas                                                                                   *)
      Q0 : set state;
    }.

    Fixpoint returnSmallerNumber (m:QArith_base.Q) (l:set QArith_base.Q) :=
      match l with
      | [] => m
      | a::t => if ((a <? m)) then 
                   returnSmallerNumber a t else returnSmallerNumber m t
      end.
    Open Scope Q_scope.
    Eval compute in returnSmallerNumber (9999#1) [222#1;31#2;4#5;5#100;69#69;8#8].

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
    - intros. unfold hasData in H1. destruct dataAssignment. exists d. reflexivity.
      inversion H1.
    - intros. unfold hasData. inversion H1. rewrite H2. reflexivity.
    Defined.

    (* mapAp is a function that given a natural number and a set of functions, returns the result *)
    (* of all functions within the set with the given natural number:                             *)
    Fixpoint mapAp (n:nat) (l:set (nat -> QArith_base.Q)) : set QArith_base.Q:=
      match l with
      | [] =>  []
      | f::t => f n :: mapAp n t
      end.

    Notation "x |> f" := (f x) (at level 69, only parsing).


    (*acima de 70000 explode o coq *)
    (*TODO é necessário verificar se teta.time(k) é maior que teta.time(k-1) p/ k = 1,2,... ? *)
    (*!!!! *)
    Definition tetaTime (k:nat) := Eval vm_compute in returnSmallerNumber (9999#1) (mapAp k (setTimeStream)).


    (*Aqui vai entrar uma função que faz timeStamp a(l) =? tetaTime(k) para algum dado l \in 1..m*)
    (* timeStamp: function within ports which type is nat ->                                   *)
    (* the definition below is no longer needed.                                               *)
    (* Definition timeIsTeta (l:nat) (k:nat) (a:port) : bool := timeStamp a(l) =? tetaTime(k). *)
    Close Scope Q_scope.

    (* By algorithmic aspects, we define the following function as a function that implements the *)
    (* idea behind the calculus of theta.N(k) by imposing a upper bound to find the li value where*)
    (* ai(li) = theta.time(k)                                                                     *)
    Fixpoint timeStampEqThetaTime (k: nat) (l: nat) (a:port) :=
      match l with
      | 0 => if timeStamp a(0) =? tetaTime(k) then true else false
      | S n => if timeStamp a(S n) =? tetaTime(k) then true else timeStampEqThetaTime (k) (n) (a)
      end.

    (*The following definition returns the i-th natural number where timeStamp a(S n) = tetaTime(k).*)
    (* For it to work properly, one must supply a default return number greater than the specified  *)
    (* l number. Therefore, it returns 0<=i<=l if if timeStamp a(i) =? tetaTime(k) and default      *)
    (* otherwise                                                                                    *)
    (* TODO: definir se o default será fixo ou deixa para o usuário especificar o número que ele desejar? *)
     Fixpoint timeStampIndex (k:nat) (l:nat) (a:port) (default: nat) :=
      match l with
      | 0 => if timeStamp a(0) =? tetaTime(k) then 0 else default
      | S n => if timeStamp a(S n) =? tetaTime(k) then S n else timeStampIndex(k) (n) (a) (default)
      end.
    (* Therefore it is possible to define tetaN: *)
    Fixpoint tetaN (k:nat) (l:nat) (s:set port) : set name := 
      match s with
      | a::t => match hasData a(k) with
                | true => if (timeStampEqThetaTime k l a) then
                             id a :: tetaN k l t
                          else tetaN k l t
                | false => tetaN k l t
                end
      | []   => []
      end.

    (* É possível retirar o dado de option caso necessário                                          *)
    (* Returns tuples of ports, data and the time where a given data item is "seen" in a given port *)
    (* in the instant denoted by timeStamp k                                                        *)

    (* The following function retrieves all ports as tuples (name, data(k), timeStamp(k)) iff the port*)
    (* contains data at time teta.time(k), where teta.time(k) is the smallest time stamp obtained     *)
    (* by merging all time stamps with a given natural number "k"                                     *)
    (* the two following function implements tetaDelta.                                               *)
    (* TODO definir uma função igual a timeStampEqThetaTime que retorna o indice li tal que           *)
    (* timeStamp a(S n) =? tetaTime(k)  FEITO: timeStampIndex                                         *)
    (* do jeito que tá portsWithData tá bugado. *)
    Fixpoint portsWithData (k:nat) (l:nat) (s:set port) (default:nat) : set((name * option data) * QArith_base.Q) :=
      match s with
      | [] => []
      | a::t => match hasData(a) (k) with
                | true => if (timeStampEqThetaTime k l a) then
                           ((id a) , (dataAssignment a(timeStampIndex(k) (l) (a) (default))), (timeStamp a(k))) 
                           :: portsWithData k l t default
                         else portsWithData k l t default
                | false => portsWithData k l t default
                end
      end.

    (* rever definição de teta.time no artigo e reimplementar aqui *)
    (*CORRECTED acima eu acho 22/03/2018 (bugado as of 14/04/18, revisto em 15/04/18)   *)

    Definition tetaDelta (k : nat) (l:nat) (a: constraintAutomata) (default:nat) := portsWithData k l (N a) default.

    Close Scope Q_scope. 
    (* ao importar QArith o escopo tá em números racionais. Acho que haverá um overhead          *)
    (* de ter que ficar abrindo o escopo para type e Q_scope alternativamente (espero que apenas *)
    (* em tempo de implementação                                                                 *)

    (* Isso pode ser útil no futuro                                                          *)
    (* Given a port name and a set of ports retrieves a port with the ssame port name given. *)
    Fixpoint retrievePort (na:name) (s: set port) : option port :=
      match s with
      | [] => None
      | a::t => if (na == (id a)) then (Some a) else retrievePort na t
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

    (* Now it is possible to define a function that will check if for a given CA and a given set of TDS *)
    (* there is a tds record for all ports defined by the Constraint Automaton:                         *)
    Fixpoint TDSForAllPorts (s: set port) (ca: constraintAutomata) : bool :=
      match s with 
      | [] => true
      | a::t => if (portInSet (a) (ConstraintAutomata.N ca)) then TDSForAllPorts t ca else false
      end.
    (* TODO derivative, essa eu to quebrado.                                                            *)

  End ConstraintAutomata.
End ConstraintAutomata.

  (* Example  *) 

  Definition timeStampTest (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | S n =>  Z.of_N (N.of_nat(S n)) + 1#1
    end.

  Inductive states := pumba.
  Inductive ports := A | B.

  Program Instance portsEq : EqDec ports eq :=
    {equiv_dec x y := 
      match x,y with
      | A,A | B,B => in_left
      | A,B | B,A => in_right
      end }.

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
  + unfold timeStampTest.
  Admitted.

  Definition portA := {|
        ConstraintAutomata.id := A;
        ConstraintAutomata.dataAssignment := dataAssignmentA;
        ConstraintAutomata.timeStamp := timeStampTest;
        ConstraintAutomata.portCond := timeStampTestHolds |}.

  Definition portB := {|
        ConstraintAutomata.id := B;
        ConstraintAutomata.dataAssignment := dataAssignmentB;
        ConstraintAutomata.timeStamp := timeStampTest;
        ConstraintAutomata.portCond := timeStampTestHolds |}.

  (* a função abaixo está bugada                                                               *)
  (* Definition realPorts := [(ConstraintAutomata.mkport A dataAssignmentA timeStampTest)].    *)
  Definition realPorts := [portA;portB].

  (* A transition is defined as a subset of states x a set of record ports as defined by the   *)
  (* Record port in ConstraintAutomata, a data constraint which is represented by a bool (in   *)
  (* execution time it may always be satisfied, i.e., the data constraint needs to be true     *)
  (* in order to the transition to be triggered.                                               *)
  Definition LSCA (s:states) (st:set (ConstraintAutomata.port ports nat)) (g:ConstraintAutomata.DC) : states :=
    pumba.

  Check ConstraintAutomata.port.

  Check ConstraintAutomata.CA.

  (* falta definir transição para começar a brncar com a run.                                      *)
  (* Problema: set ports NÃO é igual a um set de records que efetivamente representam as ports. OK.*)
  Definition lossySynchronousChannel_CA := {|
    ConstraintAutomata.Q := [pumba];
    ConstraintAutomata.N := realPorts;
    ConstraintAutomata.T := LSCA;
    ConstraintAutomata.Q0 := [pumba]
  |}.

