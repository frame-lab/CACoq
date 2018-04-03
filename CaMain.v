Require Import ListSet.
Require Import List.
Require Import Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import QArith.
Require Import Coq.Numbers.BinNums.

Close Scope Q_scope.

Obligation Tactic := unfold complement, equiv ; program_simpl.

(*olhar QArith, biblioteca Coq com números racionais. *)
(* a time stamp a agora é definida como uma função do tipo nat -> Q, Q o conjunto dos números racionais.*)
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
      (* dataAssignment can be a function nat -> data too, since record's fields are immutable.      *)
      (* maybe nat -> data will fit better, being usable in checking whether at some time n the port *)
      (* can have a data item x                                                                      *)
      (* maybe option data to totalize:None, if there is no data defined for a given k               *)
      (* Some x, for x in data                                                                       *)
      dataAssignment : nat -> option data; 
      timeStamp : nat -> QArith_base.Q (* nat -> real *);
      (* We need to assure that timeStamp is always crescent:                                        *)
      portCond : forall n:nat, Qle (timeStamp n) (timeStamp (S n))
      (* The above field is useful to ensure the correctness of the modelled worlds, but requires a  *)
      (* little overhead from the users                                                              *)
    }.

    Definition buildPort (i:name) (data : nat -> option data) (time: nat -> QArith_base.Q) 
        port_cond: port := {|
        id := i;
        dataAssignment := data;
        timeStamp := time ;
        portCond := port_cond
    |}.

    Notation "0" := 0 : nat_scope.
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
      T : state -> set port -> bool -> state;
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
      | Some _ => true
      | None => false
      end.

    (* caso necessário voltar para nat, basta trocar QArith_base.Q por nat *)

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


    (* Therefore it is possible to define tetaN: *)
    Fixpoint tetaN (k:nat) (s:set port) : set name := 
      match s with
      | a::t => match hasData a(k) with
                | true => if (timeStamp a(k) =? tetaTime(k)) then
                             id a :: tetaN k t
                          else tetaN k t
                | false => tetaN k t
                end
      | []   => []
      end.

    (*
    Fixpoint portsWithData (k:nat) (s:set port) : set(option data * QArith_base.Q) :=
      match s with
      | [] => []
      | a::t => match hasData(a) (k) with
                | true =>  (dataAssignment a k , timeStamp a(k)) :: portsWithData k t
                | false => portsWithData k t
                end
      end. *)
    (* É possível retirar o dado de option caso necessário                                          *)
    (* Returns tuples of ports, data and the time where a given data item is "seen" in a given port *)
    (* in the instant denoted by timeStamp k                                                        *)

    (* The following function retrieves all ports as tuples (name, data(k), timeStamp(k)) iff the port*)
    (* contains data at time teta.time(k), where teta.time(k) is the smallest time stamp obtained     *)
    (* by merging all time stamps with a given natural number "k"                                     *)
    Fixpoint portsWithData (k:nat) (s:set port) : set((name * option data) * QArith_base.Q) :=
      match s with
      | [] => []
      | a::t => match hasData(a) (k) with
                | true => if (timeStamp a(k) =? tetaTime(k)) then
                         ((id a) , (dataAssignment a(k)), (timeStamp a(k))) :: portsWithData k t
                         else portsWithData k t
                | false => portsWithData k t
                end
      end.

    (* rever definição de teta.time no artigo e reimplementar aqui *)
    (*CORRECTED acima eu acho 22/03/2018*)

    Definition tetaDelta (k : nat) (a: constraintAutomata) := portsWithData k (N a).

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

    (* We define a procedure that injects a natural number to Z: *)
    Fixpoint injection (n:nat) : Z :=
      match n with
      | 0 => 0%Z
      | S m => 1%Z + injection m
      end.

    (*Lemma injection_sound : forall n, injection n = 0%Z <-> n = 0.
    Proof.
    intros.
    split.
    - (*induction n. intros. reflexivity. intros. contradict H1.*)
      induction n. simpl. auto. intros.
    Admitted.*)
    Lemma injection_sound1 : forall n, n = 0 -> injection n = 0%Z.
    Proof.
    intros. rewrite H1. reflexivity.
    Qed.

    Lemma injection_sound2 : forall n, injection n = 0%Z -> n = 0.
    Proof.
    intros. destruct n eqn:Ha. reflexivity. unfold injection in H1. case Ha. Admitted.

    (* We need to define a TDS in order to define the input:                                  *)
    (* We define TDS as a pair of functions nat -> data and nat -> QArith_base.Q              *)
    (*Variable tds : set (nat -> data * nat -> QArith_base.Q).                                *)
    (* TODO: ou a entrada deve ter uma tds pra cada porta (obrigatoriamente) ou simplemsnete ignora *)
    (* caso falte alguma tds para alguma porta?                                               *)

  End ConstraintAutomata.
End ConstraintAutomata.

  (* Example                                                                                *) 

  Definition timeStampTest (n:nat) : QArith_base.Q :=
    match n with
    | 0 =>  1#1
    | S n => ConstraintAutomata.injection (S n) + 1#1
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
  + unfold timeStampTest. simpl.
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
  Definition LSCA (s:states) (st:set (ConstraintAutomata.port ports nat)) (g:bool) : states :=
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

