Require Import ListSet.
Require Import List.
Require Import Classes.EquivDec.
(*Real numbers                                              *)
(*Require Import Reals.                                     *)
Set implicit arguments.


Import ListNotations.
(* We define a function that computes the powerset of a set *)
Fixpoint powerset {A} (l:set A) : set (set A) :=
match l with
  | [] => [[]]
  | a::t => concat (map (fun f => [a::f;f]) (powerset t))
end.

Section ConstraintAutomata.

  Variables state name data: Type.
  Variable dataset : set data.
  Context `{EqDec name eq} `{EqDec state eq} `{EqDec data eq}.

  (* We define a port as a record containing its identifier and the data it contains *)
  Record port := {
    id : name;
    (* dataAssignment can be a function nat -> data too, since record's fields are immutable.      *)
    (* maybe nat -> data will fit better, being usable in checking whether at some time n the port *)
    (* can have a data item x                                                                      *)
    (* maybe option data to totalize:None, if there is no data defined for a given k               *)
    (* Some x, for x in data                                                                       *)
    dataAssignment : nat -> data; (
    timeStamp : nat -> nat (* nat -> real *)
  }.
  (* TDS^names can be seen as a set of ports as defined above.. *)

  (* the inductive type that follows defines all possible data constraints for a given Constraint *)
  (* automaton. It uses a Boolean as parameter instead of Prop                                    *)
  (* porta: tipo indutivo que carrega um id (que seria um outro tipo indutivo dado por name) e uma função
  ( de tipo nat -> data *)
  Inductive DC :=
  | g  : bool -> DC.

  Record constraintAutomata := CA {
    Q : set state;
    N : set name; (* ou set port?*)
    T : state -> set port -> DC -> state;
    Q0 : set state;
  }.

  (* Isso pode ser útil no futuro                                                          *)
  (* Given a port name and a set of ports retrieves a port with the ssame port name given. *)
  Fixpoint retrievePort (n:name) (s: set port) : option port :=
    match s with
    | [] => None
    | a::t => if (n == (id a)) then (Some a) else retrievePort n t
    end.



  (*Variable dataStream : nat -> data.*)
  Variable ca : constraintAutomata.
  (* for each name there might be a port associated      *)
  (* Axiom sameSize : length (tdsNames) = length (N ca). *)



End ConstraintAutomata.