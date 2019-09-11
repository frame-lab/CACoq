module SequencerCertified where

import qualified Prelude

data Bool =
   True
 | False

data Nat =
   O
 | S Nat

data Prod a b =
   Pair a b

data List a =
   Nil
 | Cons a (List a)

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data Sumbool =
   Left
 | Right

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

list_prod :: (List a1) -> (List a2) -> List (Prod a1 a2)
list_prod l l' =
  case l of {
   Nil -> Nil;
   Cons x t -> app (map (\y -> Pair x y) l') (list_prod t l')}

type Set a = List a

set_add :: (a1 -> a1 -> Sumbool) -> a1 -> (Set a1) -> Set a1
set_add aeq_dec a x =
  case x of {
   Nil -> Cons a Nil;
   Cons a1 x1 ->
    case aeq_dec a a1 of {
     Left -> Cons a1 x1;
     Right -> Cons a1 (set_add aeq_dec a x1)}}

set_union :: (a1 -> a1 -> Sumbool) -> (Set a1) -> (Set a1) -> Set a1
set_union aeq_dec x y =
  case y of {
   Nil -> x;
   Cons a1 y1 -> set_add aeq_dec a1 (set_union aeq_dec x y1)}

type EqDec a = a -> a -> Sumbool

equiv_dec :: (EqDec a1) -> a1 -> a1 -> Sumbool
equiv_dec eqDec =
  eqDec

pair_eqdec :: (EqDec a1) -> (EqDec a2) -> EqDec (Prod a1 a2)
pair_eqdec h h0 x y =
  case x of {
   Pair a b ->
    case y of {
     Pair c d ->
      case equiv_dec h a c of {
       Left -> equiv_dec h0 b d;
       Right -> Right}}}

data DC name data0 =
   TDc
 | Dc name data0
 | EqDc name name
 | AndDc (DC name data0) (DC name data0)
 | OrDc (DC name data0) (DC name data0)
 | TrDc (data0 -> data0) name name
 | NegDc (DC name data0)

data ConstraintAutomata state name data0 =
   CA (Set state) (Set name) (state -> Set
                             (Prod (Prod (Set name) (DC name data0)) state)) 
 (Set state)

q :: (ConstraintAutomata a1 a2 a3) -> Set a1
q c =
  case c of {
   CA q1 _ _ _ -> q1}

n :: (ConstraintAutomata a1 a2 a3) -> Set a2
n c =
  case c of {
   CA _ n0 _ _ -> n0}

q0 :: (ConstraintAutomata a1 a2 a3) -> Set a1
q0 c =
  case c of {
   CA _ _ _ q1 -> q1}

type ConstraintAutomata0 state name data0 =
  ConstraintAutomata state name data0

type ConstraintAutomata2 name data0 state2 =
  ConstraintAutomata state2 name data0

statesSet :: (ConstraintAutomata a1 a2 a3) -> (ConstraintAutomata a4 
             a2 a3) -> List (Prod a1 a4)
statesSet a1 a2 =
  list_prod (q a1) (q a2)

nameSet :: (EqDec a2) -> (ConstraintAutomata a1 a2 a3) -> (ConstraintAutomata
           a4 a2 a3) -> Set a2
nameSet h a1 a2 =
  set_union (equiv_dec h) (n a1) (n a2)

initialStates :: (ConstraintAutomata0 a1 a2 a3) -> (ConstraintAutomata2 
                 a2 a3 a4) -> List (Prod a1 a4)
initialStates a1 a2 =
  list_prod (q0 a1) (q0 a2)

transitionPA :: (EqDec a2) -> (EqDec a1) -> (EqDec a4) ->
                (ConstraintAutomata0 a1 a2 a3) -> (ConstraintAutomata2 
                a2 a3 a4) -> (Prod a1 a4) -> List
                (Prod (Prod (List a2) (DC a2 a3)) (Prod a1 a4))
transitionPA h h0 h1 a1 a2 s =
  let {
   recoverResultingStatesPA st t =
     case t of {
      Nil -> Nil;
      Cons a tx ->
       case case st of {
             Pair a0 b ->
              case case a of {
                    Pair x _ -> x} of {
               Pair c d -> case h0 a0 c of {
                            Left -> h1 b d;
                            Right -> Right}}} of {
        Left -> Cons (case a of {
                       Pair _ y -> y}) (recoverResultingStatesPA st tx);
        Right -> recoverResultingStatesPA st tx}}}
  in recoverResultingStatesPA s
       (let {
         app0 l m =
           case l of {
            Nil -> m;
            Cons a l1 -> Cons a (app0 l1 m)}}
        in app0
             (let {
               allTransitionsR1 q1 q2 transition1 transition2 names1 names2 =
                 case q1 of {
                  Nil -> Nil;
                  Cons a t ->
                   let {
                    app0 l m =
                      case l of {
                       Nil -> m;
                       Cons a0 l1 -> Cons a0 (app0 l1 m)}}
                   in app0
                        (let {
                          iterateOverA2R1 q3 q4 transition3 transition4 names3 names4 =
                            case q4 of {
                             Nil -> Nil;
                             Cons a0 t0 ->
                              let {
                               app0 l m =
                                 case l of {
                                  Nil -> m;
                                  Cons a3 l1 -> Cons a3 (app0 l1 m)}}
                              in app0
                                   (let {
                                     transitionsForOneStateR1 q5 q6 transition5 transition6 names5 names6 =
                                       case transition5 of {
                                        Nil -> Nil;
                                        Cons a3 t1 ->
                                         let {
                                          app0 l m =
                                            case l of {
                                             Nil -> m;
                                             Cons a4 l1 -> Cons a4
                                              (app0 l1 m)}}
                                         in app0
                                              (let {
                                                moreTransitionsR1 q7 q8 transition7 transition8 names7 names8 =
                                                  case transition8 of {
                                                   Nil -> Nil;
                                                   Cons a4 t2 ->
                                                    let {
                                                     app0 l m =
                                                       case l of {
                                                        Nil -> m;
                                                        Cons a5 l1 -> Cons a5
                                                         (app0 l1 m)}}
                                                    in app0
                                                         (case let {
                                                                s1 = 
                                                                 let {
                                                                  set_inter x y =
                                                                    case x of {
                                                                     Nil ->
                                                                    Nil;
                                                                     Cons a5
                                                                    x1 ->
                                                                    case 
                                                                    let {
                                                                    set_mem a6 x0 =
                                                                      
                                                                    case x0 of {
                                                                     Nil ->
                                                                    False;
                                                                     Cons a7
                                                                    x2 ->
                                                                    case 
                                                                    h a6 a7 of {
                                                                     Left ->
                                                                    True;
                                                                     Right ->
                                                                    set_mem
                                                                    a6 x2}}}
                                                                    in 
                                                                    set_mem
                                                                    a5 y of {
                                                                     True ->
                                                                    Cons a5
                                                                    (set_inter
                                                                    x1 y);
                                                                     False ->
                                                                    set_inter
                                                                    x1 y}}}
                                                                 in set_inter
                                                                    names8
                                                                    (case 
                                                                    case transition7 of {
                                                                     Pair x
                                                                    _ -> x} of {
                                                                     Pair x
                                                                    _ -> x})}
                                                               in
                                                               let {
                                                                s2 = 
                                                                 let {
                                                                  set_inter x y =
                                                                    case x of {
                                                                     Nil ->
                                                                    Nil;
                                                                     Cons a5
                                                                    x1 ->
                                                                    case 
                                                                    let {
                                                                    set_mem a6 x0 =
                                                                      
                                                                    case x0 of {
                                                                     Nil ->
                                                                    False;
                                                                     Cons a7
                                                                    x2 ->
                                                                    case 
                                                                    h a6 a7 of {
                                                                     Left ->
                                                                    True;
                                                                     Right ->
                                                                    set_mem
                                                                    a6 x2}}}
                                                                    in 
                                                                    set_mem
                                                                    a5 y of {
                                                                     True ->
                                                                    Cons a5
                                                                    (set_inter
                                                                    x1 y);
                                                                     False ->
                                                                    set_inter
                                                                    x1 y}}}
                                                                 in set_inter
                                                                    names7
                                                                    (case 
                                                                    case a4 of {
                                                                     Pair x
                                                                    _ -> x} of {
                                                                     Pair x
                                                                    _ -> x})}
                                                               in
                                                               case let {
                                                                    f n0 m =
                                                                      
                                                                    case n0 of {
                                                                     O ->
                                                                    case m of {
                                                                     O ->
                                                                    Left;
                                                                     S _ ->
                                                                    Right};
                                                                     S n1 ->
                                                                    case m of {
                                                                     O ->
                                                                    Right;
                                                                     S m0 ->
                                                                    f n1 m0}}}
                                                                    in 
                                                                    f
                                                                    (let {
                                                                    length l =
                                                                      case l of {
                                                                     Nil -> O;
                                                                     Cons _
                                                                    l' -> S
                                                                    (length
                                                                    l')}}
                                                                    in 
                                                                    length s1)
                                                                    (let {
                                                                    length l =
                                                                      case l of {
                                                                     Nil -> O;
                                                                     Cons _
                                                                    l' -> S
                                                                    (length
                                                                    l')}}
                                                                    in 
                                                                    length s2) of {
                                                                Left ->
                                                                 case 
                                                                 let {
                                                                  s1_in_s2 h2 s3 s4 =
                                                                    case s3 of {
                                                                     Nil ->
                                                                    True;
                                                                     Cons a5
                                                                    t3 ->
                                                                    case 
                                                                    let {
                                                                    set_mem a6 x =
                                                                      
                                                                    case x of {
                                                                     Nil ->
                                                                    False;
                                                                     Cons a7
                                                                    x1 ->
                                                                    case 
                                                                    h2 a6 a7 of {
                                                                     Left ->
                                                                    True;
                                                                     Right ->
                                                                    set_mem
                                                                    a6 x1}}}
                                                                    in 
                                                                    set_mem
                                                                    a5 s4 of {
                                                                     True ->
                                                                    s1_in_s2
                                                                    h2 t3 s4;
                                                                     False ->
                                                                    False}}}
                                                                 in s1_in_s2
                                                                    h s1 s2 of {
                                                                  True ->
                                                                   let {
                                                                    s1_in_s2 h2 s3 s4 =
                                                                      
                                                                    case s3 of {
                                                                     Nil ->
                                                                    True;
                                                                     Cons a5
                                                                    t3 ->
                                                                    case 
                                                                    let {
                                                                    set_mem a6 x =
                                                                      
                                                                    case x of {
                                                                     Nil ->
                                                                    False;
                                                                     Cons a7
                                                                    x1 ->
                                                                    case 
                                                                    h2 a6 a7 of {
                                                                     Left ->
                                                                    True;
                                                                     Right ->
                                                                    set_mem
                                                                    a6 x1}}}
                                                                    in 
                                                                    set_mem
                                                                    a5 s4 of {
                                                                     True ->
                                                                    s1_in_s2
                                                                    h2 t3 s4;
                                                                     False ->
                                                                    False}}}
                                                                   in 
                                                                   s1_in_s2 h
                                                                    s2 s1;
                                                                  False ->
                                                                   False};
                                                                Right ->
                                                                 False} of {
                                                           True -> Cons (Pair
                                                            (Pair q7 q8)
                                                            (Pair (Pair
                                                            (let {
                                                              set_union0 x y =
                                                                case y of {
                                                                 Nil -> x;
                                                                 Cons a5
                                                                  y1 ->
                                                                  let {
                                                                   set_add0 a6 x0 =
                                                                     
                                                                   case x0 of {
                                                                    Nil ->
                                                                    Cons a6
                                                                    Nil;
                                                                    Cons a7
                                                                    x1 ->
                                                                    case 
                                                                    h a6 a7 of {
                                                                     Left ->
                                                                    Cons a7
                                                                    x1;
                                                                     Right ->
                                                                    Cons a7
                                                                    (set_add0
                                                                    a6 x1)}}}
                                                                  in 
                                                                  set_add0 a5
                                                                    (set_union0
                                                                    x y1)}}
                                                             in set_union0
                                                                  (case 
                                                                   case transition7 of {
                                                                    Pair x
                                                                    _ -> x} of {
                                                                    Pair x
                                                                    _ -> x})
                                                                  (case 
                                                                   case a4 of {
                                                                    Pair x
                                                                    _ -> x} of {
                                                                    Pair x
                                                                    _ -> x}))
                                                            (AndDc
                                                            (case case transition7 of {
                                                                   Pair x
                                                                    _ -> x} of {
                                                              Pair _ y -> y})
                                                            (case case a4 of {
                                                                   Pair x
                                                                    _ -> x} of {
                                                              Pair _ y -> y})))
                                                            (Pair
                                                            (case transition7 of {
                                                              Pair _ y -> y})
                                                            (case a4 of {
                                                              Pair _ y -> y}))))
                                                            Nil;
                                                           False -> Nil})
                                                         (moreTransitionsR1
                                                           q7 q8 transition7
                                                           t2 names7 names8)}}
                                               in moreTransitionsR1 q5 q6 a3
                                                    transition6 names5 names6)
                                              (transitionsForOneStateR1 q5 q6
                                                t1 transition6 names5 names6)}}
                                    in transitionsForOneStateR1 q3 a0
                                         (transition3 q3) (transition4 a0)
                                         names3 names4)
                                   (iterateOverA2R1 q3 t0 transition3
                                     transition4 names3 names4)}}
                         in iterateOverA2R1 a q2 transition1 transition2
                              names1 names2)
                        (allTransitionsR1 t q2 transition1 transition2 names1
                          names2)}}
              in allTransitionsR1 (case a1 of {
                                    CA q1 _ _ _ -> q1})
                   (case a2 of {
                     CA q1 _ _ _ -> q1}) (case a1 of {
                                           CA _ _ t _ -> t})
                   (case a2 of {
                     CA _ _ t _ -> t}) (case a1 of {
                                         CA _ n0 _ _ -> n0})
                   (case a2 of {
                     CA _ n0 _ _ -> n0}))
             (let {
               app0 l m =
                 case l of {
                  Nil -> m;
                  Cons a l1 -> Cons a (app0 l1 m)}}
              in app0
                   (let {
                     allTransitionsR2 q1 transitions names2 a2States =
                       case q1 of {
                        Nil -> Nil;
                        Cons a t ->
                         let {
                          app0 l m =
                            case l of {
                             Nil -> m;
                             Cons a0 l1 -> Cons a0 (app0 l1 m)}}
                         in app0
                              (let {
                                rec transitions0 q2 names3 =
                                  case transitions0 of {
                                   Nil -> Nil;
                                   Cons a0 t0 ->
                                    let {
                                     app0 l m =
                                       case l of {
                                        Nil -> m;
                                        Cons a3 l1 -> Cons a3 (app0 l1 m)}}
                                    in app0
                                         (let {
                                           singleTransitionR2 q3 transition a2States0 a2Names =
                                             case a2States0 of {
                                              Nil -> Nil;
                                              Cons q4 t1 ->
                                               case let {
                                                     aux x y =
                                                       case x of {
                                                        Nil ->
                                                         case y of {
                                                          Nil -> Left;
                                                          Cons _ _ -> Right};
                                                        Cons hd tl ->
                                                         case y of {
                                                          Nil -> Right;
                                                          Cons hd' tl' ->
                                                           case h hd hd' of {
                                                            Left ->
                                                             aux tl tl';
                                                            Right -> Right}}}}
                                                    in aux
                                                         (let {
                                                           set_inter x y =
                                                             case x of {
                                                              Nil -> Nil;
                                                              Cons a3 x1 ->
                                                               case let {
                                                                    set_mem a4 x0 =
                                                                      
                                                                    case x0 of {
                                                                     Nil ->
                                                                    False;
                                                                     Cons a5
                                                                    x2 ->
                                                                    case 
                                                                    h a4 a5 of {
                                                                     Left ->
                                                                    True;
                                                                     Right ->
                                                                    set_mem
                                                                    a4 x2}}}
                                                                    in 
                                                                    set_mem
                                                                    a3 y of {
                                                                True -> Cons
                                                                 a3
                                                                 (set_inter
                                                                   x1 y);
                                                                False ->
                                                                 set_inter x1
                                                                   y}}}
                                                          in set_inter
                                                               (case 
                                                                case transition of {
                                                                 Pair x _ ->
                                                                  x} of {
                                                                 Pair x _ ->
                                                                  x}) a2Names)
                                                         Nil of {
                                                Left -> Cons (Pair (Pair q3
                                                 q4) (Pair
                                                 (case transition of {
                                                   Pair x _ -> x}) (Pair
                                                 (case transition of {
                                                   Pair _ y -> y}) q4)))
                                                 (singleTransitionR2 q3
                                                   transition t1 a2Names);
                                                Right ->
                                                 singleTransitionR2 q3
                                                   transition t1 a2Names}}}
                                          in singleTransitionR2 a a0 q2
                                               names3) (rec t0 q2 names3)}}
                               in rec (transitions a) a2States names2)
                              (allTransitionsR2 t transitions names2
                                a2States)}}
                    in allTransitionsR2 (case a1 of {
                                          CA q1 _ _ _ -> q1})
                         (case a1 of {
                           CA _ _ t _ -> t})
                         (case a2 of {
                           CA _ n0 _ _ -> n0})
                         (case a2 of {
                           CA q1 _ _ _ -> q1}))
                   (let {
                     allTransitionsR3 q2 transitions names1 a1States =
                       case q2 of {
                        Nil -> Nil;
                        Cons a t ->
                         let {
                          app0 l m =
                            case l of {
                             Nil -> m;
                             Cons a0 l1 -> Cons a0 (app0 l1 m)}}
                         in app0
                              (let {
                                rec transitions0 q1 names2 =
                                  case transitions0 of {
                                   Nil -> Nil;
                                   Cons a0 t0 ->
                                    let {
                                     app0 l m =
                                       case l of {
                                        Nil -> m;
                                        Cons a3 l1 -> Cons a3 (app0 l1 m)}}
                                    in app0
                                         (let {
                                           singleTransitionR3 q3 transition a2States a1Names =
                                             case a2States of {
                                              Nil -> Nil;
                                              Cons q4 t1 ->
                                               case let {
                                                     aux x y =
                                                       case x of {
                                                        Nil ->
                                                         case y of {
                                                          Nil -> Left;
                                                          Cons _ _ -> Right};
                                                        Cons hd tl ->
                                                         case y of {
                                                          Nil -> Right;
                                                          Cons hd' tl' ->
                                                           case h hd hd' of {
                                                            Left ->
                                                             aux tl tl';
                                                            Right -> Right}}}}
                                                    in aux
                                                         (let {
                                                           set_inter x y =
                                                             case x of {
                                                              Nil -> Nil;
                                                              Cons a3 x1 ->
                                                               case let {
                                                                    set_mem a4 x0 =
                                                                      
                                                                    case x0 of {
                                                                     Nil ->
                                                                    False;
                                                                     Cons a5
                                                                    x2 ->
                                                                    case 
                                                                    h a4 a5 of {
                                                                     Left ->
                                                                    True;
                                                                     Right ->
                                                                    set_mem
                                                                    a4 x2}}}
                                                                    in 
                                                                    set_mem
                                                                    a3 y of {
                                                                True -> Cons
                                                                 a3
                                                                 (set_inter
                                                                   x1 y);
                                                                False ->
                                                                 set_inter x1
                                                                   y}}}
                                                          in set_inter
                                                               (case 
                                                                case transition of {
                                                                 Pair x _ ->
                                                                  x} of {
                                                                 Pair x _ ->
                                                                  x}) a1Names)
                                                         Nil of {
                                                Left -> Cons (Pair (Pair q4
                                                 q3) (Pair
                                                 (case transition of {
                                                   Pair x _ -> x}) (Pair q4
                                                 (case transition of {
                                                   Pair _ y -> y}))))
                                                 (singleTransitionR3 q3
                                                   transition t1 a1Names);
                                                Right ->
                                                 singleTransitionR3 q3
                                                   transition t1 a1Names}}}
                                          in singleTransitionR3 a a0 q1
                                               names2) (rec t0 q1 names2)}}
                               in rec (transitions a) a1States names1)
                              (allTransitionsR3 t transitions names1
                                a1States)}}
                    in allTransitionsR3 (case a2 of {
                                          CA q1 _ _ _ -> q1})
                         (case a2 of {
                           CA _ _ t _ -> t})
                         (case a1 of {
                           CA _ n0 _ _ -> n0})
                         (case a1 of {
                           CA q1 _ _ _ -> q1}))))

buildPA :: (EqDec a2) -> (EqDec a1) -> (EqDec a4) -> (ConstraintAutomata0 
           a1 a2 a3) -> (ConstraintAutomata2 a2 a3 a4) -> ConstraintAutomata
           (Prod a1 a4) a2 a3
buildPA h h0 h1 a1 a2 =
  CA (statesSet a1 a2) (nameSet h a1 a2) (transitionPA h h0 h1 a1 a2)
    (initialStates a1 a2)

reoCABinaryChannel :: a1 -> a1 -> (Set a2) -> (Set a2) -> (a2 -> Set
                      (Prod (Prod (Set a1) (DC a1 a3)) a2)) ->
                      ConstraintAutomata a2 a1 a3
reoCABinaryChannel a b states initialStates0 transitionRelation =
  CA states (Cons a (Cons b Nil)) transitionRelation initialStates0

data SequencerStates =
   S0
 | Q0a
 | P0a
 | P1a

data SequencerPorts =
   A
 | B
 | C
 | D
 | E
 | F
 | G
 | H
 | I
 | J

sequencerStatesEq :: EqDec SequencerStates
sequencerStatesEq x y =
  case x of {
   S0 -> case y of {
          S0 -> Left;
          _ -> Right};
   Q0a -> case y of {
           Q0a -> Left;
           _ -> Right};
   P0a -> case y of {
           P0a -> Left;
           _ -> Right};
   P1a -> case y of {
           P1a -> Left;
           _ -> Right}}

sequencerPortsEq :: EqDec SequencerPorts
sequencerPortsEq x y =
  case x of {
   A -> case y of {
         A -> Left;
         _ -> Right};
   B -> case y of {
         B -> Left;
         _ -> Right};
   C -> case y of {
         C -> Left;
         _ -> Right};
   D -> case y of {
         D -> Left;
         _ -> Right};
   E -> case y of {
         E -> Left;
         _ -> Right};
   F -> case y of {
         F -> Left;
         _ -> Right};
   G -> case y of {
         G -> Left;
         _ -> Right};
   H -> case y of {
         H -> Left;
         _ -> Right};
   I -> case y of {
         I -> Left;
         _ -> Right};
   J -> case y of {
         J -> Left;
         _ -> Right}}

dToEFIFOrel :: SequencerStates -> List
               (Prod (Prod (List SequencerPorts) (DC SequencerPorts Nat))
               SequencerStates)
dToEFIFOrel s =
  case s of {
   S0 -> Nil;
   Q0a -> Cons (Pair (Pair (Cons D Nil) (Dc D O)) P0a) (Cons (Pair (Pair
    (Cons D Nil) (Dc D (S O))) P1a) Nil);
   P0a -> Cons (Pair (Pair (Cons E Nil) (Dc E O)) Q0a) Nil;
   P1a -> Cons (Pair (Pair (Cons E Nil) (Dc E (S O))) Q0a) Nil}

dToEFIFOCA :: ConstraintAutomata SequencerStates SequencerPorts Nat
dToEFIFOCA =
  reoCABinaryChannel D E (Cons Q0a (Cons P0a (Cons P1a Nil))) (Cons Q0a Nil)
    dToEFIFOrel

syncEACaBehavior :: SequencerStates -> List
                    (Prod
                    (Prod (List SequencerPorts) (DC SequencerPorts Nat))
                    SequencerStates)
syncEACaBehavior s =
  case s of {
   S0 -> Cons (Pair (Pair (Cons E (Cons A Nil)) (EqDc E A)) S0) Nil;
   _ -> Nil}

eAsyncCA :: ConstraintAutomata SequencerStates SequencerPorts Nat
eAsyncCA =
  reoCABinaryChannel E A (Cons S0 Nil) (Cons S0 Nil) syncEACaBehavior

eToGFIFOrel :: SequencerStates -> List
               (Prod (Prod (List SequencerPorts) (DC SequencerPorts Nat))
               SequencerStates)
eToGFIFOrel s =
  case s of {
   S0 -> Nil;
   Q0a -> Cons (Pair (Pair (Cons E Nil) (Dc E O)) P0a) (Cons (Pair (Pair
    (Cons E Nil) (Dc E (S O))) P1a) Nil);
   P0a -> Cons (Pair (Pair (Cons G Nil) (Dc G O)) Q0a) Nil;
   P1a -> Cons (Pair (Pair (Cons G Nil) (Dc G (S O))) Q0a) Nil}

eToGFIFOCA :: ConstraintAutomata SequencerStates SequencerPorts Nat
eToGFIFOCA =
  reoCABinaryChannel E G (Cons Q0a (Cons P0a (Cons P1a Nil))) (Cons Q0a Nil)
    eToGFIFOrel

syncGBCaBehavior :: SequencerStates -> List
                    (Prod
                    (Prod (List SequencerPorts) (DC SequencerPorts Nat))
                    SequencerStates)
syncGBCaBehavior s =
  case s of {
   S0 -> Cons (Pair (Pair (Cons G (Cons B Nil)) (EqDc G B)) S0) Nil;
   _ -> Nil}

gBsyncCA :: ConstraintAutomata SequencerStates SequencerPorts Nat
gBsyncCA =
  reoCABinaryChannel G B (Cons S0 Nil) (Cons S0 Nil) syncGBCaBehavior

gToHFIFOrel :: SequencerStates -> List
               (Prod (Prod (List SequencerPorts) (DC SequencerPorts Nat))
               SequencerStates)
gToHFIFOrel s =
  case s of {
   S0 -> Nil;
   Q0a -> Cons (Pair (Pair (Cons G Nil) (Dc G O)) P0a) (Cons (Pair (Pair
    (Cons G Nil) (Dc G (S O))) P1a) Nil);
   P0a -> Cons (Pair (Pair (Cons H Nil) (Dc H O)) Q0a) Nil;
   P1a -> Cons (Pair (Pair (Cons H Nil) (Dc H (S O))) Q0a) Nil}

gToHFIFOCA :: ConstraintAutomata SequencerStates SequencerPorts Nat
gToHFIFOCA =
  reoCABinaryChannel G H (Cons Q0a (Cons P0a (Cons P1a Nil))) (Cons Q0a Nil)
    gToHFIFOrel

syncHCCaBehavior :: SequencerStates -> List
                    (Prod
                    (Prod (List SequencerPorts) (DC SequencerPorts Nat))
                    SequencerStates)
syncHCCaBehavior s =
  case s of {
   S0 -> Cons (Pair (Pair (Cons H (Cons C Nil)) (EqDc H C)) S0) Nil;
   _ -> Nil}

hCsyncCA :: ConstraintAutomata SequencerStates SequencerPorts Nat
hCsyncCA =
  reoCABinaryChannel H C (Cons S0 Nil) (Cons S0 Nil) syncHCCaBehavior

fifo1Product :: ConstraintAutomata (Prod SequencerStates SequencerStates)
                SequencerPorts Nat
fifo1Product =
  buildPA sequencerPortsEq sequencerStatesEq sequencerStatesEq dToEFIFOCA
    eAsyncCA

fifo2Product :: ConstraintAutomata
                (Prod (Prod SequencerStates SequencerStates) SequencerStates)
                SequencerPorts Nat
fifo2Product =
  buildPA sequencerPortsEq (pair_eqdec sequencerStatesEq sequencerStatesEq)
    sequencerStatesEq fifo1Product eToGFIFOCA

fifo3Product :: ConstraintAutomata
                (Prod
                (Prod (Prod SequencerStates SequencerStates) SequencerStates)
                SequencerStates) SequencerPorts Nat
fifo3Product =
  buildPA sequencerPortsEq
    (pair_eqdec (pair_eqdec sequencerStatesEq sequencerStatesEq)
      sequencerStatesEq) sequencerStatesEq fifo2Product gBsyncCA

fifo4Product :: ConstraintAutomata
                (Prod
                (Prod
                (Prod (Prod SequencerStates SequencerStates) SequencerStates)
                SequencerStates) SequencerStates) SequencerPorts Nat
fifo4Product =
  buildPA sequencerPortsEq
    (pair_eqdec
      (pair_eqdec (pair_eqdec sequencerStatesEq sequencerStatesEq)
        sequencerStatesEq) sequencerStatesEq) sequencerStatesEq fifo3Product
    gToHFIFOCA

resultingSequencerProduct :: ConstraintAutomata
                             (Prod
                             (Prod
                             (Prod
                             (Prod (Prod SequencerStates SequencerStates)
                             SequencerStates) SequencerStates)
                             SequencerStates) SequencerStates) SequencerPorts
                             Nat
resultingSequencerProduct =
  buildPA sequencerPortsEq
    (pair_eqdec
      (pair_eqdec
        (pair_eqdec (pair_eqdec sequencerStatesEq sequencerStatesEq)
          sequencerStatesEq) sequencerStatesEq) sequencerStatesEq)
    sequencerStatesEq fifo4Product hCsyncCA

