---------------------------- MODULE FridjappImpl ----------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS INGREDIENT_TYPES, MAX_QTTY, USERS

VARIABLES userData, msgs

PT == INSTANCE PT

(***************************************************************************)
(* Sum up all integers in function FUN.                                    *)
(***************************************************************************)
Sum(fun) == PT!ReduceSet(LAMBDA k, acc: acc + fun[k],
                         DOMAIN fun, 0)

(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)
SHOP == "shop" \* shopping list
FRDJ == "frdj" \* fridj
CNT == "cnt"   \* count of cooked recipes

(***********************************************************************)
(* Every user's device holds a collection of fridjs and subscribe to   *)
(* other user's fridjs                                                 *)
(***********************************************************************)
UserData(data) == 
    /\ DOMAIN data = USERS
    /\ \A u \in DOMAIN data:
        /\ DOMAIN data[u] \subseteq Nat
        /\ \A f \in DOMAIN data[u]: 
            data[u][f] \in [frdj: [INGREDIENT_TYPES -> Nat],
                             shop: [INGREDIENT_TYPES -> Nat],
                             cnt: Nat,
                             sync: SUBSET USERS]

(***********************************************************************)
(* The sequence of messages sent to USERS by Message.user              *)
(* In "real life", all messages of one Fridj instance should be sent   *)
(* inside of a single queue so that messages are kept in order.        *)
(***********************************************************************)               
Msgs(msgsList) ==
    /\ DOMAIN msgsList = USERS 
    /\ \A u \in DOMAIN msgsList: 
        \/ msgsList[u] = <<>>
        \/ PT!ReduceSeq(LAMBDA m, acc: 
                         \/ ~ acc
                         \/ /\ m.user \in USERS
                            /\ m.type \in {FRDJ, SHOP}
                            /\ \/ m.type \in {FRDJ, SHOP} /\ 
                                    m.val \in [INGREDIENT_TYPES -> Nat]
                               \/ m.type = CNT /\ m.val \in Nat,
                        msgsList[u], TRUE)

(***************************************************************************)
(* Type checking invariant.                                                *)
(***************************************************************************)
TypeOK == 
    /\ UserData(userData)   
    /\ Msgs(msgs)

(***************************************************************************)
(* The list of all the variables in the spec.                              *)
(***************************************************************************)
vars == <<userData, msgs>>

Min(a, b) == IF a < b THEN a ELSE b

(***************************************************************************)
(* Definitions for creating messages.                                      *)
(***************************************************************************)
Msg(user, type, new_val) == 
    [user |-> user,
     type |-> type,
     val |-> new_val]

(***************************************************************************)
(* Send messages to all users listening for FROM fridj                     *)
(***************************************************************************)
Send(from, new_msgs) == 
    msgs' = [msgs EXCEPT ![from] = @ \o new_msgs]

(***************************************************************************)
(* Actions taken by users.                                                 *)
(* Create Fridj and shopping list!                                         *)
(***************************************************************************)
Ids(user) == DOMAIN userData[user]
CreateFridj(user) == \E id \in Nat \ Ids(user):
    /\ userData' = [userData EXCEPT ![user] = [x \in DOMAIN @ \union {id} |-> 
                                                  IF x = id
                                                  THEN
                                                  [frdj |-> [t \in INGREDIENT_TYPES |-> 0],
                                                   shop |-> [t \in INGREDIENT_TYPES |-> 0],
                                                   cnt |-> 0,
                                                   sync |-> {}]
                                                  ELSE @[x]]]
    /\ UNCHANGED msgs

DeleteFridj(user) == \E id \in Ids(user):
    /\ userData' = [userData EXCEPT ![user] = [x \in DOMAIN @ \ {id} |-> @[x]]]
    /\ UNCHANGED msgs

SubscribeToFridj(user) == \E u \in USERS \ {user}: \E id \in Ids(u):
    /\ userData' = [userData EXCEPT ![u][id].sync = @ \union {user}]
    /\ UNCHANGED msgs

(***************************************************************************)
(* Add one item in one of its shopping lists.                              *)
(***************************************************************************)
AddToShoppingList(user) ==
    \E t \in INGREDIENT_TYPES, id \in Ids(user):
        \* update users data with new shopping list
        LET _userData == [userData EXCEPT ![user][id].shop[t] = @ + 1]
        IN /\ userData' = _userData
           /\ Send(user, <<Msg(user, SHOP, _userData[user][id].shop)>>)

(***************************************************************************)
(* Next, users add bought items in their fridj instance.                   *)
(***************************************************************************)
BuyIngredients(user) == 
    \E t \in INGREDIENT_TYPES, id \in Ids(user):
        \* move elements of the shop list in the fridj
        LET data == userData[user][id]
            \* fridj accepts MAX_QTTY elements by ingredients
            bought_n == Min(MAX_QTTY - data.frdj[t], data.frdj[t])
            _userData == [userData EXCEPT ![user][id].shop[t] = @ - bought_n,
                                          ![user][id].frdj[t] = @ + bought_n]
        IN /\ bought_n > 0
           /\ userData' = _userData
           /\ Send(user, <<Msg(user, SHOP, _userData[user][id].shop), 
                           Msg(user, FRDJ, _userData[user][id].frdj)>>)

(***************************************************************************)
(* Finally, users cook! They remove items from the fridj.                  *)
(***************************************************************************)
AllRecipes == 
    [INGREDIENT_TYPES -> 0..MAX_QTTY] \ {[t \in INGREDIENT_TYPES |-> 0]}

MakeRecipe(user) == 
    \E r \in AllRecipes, id \in Ids(user): 
        LET _userData == [userData EXCEPT ![user][id].frdj = [t \in DOMAIN @ |-> @[t] - r[t]],
                                          ![user][id].cnt = @ + 1]
        IN /\ \A t \in DOMAIN r: userData[user][id].frdj[t] >= r[t]
           /\ userData' = _userData
           /\ Send(user, <<Msg(user, FRDJ, _userData[user][id].frdj)>>)

(***************************************************************************)
(* Specification compilation of all state predicates.                      *)
(***************************************************************************)
Next == 
    \E u \in USERS:  
        \/ CreateFridj(u)
        \/ DeleteFridj(u)
        \/ SubscribeToFridj(u)
        \/ AddToShoppingList(u) 
        \/ BuyIngredients(u) 
        \/ MakeRecipe(u)

Init == 
    /\ userData = [u \in USERS |-> <<[frdj |-> [t \in INGREDIENT_TYPES |-> 0],
                                      shop |-> [t \in INGREDIENT_TYPES |-> 0],
                                      cnt |-> 0,
                                      sync |-> {}]>>]
    /\ msgs = [u \in USERS |-> <<>>]

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Manage Fairness                                                         *)
(***************************************************************************)
FairSpec == 
    /\ Spec
    /\ \A u \in USERS: /\ WF_vars(BuyIngredients(u)) 
                       /\ WF_vars(MakeRecipe(u))
                       /\ WF_vars(AddToShoppingList(u))

(***************************************************************************)
(* Compose liveness properties and invariants                              *)
(***************************************************************************)
TempInv == <>(\A u \in USERS: \A id \in Ids(u): userData[u][id].cnt > 0)

=============================================================================
\* Modification History
\* Last modified Fri Aug 02 13:29:04 CEST 2024 by davd33
\* Created Thu Jul 25 23:17:45 CEST 2024 by davd33
