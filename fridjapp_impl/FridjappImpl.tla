---------------------------- MODULE FridjappImpl ----------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS INGREDIENT_TYPES, MAX_QTTY, USERS, EMPTY

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

(***********************************************************************)
(* Every user's device holds a collection of fridjs and subscribe to   *)
(* other user's fridjs                                                 *)
(***********************************************************************)
UserData(data) == 
    /\ DOMAIN data = USERS
    /\ \A u \in DOMAIN data:
        \/ data[u] = EMPTY
        \/ /\ DOMAIN data[u] \subseteq Nat
           /\ \A f \in DOMAIN data[u]: 
               data[u][f] \in [frdj: [INGREDIENT_TYPES -> Nat],
                               shop: [INGREDIENT_TYPES -> Nat],
                               cnt: Nat,
                               sync: SUBSET USERS,
                               owner: USERS]

(***********************************************************************)
(* The sequence of messages sent to USERS by Message.user              *)
(* In "real life", all messages of one Fridj instance should be sent   *)
(* inside of a single queue so that messages are kept in order.        *)
(***********************************************************************)               
Msgs(messages) ==
    /\ DOMAIN messages = USERS 
    /\ \A u \in DOMAIN messages: 
        \/ messages[u] = <<>>
        \/ PT!ReduceSeq(LAMBDA m, acc: 
                         \/ ~ acc
                         \/ m \in [user: USERS,
                                   type: {FRDJ, SHOP},
                                   frdjId: Nat,
                                   val: [INGREDIENT_TYPES -> Nat]],
                        messages[u], TRUE)

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
Msg(user, type, frdjId, new_val) == 
    [user |-> user,
     type |-> type,
     frdjId |-> frdjId,
     val |-> new_val]

(***************************************************************************)
(* Send messages to all users listening for FROM fridj                     *)
(***************************************************************************)
Send(from, new_msgs) == 
    msgs' = [msgs EXCEPT ![from] = @ \o new_msgs]

(***************************************************************************)
(* Ids are uniq through all the users                                      *)
(***************************************************************************)
AllIds == PT!ReduceSet(LAMBDA u, a:
                            IF userData[u] = EMPTY
                            THEN a 
                            ELSE a \union DOMAIN userData[u],
                       USERS, {})
Ids(user) == IF userData[user] = EMPTY
             THEN {}
             ELSE DOMAIN userData[user]

(***************************************************************************)
(* Actions taken by users.                                                 *)
(* Create Fridj and shopping list!                                         *)
(***************************************************************************)
NewFridj(user) == [frdj |-> [t \in INGREDIENT_TYPES |-> 0],
                       shop |-> [t \in INGREDIENT_TYPES |-> 0],
                       cnt |-> 0,
                       owner |-> user,
                       sync |-> {}]

AddFridj(user, id, frdjData) == [x \in Ids(user) \union {id} |-> 
                                  IF x = id
                                  THEN frdjData
                                  ELSE userData[user][x]]

CreateFridj(user) ==
    /\ \E id \in Nat \ AllIds:
           userData' = [userData EXCEPT ![user] = AddFridj(user, id, NewFridj(user))]
    /\ UNCHANGED msgs

DeleteFridj(user) == \E id \in Ids(user):
    /\ userData[user][id].owner = user
    /\ userData' = [userData EXCEPT ![user] = [x \in Ids(user) \ {id} |-> @[x]]]
    /\ UNCHANGED msgs

Subscribe(user) == \E u \in USERS \ {user}: \E id \in Ids(u):
    /\ userData[u][id].owner = u
    /\ userData' = [userData EXCEPT ![u][id].sync = @ \union {user},
                                    ![user] = AddFridj(user, id, userData[u][id])]
    /\ UNCHANGED msgs

Unsubscribe(user) == \E id \in Ids(user):
    /\ userData[user][id].owner /= user
    /\ userData' = [u \in USERS |->   
                        IF u = user 
                        THEN [uid \in Ids(u) \ {id} |-> userData[u][uid]]
                        ELSE [uid \in Ids(u)        |->
                                [userData[u][uid] EXCEPT !.sync = 
                                   IF uid = id THEN @ \ {user}
                                               ELSE @]]]
    /\ UNCHANGED msgs

(***************************************************************************)
(* Add one item in one of its shopping lists.                              *)
(***************************************************************************)
AddToShoppingList(user) ==
    \E t \in INGREDIENT_TYPES, id \in Ids(user):
        \* update users data with new shopping list
        LET _userData == [userData EXCEPT ![user][id].shop[t] = @ + 1]
        IN /\ userData' = _userData
           /\ Send(user, <<Msg(user, SHOP, id, _userData[user][id].shop)>>) \* TODO must send to subcribed users

(***************************************************************************)
(* Next, users add bought items in their fridj instance.                   *)
(***************************************************************************)
BuyIngredients(user) == 
    \E t \in INGREDIENT_TYPES, id \in Ids(user):
        \* move elements of the shop list in the fridj
        LET data == userData[user][id]
            \* fridj accepts MAX_QTTY elements by ingredients
            bought_n == Min(MAX_QTTY - data.frdj[t], data.shop[t])
            _userData == [userData EXCEPT ![user][id].shop[t] = @ - bought_n,
                                          ![user][id].frdj[t] = @ + bought_n]
        IN /\ bought_n > 0
           /\ userData' = _userData
           /\ Send(user, <<Msg(user, SHOP, id, _userData[user][id].shop), 
                           Msg(user, FRDJ, id, _userData[user][id].frdj)>>) \* TODO must send to subcribed users

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
           /\ Send(user, <<Msg(user, FRDJ, id, _userData[user][id].frdj)>>) \* TODO must send to subcribed users

RcvMsg(user) == 
    /\ msgs[user] /= <<>>
    /\ LET msg == Head(msgs[user])
       IN userData' = CASE msg.type = FRDJ -> [userData EXCEPT ![user][msg.frdjId].frdj = msg.val]
                        [] msg.type = SHOP -> [userData EXCEPT ![user][msg.frdjId].shop = msg.val]
    /\ msgs' = [msgs EXCEPT ![user] = Tail(@)]

(***************************************************************************)
(* Specification compilation of all state predicates.                      *)
(***************************************************************************)
Next == 
    \E u \in USERS:  
        \/ CreateFridj(u)
        \/ DeleteFridj(u)
        \/ Subscribe(u)
        \/ Unsubscribe(u)
        \/ AddToShoppingList(u) 
        \/ BuyIngredients(u) 
        \/ MakeRecipe(u)
        \/ RcvMsg(u)

Init == 
    /\ userData = [u \in USERS |-> EMPTY]
    /\ msgs = [u \in USERS |-> <<>>]

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Manage Fairness                                                         *)
(***************************************************************************)
FairSpec == 
    /\ Spec
    /\ \A u \in USERS: /\ SF_vars(CreateFridj(u))
                       /\ SF_vars(DeleteFridj(u))
                       /\ SF_vars(Subscribe(u))
                       /\ SF_vars(Unsubscribe(u))
                       /\ SF_vars(BuyIngredients(u)) 
                       /\ SF_vars(MakeRecipe(u))
                       /\ SF_vars(AddToShoppingList(u))
                       /\ SF_vars(RcvMsg(u))

(***************************************************************************)
(* Compose liveness properties and invariants                              *)
(***************************************************************************)
AllUsersMakeRecipes == \A u \in USERS: <>(\A id \in Ids(u): userData[u][id].cnt > 0)
FridjesCreated == \A u \in USERS: <>(userData[u] /= EMPTY)
UserDataIsSynchronized ==
    /\ <>(\E u \in USERS: msgs[u] /= <<>>)
    \* messages are sent and received
    /\ \A u \in USERS: msgs[u] /= <<>> ~> msgs[u] = <<>>
    \* user data is coherent through all subscribed users
    /\ \A id \in AllIds: \E owner \in USERS: 
        /\ userData[owner][id].owner = owner
        /\ \A u \in USERS \ {owner}:
            /\ u \in userData[owner][id].sync
            /\ userData[u][id].frdj = userData[owner][id].frdj
            /\ userData[u][id].shop = userData[owner][id].shop

=============================================================================
\* Modification History
\* Last modified Mon Aug 05 09:55:47 CEST 2024 by davd33
\* Created Thu Jul 25 23:17:45 CEST 2024 by davd33
