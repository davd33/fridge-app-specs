---------------------------- MODULE FridjappImpl ----------------------------

EXTENDS Integers, FiniteSets, Sequences, PT, TLC

CONSTANTS INGREDIENT_TYPES, 
          MAX_QTTY, 
          USERS, 
          EMPTY, 
          FRIDJ_IDS,
          MSG_IDS,
          MAX_OP_COUNT

VARIABLES
    \* user managed frjd list (a fridj and a shopping list 
    userData,
    \* message queue by frjd ID
    msgs,
    \* the set messages not acked by everyone yet
    msgsRcvd,
    \* number of executions by action X user
    operationsCount

(***************************************************************************)
(* The list of all the variables in the spec.                              *)
(***************************************************************************)
vars == <<userData, msgs, msgsRcvd, operationsCount>>

(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)
SHOP == "shop" \* shopping list
FRDJ == "frdj" \* fridj

(***************************************************************************)
(* Fridj Ids are uniq through all the users                                *)
(***************************************************************************)
AllIds == ReduceSet(LAMBDA u, a:
                        IF userData[u] = EMPTY
                        THEN a 
                        ELSE a \union DOMAIN userData[u],
                    USERS, {})

Ids(user) == IF userData[user] = EMPTY
             THEN {}
             ELSE DOMAIN userData[user]

(***********************************************************************)
(* Every user's device holds a collection of fridjs and subscribe to   *)
(* other user's fridjs                                                 *)
(***********************************************************************)
UserData(data) == 
    /\ DOMAIN data = USERS
    /\ \A u \in DOMAIN data:
        \/ data[u] = EMPTY
        \/ /\ DOMAIN data[u] \subseteq FRIDJ_IDS
           /\ \A f \in DOMAIN data[u]: 
               data[u][f] \in [frdj: [INGREDIENT_TYPES -> Nat],
                               shop: [INGREDIENT_TYPES -> Nat],
                               cnt: Nat,
                               sync: SUBSET USERS,
                               owner: USERS]

(****************************************************************************
The sequence of messages sent to USERS by Message.user.
****************************************************************************)               
Msgs(messages) == messages = EMPTY \/
    /\ DOMAIN messages \subseteq FRIDJ_IDS
    /\ \A queueId \in DOMAIN messages: 
        \/ messages[queueId] = <<>>
        \/ ForAllSeq(LAMBDA m: m \in [changedBy: USERS,
                                      id: MSG_IDS,
                                      owner: USERS,
                                      type: {FRDJ, SHOP},
                                      frdjId: FRIDJ_IDS,
                                      val: [INGREDIENT_TYPES -> Nat]],
                     messages[queueId])

MsgsRcvd == 
    \E all_possibilities \in {[mIds -> SUBSET USERS \ {{}}]: mIds \in (SUBSET MSG_IDS \ {{}})}:
        msgsRcvd \in all_possibilities

(***************************************************************************)
(* Definitions for creating messages.                                      *)
(***************************************************************************)
\* all used message IDs
AllMsgsIds ==
    IF msgs = EMPTY
    THEN {}
    ELSE ReduceSet(LAMBDA e, acc: LET msgQueue == msgs[e] 
                       IN acc \union {msg.id: msg \in Range(msgQueue)},
                   DOMAIN msgs, {})

\* Return new message with unique ID
Msg(msgId, user, idOwner, type, frdjId, new_val) == 
    [id         |-> msgId,
     changedBy  |-> user,
     owner      |-> idOwner,
     type       |-> type,
     frdjId     |-> frdjId,
     val        |-> new_val]

(***************************************************************************)
(* Send messages to all users listening for FROM fridj                     *)
(***************************************************************************)
Send(queueId, new_msgs) ==
    IF msgs = EMPTY
    THEN msgs' = [m \in {queueId} |-> new_msgs]
    ELSE msgs' = IF queueId \notin DOMAIN msgs
        THEN [mId \in (DOMAIN msgs) \union {queueId} 
                |-> IF mId = queueId THEN new_msgs 
                                     ELSE msgs[mId]]
        ELSE [mId \in DOMAIN msgs 
                |-> IF mId = queueId THEN msgs[mId] \o new_msgs
                                     ELSE msgs[mId]]

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
    /\ \E id \in FRIDJ_IDS \ AllIds:
           userData' = [userData EXCEPT ![user] = AddFridj(user, id, NewFridj(user))]
    /\ UNCHANGED <<msgs, msgsRcvd>>

DeleteFridj(user) == \E id \in Ids(user):
    /\ userData[user][id].owner = user
    /\ userData' = [userData EXCEPT ![user] = [x \in Ids(user) \ {id} |-> @[x]]]
    /\ UNCHANGED <<msgs, msgsRcvd>>

Subscribe(user) == \E u \in USERS \ {user}: \E id \in Ids(u):
    /\ userData[u][id].owner = u
    /\ userData[user] /= EMPTY => id \notin DOMAIN userData[user]
    /\ userData' = [userData EXCEPT ![u][id].sync = @ \union {user},
                                    ![user] = [AddFridj(user, id, userData[u][id])
                                                EXCEPT ![id].sync = @ \union {user}]]
    /\ UNCHANGED <<msgs, msgsRcvd>>

Unsubscribe(user) == \E id \in Ids(user):
    /\ userData[user][id].owner /= user
    /\ userData' = [u \in USERS |->   
            IF u = user 
            THEN [uid \in Ids(u) \ {id} |-> userData[u][uid]]
            ELSE [uid \in Ids(u)        |->
                    [userData[u][uid] EXCEPT !.sync = 
                       IF uid = id THEN @ \ {user}
                                   ELSE @]]]
    /\ UNCHANGED <<msgs, msgsRcvd>>

(***************************************************************************)
(* Add one item in one of its shopping lists.                              *)
(***************************************************************************)
RangeMsgs(fridjId) ==
    IF msgs = EMPTY \/ fridjId \notin DOMAIN msgs
    THEN {}
    ELSE Range(msgs[fridjId])

AddToShoppingList(user) ==
    \E t \in INGREDIENT_TYPES, fridjId \in Ids(user), msgId \in MSG_IDS \ AllMsgsIds:
        /\ \A m \in RangeMsgs(fridjId): m.changedBy = user 
        /\ \* update users data with new shopping list
           LET _userData == [userData EXCEPT ![user][fridjId].shop[t] = @ + 1]
               owner == userData[user][fridjId].owner
           IN /\ userData' = _userData
              /\ /\ userData[user][fridjId].sync /= {}
                 /\ Send(fridjId, <<Msg(msgId, user, owner, SHOP, fridjId, _userData[user][fridjId].shop)>>)
              /\ UNCHANGED msgsRcvd

(***************************************************************************)
(* Next, users add bought items in their fridj instance.                   *)
(***************************************************************************)
BuyIngredients(user) == 
    \E t \in INGREDIENT_TYPES, fridjId \in Ids(user), 
       msgId1 \in MSG_IDS \ AllMsgsIds: \E msgId2 \in (MSG_IDS \ AllMsgsIds) \ {msgId1}:
        \* Cannot change if I'm not in sync
        /\ \A m \in RangeMsgs(fridjId): m.changedBy = user 
        /\ \* move elements of the shop list in the fridj
           LET data == userData[user][fridjId]
               \* fridj accepts MAX_QTTY elements by ingredients
               bought_n == Min(MAX_QTTY - data.frdj[t], data.shop[t])
               _userData == [userData EXCEPT ![user][fridjId].shop[t] = @ - bought_n,
                                             ![user][fridjId].frdj[t] = @ + bought_n]
           IN /\ bought_n > 0
              /\ userData' = _userData
              /\ /\ data.sync /= {}
                 /\ Send(fridjId, <<Msg(msgId1, user, data.owner, SHOP, fridjId, _userData[user][fridjId].shop), 
                                    Msg(msgId2, user, data.owner, FRDJ, fridjId, _userData[user][fridjId].frdj)>>)
              /\ UNCHANGED msgsRcvd

(***************************************************************************)
(* Finally, users cook! They remove items from the fridj.                  *)
(***************************************************************************)
AllRecipes == 
    [INGREDIENT_TYPES -> 0..MAX_QTTY] \ {[t \in INGREDIENT_TYPES |-> 0]}

MakeRecipe(user) == 
    \E r \in AllRecipes, fridjId \in Ids(user), msgId \in MSG_IDS \ AllMsgsIds: 
        \* Cannot change if I'm not in sync
        /\ \A m \in RangeMsgs(fridjId): m.changedBy = user 
        /\ \* removes elements from the fridj
           LET _userData == [userData EXCEPT ![user][fridjId].frdj = [t \in DOMAIN @ |-> @[t] - r[t]],
                                             ![user][fridjId].cnt = @ + 1]
               owner == userData[user][fridjId].owner
           IN /\ \A t \in DOMAIN r: userData[user][fridjId].frdj[t] >= r[t]
              /\ userData' = _userData
              /\ /\ userData[user][fridjId].sync /= {}
                 /\ Send(fridjId, <<Msg(msgId, user, owner, FRDJ, fridjId, _userData[user][fridjId].frdj)>>)
              /\ UNCHANGED msgsRcvd

(***************************************************************************)
(* A user pulls the next message in the queue for one ID.                  *)
(* Every message needs to be consumed by all the subscribed user to an ID. *)
(***************************************************************************)
RcvMsg(user) == \E queueId \in Ids(user):
    /\ msgs /= EMPTY
    /\ queueId \in DOMAIN msgs
    /\ msgs[queueId] /= <<>>
    /\ LET msg == Head(msgs[queueId])
           subscribed == userData[user][queueId].sync
       IN /\ msg.changedBy /= user
          /\ user /= userData[user][queueId].owner
          /\ userData' = CASE msg.type = FRDJ -> [userData EXCEPT ![user][msg.frdjId].frdj = msg.val]
                           [] msg.type = SHOP -> [userData EXCEPT ![user][msg.frdjId].shop = msg.val]
          /\ IF msgsRcvd = EMPTY
             THEN IF subscribed = {user}
                  THEN /\ msgs' = [msgs EXCEPT ![queueId] = Tail(@)]
                       /\ UNCHANGED msgsRcvd
                  ELSE /\ msgsRcvd' = [mId \in {msg.id} |-> {user}]
                       /\ UNCHANGED msgs
             ELSE IF msg.id \notin DOMAIN msgsRcvd
             THEN /\ msgsRcvd' = [mId \in (DOMAIN msgsRcvd) \union {msg.id} |-> 
                                    IF mId = msg.id THEN {user} ELSE msgsRcvd[mId]]
                  /\ UNCHANGED msgs
             ELSE IF msgsRcvd[msg.id] = subscribed \union {user}
                  THEN /\ msgs' = [msgs EXCEPT ![queueId] = Tail(@)]
                       /\ msgsRcvd' = [mId \in (DOMAIN msgsRcvd) \ {msg.id} |-> 
                                        msgsRcvd[mId]]
                  ELSE /\ msgsRcvd' = [msgsRcvd EXCEPT ![msg.id] = @ \union {user}]
                       /\ UNCHANGED msgs

(***************************************************************************)
(* Manage Spec Actions run, to decrease the state space.                   *)
(* Allow for MAX_OP_COUNT executions per action X user.                    *)
(***************************************************************************)
Actions == {"Unsubscribe", "AddToShoppingList", "BuyIngredients", "MakeRecipe", "RcvMsg", "CreateFridj", "DeleteFridj",  "Subscribe"}

GetActionFormula(actionName, user) ==
    CASE actionName = "Unsubscribe" -> Unsubscribe(user) 
      [] actionName = "AddToShoppingList" -> AddToShoppingList(user) 
      [] actionName = "BuyIngredients" -> BuyIngredients(user) 
      [] actionName = "MakeRecipe" -> MakeRecipe(user)
      [] actionName = "RcvMsg" -> RcvMsg(user)
      [] actionName = "CreateFridj" -> CreateFridj(user)
      [] actionName = "DeleteFridj" -> DeleteFridj(user)
      [] actionName = "Subscribe" -> Subscribe(user)
      
RunAction(action, user) ==
    IF operationsCount[action][user] = MAX_OP_COUNT
    THEN UNCHANGED vars
    ELSE /\ GetActionFormula(action, user)
         /\ operationsCount' = [operationsCount EXCEPT ![action][user] = @ + 1]

A_Unsubscribe(u) == RunAction("Unsubscribe", u)
A_AddToShoppingList(u) == RunAction("AddToShoppingList", u)
A_BuyIngredients(u) == RunAction("BuyIngredients", u)
A_MakeRecipe(u) == RunAction("MakeRecipe", u)
A_RcvMsg(u) == RunAction("RcvMsg", u)
A_CreateFridj(u) == RunAction("CreateFridj", u)
A_DeleteFridj(u) == RunAction("DeleteFridj", u)
A_Subscribe(u) == RunAction("Subscribe", u)

(***************************************************************************)
(* Specification compilation of all state predicates.                      *)
(***************************************************************************)
Next == 
    \E u \in USERS:
        \/ A_Subscribe(u)
        \/ A_Unsubscribe(u)
        \/ A_AddToShoppingList(u)
        \/ A_BuyIngredients(u)
        \/ A_MakeRecipe(u)
        \/ A_RcvMsg(u)
        \/ A_CreateFridj(u)
        \/ A_DeleteFridj(u)

Init == 
    /\ operationsCount = [a \in Actions |-> [u \in USERS |-> 0]]
    /\ userData = [u \in USERS |-> EMPTY]
    /\ msgs = EMPTY
    /\ msgsRcvd = EMPTY

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Manage Fairness                                                         *)
(***************************************************************************)
FairSpec == 
    /\ Spec
    /\ \A u \in USERS:
        /\ SF_vars(A_CreateFridj(u))
        /\ SF_vars(A_DeleteFridj(u))
        /\ SF_vars(A_Subscribe(u))
        /\ SF_vars(A_Unsubscribe(u))
        /\ SF_vars(A_BuyIngredients(u))
        /\ SF_vars(A_MakeRecipe(u))
        /\ SF_vars(A_AddToShoppingList(u))
        /\ SF_vars(A_RcvMsg(u))

(***************************************************************************)
(* Type checking invariants.                                                *)
(***************************************************************************)
UserDataTypeOk == UserData(userData)   
MsgsTypeOk == Msgs(msgs)
MsgsRcvdTypeOk == msgsRcvd = EMPTY \/ MsgsRcvd
OperatorsCountTypeOk == operationsCount \in [Actions -> [USERS -> 0..MAX_OP_COUNT]]

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
EmptyQueuesImplySynchedUsers ==
    \/ msgs = EMPTY  
    \/ \A queueId \in AllIds:
          (queueId \in DOMAIN msgs /\ msgs[queueId] = <<>>) => 
             \A u1, u2 \in USERS: userData[u1][queueId] = userData[u2][queueId]

(***************************************************************************)
(* Compose liveness properties and invariants                              *)
(***************************************************************************)
AllUsersMakeRecipes == \A u \in USERS: 
    <>( /\ Ids(u) /= {}
        /\ \A id \in Ids(u): userData[u][id].cnt > 0)
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
\* Last modified Sat Aug 24 14:46:33 CEST 2024 by Davd
\* Last modified Mon Aug 05 09:55:47 CEST 2024 by davd33
\* Created Thu Jul 25 23:17:45 CEST 2024 by davd33
