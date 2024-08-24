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
CHOWN == "chown" \* change owner
SUB == "sub" \* user subscribe
UNSUB == "unsub" \* user unsubscribe

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
        \/ ForAllSeq(LAMBDA m:
                        IF m.type = CHOWN
                        THEN m \in [changedBy: USERS,
                                    id: MSG_IDS,
                                    owner: USERS,
                                    type: {CHOWN},
                                    frdjId: FRIDJ_IDS,
                                    val: USERS]
                        ELSE IF m.type \in {SUB, UNSUB}
                        THEN m \in [changedBy: USERS,
                                    id: MSG_IDS,
                                    owner: USERS,
                                    type: {SUB, UNSUB},
                                    frdjId: FRIDJ_IDS,
                                    val: SUBSET USERS]
                        ELSE m \in [changedBy: USERS,
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

RangeMsgs(queueId) ==
    IF msgs = EMPTY \/ queueId \notin DOMAIN msgs
    THEN {}
    ELSE Range(msgs[queueId])

WaitSync(user, queueId) == \A m \in RangeMsgs(queueId): m.changedBy = user 

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

DeleteFridj(user) == \E queueId \in Ids(user), msgId \in MSG_IDS \ AllMsgsIds:
    /\ userData[user][queueId].owner = user
    /\ WaitSync(user, queueId)
    /\ userData' = [userData EXCEPT ![user] = [x \in Ids(user) \ {queueId} |-> @[x]]]
    /\ IF userData[user][queueId].sync \ {userData[user][queueId].owner} /= {}
       THEN Send(queueId, <<Msg(msgId, user, userData[user][queueId].owner, CHOWN, queueId, 
                    CHOOSE newOwner \in userData[user][queueId].sync: newOwner /= user)>>)
       ELSE UNCHANGED msgs
    /\ UNCHANGED msgsRcvd

Subscribe(user) == \E u \in USERS \ {user}: \E queueId \in Ids(u), msgId \in MSG_IDS \ AllMsgsIds:
    /\ userData[u][queueId].owner = u
    /\ WaitSync(user, queueId)
    /\ userData[user] /= EMPTY => queueId \notin DOMAIN userData[user]
    /\ userData' = [userData EXCEPT ![u][queueId].sync = @ \union {user},
                                    ![user] = [AddFridj(user, queueId, userData[u][queueId])
                                                EXCEPT ![queueId].sync = @ \union {user}]]
    /\ IF userData[u][queueId].sync \ {userData[u][queueId].owner} /= {}
       THEN Send(queueId, <<Msg(msgId, user, userData[u][queueId].owner, SUB, queueId, {user})>>)
       ELSE UNCHANGED msgs
    /\ UNCHANGED msgsRcvd

Unsubscribe(user) == \E queueId \in Ids(user), msgId \in MSG_IDS \ AllMsgsIds:
    /\ userData[user][queueId].owner /= user
    /\ WaitSync(user, queueId)
    /\ userData' = [u \in USERS |->   
            IF u = user 
            THEN [uid \in Ids(u) \ {queueId} |-> userData[u][uid]]
            ELSE [uid \in Ids(u)             |-> userData[u][uid]]]
    /\ IF \E u \in USERS \ {user}:
                u \in userData[user][queueId].sync \union {userData[user][queueId].owner} 
       THEN Send(queueId, <<Msg(msgId, user, userData[user][queueId].owner, UNSUB, queueId, {user})>>)
       ELSE UNCHANGED msgs
    /\ UNCHANGED msgsRcvd

(***************************************************************************)
(* Add one item in one of its shopping lists.                              *)
(***************************************************************************)
AddToShoppingList(user) ==
    \E t \in INGREDIENT_TYPES, queueId \in Ids(user), msgId \in MSG_IDS \ AllMsgsIds:
        /\ WaitSync(user, queueId)
        /\ \* update users data with new shopping list
           LET _userData == [userData EXCEPT ![user][queueId].shop[t] = @ + 1]
               owner == userData[user][queueId].owner
           IN /\ userData' = _userData
              /\ IF \E u \in USERS \ {user}: 
                        u \in userData[user][queueId].sync \union {owner}
                 THEN Send(queueId, <<Msg(msgId, user, owner, SHOP, queueId, _userData[user][queueId].shop)>>)
                 ELSE UNCHANGED msgs
              /\ UNCHANGED msgsRcvd

(***************************************************************************)
(* Next, users add bought items in their fridj instance.                   *)
(***************************************************************************)
BuyIngredients(user) == 
    \E t \in INGREDIENT_TYPES, queueId \in Ids(user), 
       msgId1 \in MSG_IDS \ AllMsgsIds: \E msgId2 \in (MSG_IDS \ AllMsgsIds) \ {msgId1}:
        /\ WaitSync(user, queueId)
        /\ \* move elements of the shop list in the fridj
           LET data == userData[user][queueId]
               \* fridj accepts MAX_QTTY elements by ingredients
               bought_n == Min(MAX_QTTY - data.frdj[t], data.shop[t])
               _userData == [userData EXCEPT ![user][queueId].shop[t] = @ - bought_n,
                                             ![user][queueId].frdj[t] = @ + bought_n]
           IN /\ bought_n > 0
              /\ userData' = _userData
              /\ /\ data.sync /= {}
                 /\ Send(queueId, <<Msg(msgId1, user, data.owner, SHOP, queueId, _userData[user][queueId].shop), 
                                    Msg(msgId2, user, data.owner, FRDJ, queueId, _userData[user][queueId].frdj)>>)
              /\ UNCHANGED msgsRcvd

(***************************************************************************)
(* Finally, users cook! They remove items from the fridj.                  *)
(***************************************************************************)
AllRecipes == 
    [INGREDIENT_TYPES -> 0..MAX_QTTY] \ {[t \in INGREDIENT_TYPES |-> 0]}

MakeRecipe(user) == 
    \E r \in AllRecipes, queueId \in Ids(user), msgId \in MSG_IDS \ AllMsgsIds: 
        /\ WaitSync(user, queueId)
        /\ \* removes elements from the fridj
           LET _userData == [userData EXCEPT ![user][queueId].frdj = [t \in DOMAIN @ |-> @[t] - r[t]],
                                             ![user][queueId].cnt = @ + 1]
               owner == userData[user][queueId].owner
           IN /\ \A t \in DOMAIN r: userData[user][queueId].frdj[t] >= r[t]
              /\ userData' = _userData
              /\ /\ userData[user][queueId].sync /= {}
                 /\ Send(queueId, <<Msg(msgId, user, owner, FRDJ, queueId, _userData[user][queueId].frdj)>>)
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
          /\ msgsRcvd /= EMPTY /\ msg.id \in DOMAIN msgsRcvd 
                    => user \notin msgsRcvd[msg.id]
          
          \* update user's data with new value
          /\ userData' = CASE msg.type = FRDJ  -> [userData EXCEPT ![user][msg.frdjId].frdj = msg.val]
                           [] msg.type = SHOP  -> [userData EXCEPT ![user][msg.frdjId].shop = msg.val]
                           [] msg.type = CHOWN -> [userData EXCEPT ![user][msg.frdjId].owner = msg.val,
                                                                   ![user][msg.frdjId].sync  = @ \ {user}]
                           [] msg.type = SUB   -> [userData EXCEPT ![user][msg.frdjId].sync = @ \union msg.val]
                           [] msg.type = UNSUB -> [userData EXCEPT ![user][msg.frdjId].sync = @ \ msg.val]

          \* ensure that all subscribed users receive the message
          /\ IF msgsRcvd = EMPTY
             THEN IF subscribed = {user} \/ (Cardinality(subscribed) = 1 /\ msg.owner = user)
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
MsgsRcvdTypeOk == msgsRcvd = EMPTY \/ msgsRcvd = <<>> \/ MsgsRcvd
OperatorsCountTypeOk == operationsCount \in [Actions -> [USERS -> 0..MAX_OP_COUNT]]

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
EmptyQueuesImplySynchedUsers ==
    \/ msgs = EMPTY  
    \/ \A u1 \in USERS: \A queueId \in {i \in Ids(u1): userData[u1][i].sync /= {}}:
          (msgs = EMPTY \/ (queueId \in DOMAIN msgs /\ msgs[queueId] = <<>>)) => 
             (\A u2 \in userData[u1][queueId].sync: 
                LET u1d == userData[u1][queueId] 
                    u2d == userData[u2][queueId]
                IN /\ u1d.frdj = u2d.frdj
                   /\ u1d.shop = u2d.shop
                   /\ u1d.sync = u2d.sync
                   /\ u1d.owner = u2d.owner)

NotSubscribedToDeletedFridj ==
    \A u \in USERS:
        \A queueId \in Ids(u):
            LET owner == userData[u][queueId].owner
            IN \/ /\ \/ queueId \in DOMAIN userData[owner]
                     \/ \E msg \in RangeMsgs(queueId):
                            /\ msg.owner = owner
                            /\ msg.type = CHOWN
                            /\ msg.changedBy = owner
                            /\ msg.frdjId = queueId
               \/ /\ msgs /= EMPTY
                  /\ queueId \in DOMAIN msgs
                  /\ \E msg \in RangeMsgs(queueId):
                        /\ msg.type = CHOWN
                        /\ msg.frdjId = queueId
                        /\ msg.val \in userData[u][queueId].sync \ {owner}

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
\* Last modified Sat Aug 24 18:47:47 CEST 2024 by Davd
\* Last modified Mon Aug 05 09:55:47 CEST 2024 by davd33
\* Created Thu Jul 25 23:17:45 CEST 2024 by davd33
