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
UpdateUserData(msg, user, data) ==
    CASE msg.type = FRDJ  -> [data EXCEPT ![user][msg.frdjId].frdj = msg.val]
      [] msg.type = SHOP  -> [data EXCEPT ![user][msg.frdjId].shop = msg.val]
      [] msg.type = CHOWN -> [data EXCEPT ![user][msg.frdjId].owner = msg.val,
                                          ![user][msg.frdjId].sync  = @ \ {user}]
      [] msg.type = SUB   -> [data EXCEPT ![user][msg.frdjId].sync = @ \union msg.val]
      [] msg.type = UNSUB -> [data EXCEPT ![user][msg.frdjId].sync = @ \ msg.val]

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
    /\ LET _userData == \* copy owner's fridj
            [userData EXCEPT ![u][queueId].sync = @ \union {user},
                                    ![user] = [AddFridj(user, queueId, userData[u][queueId])
                                                EXCEPT ![queueId].sync = @ \union {user}]]
       IN userData' = IF msgs /= EMPTY /\ queueId \in DOMAIN msgs
                      \* get previous changes when subcribing more than once
                      THEN ReduceSeq(LAMBDA msg, acc: 
                                        IF msg.changedBy = user /\ msg.type \in {SHOP, FRDJ}
                                        THEN UpdateUserData(msg, user, acc)
                                        ELSE acc,
                                     msgs[queueId], _userData)
                      ELSE _userData
    /\ IF userData[u][queueId].sync \ {userData[u][queueId].owner} /= {}
           \/ \E m \in RangeMsgs(queueId): m.changedBy = user
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
          /\ userData' = UpdateUserData(msg, user, userData)

          \* ensure that all subscribed users receive the message
          /\ IF msgsRcvd = EMPTY
             THEN IF {user} = (subscribed \union {msg.owner}) \ {msg.changedBy}
                  THEN /\ msgs' = [msgs EXCEPT ![queueId] = Tail(@)]
                       /\ UNCHANGED msgsRcvd
                  ELSE /\ msgsRcvd' = [mId \in {msg.id} |-> {user}]
                       /\ UNCHANGED msgs
             ELSE IF msg.id \notin DOMAIN msgsRcvd
             THEN IF {user} = (subscribed \union {msg.owner}) \ {msg.changedBy}
                  THEN /\ msgs' = [msgs EXCEPT ![queueId] = Tail(@)]
                       /\ UNCHANGED msgsRcvd
                  ELSE /\ msgsRcvd' = [mId \in (DOMAIN msgsRcvd) \union {msg.id} |-> 
                                          IF mId = msg.id THEN {user} ELSE msgsRcvd[mId]]
                       /\ UNCHANGED msgs
             ELSE IF msgsRcvd[msg.id] \union {user} = 
                        (subscribed \ {msg.changedBy}) \union {msg.owner}
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

A_Unsubscribe(u) ==
    IF operationsCount["Unsubscribe"][u] = MAX_OP_COUNT
    THEN UNCHANGED vars
    ELSE /\ GetActionFormula("Unsubscribe", u)
         /\ operationsCount' = [operationsCount EXCEPT !["Unsubscribe"][u] = @ + 1]
A_AddToShoppingList(u) ==
    IF operationsCount["AddToShoppingList"][u] = MAX_OP_COUNT
    THEN UNCHANGED vars
    ELSE /\ GetActionFormula("AddToShoppingList", u)
         /\ operationsCount' = [operationsCount EXCEPT !["AddToShoppingList"][u] = @ + 1]
A_BuyIngredients(u) ==
    IF operationsCount["BuyIngredients"][u] = MAX_OP_COUNT
    THEN UNCHANGED vars
    ELSE /\ GetActionFormula("BuyIngredients", u)
         /\ operationsCount' = [operationsCount EXCEPT !["BuyIngredients"][u] = @ + 1]
A_MakeRecipe(u) ==
    IF operationsCount["MakeRecipe"][u] = MAX_OP_COUNT
    THEN UNCHANGED vars
    ELSE /\ GetActionFormula("MakeRecipe", u)
         /\ operationsCount' = [operationsCount EXCEPT !["MakeRecipe"][u] = @ + 1]
A_RcvMsg(u) ==
    IF operationsCount["RcvMsg"][u] = MAX_OP_COUNT
    THEN UNCHANGED vars
    ELSE /\ GetActionFormula("RcvMsg", u)
         /\ operationsCount' = [operationsCount EXCEPT !["RcvMsg"][u] = @ + 1]
A_CreateFridj(u) ==
    IF operationsCount["CreateFridj"][u] = MAX_OP_COUNT
    THEN UNCHANGED vars
    ELSE /\ GetActionFormula("CreateFridj", u)
         /\ operationsCount' = [operationsCount EXCEPT !["CreateFridj"][u] = @ + 1]
A_DeleteFridj(u) ==
    IF operationsCount["DeleteFridj"][u] = MAX_OP_COUNT
    THEN UNCHANGED vars
    ELSE /\ GetActionFormula("DeleteFridj", u)
         /\ operationsCount' = [operationsCount EXCEPT !["DeleteFridj"][u] = @ + 1]
A_Subscribe(u) ==
    IF operationsCount["Subscribe"][u] = MAX_OP_COUNT
    THEN UNCHANGED vars
    ELSE /\ GetActionFormula("Subscribe", u)
         /\ operationsCount' = [operationsCount EXCEPT !["Subscribe"][u] = @ + 1]

(***************************************************************************)
(* Specification compilation of all state predicates.                      *)
(***************************************************************************)
Next == 
    \E u \in USERS:
        \/ A_Subscribe(u) \* copy data over (from owner's client to U)
        \/ A_Unsubscribe(u) \* send UNSUB message over the queue
        \/ A_AddToShoppingList(u) \* send msg
        \/ A_BuyIngredients(u) \* send msg
        \/ A_MakeRecipe(u) \* send msg
        \/ A_RcvMsg(u) \* read from msg queue
        \/ A_CreateFridj(u) \* local
        \/ A_DeleteFridj(u) \* send CHOWN msg if subscribed users

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
        /\ WF_vars(A_RcvMsg(u))

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
          (queueId \in DOMAIN msgs /\ msgs[queueId] = <<>>) => 
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
            IN \/ \/ queueId \in DOMAIN userData[owner]
                  \/ \E msg \in RangeMsgs(queueId):
                         /\ msg.owner = owner
                         /\ msg.type = CHOWN
                         /\ msg.changedBy = owner
                         /\ msg.frdjId = queueId
                         /\ msg.val \in userData[u][queueId].sync \ {owner}
               \/ /\ msgs /= EMPTY
                  /\ queueId \in DOMAIN msgs
                  /\ \E msg \in RangeMsgs(queueId):
                        /\ msg.type = CHOWN
                        /\ msg.frdjId = queueId
                        /\ msg.val \in userData[u][queueId].sync \ {owner}

(***************************************************************************)
(* Compose liveness properties and invariants                              *)
(***************************************************************************)
MsgsAreConsumed == 
    \A queueId \in FRIDJ_IDS: 
         (msgs /= EMPTY /\ queueId \in DOMAIN msgs /\ msgs[queueId] /= <<>>)
             ~> (msgs /= EMPTY /\ queueId \in DOMAIN msgs /\ msgs[queueId] = <<>>)

=============================================================================
\* Modification History
\* Last modified Sun Aug 25 16:53:57 CEST 2024 by Davd
\* Last modified Mon Aug 05 09:55:47 CEST 2024 by davd33
\* Created Thu Jul 25 23:17:45 CEST 2024 by davd33
