---------------------------- MODULE FridjappImpl ----------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS INGREDIENT_TYPES, MAX_QTTY, USERS, SERVER

ASSUME SERVER \in USERS

VARIABLES fridj, shoppingList, nRecipesMade, msgs

PT == INSTANCE PT

(***************************************************************************)
(* Sum up all integers in function FUN.                                    *)
(***************************************************************************)
Sum(fun) == PT!ReduceSet(LAMBDA k, acc: acc + fun[k],
                         DOMAIN fun, 0)

(***************************************************************************)
(* Refinement mapping: the number of recipes split by users is summed up.  *)
(* The fridj of reference is the server's.                                 *)
(* The server sums up the count of recipes made by all the users           *)
(* of a managed fridj.                                                     *)
(***************************************************************************)
fj == INSTANCE fridjapp WITH nRecipesMade <- nRecipesMade[SERVER],
                             fridj <- fridj[SERVER]

(***************************************************************************)
(* What's a Fridj and a Shopping List.                                     *)
(***************************************************************************)
AllFridjes == [INGREDIENT_TYPES -> Nat]
AllShoppingLists == AllFridjes

FinalUsers == USERS \ {SERVER}

(***************************************************************************)
(* What's a synchronisation message, and it's actions.                     *)
(***************************************************************************)
FridjObject == "fridj"
ShoppingListObject == "shoppingList"
NbRecipesCountObject == "nbRecipesCount"
Objects == {FridjObject, ShoppingListObject, NbRecipesCountObject}

TypeOK == 
    (***********************************************************************)
    (* Every user's device is assigned a fridj function.                   *)
    (* One of these users is the server.                                   *)
    (***********************************************************************)
    /\ fridj \in [USERS -> AllFridjes]
    (***********************************************************************)
    (* Each user has a shopping list as well.                              *)
    (***********************************************************************)
    /\ shoppingList \in [USERS -> AllShoppingLists]
    (***********************************************************************)
    (* We count the number of recipes made by each user.                   *)
    (***********************************************************************)
    /\ nRecipesMade \in [USERS -> Nat]
    (***********************************************************************)
    (* The sequence of messages sent to USERS by Message.user              *)
    (* In "real life", all messages of one Fridj instance should be sent   *)
    (* inside of a single queue so that messages are kept in order.        *)
    (***********************************************************************)    
    /\ DOMAIN msgs = USERS 
    /\ \A u \in DOMAIN msgs: 
        \/ msgs[u] = <<>>
        \/ PT!ReduceSeq(LAMBDA m, acc: 
                         \/ ~ acc
                         \/ /\ m.user \in USERS
                            /\ m.object \in Objects
                            /\ \/ ~(m.object = NbRecipesCountObject) /\ m.value \in AllFridjes
                               \/ m.value \in Nat,
                     msgs[u], TRUE)

(***************************************************************************)
(* The list of all the variables in the spec.                              *)
(***************************************************************************)
vars == <<fridj, shoppingList, nRecipesMade, msgs>>

Min(a, b) == IF a < b THEN a ELSE b

(***************************************************************************)
(* Definitions for creating messages.                                      *)
(***************************************************************************)
NewMessage(user, object, value) == 
    [user |-> user,
     object |-> object,
     value |-> value]

ShoppingListMsg(user, value) ==
    NewMessage(user, ShoppingListObject, value)

FridjMsg(user, value) ==
    NewMessage(user, FridjObject, value)

NbRecipesCountMsg(user, value) ==
    NewMessage(user, NbRecipesCountObject, value)

(***************************************************************************)
(* The server operators to update its Fridj and Shopping list.             *)
(***************************************************************************)


(***************************************************************************)
(* Send messages, that is the value of the 'msgs' variable in the second   *)
(* state of a step.                                                        *)
(***************************************************************************)
Send(to, new_msgs) == 
    msgs' = [msgs EXCEPT ![to] = @ \o new_msgs]

NotifyServer(messages) == 
    Send(SERVER, messages)

(***************************************************************************)
(* Actions taken by users.                                                 *)
(* The first is when users add items in the shopping list.                 *)
(***************************************************************************)
AddToShoppingList(user) ==
    \E t \in INGREDIENT_TYPES, n \in 1..MAX_QTTY: 
        LET new_shopping_list == [shoppingList EXCEPT ![user][t] = @ + n]
        IN /\ shoppingList' = new_shopping_list
           /\ NotifyServer(<<ShoppingListMsg(user, new_shopping_list[user])>>)
           /\ UNCHANGED <<fridj, nRecipesMade>>

(***************************************************************************)
(* Next, users add bought items in their fridj instance.                   *)
(***************************************************************************)
BuyIngredients(user) == 
    \E t \in INGREDIENT_TYPES:
        LET bought_n == Min(MAX_QTTY - fridj[user][t], shoppingList[user][t])
            new_shopping_list == [shoppingList EXCEPT ![user][t] = @ - bought_n]
            new_fridj == [fridj EXCEPT ![user][t] = @ + bought_n]
        IN /\ bought_n > 0
           /\ shoppingList' = new_shopping_list
           /\ fridj' = new_fridj
           /\ NotifyServer(<<ShoppingListMsg(user, new_shopping_list[user]), 
                             FridjMsg(user, new_fridj[user])>>)
           /\ UNCHANGED <<nRecipesMade>>

(***************************************************************************)
(* Finally, users cook! They remove items from the fridj.                  *)
(***************************************************************************)
MakeRecipe(user) == 
    \E r \in fj!AllRecipes: 
        LET new_fridj == [fridj EXCEPT ![user] = [t \in DOMAIN @ |-> @[t] - r[t]]]
            new_nRecipesMade == [nRecipesMade EXCEPT ![user] = @ + 1]
        IN /\ \A t \in DOMAIN r: fridj[user][t] >= r[t]
           /\ fridj' = new_fridj
           /\ nRecipesMade' = new_nRecipesMade
           /\ NotifyServer(<<FridjMsg(user, new_fridj[user]),
                             NbRecipesCountMsg(user, new_nRecipesMade[user])>>)
           /\ UNCHANGED shoppingList

(***************************************************************************)
(* The server takes the first message in the queue and changes its state.  *)
(* Then a message is sent to notify other users of a change.               *)
(***************************************************************************)
FridjUpdated == 
    LET msg == Head(msgs[SERVER])
    IN /\ msg.object = FridjObject
       /\ fridj' = [fridj EXCEPT ![SERVER] = msg.value]
       /\ msgs' = [msgs EXCEPT ![SERVER] = Tail(@)]
       /\ UNCHANGED <<shoppingList, nRecipesMade>>

ShoppingListUpdated ==
    LET msg == Head(msgs[SERVER])
    IN /\ msg.object = ShoppingListObject
       /\ shoppingList' = [shoppingList EXCEPT ![SERVER] = msg.value]
       /\ msgs' = [msgs EXCEPT ![SERVER] = Tail(@)]
       /\ UNCHANGED <<fridj, nRecipesMade>>

NbRecipesCountUpdated ==
    LET msg == Head(msgs[SERVER])
    IN /\ msg.object = NbRecipesCountObject
       /\ nRecipesMade' = [nRecipesMade EXCEPT ![SERVER] = @ + msg.value]
       /\ msgs' = [msgs EXCEPT ![SERVER] = Tail(@)]
       /\ UNCHANGED <<fridj, shoppingList>>

ServerSync ==
    /\ msgs[SERVER] /= <<>>
    /\ FridjUpdated \/ ShoppingListUpdated \/ NbRecipesCountUpdated

Next == 
    \/ \E u \in FinalUsers:  
        \/ AddToShoppingList(u) 
        \/ BuyIngredients(u) 
        \/ MakeRecipe(u)
    \/ ServerSync

Init == 
    /\ fridj = [u \in USERS |-> [t \in INGREDIENT_TYPES |-> 0]]
    /\ shoppingList = [u \in USERS |-> [t \in INGREDIENT_TYPES |-> 0]]
    /\ nRecipesMade = [u \in USERS |-> 0]
    /\ msgs = [u \in USERS |-> <<>>]

Spec == Init /\ [][Next]_vars
FairSpec == 
    /\ Spec
    /\ \A u \in USERS: /\ WF_vars(BuyIngredients(u)) 
                       /\ WF_vars(MakeRecipe(u))
                       /\ WF_vars(AddToShoppingList(u))

THEOREM Spec => fj!Spec
THEOREM FairSpec => fj!FairSpec

TempInv == <>(\A u \in USERS: nRecipesMade[u] > 0)

=============================================================================
\* Modification History
\* Last modified Mon Jul 29 18:32:33 CEST 2024 by davd33
\* Created Thu Jul 25 23:17:45 CEST 2024 by davd33
