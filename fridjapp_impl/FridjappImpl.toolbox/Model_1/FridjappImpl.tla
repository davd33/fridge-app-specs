---------------------------- MODULE FridjappImpl ----------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS INGREDIENT_TYPES, MAX_QTTY, USERS

VARIABLES fridj, shoppingList, nRecipesMade

PT == INSTANCE PT

(***************************************************************************)
(* Sum up all integers in function FUN.                                    *)
(***************************************************************************)
Sum(fun) == PT!ReduceSet(LAMBDA k, acc: acc + fun[k],
                         DOMAIN fun, 0)

(***************************************************************************)
(* Refinement mapping: the number of recipes split by users is summed up.  *)
(***************************************************************************)
fj == INSTANCE fridjapp WITH nRecipesMade <- Sum(nRecipesMade)

TypeOK == 
    /\ fridj \in [INGREDIENT_TYPES -> Nat]
    /\ shoppingList \in [INGREDIENT_TYPES -> Nat]
    /\ nRecipesMade \in [USERS -> Nat]

vars == <<fridj, shoppingList, nRecipesMade>>

Min(a, b) == IF a < b THEN a ELSE b

AddToShoppingList(user) ==
    \E t \in INGREDIENT_TYPES, n \in 1..MAX_QTTY: 
        /\ shoppingList' = [shoppingList EXCEPT ![t] = @ + n]
        /\ UNCHANGED <<fridj, nRecipesMade>>

BuyIngredients(user) == 
    \E t \in INGREDIENT_TYPES:
        LET bought_n == Min(MAX_QTTY - fridj[t], shoppingList[t])
        IN /\ bought_n > 0
           /\ shoppingList' = [shoppingList EXCEPT ![t] = @ - bought_n]
           /\ fridj' = [fridj EXCEPT ![t] = @ + bought_n]
           /\ UNCHANGED <<nRecipesMade>>

MakeRecipe(user) == 
    \E r \in fj!AllRecipes: 
        /\ \A t \in DOMAIN r: fridj[t] >= r[t]
        /\ fridj' = [t \in DOMAIN fridj |-> fridj[t] - r[t]]
        /\ nRecipesMade' = [nRecipesMade EXCEPT ![user] = @ + 1]
        /\ UNCHANGED shoppingList

Next == \E u \in USERS: 
    \/ AddToShoppingList(u) 
    \/ BuyIngredients(u) 
    \/ MakeRecipe(u)

Init == 
    /\ fridj = [t \in INGREDIENT_TYPES |-> 0]
    /\ shoppingList = [t \in INGREDIENT_TYPES |-> 0]
    /\ nRecipesMade = [u \in USERS |-> 0]

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
\* Last modified Sat Jul 27 08:31:03 CEST 2024 by davd33
\* Created Thu Jul 25 23:17:45 CEST 2024 by davd33
