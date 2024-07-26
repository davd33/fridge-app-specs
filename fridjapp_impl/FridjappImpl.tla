---------------------------- MODULE FridjappImpl ----------------------------

EXTENDS Integers

CONSTANTS INGREDIENT_TYPES, MAX_QTTY, USERS

VARIABLES fridj, nRecipesMade, nRecipesMadeByUser

fj == INSTANCE fridjapp 

TypeOK == 
    /\ fj!TypeOK
    /\ nRecipesMadeByUser \in [USERS -> Nat]

vars == <<fridj, nRecipesMade, nRecipesMadeByUser>>

Min(a, b) == IF a < b THEN a ELSE b

BuyIngredients(user) == 
    \E t \in INGREDIENT_TYPES, n \in 1..MAX_QTTY: 
        /\ fridj' = [fridj EXCEPT ![t] = Min(MAX_QTTY, @ + n)]
        /\ UNCHANGED <<nRecipesMade, nRecipesMadeByUser>>

MakeRecipe(user) == 
    \E r \in fj!AllRecipes: 
        /\ \A t \in DOMAIN r: fridj[t] >= r[t]
        /\ fridj' = [t \in DOMAIN fridj |-> fridj[t] - r[t]]
        /\ nRecipesMade' = nRecipesMade + 1
        /\ nRecipesMadeByUser' = [nRecipesMadeByUser EXCEPT ![user] = @ + 1]

Next == \E u \in USERS: BuyIngredients(u) \/ MakeRecipe(u)

Init == 
    /\ fridj = [t \in INGREDIENT_TYPES |-> 0]
    /\ nRecipesMade = 0
    /\ nRecipesMadeByUser = [u \in USERS |-> 0]

Spec == Init /\ [][Next]_vars
FairSpec == 
    /\ Spec
    /\ \A u \in USERS: /\ WF_vars(BuyIngredients(u)) 
                       /\ WF_vars(MakeRecipe(u))

THEOREM Spec => fj!Spec
THEOREM FairSpec => fj!FairSpec

TempInv == <>(\A u \in USERS: nRecipesMadeByUser[u] > 0)

=============================================================================
\* Modification History
\* Last modified Fri Jul 26 12:12:46 CEST 2024 by davd33
\* Created Thu Jul 25 23:17:45 CEST 2024 by davd33
