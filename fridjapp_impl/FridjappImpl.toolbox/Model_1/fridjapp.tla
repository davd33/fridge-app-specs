------------------------------ MODULE fridjapp ------------------------------

EXTENDS Sequences, Integers

CONSTANTS INGREDIENT_TYPES, MAX_QTTY
VARIABLES fridj, nRecipesMade

AllRecipes == 
    [INGREDIENT_TYPES -> 0..MAX_QTTY] \ {[t \in INGREDIENT_TYPES |-> 0]}

TypeOK == 
    /\ fridj \in [INGREDIENT_TYPES -> 0..MAX_QTTY]
    /\ nRecipesMade \in Nat

vars == <<fridj, nRecipesMade>>

Min(a, b) == IF a < b THEN a ELSE b

BuyIngredients == 
    \E t \in INGREDIENT_TYPES, n \in 1..MAX_QTTY: 
        /\ fridj' = [fridj EXCEPT ![t] = Min(MAX_QTTY, @ + n)]
        /\ UNCHANGED nRecipesMade

MakeRecipe == 
    \E r \in AllRecipes: 
        /\ \A t \in DOMAIN r: fridj[t] >= r[t]
        /\ fridj' = [t \in DOMAIN fridj |-> fridj[t] - r[t]]
        /\ nRecipesMade' = nRecipesMade + 1 

Init == 
    /\ fridj = [t \in INGREDIENT_TYPES |-> 0]
    /\ nRecipesMade = 0

Next == BuyIngredients \/ MakeRecipe

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(MakeRecipe) /\ WF_vars(BuyIngredients)

TempInv == <>(nRecipesMade > 0)

=============================================================================
\* Modification History
\* Last modified Mon Jul 29 16:12:04 CEST 2024 by davd33
\* Created Thu Jul 25 15:31:23 CEST 2024 by davd33
