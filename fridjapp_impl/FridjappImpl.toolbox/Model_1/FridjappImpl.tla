---------------------------- MODULE FridjappImpl ----------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS INGREDIENT_TYPES, MAX_QTTY, USERS

VARIABLES fridj, nRecipesMade

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
    /\ fj!TypeOK
    /\ nRecipesMade \in [USERS -> Nat]

vars == <<fridj, nRecipesMade>>

Min(a, b) == IF a < b THEN a ELSE b

BuyIngredients(user) == 
    \E t \in INGREDIENT_TYPES, n \in 1..MAX_QTTY: 
        /\ fridj' = [fridj EXCEPT ![t] = Min(MAX_QTTY, @ + n)]
        /\ UNCHANGED <<nRecipesMade>>

MakeRecipe(user) == 
    \E r \in fj!AllRecipes: 
        /\ \A t \in DOMAIN r: fridj[t] >= r[t]
        /\ fridj' = [t \in DOMAIN fridj |-> fridj[t] - r[t]]
        /\ nRecipesMade' = [nRecipesMade EXCEPT ![user] = @ + 1]

Next == \E u \in USERS: BuyIngredients(u) \/ MakeRecipe(u)

Init == 
    /\ fridj = [t \in INGREDIENT_TYPES |-> 0]
    /\ nRecipesMade = [u \in USERS |-> 0]

Spec == Init /\ [][Next]_vars
FairSpec == 
    /\ Spec
    /\ \A u \in USERS: /\ WF_vars(BuyIngredients(u)) 
                       /\ WF_vars(MakeRecipe(u))

THEOREM Spec => fj!Spec
THEOREM FairSpec => fj!FairSpec

TempInv == <>(\A u \in USERS: nRecipesMade[u] > 0)

=============================================================================
\* Modification History
\* Last modified Fri Jul 26 21:53:38 CEST 2024 by davd33
\* Created Thu Jul 25 23:17:45 CEST 2024 by davd33
