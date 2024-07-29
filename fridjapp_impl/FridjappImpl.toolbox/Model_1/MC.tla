---- MODULE MC ----
EXTENDS FridjappImpl, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
banana, orange, kiwi
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
davd, mj, server
----

\* MV CONSTANT definitions INGREDIENT_TYPES
const_1722271135478475000 == 
{banana, orange, kiwi}
----

\* MV CONSTANT definitions USERS
const_1722271135478476000 == 
{davd, mj, server}
----

\* CONSTANT definitions @modelParameterConstants:1MAX_QTTY
const_1722271135478477000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3SERVER
const_1722271135478478000 == 
server
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1722271135478479000 ==
/\ \A u \in USERS: nRecipesMade[u] < 3
/\ \A t \in INGREDIENT_TYPES, u \in USERS: shoppingList[u][t] < 3
/\ \A t \in INGREDIENT_TYPES, u \in USERS: fridj[u][t] < 3
/\ \A u \in USERS: Len(msgs[u]) < 10
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1722271135478481000 ==
fj!FairSpec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1722271135478482000 ==
fj!TempInv
----
=============================================================================
\* Modification History
\* Created Mon Jul 29 18:38:55 CEST 2024 by davd33
