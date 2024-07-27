---- MODULE MC ----
EXTENDS FridjappImpl, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
banana, orange, kiwi
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
davd, mj
----

\* MV CONSTANT definitions INGREDIENT_TYPES
const_17220631547701124000 == 
{banana, orange, kiwi}
----

\* MV CONSTANT definitions USERS
const_17220631547701125000 == 
{davd, mj}
----

\* CONSTANT definitions @modelParameterConstants:1MAX_QTTY
const_17220631547701126000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_17220631547701127000 ==
/\ \A u \in USERS: nRecipesMade[u] < 3
/\ \A t \in INGREDIENT_TYPES: shoppingList[t] < 3
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_17220631547701129000 ==
fj!FairSpec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_17220631547701130000 ==
fj!TempInv
----
=============================================================================
\* Modification History
\* Created Sat Jul 27 08:52:34 CEST 2024 by davd33
