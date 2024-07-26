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
const_1721988778638538000 == 
{banana, orange, kiwi}
----

\* MV CONSTANT definitions USERS
const_1721988778638539000 == 
{davd, mj}
----

\* CONSTANT definitions @modelParameterConstants:1MAX_QTTY
const_1721988778638540000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1721988778638541000 ==
\A u \in USERS: nRecipesMadeByUser[u] < 10
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1721988778638543000 ==
fj!FairSpec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1721988778638544000 ==
fj!TempInv
----
=============================================================================
\* Modification History
\* Created Fri Jul 26 12:12:58 CEST 2024 by davd33
