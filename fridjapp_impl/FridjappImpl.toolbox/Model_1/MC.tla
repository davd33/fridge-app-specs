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
const_1722059596972988000 == 
{banana, orange, kiwi}
----

\* MV CONSTANT definitions USERS
const_1722059596972989000 == 
{davd, mj}
----

\* CONSTANT definitions @modelParameterConstants:1MAX_QTTY
const_1722059596972990000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1722059596972991000 ==
\A u \in USERS: nRecipesMade[u] < 10
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1722059596972993000 ==
fj!FairSpec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1722059596972994000 ==
fj!TempInv
----
=============================================================================
\* Modification History
\* Created Sat Jul 27 07:53:16 CEST 2024 by davd33
