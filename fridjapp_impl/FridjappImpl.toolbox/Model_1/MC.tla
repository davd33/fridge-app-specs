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
const_1722598287411650000 == 
{banana, orange, kiwi}
----

\* MV CONSTANT definitions USERS
const_1722598287411651000 == 
{davd, mj}
----

\* CONSTANT definitions @modelParameterConstants:1MAX_QTTY
const_1722598287411652000 == 
3
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1722598287411653000 ==
0..1000
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1722598287411654000 ==
/\ \A u \in USERS: \A id \in Ids(u): userData[u][id].cnt < 3
/\ \A t \in INGREDIENT_TYPES, u \in USERS: \A id \in Ids(u): userData[u][id].shop[t] < 3
/\ \A t \in INGREDIENT_TYPES, u \in USERS: \A id \in Ids(u): userData[u][id].frdj[t] < 3
/\ \A u \in USERS: Len(msgs[u]) < 10
----
=============================================================================
\* Modification History
\* Created Fri Aug 02 13:31:27 CEST 2024 by davd33
