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
const_1723739047361540000 == 
{banana, orange, kiwi}
----

\* MV CONSTANT definitions USERS
const_1723739047361541000 == 
{davd, mj}
----

\* SYMMETRY definition
symm_1723739047361542000 == 
Permutations(const_1723739047361540000) \union Permutations(const_1723739047361541000)
----

\* CONSTANT definitions @modelParameterConstants:1MAX_QTTY
const_1723739047361543000 == 
3
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1723739047361544000 ==
0..1000
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1723739047361545000 ==
/\ \A u \in USERS: \A id \in Ids(u): userData[u][id].cnt < 3
/\ \A t \in INGREDIENT_TYPES, u \in USERS: \A id \in Ids(u): userData[u][id].shop[t] < 3
/\ \A t \in INGREDIENT_TYPES, u \in USERS: \A id \in Ids(u): userData[u][id].frdj[t] < 3
/\ \A u \in USERS: Len(msgs[u]) < 10
----
=============================================================================
\* Modification History
\* Created Thu Aug 15 18:24:07 CEST 2024 by Davd
