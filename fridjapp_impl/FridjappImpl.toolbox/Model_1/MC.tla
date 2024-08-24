---- MODULE MC ----
EXTENDS FridjappImpl, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
banana, orange
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
davd, mj, luk
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d, e, f
----

\* MV CONSTANT definitions INGREDIENT_TYPES
const_1724518096497957000 == 
{banana, orange}
----

\* MV CONSTANT definitions USERS
const_1724518096497958000 == 
{davd, mj, luk}
----

\* MV CONSTANT definitions FRIDJ_IDS
const_1724518096497959000 == 
{a, b, c}
----

\* MV CONSTANT definitions MSG_IDS
const_1724518096497960000 == 
{d, e, f}
----

\* SYMMETRY definition
symm_1724518096497961000 == 
Permutations(const_1724518096497957000) \union Permutations(const_1724518096497958000) \union Permutations(const_1724518096497959000) \union Permutations(const_1724518096497960000)
----

\* CONSTANT definitions @modelParameterConstants:1MAX_QTTY
const_1724518096497962000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:6MAX_OP_COUNT
const_1724518096497963000 == 
30
----

=============================================================================
\* Modification History
\* Created Sat Aug 24 18:48:16 CEST 2024 by Davd
