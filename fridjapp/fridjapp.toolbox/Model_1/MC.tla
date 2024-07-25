---- MODULE MC ----
EXTENDS fridjapp, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
orange, banana, kiwi
----

\* MV CONSTANT definitions INGREDIENT_TYPES
const_1721930958289396000 == 
{orange, banana, kiwi}
----

\* CONSTANT definitions @modelParameterConstants:1MAX_QTTY
const_1721930958289397000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1721930958289398000 ==
nRecipesMade < 10
----
\* Constant expression definition @modelExpressionEval
const_expr_1721930958289399000 == 
AllRecipes
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1721930958289399000>>)
----

=============================================================================
\* Modification History
\* Created Thu Jul 25 20:09:18 CEST 2024 by davd33
