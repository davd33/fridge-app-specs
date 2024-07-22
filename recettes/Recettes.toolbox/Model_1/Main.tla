-------------------------------- MODULE Main --------------------------------

EXTENDS TLC, Sequences, FiniteSets, Integers, PT
CONSTANTS INGREDIENTS, MAX_QTTY, USERS

\* Ingredient records have an type (banana...) and a integer quantity
AllIngredientSets == 
    {x \in (SUBSET [type: INGREDIENTS, qtty: 1..MAX_QTTY]): 
        ~ \E i, j \in x: i /= j /\ i.type = j.type} \ {{}}

(* --algorithm recettes
variables fridge = {},
          recipe_items = [u \in USERS |-> {}];

define
\* Recipes with all ingredients available in the fridge
CraftableRecipes == 
    {r \in AllIngredientSets: \A item \in r: \E elt \in fridge: 
        item.type = elt.type /\ item.qtty <= elt.qtty}

EnoughInFridgeForARecipe ==
    Cardinality(CraftableRecipes) > 0

NoOtherUserInTheKitchen(user) ==
    ~ \E u \in USERS: u /= user /\ recipe_items[u] /= {}

GetOneRecipe ==
    CHOOSE r \in CraftableRecipes: TRUE
    
GetBoughtItems ==
    CHOOSE is \in AllIngredientSets: TRUE
end define;

fair+ process client \in USERS
variable bought_items = {},
         n_recipes = 0;

begin Client:
    while TRUE do
        either
            BuyIngredients:
            bought_items := GetBoughtItems;
            FillFridge:
            while bought_items /= {} do
                with b_item \in bought_items do 
                    fridge := IF \E i \in fridge: i.type = b_item.type
                              THEN LET f_item == CHOOSE i \in fridge: i.type = b_item.type
                                   IN (fridge \ {f_item}) \union {[type |-> b_item.type, qtty |-> f_item.qtty + b_item.qtty]}
                              ELSE fridge \union {b_item};
                    bought_items := bought_items \ {b_item};
                end with;
            end while;
        or
            await EnoughInFridgeForARecipe;
            ChooseRecipe:
            await EnoughInFridgeForARecipe /\ NoOtherUserInTheKitchen(self);
            recipe_items[self] := GetOneRecipe;
            MakeRecipe:
            while recipe_items[self] /= {} do
                with r_item \in recipe_items[self] do 
                    fridge := LET f_item == CHOOSE i \in fridge: i.type = r_item.type
                                  new_item == [type |-> r_item.type, qtty |-> f_item.qtty - r_item.qtty]
                              IN (fridge \ {f_item}) \union IF new_item.qtty > 0 THEN {new_item} ELSE {};
                    recipe_items[self] := recipe_items[self] \ {r_item};
                end with;
            end while;
            n_recipes := n_recipes + 1;
        end either;
    end while;
end process;
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "561b9c1c" /\ chksum(tla) = "f186b71f")
VARIABLES pc, fridge, recipe_items

(* define statement *)
CraftableRecipes ==
    {r \in AllIngredientSets: \A item \in r: \E elt \in fridge:
        item.type = elt.type /\ item.qtty <= elt.qtty}

EnoughInFridgeForARecipe ==
    Cardinality(CraftableRecipes) > 0

NoOtherUserInTheKitchen(user) ==
    ~ \E u \in USERS: u /= user /\ recipe_items[u] /= {}

GetOneRecipe ==
    CHOOSE r \in CraftableRecipes: TRUE

GetBoughtItems ==
    CHOOSE is \in AllIngredientSets: TRUE

VARIABLES bought_items, n_recipes

vars == << pc, fridge, recipe_items, bought_items, n_recipes >>

ProcSet == (USERS)

Init == (* Global variables *)
        /\ fridge = {}
        /\ recipe_items = [u \in USERS |-> {}]
        (* Process client *)
        /\ bought_items = [self \in USERS |-> {}]
        /\ n_recipes = [self \in USERS |-> 0]
        /\ pc = [self \in ProcSet |-> "Client"]

Client(self) == /\ pc[self] = "Client"
                /\ \/ /\ pc' = [pc EXCEPT ![self] = "BuyIngredients"]
                   \/ /\ EnoughInFridgeForARecipe
                      /\ pc' = [pc EXCEPT ![self] = "ChooseRecipe"]
                /\ UNCHANGED << fridge, recipe_items, bought_items, n_recipes >>

BuyIngredients(self) == /\ pc[self] = "BuyIngredients"
                        /\ bought_items' = [bought_items EXCEPT ![self] = GetBoughtItems]
                        /\ pc' = [pc EXCEPT ![self] = "FillFridge"]
                        /\ UNCHANGED << fridge, recipe_items, n_recipes >>

FillFridge(self) == /\ pc[self] = "FillFridge"
                    /\ IF bought_items[self] /= {}
                          THEN /\ \E b_item \in bought_items[self]:
                                    /\ fridge' = (IF \E i \in fridge: i.type = b_item.type
                                                  THEN LET f_item == CHOOSE i \in fridge: i.type = b_item.type
                                                       IN (fridge \ {f_item}) \union {[type |-> b_item.type, qtty |-> f_item.qtty + b_item.qtty]}
                                                  ELSE fridge \union {b_item})
                                    /\ bought_items' = [bought_items EXCEPT ![self] = bought_items[self] \ {b_item}]
                               /\ pc' = [pc EXCEPT ![self] = "FillFridge"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Client"]
                               /\ UNCHANGED << fridge, bought_items >>
                    /\ UNCHANGED << recipe_items, n_recipes >>

ChooseRecipe(self) == /\ pc[self] = "ChooseRecipe"
                      /\ EnoughInFridgeForARecipe /\ NoOtherUserInTheKitchen(self)
                      /\ recipe_items' = [recipe_items EXCEPT ![self] = GetOneRecipe]
                      /\ pc' = [pc EXCEPT ![self] = "MakeRecipe"]
                      /\ UNCHANGED << fridge, bought_items, n_recipes >>

MakeRecipe(self) == /\ pc[self] = "MakeRecipe"
                    /\ IF recipe_items[self] /= {}
                          THEN /\ \E r_item \in recipe_items[self]:
                                    /\ fridge' = (LET f_item == CHOOSE i \in fridge: i.type = r_item.type
                                                      new_item == [type |-> r_item.type, qtty |-> f_item.qtty - r_item.qtty]
                                                  IN (fridge \ {f_item}) \union IF new_item.qtty > 0 THEN {new_item} ELSE {})
                                    /\ recipe_items' = [recipe_items EXCEPT ![self] = recipe_items[self] \ {r_item}]
                               /\ pc' = [pc EXCEPT ![self] = "MakeRecipe"]
                               /\ UNCHANGED n_recipes
                          ELSE /\ n_recipes' = [n_recipes EXCEPT ![self] = n_recipes[self] + 1]
                               /\ pc' = [pc EXCEPT ![self] = "Client"]
                               /\ UNCHANGED << fridge, recipe_items >>
                    /\ UNCHANGED bought_items

client(self) == Client(self) \/ BuyIngredients(self) \/ FillFridge(self)
                   \/ ChooseRecipe(self) \/ MakeRecipe(self)

Next == (\E self \in USERS: client(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in USERS : SF_vars(client(self))

\* END TRANSLATION 

\* INVARIANTS
TypeOK == 
    /\ fridge = {} \/ \A i \in fridge: i.type \in INGREDIENTS /\ i.qtty > 0

\* PROPERTIES
BuysIngredientsInFridge == \E self \in ProcSet: pc[self] = "BuyIngredients" ~> fridge /= {}

MakeRecipeHappens == <>(\E self \in ProcSet: pc[self] = "MakeRecipe")


=============================================================================
\* Modification History
\* Last modified Sun Jul 21 00:11:52 CEST 2024 by davd33
\* Created Wed Jul 17 21:03:29 CEST 2024 by davd33
