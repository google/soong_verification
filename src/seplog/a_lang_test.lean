import utils
import seplog.a_lang

open TypeDecl open Val

/-
 - The default Go type
 -/
run_cmd test TypeDecl.inhabited.default gInt


/-
 - Type enforcement
 -/

run_cmd test (as_type (pBool tt) gBool) (some tt)
run_cmd test none $ as_type (pBool tt) gInt -- expected a Val gInt
run_cmd test (as_type_opt (some (pBool tt)) gBool) (some tt)
run_cmd test none $ @as_type_opt gBool none gBool

/-
 - Printing
 -/
run_cmd test_str "*MyStruct" $ gPtr (gRef "MyStruct")



/-
 - Instance of a linked list class
 -/
def ll_inst: Val (gRef "LL") :=
    list_to_struct "LL" [("val", ⟨_,pInt 1⟩),
                         ("next", ⟨_,pPtr (gRef "LL") (some 1)⟩) ]

run_cmd test (ll_inst.get "val").iget.2 (pInt 1)

run_cmd test_str "LL{next: 1, val: 1}" ll_inst

/-
 - Instance of a type isomorphic to a tuple of linked lists.
 -/
def struct_pair_inst:= list_to_struct "LLPair"
    [("ll1", ⟨_, ll_inst⟩), ("ll2", ⟨_, ll_inst⟩)]
