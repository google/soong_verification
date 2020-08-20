import seplog.c_program
import seplog.b_memory_test

open TypeDecl open Val open Expr open Binop open cmd

/-
 - Variable declaration
 -/
def va: Var gBool := ⟨"a"⟩
def vy: Var gInt  := ⟨"y"⟩

/-
 - Expression declarations
 -/
def vy': Expr gInt := getvar vy
def yy: Expr gInt:= binop PLUS vy' vy'

def ex_ptr1: Expr (gPtr gInt) := const $ pPtr _ $ some 1
def ex_str: Expr (gRef "LL") := const ll_inst
def ex_update := update_field ex_str "val" goZero

/-
 - Extracting type level info to term level
 -/
run_cmd test yy.gotype gInt
run_cmd test goTrue.gotype gBool

/-
 - Evaluating variables w/r/t a Store
 -/

run_cmd test (some $ pBool tt) $ get_var va exStore
run_cmd test none $ get_var va exEmpStore

/-
 - Example program commands
 -/
def assign1   := va ⇐ goTrue     -- add the eval of ⊤ to the store under "a"
def lookup1   := vy ↩ ex_ptr1 -- lookup a ptr in the heap, write to store "y"
def mutate_yy := ex_ptr1 ≪ yy
def inf_loop  := while goTrue assign1
def ex_seq    := assign1  ∣  lookup1
def ex_if     := ifte goTrue ex_seq mutate_yy
def ex_call   := call (sum.inr ex_str) "foo" [⟨_, yy⟩] [⟨_,va⟩]
