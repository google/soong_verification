import seplog.e_semantics
import seplog.d_context_test
import data.finset.basic

open Binop open Relop open Unop open TypeDecl open Expr open Val
open cmd

-- Const
--------
run_cmd test (eval (@const gBool tt) ∅) $ some tt

-- Get Var
----------
run_cmd test (eval (getvar $ @Var.mk gBool "x") ∅) none
run_cmd test (eval (getvar $ @Var.mk gBool "x") (@Store.singleton gBool "x" tt))
             $ some tt

-- Relop
--------
run_cmd test (@relop_eval (gInt) EQ
                          (some 1) (some 0)) ff
-- Binop
--------

run_cmd test (@binop_eval gInt PLUS (some 1) (some 2147483647))
             none -- Overflow

run_cmd test (@binop_eval gStr PLUS (some "a") (some "b")) $ some "ab"

-- Unop
--------
run_cmd test (@unop_eval gBool NOT (some tt)) (some ff)

-- Get field
------------
-- TODO

-- Compute
----------
run_cmd test (some ∅) $ compute ∅ skip

run_cmd test (compute ∅ assign1) $ some (@Store.singleton gBool "a" tt, ∅, ∅)

run_cmd test (compute ∅ lookup1) none  -- lookup fails, as heap is empty

def heap_1_10: Heap := Heap.singleton 1 (pInt 10) -- 10 written to memory #1
run_cmd test (compute (∅, heap_1_10, ∅) lookup1)
           $ some (Store.singleton "y" (pInt 10), heap_1_10, ∅)

-- Looks up value at y, doubles, then writes it to address #1 in Heap
run_cmd test (compute (@Store.singleton gInt "y" 10, heap_1_10, ∅) mutate_yy)
           $ some (@Store.singleton gInt "y" 10,
                   @Heap.singleton gInt 1 20, ∅)


def vndk:= gRef "Vndkdep"
def vvndk: Var (gPtr vndk) := ⟨"x"⟩

run_cmd test (compute (∅,∅,imb_decls) $ new vvndk) (some (
  @Store.singleton (gPtr vndk) "x" 1, -- store a pointer to the value
  @Heap.singleton vndk 1 default_vndkdep, -- actual value stored here
  imb_decls))

--------------------------------------------------------------------------------
def ll := gRef "LL"

def callee: Expr (gPtr ll) := const 1
def nullptr: Expr (gPtr ll) := goNil
def llargs: list (Σ α, Expr α) := [⟨_, goTrue⟩, ⟨_, nullptr⟩]

def create_ll_heap: list (ℤ × ℤ) → Heap
 | [] := ∅
 | [(adr, val)]  := @Heap.singleton (gRef "LL") ⟨adr⟩
   (list_to_struct "LL" [("val",  ⟨_, pInt val⟩),
                         ("next", ⟨gPtr ll, pPtr ll none⟩)])
 | ((adr,v)::(nxt,nv)::t)  :=
    @Heap.update (create_ll_heap ((nxt,nv)::t) ) ll
      (list_to_struct "LL" [("val",  ⟨_, pInt v⟩),
                                ("next", ⟨_, pPtr ll (some nxt)⟩)]) ⟨adr⟩

def llctx (vs: list (ℤ × ℤ)): Ctx := (∅, create_ll_heap vs, ll_decl)

#eval render $ llctx [(1,10),(2,20),(1,30)]
/-
 - Updating the value of a struct
 -/
run_cmd test_str -- "val" field has been updated from 1 to 0
"Store
 - x: LL{next: 1, val: 0} (LL)
Heap

Decls
" $ option.iget $ compute ∅ (⟨"x"⟩ ⇐ ex_update)

/-
 - Context fed as input to the cyclic method call
 -/
 def fed_input := option.iget $ method_input_ctx (llctx [(1, 1)]) cycsig
                                                 llargs (sum.inl callee)
run_cmd test_str
"Store
 - first: tt (Bool)
 - head: ? (*LL)
 - this: 1 (*LL)
Heap
 - 1: LL{next: ?, val: 1} (LL)
Decls
 - LL" $ fed_input

/-
 - Resulting output context after executing the program on the above input
 - Note we have added `this_inst` and `res` to the store.
 -/
run_cmd test_str --
"Store
 - first: tt (Bool)
 - head: 1 (*LL)
 - res: ff (Bool)
 - this: 1 (*LL)
 - this_inst: LL{next: ?, val: 1} (LL)
Heap
 - 1: LL{next: ?, val: 1} (LL)
Decls
 - LL" (compute fed_input cycprog).iget

/-
 - Create input, run command, and extract output. Only change to context is the
 - storage of the result in the variable 'x' in the store.
 -/
meta def run_cyc (lst: list (ℤ × ℤ)): option bool :=
  (@Store.lookup gBool -- getting the result at 'x'
    (prod.fst -- extract the store component of the result context
      $ option.iget -- if program fails just return empty store
        $ compute (llctx lst) -- use input data to create Ctx prior to call
            (call (sum.inl callee) "cyclic" -- call w/ the LL in heap pos #1
                llargs -- (first=true, head=NULL)
                    [⟨gBool, ⟨"x"⟩⟩])) -- write result to this variable
  "x") >>= some ∘ bval -- (last argument for Store.lookup)

-- 3-cycle
run_cmd test (run_cyc [(1, 10), (2, 30), (1, 20)]) (some tt)
-- 1-cycle
run_cmd test (run_cyc [(1, 10), (1,10)]) (some tt)
-- Not a cycle
run_cmd test (run_cyc [(1, 10)]) (some ff)

-- Program error b/c we initially call method with a pointer to a LL at heap#1.
run_cmd test (run_cyc [(2, 10)]) none

-- spec
def is_cyclic': finset ℤ → list (ℤ × ℤ) → bool
 | seen [] := ff
 | seen ((h,_)::t) := if h ∈ seen then tt else is_cyclic' (seen ∪ {h}) t

def is_cyclic (l: list (ℤ × ℤ)): bool:= is_cyclic' ∅ l

-- Look up a boolean variable named "res" in the store of a context
def extract (c: option Ctx): option bool:=
  c >>= λ ⟨s,_,_⟩, @Store.lookup gBool s "res" >>= some ∘ bval

/-
 - The program always terminates and always returns the same result as is_cyclic
 -/
theorem cyc_meets_spec: ∀ (lst: list (ℤ × ℤ)) (res: Ctx),
    exec (some $ llctx lst) cycprog res
    → some (is_cyclic lst) = extract res :=  sorry

