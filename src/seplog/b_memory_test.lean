import seplog.b_memory
import seplog.a_lang_test

open TypeDecl open Val

/-
 - Abbreviation
 -/
def to_m {α: Type*} [decidable_eq α] {β: α → Type*} (l: list (sigma β))
          : finmap β:= list.to_finmap l

/-
 - Interconverting GoInt and Address
 -/


run_cmd test (some 1) (val2loc (some (pPtr gInt $ some 1)))

/-
 - Heap operations
 -/
def exHeap: Heap := Heap.mk $ to_m [⟨1, gBool, pBool tt⟩,
                                    ⟨0, gInt, (3:ℤ)⟩]

def exEmp:= Heap.emp

run_cmd test (Heap.mk  $ to_m [⟨0, gBool, pBool tt⟩])
             (Heap.singleton 0 $ pBool tt)

run_cmd test none $ @Heap.lookup gBool exEmp 0
run_cmd test (some $ pBool tt) $ exHeap.lookup 1

run_cmd test (exHeap.update (pBool ff) 1)
             (Heap.mk $ to_m [⟨1, _, pBool ff⟩, ⟨0, _, pInt 3⟩])

run_cmd test exHeap (exHeap ++ exHeap)
run_cmd test exHeap (exHeap ++ exEmp)

run_cmd test_str
" - 0: 3 (Int)
 - 1: tt (Bool)" exHeap

/-
 - Stores
 -/


def exStore: Store  := Store.mk $ to_m [⟨"a", _, pBool tt⟩,
                                        ⟨"b", _, pInt 3⟩]

def exEmpStore := Store.emp

run_cmd test (exStore.update (pBool ff) "a")
             (Store.mk $ to_m [⟨"a", _, pBool ff⟩, ⟨"b", _, pInt 3⟩])

run_cmd test_str
" - a: tt (Bool)
 - b: 3 (Int)" exStore
