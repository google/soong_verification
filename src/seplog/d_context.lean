
import seplog.c_program
import seplog.a_lang

import data.finset.basic
import utils

open TypeDecl open Val

section single_decl
  @[derive decidable_eq]
  structure Sig :=
    (args: pairmap string TypeDecl)
    (return: pairmap string TypeDecl)
    (receiver: string) (is_ptr: bool)

  @[derive decidable_eq]
  structure GoStructDecl (s:string) :=
    (fields: pairmap string TypeDecl)
    (methods: pairmap string (Sig × cmd))

  instance: ∀ s, inhabited (GoStructDecl s):= λ_, ⟨⟨∅, ∅⟩⟩
end single_decl

section many_decls

  @[derive decidable_eq]
  structure Decls :=
    (structs: finmap ((λ s: string, Σ _:unit, GoStructDecl s)))

  def Decls.singleton  {s: string} (d: GoStructDecl s): Decls :=
  ⟨finmap.singleton s ⟨(), d⟩⟩

  def Decls.emp : Decls := ⟨∅⟩

  instance: has_emptyc Decls:= ⟨Decls.emp⟩
  instance: inhabited Decls:= ⟨Decls.emp⟩

  instance : ∀ s, has_singleton (GoStructDecl s) (Decls) :=
    λ _, ⟨Decls.singleton⟩


  def list_to_decls: list (Σ s, GoStructDecl s) → Decls
   | []     := Decls.emp -- impossible to have member of ∅
   | (d::t) := ⟨(list_to_decls t).structs.insert d.1 ⟨(), d.2⟩⟩

  def str_decls (d: Decls): string :=  if d = ∅ then "" else
    " - " ++joinstr (d.structs.keys.sort (λ a b, a <= b)) to_string "\n - "

  instance: has_to_string Decls:= ⟨str_decls⟩


end many_decls

section context
  def Ctx := Store × Heap × Decls

  def Ctx.update_store  (s: Ctx) (x: Store):
    Ctx:= ⟨x, s.2⟩

  def Ctx.update_heap  (s: @Ctx) (x: Heap):
    Ctx := ⟨s.1, x, s.2.2⟩

  def Ctx.emp: Ctx := (∅, ∅, ∅)
  instance: has_emptyc Ctx:= ⟨Ctx.emp⟩
  instance: inhabited Ctx:= ⟨Ctx.emp⟩

  /-
   - Access information about a particular method
   -/
  def Ctx.method: Ctx → string → string → option (Sig × cmd)
   | ctx  struct method := do
      ⟨_, decl⟩    ← ctx.2.2.structs.lookup struct,
      ⟨_, sig_cmd⟩ ← decl.methods.lookup method ,
      sig_cmd



  meta def str_ctx (h: Ctx): string :=
    "Store\n"++to_string h.1++"\nHeap\n"++to_string h.2.1
    ++"\nDecls\n"++to_string h.2.2

  meta instance: has_to_string Ctx:= ⟨str_ctx⟩
  meta instance: has_repr Ctx:= ⟨str_ctx⟩

  /-
   - Initialize a value from a type. In the case of GoStructs, we need to look
   - at the global Decls
   -/
  mutual def default, mk_s_list
  with default: Π(dt: TypeDecl), Decls → option (Val dt)

   | (gRef s) c := match c.structs.lookup s with
    | none := none
    | (some ⟨_,⟨s',_⟩⟩) :=
                    have H:(from_pairmap s').sizeof < 1 + s.length := sorry,
                        mk_s_list c (from_pairmap s')
                        >>= λ lst, (some $ list_to_struct s lst)
    end
   | x _ := some $ (Val.inhabited x).default

  with mk_s_list: Decls → list (string × TypeDecl)
                  → option (list (string × (Σ t, Val t)))
    | _ []             := some []
    | d ((key,val)::t) := do d'   ← default val d,
                             tail ← mk_s_list d t,
                             some $ (key, ⟨_, d'⟩)::tail


end context