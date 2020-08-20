import seplog.a_lang
import utils             -- join, pairmap/alist things
import data.finmap
import order.basic
import logic.function.basic

section heaps
  open TypeDecl open Val

  -- Memory addresses are just represented as integers
  @[derive decidable_eq]
  structure Address := (val: ℤ)

  def to_z (a:Address): ℤ := a.val

  /-
   - Bijection which can be used to transport lemmas about integers
   -/
  def bij_address: equiv Address ℤ :=
    { to_fun := to_z,
      inv_fun := Address.mk,
      left_inv := by {rintro ⟨n⟩, refl},
      right_inv := by {intro n, refl}}

  lemma to_z_inj: function.injective to_z := bij_address.injective

  def val2loc: Π {t}, option (Val (gPtr t)) → option (Address)
   | _ (some (pPtr _ p)) := p >>= (λ i, some ⟨i⟩)
   | _ none              := none

  def str_address (a: Address): string := to_string a.val

  instance: has_to_string Address := ⟨str_address⟩
  instance: has_repr Address      := ⟨str_address⟩
  instance: has_zero Address      := ⟨Address.mk 0⟩
  instance: has_one Address       := ⟨Address.mk 1⟩
  instance: has_add Address       := ⟨λ x y, ⟨x.val + y.val⟩⟩

  -- Heap is a map from address to Go values
  @[derive decidable_eq]
  structure Heap :=
    (vals: finmap (λ _: Address, Σ dt: TypeDecl, Val dt))

  /-
   - Bijection which can be used to transport lemmas about finmaps
   -/
  def bij_heap : equiv Heap
                      (finmap (λ _: Address, Σ dt: TypeDecl, Val dt)) :=
    { to_fun    := λ h, h.vals,
      inv_fun   := Heap.mk,
      left_inv  := by {rintro ⟨n⟩, refl},
      right_inv := by {intro n, refl}}

  @[simp]
  def Heap.emp : Heap := ⟨∅⟩
  instance: has_emptyc Heap := ⟨Heap.emp⟩
  instance: inhabited Heap := ⟨Heap.emp⟩

  def Heap.singleton  {dt: TypeDecl} (a: Address) (v: Val dt): Heap:=
    ⟨finmap.singleton a ⟨dt, v⟩⟩

  def Heap.lookup  {t: TypeDecl} (h: Heap)
                   (p: Address): option (Val t)
      := h.vals.lookup p >>= λ ⟨_,v⟩, as_type v t

  def Heap.update (s: Heap) {t: TypeDecl}
                  (v: Val t) (key: Address): Heap :=
      ⟨s.vals.insert key ⟨t,v⟩⟩

  def Heap.erase (h: Heap)(p: Address): Heap := ⟨h.vals.erase p ⟩

  @[simp]
  def Heap.disjoint (a: Heap) (b:Heap): Prop := a.vals.disjoint b.vals
  notation x ` # ` e  := (Heap.disjoint x e) -- **

  def Heap.append  (a b: Heap): Heap :=
    ⟨a.vals.union b.vals⟩
  instance heap_append: has_append (Heap):= ⟨Heap.append⟩

  instance: decidable_linear_order Address :=
    decidable_linear_order.lift to_z to_z_inj

  /-
   - Inserts into an unused address. Returns updated Heap and the fresh address.
   - Because pointers default to zero, we make the minimum value equal to 1 so
   - that nothing gets accidentally pointed to.
   -/
  def Heap.insert (s: Heap) (t: TypeDecl) (v: Val t): Heap × Address :=
    let p := (s.vals.keys.max.elim 1 (λ a, a+1)) in
        (@Heap.update s t v p, p)


  meta def str_heap (h: Heap): string := show_finmap h.vals

  meta instance: has_to_string Heap:= ⟨str_heap⟩
  meta instance: has_repr Heap:= ⟨str_heap⟩

  lemma emp_disjoint: ∀ h: Heap, ∅ # h := begin
    intros, simp, apply finmap.disjoint_empty,
  end

end heaps

section stores

  @[derive decidable_eq]
  structure Store :=
    (vals: finmap (λ _: string, Σ dt: TypeDecl, Val dt))

  /-
   - Bijection which can be used to transport lemmas about finmaps
   -/
  def bij_store: equiv Store
                       (finmap (λ _: string, Σ dt: TypeDecl, Val dt)) :=
  { to_fun    := λ h, h.vals,
    inv_fun   := Store.mk,
    left_inv  := by {rintro ⟨n⟩, refl},
    right_inv := by {intro n, refl}}

  def Store.emp: Store := ⟨∅⟩
  instance: has_emptyc Store := ⟨Store.emp⟩
  instance: inhabited  Store := ⟨Store.emp⟩

  def Store.singleton  {dt: TypeDecl} (a: string)
                      (v: Val dt): Store:=
    ⟨finmap.singleton a ⟨dt, v⟩⟩

  def Store.update  (s: Store) {t: TypeDecl}
                    (v: Val t) (key: string) : Store :=
      ⟨s.vals.insert key ⟨t,v⟩⟩

  def Store.updates: Store → list (string × Σ t, Val t) →  Store
   | s []                  := s
   | s ((a,⟨typ, val⟩)::t) := @Store.update (Store.updates s t) typ val a

  def Store.from_list (l: list (string × Σ t, Val t)): Store :=
    Store.updates ∅ l

  def Store.lookup  {t: TypeDecl} (h: Store)
                   (p: string): option (Val t)
      := h.vals.lookup p >>= λ ⟨_,v⟩, as_type v t

  meta def str_store (h: Store): string := show_finmap h.vals

  meta instance: has_to_string Store := ⟨str_store⟩
  meta instance: has_repr Store      := ⟨str_store⟩

end stores
