import seplog.e_semantics

/-
 - Propositions about Stores+Heaps
 -/

section asserts
  def Assert := Store → Heap →  Prop
  def TT: Assert := λ _ _, true
  def FF: Assert := λ _ _, false
  def And (P Q: Assert): Assert:= λ s h, P s h ∧ Q s h

  notation x ` ⋀ ` e  := (And x e)

  instance: has_top Assert := ⟨TT⟩ -- ⊤
  instance: has_bot Assert := ⟨FF⟩ -- ⊥


  /-
   - Separation conjunction. Says that P and Q hold independently of each other
   - (i.e. depend on distinct heaplets)
   -/
  def a_con (P Q: Assert): Assert := λ (s: Store) (h: Heap),
	   ∃ h1 h2, (h1 # h2) ∧ (h = h1 ++ h2) ∧ (P s h1) ∧ (Q s h2).

  notation x ` ∗ ` e  := (a_con x e) -- **

  /-
   - Separation implication
   - whenever the current heaplet is extended with a separate heaplet satisfying
   - P, the resulting  combined  heaplet  will  satisfy  Q
   -/
  def a_imp (P Q:Assert) : Assert := λ s h,
    ∀ h', (h # h') ∧ P s h' →
      ∀ h'', h'' = h ++ h' → Q s h''.

  notation x ` ⊸ ` e  := (a_imp x e)

  def a_entails (P Q:Assert) : Prop := ∀ s h, P s h → Q s h.

  notation x ` ⟹ ` e  := (a_entails x e) -- ==>

  def a_equiv (P Q:Assert) : Prop := ∀ s h, P s h ↔ Q s h.

  notation x ` ⟺ ` e  := (a_equiv x e)

end asserts

axiom assert_ext: ∀ P Q, (P ⟺ Q) → P = Q. -- axiom cannot be in section

section assert_lemmas
  open TypeDecl
  lemma con_com_equiv : ∀ P Q, (P ∗ Q) = (Q ∗ P) := sorry.

  lemma con_assoc: ∀ P Q R, (P ∗ Q) ∗ R ⟹ (P ∗ (Q ∗ R)) := sorry.
  lemma con_assoc_equiv : ∀ P Q R, ((Q ∗ P) ∗ R) = (Q ∗ (P ∗ R)) := sorry.
  lemma mp : ∀ P Q, Q ∗ (Q ⊸ P) ⟹ P := sorry

  lemma monotony : ∀ (P1 P2 Q1 Q2: Assert) (s: Store) (h: Heap),
	    ((∀ h', P1 s h' → P2 s h') ∧ (∀ h'', Q1 s h'' → Q2 s h'')) →
	    ((P1 ∗ Q1) s h → (P2 ∗ Q2) s h) := sorry.

  lemma monotony': ∀ P1 P2 P3 P4,
    (P1 ⟹ P2) →
    (P3 ⟹ P4) →
    (P1 ∗ P3 ⟹ (P2 ∗ P4)) := sorry.

  lemma monotony'': ∀ P1 P2 P3 P4,
    (P2 ⟹ P1) →
    (P3 ⟹ P4) →
    (P1 ⊸ P3 ⟹ (P2 ⊸ P4)) := sorry.

  lemma adjunction : ∀ (P1 P2 P3:Assert),
      ∀ s,
        (∀ h, (P1 ∗ P2) s h → P3 s h) →
        (∀ h, P1 s h → (P2 ⊸ P3) s h) := sorry.

  lemma adjunction' : ∀ (P1 P2 P3:Assert),
    ∀ s,
      (∀ h, P1 s h → (P2 ⊸ P3) s h) →
        (∀ h, (P1 ∗ P2) s h → P3 s h) := sorry.

  lemma imp_reg : ∀ P Q, P ⟹ (Q ⊸ (P ∗ Q)) := sorry.

  def Sep.emp : Assert := λ _ h, h = ∅.
  instance: has_emptyc Assert := ⟨Sep.emp⟩

  lemma con_emp: ∀ P, (P ∗ Sep.emp) ⟹ P := sorry.

  lemma con_emp': ∀ P, P  ⟹ (P ∗ Sep.emp) := sorry.

  lemma con_cons  (P Q : Assert) (s: Store) (h1 h2: Heap): (h1 # h2) →
    P s h1 → Q s h2 → (P ∗ Q) s (h1 ++ h2) := sorry.

  lemma semi_distributivity (P1 P2 Q : Assert):
    ((P1 ⋀ P2) ∗ Q) ⟹ ((P1 ∗ Q) ⋀ (P2 ∗ Q)) := sorry.

  /-
   - Pure assertions - independent of the heap
   -/

  def Pure (Q : Assert) := ∀ s h h', Q s h ↔ Q s h'.

  lemma con_and_pure (P Q R: Assert): Pure R → (((P ∗ Q) ⋀ R) ⟹ (P ∗ (Q ⋀ R)))
    := sorry.

  /-
   - Mapping assertion
   -/
  def mapsto {α: TypeDecl} (e: Expr (gPtr α)) (e': Expr α)
             (s: Store) (h: Heap): Prop :=
      ∃ (p: Address) (v: Val α),
          val2loc (eval e s) = some p
        ∧ eval e' s = some v
        ∧ h = Heap.singleton p v.

  notation x ` ↦ ` e  := (mapsto x e)

  lemma mapsto_con_inversion : ∀ {α: TypeDecl}
    (l: Expr (gPtr α)) (e: Expr α) P s h,
      ((l ↦ e) ∗ P) s h →
        ∃ n: Address,
          val2loc (eval l s) = some n ∧
        ∃ v: Val α,
          eval e s = some v ∧
        ∃ h': Heap,
          h = (Heap.singleton n v) ++ h' ∧ P s h' := sorry.

  def cell_exists {α: TypeDecl} (e1: Expr (gPtr α)) : Assert :=
    λ s h, ∃ (y: Expr α), (e1 ↦ y) s h.

  notation x ` ⤇ ` e  := (cell_exists x e)

  lemma mapsto_equiv' : ∀ {α: TypeDecl} (s s' : Store) (h: Heap)
                          (e1 e3: Expr (gPtr α)) (e2 e4: Expr α),
      (e1 ↦ e2) s' h →
      eval e1 s' = eval e3 s →
      eval e2 s' = eval e4 s →
      (e3 ↦ e4) s h := sorry.
  /-
  - Uses mapsto_equiv'
  -/
  lemma mapsto_equiv : ∀ {α: TypeDecl} (s : Store) (h: Heap)
                          (e1 e3: Expr (gPtr α)) (e2 e4: Expr α),
        (e1 ↦ e2) s h →
        eval e1 s = eval e3 s →
        eval e2 s = eval e4 s →
        (e3 ↦ e4) s h := sorry.

  def inde (l:list (Σ α, Var α)) (P:Assert) :=
      ∀ s h,
        (∀ (α: TypeDecl) (x: Val α) (v: Var α),
          ((sigma.mk α v) ∈ l) → (P s h <-> P (s.update  x v.name) h))
      .

  lemma inde_update_store : ∀ {α: TypeDecl} (P:Assert) (x: Var α)
                              (z: Val α) (s: Store) (h: Heap),
    inde [⟨_, x⟩] P ->
      P s h ->
      P (s.update z x.name) h := sorry.

  lemma inde_update_store' : ∀ {α: TypeDecl} (P:Assert) (x: Var α)
                              (z: Val α) (s: Store) (h: Heap),
      inde [⟨_,x⟩] P →
      P (s.update z x.name) h →
      P s h := sorry.

  lemma inde_TT : ∀ {α: TypeDecl} (l:list (Σ α, Var α)), inde l TT := sorry.

  lemma inde_sep_con : ∀ {α: TypeDecl} (l:list (Σα, Var α)) (P Q:Assert),
    inde l P → inde l Q →
      inde l (P ∗ Q) := sorry.

	lemma inde_sep_imp : ∀ {α: TypeDecl} (l:list (Σα, Var α)) (P Q:Assert),
	  inde l P → inde l Q →
	  inde l (P ⊸ Q) := sorry.

end assert_lemmas

