import seplog.f_assertions

section axiomatic_semantics
  open TypeDecl

  /-
   - update the store used in an assertion using the value of an expr
   -/
	def update_store2 {α: TypeDecl} (x: Var α) (e: Expr α) (P: Assert)
                    : Assert :=
    λ s h, (eval e s).elim ⊤ (λ v, P (s.update v x.name) h).

  /-
   - update the store used in an assertion using the value held in a heap
   -/
	def lookup2 {α: TypeDecl} (x: Var α) (e: Expr (gPtr α)) (P: Assert)
              : Assert :=
	  λ s h,
	    ∃ p, val2loc (eval e s) = some p ∧
	      ∃ (z: Val α), h.lookup p = some z ∧
	        P (s.update z x.name) h.

	/-
   - update the heap used in an assertion
   -/
	def update_heap2 {α: TypeDecl} (e:Expr (gPtr α)) (e':Expr α) (P:Assert)
                  : Assert :=
	  λ s h ,
      (eval e' s).elim ⊤ (λ v, -- 2nd expr being an error gives trivial Assert
	    ∃ p, val2loc (eval e s) = some p ∧
	      ∃ (z: Val α), h.lookup p = some z ∧
	        P s (h.update v p)).

  open cmd

	inductive semax: Assert -> cmd -> Assert -> Prop
	  | semax_skip: ∀ P, semax P skip P
	  | semax_assign: ∀ {α: TypeDecl} (P: Assert) (x: Var α) (e: Expr α),
	    semax (update_store2 x e P) (x ⇐ e) P
	  | semax_lookup: ∀ {α: TypeDecl} (P: Assert) (x: Var α) (e: Expr (gPtr α)),
	    semax (lookup2 x e P) (x ↩ e) P
	  | semax_mutation: ∀ {α: TypeDecl} (P: Assert) (e: Expr (gPtr α))
                        (e': Expr α),
	    semax (update_heap2 e e' P) (e ≪ e') P

	  | semax_seq: ∀ P Q R c d,
	    semax P c Q -> semax Q d R -> semax P (c ∣ d) R
	  | semax_while: ∀ (P: Assert) (b: Expr gBool) c,
	    semax (λ s h, (P s h ∧ eval b s = some tt)) c P ->
	    semax P (while b c) (λ s h, P s h ∧ eval b s = some ff)
	  | semax_conseq: ∀ (P P' Q Q':Assert) c,
	    (Q' ⟹ Q) -> (P ⟹ P') ->
	    semax P' c Q' -> semax P c Q
	  | semax_ifte: ∀ (P Q: Assert) (b: Expr gBool) c d,
	    semax (λ s h, P s h ∧ eval b s = some tt) c Q ->
	    semax (λ s h, P s h ∧ eval b s = some ff) d Q ->
	    semax P (ifte b c d) Q.

  notation `{{ ` P ` }} ` c ` {{` Q `}} `   := (semax P c Q)

	/- axiomatic semantic lemmas -/

	lemma semax_weaken_post : ∀ (P Q Q': Assert) c,
	  (Q' ⟹ Q) -> {{ P }} c {{ Q' }} -> {{ P }} c {{ Q }} := sorry.

  lemma semax_strengthen_pre : ∀ (P P':Assert) Q c,
  	  (P ⟹ P') -> {{ P' }} c {{ Q }} -> {{ P }} c {{ Q }} := sorry.

    /- link to operational sematnics-/
  def semax' (P:Assert) (c:cmd) (Q:Assert) : Prop :=
        ∀ s h, (P s h -> ¬(exec (some (s, h)) c none)) ∧
          (∀ s' h', P s h -> (exec (some (s, h)) c  (some (s', h'))) -> Q s' h')

	lemma semax_sound : ∀ P Q c,
	  {{ P }} c {{ Q }} -> semax' P c Q
    := sorry.

  /-
   - Class-definition-dependent assertions
   -/
  def Assert' := Decls → Assert


  def wp_semantics (c: cmd) (Q: Assert'): Assert' :=
      λ d s h,
        ¬ (exec (some (s, h, d))  c none) ∧
        ∀ s' h',
          exec (some (s, h, d)) c  (some (s', h', d)) -> Q d s' h'
          .

	lemma exec_lookup_not_None:
    ∀ {α: TypeDecl} (s: Store) (h: Heap) (d: Decls) (v: Var α)
      (e: Expr (gPtr α)),
        ¬ (exec (some (s, h, d)) (v ↩ e) none) ->
          ∃ p : Address,
            val2loc (eval e s) = some p ∧
            (∃ z: Val α, h.lookup p = some z)
            := sorry.

  lemma exec_mutation_not_None:
    ∀ {α: TypeDecl} (s: Store) (h: Heap) (d: Decls) (e: Expr (gPtr α))
      (e0: Expr α),
        ¬ exec (some (s, h, d)) (e ≪ e0) none ->
        ∃ p : Address,
          val2loc (eval e s) = some p ∧
          (∃ z: Val α, h.lookup p = some z)
          := sorry.

  lemma exec_seq1_not_None: ∀ (s: Store) (h: Heap) (c1 c2: cmd),
      ¬ exec (some (s, h))  (c1 ∣ c2)  none ->
      ¬ exec (some (s, h)) c1 none
      := sorry.

  lemma exec_seq2_not_None:
    ∀ (s: Store) (h: Heap) (c1 c2: cmd) (s': Store) (h': Heap),
      ¬ exec (some (s, h)) (c1 ∣ c2) none ->
      exec (some (s, h)) c1 (some (s',h')) ->
      ¬ exec (some (s', h')) c2 none
      := sorry.

  lemma exec_ifte1_not_None: ∀ s h c1 c2 e,
      ¬ exec (some (s, h))  (ifte e  c1  c2)  none ->
      eval e s = some tt ->
      ¬ exec (some (s, h)) c1  none
      := sorry.

  lemma exec_ifte2_not_None: ∀ s h c1 c2 e,
      ¬ exec (some (s, h))  (ifte e  c1  c2)  none ->
      eval e s = some ff ->
      ¬ exec (some (s, h)) c2  none
      := sorry.

  lemma exec_while1_not_None: ∀ s h e c,
        ¬ exec (some (s, h)) (while e c) none ->
        eval e s = some tt ->
        ¬ exec (some (s, h)) c none
        := sorry.

  lemma exec_while2_not_None: ∀ s h e c s' h',
        ¬ exec (some (s, h)) (while e c) none ->
        eval e s = some tt ->
        exec (some (s, h)) c (some (s', h')) ->
      ¬ exec (some (s', h')) (while e c)  none
      := sorry.

  lemma wp_semantics_sound: ∀ c Q,
      {{wp_semantics c Q}} c {{Q}} := sorry.

  lemma semax_complete : ∀ P Q c,
      semax' P c Q -> {{ P }} c {{ Q }} := sorry.

  def semax_alternative (P:Assert) (c:cmd) (Q:Assert) : Prop :=
      ∀ s h, P s h ->
        (∀ s' h', exec (some (s, h))  c  (some (s', h')) -> (Q s' h')).

  lemma semax_sound_alternative : ∀ P Q c,
    {{ P }} c {{ Q }} -> semax_alternative P c Q := sorry.

  /- Derived reynolds' axioms-/
  lemma semax_lookup_backwards:
    ∀{α: TypeDecl} (x : Var α) (e: Expr (gPtr α)) (P: Assert),
      {{ λ s h, ∃ e0, (e ↦ e0 ∗ (e ↦ e0 ⊸ update_store2 x e0 P)) s h }}
       (x ↩ e) {{ P }} := sorry.

  lemma semax_lookup_backwards_alternative :
    ∀{α: TypeDecl} (x : Var ( α)) (e: Expr (gPtr α)) (P: Assert) (e0: Expr α),
      {{ ((e ↦ e0) ∗ ((e ↦ e0) ⊸ (update_store2 x e0 P))) }} (x ↩ e) {{ P }}
      := sorry.

  lemma semax_mutation_local: ∀{α: TypeDecl} (x : Expr (gPtr α)) v v',
        {{ (x ↦ v) }} (x ≪ v') {{ (x ↦ v') }} := sorry.

  /-
   - Frame rule
   -/

  /-
   - Get list of variables that are modified by a program
   -/
  def modified_cmd_var: cmd → list (Σ α: TypeDecl, Var α)
    | skip              := list.nil
    | (assign x e)      := [⟨_, x⟩]
    | (lookup x e)      := [⟨_, x⟩]
    | (mutation e f)    := list.nil
    | (seq c1 c2)       := modified_cmd_var c1 ++ modified_cmd_var c2
    | (ifte a c1 c2)    := modified_cmd_var c1 ++ modified_cmd_var c2
    | (while a c1)      := modified_cmd_var c1
    | (declare x)       := [⟨_, x⟩]
    | (new x)           := [⟨_, x⟩]
    | (call _ _ _ vars) := vars

  lemma inde_seq : ∀ R (c d: cmd),
	  inde (modified_cmd_var (c ∣ d)) R ->
	  inde (modified_cmd_var c) R ∧ inde (modified_cmd_var d) R := sorry.

  lemma inde_ifte : ∀ R b c d,
      inde (modified_cmd_var (ifte b  c  d)) R →
      inde (modified_cmd_var c) R ∧ inde (modified_cmd_var d) R := sorry.

  lemma frame_rule : ∀ (P: Assert) (c: cmd) (Q: Assert),
      {{P}} c {{Q}} ->
      ∀ (R: Assert) ,
        (inde (modified_cmd_var c) R ->
          {{ (P ∗ R) }} c {{ (Q ∗ R) }}) := sorry.

  /-
  - More reynolds axioms
  -/

	lemma semax_mutation_global :
    ∀ {α: TypeDecl} (P: Assert) (e: Expr (gPtr α)) e',
	  {{((λ s' h', ∃ e'', (((e ↦ e'') s' h'))) ∗ P) }} (e ≪ e') {{((e ↦ e')∗P)}}
    := sorry.

  lemma semax_mutation_global_alternative :
    ∀ {α: TypeDecl} (P: Assert) (e: Expr (gPtr α)) e' e'',
      {{ ((e ↦ e'') ∗ P) }} (e ≪ e') {{ ((e ↦ e') ∗ P) }} := sorry.

  lemma semax_mutation_backwards :
    ∀ {α: TypeDecl} (P: Assert) (e: Expr (gPtr α)) e',
      {{λ s h, ∃ e'', ((e ↦ e'')∗(e ↦ e' ⊸ P)) s h}} (e ≪ e') {{P}} := sorry.


	lemma semax_mutation_backwards_alternative :
   ∀ {α: TypeDecl} (P: Assert) (e: Expr (gPtr α)) e' e'',
	  {{ ((e ↦ e'') ∗ ((e ↦ e') ⊸ P)) }} (e ≪ e') {{ P }} := sorry.


end axiomatic_semantics
