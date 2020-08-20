import seplog.g_frame_rule

section weakest_preconditions
  open cmd open TypeDecl

  /-
   - An almost duplicate type for specifying programs, except we are allowed to
   - specify an invariant for while loops.
   -/
  inductive cmd' : Type
    | skip': cmd'
    | assign_var_e' {α: TypeDecl}: Var α → Expr α → cmd'
    | assign_var_deref' {α: TypeDecl}: Var α → Expr (gPtr α) → cmd'
    | assign_deref_expr' {α: TypeDecl}: Expr (gPtr α) → Expr α → cmd'
    | while' : Expr gBool → Assert → cmd' → cmd'
    | seq' : cmd' → cmd' → cmd'
    | ifte' : Expr gBool → cmd' → cmd' → cmd'.

  open cmd'

  /-
   - Project this new kind of program onto the old kind by discarding the
   - additional invariants specified.
   -/
	def proj_cmd : cmd' → cmd
    | skip' := skip
    | (assign_var_e' x e) := x ⇐ e
    | (assign_var_deref' x e) := x ↩ e
    | (assign_deref_expr' e f) := e ≪ f
    | (while' b Q c'')  := while b (proj_cmd c'')
    | (seq' c1 c2) := ((proj_cmd c1) ∣ (proj_cmd c2))
    | (ifte' b c1 c2) := (ifte b  (proj_cmd c1) (proj_cmd c2))

  /-
   - compute the weakest precondition under the assumption that
   -	while loops are annotated with invariants
   -/
	def wp: cmd' → Assert → Assert
	    | skip' P := P
	    | (assign_var_e' x e) P := update_store2 x e P
	    | (assign_var_deref' x e) P :=
	      λ s h, ∃ e0, ((e ↦ e0) ∗ ((e ↦ e0) ⊸ (update_store2 x e0 P))) s h
	    | (assign_deref_expr' e f) P :=
	      λ s h, ∃ x, (((e ↦ x) ∗ ((e ↦ f) ⊸ P)) s h)
	    | (while' b Q c') P := Q
	    | (seq' c1 c2) P := wp c1 (wp c2 P)
	    | (ifte' b c1 c2) P := (λ s h,
	      ( eval b s = some tt → (wp c1 P) s h) ∧
	      ( eval b s = some ff → (wp c2 P) s h))
        -- if fails?


  /-
   - Simplified version which ignores while loops and method calls
   - Although this could never be complete, it should be provably sound.
   -/
	def wp_appx: cmd → Assert → Assert
    | skip P := P
    | (assign x e) P := update_store2 x e P
    | (lookup x e) P :=
      λ s h, ∃ e0, ((e ↦ e0) ∗ ((e ↦ e0) ⊸ (update_store2 x e0 P))) s h
    | (mutation e f) P :=
      λ s h, ∃ x, (((e ↦ x) ∗ ((e ↦ f) ⊸ P)) s h)
    | (while _ _) _ := sorry -- complicated / not needed for `ImageMutatorBegin`
    | (seq c1 c2) P := wp_appx c1 (wp_appx c2 P)
    | (ifte b c1 c2) P := (λ s h,
      ( eval b s = some tt → (wp_appx c1 P) s h) ∧
      ( eval b s = some ff → (wp_appx c2 P) s h))
      -- if eval b s = none, then weakest precondition is ⊥ which implies
      -- anything. We don't need to explicitly treat this case.

    | (call _ _ _ _) _ := sorry -- complicated / not needed for I.M.B.
    | (declare _) P := sorry -- TODO implement
    | (new  _) P    := sorry -- TODO implement

  /-
   - This is a placeholder theorem, since it can't actually be proved due to
   - the `sorry`s in `wp_appx`.
   - It should be valid for programs that don't involve `while` or `call` though
   -/
	def wp_appx_sound_complete: ∀ c P Q, {{ P }} c {{ Q }} ↔ (P ⟹ wp_appx c Q)
   := sorry

end weakest_preconditions
