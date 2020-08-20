import seplog.h_weakest_preconditions
import seplog.f_assertions_test

/-
 - Proof that for any input, the running of the `ImageMutatorBegin` program
 - behaves exactly as `library_to_variant` behaves.
 -/
def imb_meets_spec: ∀ lib: Library,
  {{ imb_precondition lib  }} imb {{  imb_postcondition lib  }} := begin
    -- Translate into logic problem
    intros lib,
    rw wp_appx_sound_complete,
    unfold a_entails,
    intros s h pre,
    -- Inspect precondition
    unfold imb_precondition at pre,
    --unfold lib_to_module at pre,
    unfold mapsto at pre,
    rcases pre with ⟨adr, v, h_mptr, ⟨h_v, h_heq⟩⟩,
    subst h_heq,

    sorry,



end