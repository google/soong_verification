import seplog.f_assertions
import seplog.d_context
import soong_model.soong_model
import seplog.e_semantics_test

open cmd open Expr open TypeDecl open Val open Variant


def lib_to_module (l:Library): Val (gRef "Module") :=
  list_to_struct "Module" [
    ("name", ⟨_, pStr l.name⟩),
    ("PropertyError", ⟨_, pPtr gErr none⟩),
    ("ExtraVariants", ⟨_, pPtr (gRef "MutatorSet") none⟩)
  ]

  /-,
                  ("PropertyError",         gPtr gErr),
                  ("ExtraVariants",         gPtr (gRef "MutatorSet")),
                  ("SoCSpecific",           gBool),
                  ("vendor_available",      gPtr gBool),
                  ("DeviceSpecific",        gBool),
                  ("ProductSpecific",       gBool),
                  ("vndkdep",               gPtr $ gRef "Vndkdep"),
                  ("llndkHeadersDecorator", gBool),
                  ("llndkStubDecorator",    gBool),
                  ("moduleDirIsVendorPath", gBool),
                  ("isVndk",                gBool),
                  ("Ramdisk_available",     gBool),
                  ("installInRamdisk",      gBool),
                  ("Recovery_available",    gBool),
                  ("installInRecovery",     gBool),
                  ("HasVendorVariant",      gBool),
                  ("boardVndkVersion",      gStr),
                  ("productVndkVersion",    gStr),
                  ("boardSdkVersion",       gStr),
                  ("PropertyError",         gPtr gErr)
    )]-/

/-
 - Given a library, create an instance of a "Module" in Go and assert that is
 - the callee of the ImageMutatorBegin.
 -/
def imb_precondition (l: Library): Assert :=
  (getvar mptr) ↦ (const $ lib_to_module l)

--------------------------------------------------------------------------------
/-
 - Variants correspond to attributes of MutatorSet
 -/
def to_key: Variant → string
 | core             := "core"
 | vendor_platform  := "vendor_platform"
 | vendor_board     := "vendor_board"
 | product_platform := "product_platform"
 | product_product  := "product_product"
 | ramdisk          := "ramdisk"
 | recovery         := "recovery"

/-
 - The ptr value in MutatorSet must point to a truth value that is the same as
 - whether or not the corresponding variant is in `vars`, for all variants.
 -/
def check_mutator_set (h: Heap) (vars: option (finset Variant))
                      (v: Val (gRef "MutatorSet")) : Prop :=
   ∀ i: Variant,
    vars.elim
    -- If `vars` is none, i.e. the program is expected to have an error
    (∃ err_ptr, v.get "PropertyError" = some ⟨_, pPtr gErr (some err_ptr)⟩)
    -- If `vars` is `some vars'`
    (λ vars',
      ∃ bool_ptr, (v.get (to_key i) = some ⟨_, pPtr gBool (some bool_ptr)⟩)
        ∧ ∃ boolval, (h.lookup ⟨bool_ptr⟩ = some (pBool boolval)
          ∧ boolval = (i ∈ vars'))))

/-
 - Given a library, map it to the correct variants and then create a
 - "MutatorSet" object and assert that is in the callee's ExtraVariants field.
 -/
def imb_postcondition (l: Library): Assert := λ s h,

  ∃ lib_ptr, val2loc (eval (getvar mptr) s) = some lib_ptr
    ∧ (∃ lib_val: Val (gRef "Module"),
      h.lookup lib_ptr = some lib_val
        ∧ (
          ∃ var_ptr, lib_val.get "ExtraVariants" = some ⟨_, (pInt var_ptr)⟩
            ∧ (
              ∃ v: Val (gRef "MutatorSet"), h.lookup ⟨var_ptr⟩ = some v
                ∧ (
                    check_mutator_set h (libary_to_variant l) v
                  )
              )
          )
      )
